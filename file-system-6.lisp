(in-package "ACL2")

;  file-system-6.lisp                                  Mihir Mehta

; Here we build on model 4 to add a file allocation table. We follow exactly
; the allocation strategy laid out in model 4. To allow this to happen, we must
; set our cluster size to 1 sector, and our sector size to 8 bytes. This is
; based on every character in ACL2 being a byte.

(include-book "file-system-4")
(include-book "centaur/fty/top" :dir :system)

(defund fat32-entry-p (x)
  (declare (xargs :guard t))
  (Unsigned-byte-p 32 x))

;; 0 is chosen as the default value based on this comment from Microsoft's FAT
;; overview:
;; The only time that the high 4 bits of FAT32 FAT entries should ever be
;; changed is when the volume is formatted, at which time the whole 32-bit FAT
;; entry should be zeroed, including the high 4 bits.
(defund fat32-entry-fix (x)
  (declare (xargs :guard t))
  (if (fat32-entry-p x)
      x 0))

(in-theory (enable fat32-entry-p fat32-entry-fix))

(fty::deffixtype fat32-entry
                 :pred   fat32-entry-p
                 :fix    fat32-entry-fix
                 :equiv  fat32-entry-equiv
                 :define t
                 :forward t
                 )

(fty::deflist fat32-entry-list :elt-type fat32-entry-p :true-listp t)

(in-theory (disable fat32-entry-p fat32-entry-fix))

;; question: if fat entries are 28 bits long, then how is the maximum size
;; determined to be 4 GB?
(defund l6-regular-file-entry-p (entry)
  (declare (xargs :guard t))
  (and (consp entry)
       ;; fat entries are effectively 28 bits long
       (unsigned-byte-p 28 (car entry))
       (natp (cdr entry))
       (feasible-file-length-p (len (car entry)) (cdr entry))))

(defund l6-regular-file-first-cluster (entry)
  (declare (xargs :guard (l6-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l6-regular-file-entry-p)))))
  (car entry))

(defund l6-regular-file-length (entry)
  (declare (xargs :guard (l6-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l6-regular-file-entry-p)))))
  (cdr entry))

; This function defines a valid filesystem. It's an alist where all the cars
; are symbols and all the cdrs are either further filesystems or regular files.
(defun l6-fs-p (fs)
  (declare (xargs :guard t))
  (if (atom fs)
      (null fs)
    (and (let ((directory-or-file-entry (car fs)))
           (if (atom directory-or-file-entry)
               nil
             (let ((name (car directory-or-file-entry))
                   (entry (cdr directory-or-file-entry)))
               (and (symbolp name)
                    (or (l6-regular-file-entry-p entry)
                        (l6-fs-p entry))))))
         (l6-fs-p (cdr fs)))))

(defthm alistp-l6-fs-p
  (implies (l6-fs-p fs)
           (alistp fs)))

(defthm l6-fs-p-assoc
  (implies (and (l6-fs-p fs)
                (consp (assoc-equal name fs))
                (not (l6-regular-file-entry-p (cdr (assoc-equal name fs)))))
           (l6-fs-p (cdr (assoc-equal name fs)))))

;; taken from page 18 of the fat overview - the constant 268435448 is written
;; out as 0xFFFFFF8 therein
(defund l6-is-eof (fat-content)
  (>= fat-content 268435448))

;; we have what we need to define a disk traversal to get the contents of the
;; file

;; let's define it as an operation to get an index list

;; the trouble with doing it "directly" is that one cannot prove termination
;; because an arbitrary file allocation table may have loops in the way entries
;; point to each other

;; thus, we are obliged to define a function which always terminates, and in
;; the sane case returns the list we want

(defund
  masked-set-difference
  (fa-table index-list)
  (if (atom fa-table)
      0
    (+ (masked-set-difference (cdr fa-table)
                              index-list)
       (if (member (logand (car fa-table) (- (ash 1 28) 1))
                   index-list)
           0 1))))

(in-theory (e/d (masked-set-difference) (ash)))

(defthm
  l6-build-index-list-measure-lemma-1
  (implies (and (member-equal next-cluster fa-table)
                (not (member-equal (logand next-cluster (- (ash 1 28) 1))
                                   acc)))
           (< (masked-set-difference fa-table
                                     (cons (logand next-cluster (- (ash 1 28) 1))
                                           acc))
              (masked-set-difference fa-table acc)))
  :rule-classes (:rewrite :linear))

(defun
  l6-build-index-list
  (fa-table masked-current-cluster acc)
  (declare
   (xargs
    :measure (masked-set-difference fa-table acc)
    :hints
    (("subgoal 1'"
      :in-theory (disable l6-build-index-list-measure-lemma-1)
      :use
      (:instance
       l6-build-index-list-measure-lemma-1
       (next-cluster (nth masked-current-cluster fa-table)))))))
  (if
   (or (< masked-current-cluster 2)
       (>= masked-current-cluster (len fa-table)))
   (reverse acc)
   (let
    ((masked-next-cluster
      (logand (nth masked-current-cluster fa-table)
              (- (ash 1 28) 1))))
    (if (or (l6-is-eof masked-next-cluster)
            (member masked-next-cluster acc))
        (reverse acc)
        (l6-build-index-list fa-table masked-next-cluster
                             (cons masked-next-cluster acc))))))

(in-theory (e/d (ash) (masked-set-difference)))
