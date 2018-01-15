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
  (unsigned-byte-p 32 x))

(defund fat32-masked-entry-p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 28 x))

;; 0 is chosen as the default value based on this comment from Microsoft's FAT
;; overview:
;; The only time that the high 4 bits of FAT32 FAT entries should ever be
;; changed is when the volume is formatted, at which time the whole 32-bit FAT
;; entry should be zeroed, including the high 4 bits.
(defund fat32-entry-fix (x)
  (declare (xargs :guard t))
  (if (fat32-entry-p x)
      x 0))

(defund fat32-masked-entry-fix (x)
  (declare (xargs :guard t))
  (if (fat32-masked-entry-p x)
      x 0))

(in-theory (enable fat32-entry-p fat32-entry-fix fat32-masked-entry-p fat32-masked-entry-fix))

;; Use a mask to take the low 28 bits.
(defund fat32-entry-mask (x)
  (declare (xargs :guard (fat32-entry-p x)))
  (logand x (- (ash 1 28) 1)))

(defthm
  fat32-entry-mask-correctness-1
  (fat32-masked-entry-p (fat32-entry-mask x))
  :hints (("goal" :in-theory (e/d (fat32-entry-mask fat32-masked-entry-p)
                                  (unsigned-byte-p logand-ash-lemma-1))
           :use (:instance logand-ash-lemma-1 (c 28)
                           (i x)))))

(fty::deffixtype fat32-entry
                 :pred   fat32-entry-p
                 :fix    fat32-entry-fix
                 :equiv  fat32-entry-equiv
                 :define t
                 :forward t
                 )

(fty::deffixtype fat32-masked-entry
                 :pred   fat32-masked-entry-p
                 :fix    fat32-masked-entry-fix
                 :equiv  fat32-masked-entry-equiv
                 :define t
                 :forward t
                 )

(fty::deflist fat32-entry-list :elt-type fat32-entry-p :true-listp t)

(fty::deflist fat32-masked-entry-list :elt-type fat32-masked-entry-p :true-listp t)

(defthm nat-listp-if-fat32-masked-entry-list-p
  (implies (fat32-masked-entry-list-p x)
           (nat-listp x))
  :rule-classes (:forward-chaining))

(in-theory (disable fat32-entry-p fat32-entry-fix fat32-masked-entry-p fat32-masked-entry-fix))

(defthm member-of-fat32-entry-list-p
  (implies (and (member-equal x lst)
                (fat32-entry-list-p lst))
           (fat32-entry-p x)))

;; question: if fat entries are 28 bits long, then how is the maximum size
;; determined to be 4 GB?
;; also, how are we gonna do this without a feasible length restriction?
(defund l6-regular-file-entry-p (entry)
  (declare (xargs :guard t))
  (and (consp entry)
       ;; fat entries are effectively 28 bits long
       (fat32-masked-entry-p (car entry))
       (natp (cdr entry))))

(defund l6-regular-file-first-cluster (entry)
  (declare (xargs :guard (l6-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l6-regular-file-entry-p)))))
  (car entry))

(defund l6-regular-file-length (entry)
  (declare (xargs :guard (l6-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l6-regular-file-entry-p)))))
  (cdr entry))

(defthm
  l6-regular-file-entry-p-correctness-1
  (implies (l6-regular-file-entry-p entry)
           (and (fat32-masked-entry-p (l6-regular-file-first-cluster entry))
                (natp (l6-regular-file-length entry))))
  :hints (("goal" :in-theory (enable l6-regular-file-entry-p
                                     l6-regular-file-first-cluster
                                     l6-regular-file-length))))

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
  (declare (xargs :guard (fat32-masked-entry-p fat-content)
                  :guard-hints (("Goal'" :in-theory (enable fat32-masked-entry-p)))))
  (>= fat-content 268435448))

;; we have what we need to define a disk traversal to get the contents of the
;; file

;; let's define it as an operation to get an index list

;; the trouble with doing it "directly" is that one cannot prove termination
;; because an arbitrary file allocation table may have loops in the way entries
;; point to each other

;; thus, we are obliged to define a function which always terminates, and in
;; the sane case returns the list we want

(encapsulate
  ()

  (local
   (defun
       masked-set-difference
       (fa-table index-list)
     (if (atom fa-table)
         0
       (+ (masked-set-difference (cdr fa-table)
                                 index-list)
          (if (member (fat32-entry-mask (car fa-table))
                      index-list)
              0 1)))))

  (local
   (defthm
     l6-build-index-list-measure-lemma-1
     (implies (and (member-equal next-cluster fa-table)
                   (not (member-equal (fat32-entry-mask next-cluster)
                                      acc)))
              (< (masked-set-difference fa-table
                                        (cons (fat32-entry-mask next-cluster)
                                              acc))
                 (masked-set-difference fa-table acc)))
     :rule-classes (:linear)))

  (local
   (defun
       l6-build-index-list
       (fa-table masked-current-cluster acc)
     (declare
      (xargs
       :guard (and (fat32-entry-list-p fa-table)
                   (fat32-masked-entry-p masked-current-cluster)
                   (true-listp acc))
       :guard-hints
       (("subgoal 4" :in-theory (enable fat32-masked-entry-p))
        ("subgoal 2'" :in-theory (enable fat32-masked-entry-p))
        ("subgoal 1'"
         :in-theory (disable member-of-fat32-entry-list-p)
         :use
         (:instance member-of-fat32-entry-list-p
                    (lst fa-table)
                    (x (nth masked-current-cluster fa-table)))))
       :measure (masked-set-difference fa-table acc)
       :hints
       (("subgoal 1'"
         :in-theory (disable l6-build-index-list-measure-lemma-1)
         :use
         (:instance
          l6-build-index-list-measure-lemma-1
          (next-cluster
           (nth masked-current-cluster fa-table)))))))
     (if
         (or (< masked-current-cluster 2)
             (>= masked-current-cluster (len fa-table)))
         (reverse acc)
       (let
           ((masked-next-cluster
             (fat32-entry-mask
              (nth masked-current-cluster fa-table))))
         (if
             (or (l6-is-eof masked-next-cluster)
                 (member masked-next-cluster acc))
             (reverse acc)
           (l6-build-index-list fa-table masked-next-cluster
                                (cons masked-next-cluster acc)))))))

  (defun
    l6-build-index-list
    (fa-table masked-current-cluster acc)
    (declare
     (xargs
      :guard (and (fat32-entry-list-p fa-table)
                  (fat32-masked-entry-p masked-current-cluster)
                  (true-listp acc))
      :guard-hints
      (("subgoal 4" :in-theory (enable fat32-masked-entry-p))
       ("subgoal 2'" :in-theory (enable fat32-masked-entry-p))
       ("subgoal 1'"
        :in-theory (disable member-of-fat32-entry-list-p)
        :use
        (:instance member-of-fat32-entry-list-p
                   (lst fa-table)
                   (x (nth masked-current-cluster fa-table)))))
      :measure (:? fa-table acc)
      :hints
      (("subgoal 1'"
        :in-theory (disable l6-build-index-list-measure-lemma-1)
        :use
        (:instance
         l6-build-index-list-measure-lemma-1
         (next-cluster
          (nth masked-current-cluster fa-table)))))))
    (if
     (or (< masked-current-cluster 2)
         (>= masked-current-cluster (len fa-table)))
     (reverse acc)
     (let
      ((masked-next-cluster
        (fat32-entry-mask
         (nth masked-current-cluster fa-table))))
      (if
       (or (l6-is-eof masked-next-cluster)
           (member masked-next-cluster acc))
       (reverse acc)
       (l6-build-index-list fa-table masked-next-cluster
                            (cons masked-next-cluster acc)))))))

(defthm
  l6-build-index-list-correctness-1
  (implies
   (fat32-masked-entry-list-p acc)
   (fat32-masked-entry-list-p
    (l6-build-index-list fa-table masked-current-cluster acc))))

(defund find-n-free-clusters-helper (fa-table n start)
  (if (or (atom fa-table) (zp n))
      nil
    (if (not (equal (fat32-entry-mask (car fa-table)) 0))
        ;; this block is taken
        (find-n-free-clusters-helper (cdr fa-table) n (+ start 1))
      ;; this block isn't taken
      (cons start (find-n-free-clusters-helper (cdr fa-table) (- n 1) (+ start 1))))))

(defund find-n-free-clusters (fa-table n)
  ;; the first 2 clusters are excluded
  (find-n-free-clusters-helper (nthcdr 2 fa-table) n 2))

;; This function allows a file or directory to be found in a filesystem given a
;; path.
(defun l6-stat (hns fs disk)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l6-fs-p fs)
                              (block-listp disk))))
  (if (atom hns)
      fs
    (if (atom fs)
        nil
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            nil
          (if (l6-regular-file-entry-p (cdr sd))
              (and (null (cdr hns))
                   (cdr sd))
            (l6-stat (cdr hns) (cdr sd) disk)))))))

(defthm l6-rdchs-guard-lemma-1
  (implies (and (block-listp lst)
                (member-equal x lst))
           (and (character-listp x)
                (equal (len x) *blocksize*))))

;; This function finds a text file given its path and reads a segment of
;; that text file.
(defun l6-rdchs (hns fs disk fa-table start n)
  (declare (xargs :guard-debug t
                  :guard (and (symbol-listp hns)
                              (l6-fs-p fs)
                              (natp start)
                              (natp n)
                              (block-listp disk)
                              (fat32-entry-list-p fa-table))
                  :guard-hints (("SubGoal 3" :in-theory (e/d (fat32-masked-entry-p)
                                                         (l6-regular-file-entry-p-correctness-1))
                                 :use (:instance
                                       l6-regular-file-entry-p-correctness-1
                                       (entry (L6-STAT HNS FS DISK))))
                                ("SubGoal 2.8" :in-theory (e/d (fat32-masked-entry-p)
                                                         (l6-regular-file-entry-p-correctness-1))
                                 :use (:instance
                                       l6-regular-file-entry-p-correctness-1
                                       (entry (L6-STAT HNS FS DISK))))
                                ("Subgoal 2.5" :in-theory (disable
                                                             l6-rdchs-guard-lemma-1
                                                             MEMBER-EQUAL-OF-NTH)
                                 :use ((:instance l6-rdchs-guard-lemma-1 (lst disk) (x (NTH (L6-REGULAR-FILE-FIRST-CLUSTER (L6-STAT HNS FS DISK))
                        DISK))) (:instance MEMBER-EQUAL-OF-NTH (n (L6-REGULAR-FILE-FIRST-CLUSTER (L6-STAT HNS FS DISK))) (l DISK)))))))
  (let ((file (l6-stat hns fs disk)))
    (if (not (l6-regular-file-entry-p file))
        nil
      (let* ((first-cluster (l6-regular-file-first-cluster file))
             (index-list (if (< first-cluster 2)
                             nil
                           (list* first-cluster (l6-build-index-list fa-table first-cluster nil))))
             (file-text
              (coerce
               (unmake-blocks (fetch-blocks-by-indices
                               disk
                               index-list)
                              (l6-regular-file-length file))
               'string))
             (file-length (length file-text))
             (end (+ start n)))
        (if (< file-length end)
            nil
          (subseq file-text start (+ start n)))))))
