(in-package "ACL2")

;  file-system-6.lisp                                  Mihir Mehta

; Here we build on model 4 to add a file allocation table. We follow exactly
; the allocation strategy laid out in model 4. To allow this to happen, we must
; set our cluster size to 1 sector, and our sector size to 8 bytes. This is
; based on every character in ACL2 being a byte.

(include-book "file-system-4")
(include-book "centaur/fty/top" :dir :system)

(defconst *expt-2-28* (expt 2 28))

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
  :rule-classes (:forward-chaining :rewrite))

(in-theory (disable fat32-entry-p fat32-entry-fix fat32-masked-entry-p fat32-masked-entry-fix))

(defthm member-of-fat32-entry-list
  (implies (and (member-equal x lst)
                (fat32-entry-list-p lst))
           (fat32-entry-p x)))

(defthm set-indices-in-fa-table-guard-lemma-1
  (implies (and (natp key)
                (< key (len l))
                (fat32-entry-list-p l)
                (fat32-entry-p val))
           (fat32-entry-list-p (update-nth key val l))))

(defthm set-indices-in-fa-table-guard-lemma-2
  (implies (fat32-entry-p x) (natp x))
  :hints (("goal" :in-theory (enable fat32-entry-p)))
  :rule-classes
  (:forward-chaining
   (:rewrite :corollary (implies (fat32-entry-p x)
                                 (integerp x)))))

(defthm set-indices-in-fa-table-guard-lemma-3
  (implies (and (fat32-entry-list-p l)
                (natp n)
                (< n (len l)))
           (fat32-entry-p (nth n l))))

(defund
  fat32-update-lower-28
  (entry masked-entry)
  (declare
   (xargs
    :guard-hints
    (("goal"
      :in-theory (enable fat32-entry-p fat32-masked-entry-p)))
    :guard (and (fat32-entry-p entry)
                (fat32-masked-entry-p masked-entry))))
  (logior (logand entry (- (ash 1 32) (ash 1 28)))
          masked-entry))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (defthm
    fat32-update-lower-28-correctness-1
    (implies
     (and (fat32-entry-p entry)
          (fat32-masked-entry-p masked-entry))
     (fat32-entry-p (fat32-update-lower-28 entry masked-entry)))
    :hints
    (("goal"
      :in-theory (e/d nil (unsigned-byte-p logand logior)
                      (fat32-entry-p fat32-masked-entry-p
                                     fat32-update-lower-28)))
     ("goal''" :in-theory (enable unsigned-byte-p)))))

(defun
  set-indices-in-fa-table
  (v index-list value-list)
  (declare
   (xargs :guard (and (fat32-entry-list-p v)
                      (nat-listp index-list)
                      (fat32-masked-entry-list-p value-list)
                      (equal (len index-list)
                             (len value-list)))))
  (if
   (atom index-list)
   v
   (let
    ((current-index (car index-list)))
    (if (or (not (natp current-index))
            (>= current-index (len v)))
        v
        (update-nth current-index
                    (fat32-update-lower-28 (nth current-index v)
                                           (car value-list))
                    v)))))

(defthm
  set-indices-in-fa-table-correctness-1
  (implies
   (and (fat32-entry-list-p v)
        (bounded-nat-listp index-list (len v))
        (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list)))
   (fat32-entry-list-p
    (set-indices-in-fa-table v index-list value-list))))

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
  (implies
   (l6-regular-file-entry-p entry)
   (and
    (fat32-masked-entry-p (l6-regular-file-first-cluster entry))
    (integerp (l6-regular-file-first-cluster entry))
    (>= (l6-regular-file-first-cluster entry)
        0)
    (< (l6-regular-file-first-cluster entry)
       *expt-2-28*)
    (integerp (l6-regular-file-length entry))
    (>= (l6-regular-file-length entry) 0)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (l6-regular-file-entry-p entry)
     (and (fat32-masked-entry-p
           (l6-regular-file-first-cluster entry))
          (integerp (l6-regular-file-first-cluster entry))
          (integerp (l6-regular-file-length entry)))))
   (:linear
    :corollary
    (implies (l6-regular-file-entry-p entry)
             (and (>= (l6-regular-file-first-cluster entry)
                      0)
                  (< (l6-regular-file-first-cluster entry)
                     *expt-2-28*)
                  (>= (l6-regular-file-length entry)
                      0)))))
  :hints
  (("goal" :in-theory (enable l6-regular-file-entry-p
                              l6-regular-file-first-cluster
                              l6-regular-file-length
                              fat32-masked-entry-p))))

(defund
  l6-make-regular-file
  (first-cluster length)
  (declare
   (xargs :guard (and (fat32-masked-entry-p first-cluster)
                      (natp length))))
  (cons first-cluster length))

(defthm
  l6-make-regular-file-correctness-1
  (implies (and (fat32-masked-entry-p first-cluster)
                (natp length))
           (l6-regular-file-entry-p
            (l6-make-regular-file first-cluster length)))
  :hints (("goal" :in-theory (enable l6-regular-file-entry-p
                                     l6-make-regular-file))))

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
         :in-theory (disable member-of-fat32-entry-list)
         :use
         (:instance member-of-fat32-entry-list
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
        :in-theory (disable member-of-fat32-entry-list)
        :use
        (:instance member-of-fat32-entry-list
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
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (natp n)
                              (natp start))))
  (if (or (atom fa-table) (zp n))
      nil
    (if (not (equal (fat32-entry-mask (car fa-table)) 0))
        ;; this block is taken
        (find-n-free-clusters-helper (cdr fa-table) n (+ start 1))
      ;; this block isn't taken
      (cons start (find-n-free-clusters-helper (cdr fa-table) (- n 1) (+ start 1))))))

(defthmd
  find-n-free-clusters-helper-correctness-1
  (implies (and (fat32-entry-list-p fa-table)
                (natp n)
                (natp start)
                (equal b (+ start (len fa-table))))
           (bounded-nat-listp
            (find-n-free-clusters-helper fa-table n start)
            b))
  :hints
  (("goal'" :in-theory (enable find-n-free-clusters-helper))))

(defthm find-n-free-clusters-guard-lemma-1
  (implies (fat32-entry-list-p l)
           (fat32-entry-list-p (nthcdr n l))))

(defund find-n-free-clusters (fa-table n)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (natp n))))
  ;; the first 2 clusters are excluded
  (find-n-free-clusters-helper (nthcdr 2 fa-table) n 2))

(defthm
  find-n-free-clusters-correctness-1
  (implies (and (fat32-entry-list-p fa-table)
                (natp n)
                (equal b (len fa-table))
                (>= (len fa-table) 2))
           (bounded-nat-listp (find-n-free-clusters fa-table n)
                              b))
  :hints
  (("goal"
    :in-theory (enable find-n-free-clusters)
    :use ((:instance find-n-free-clusters-helper-correctness-1
                    (start 2)
                    (fa-table (nthcdr 2 fa-table))
                    (b (len fa-table)))))))

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
  (implies (and (member-equal x lst)
                (block-listp lst))
           (and (character-listp x)
                (equal (len x) *blocksize*)))
  :rule-classes (:forward-chaining))

;; a note on why this function needs to exist and why it should not replace
;; unmake-blocks
;; unmake-blocks has been used thus far in contexts where the length of the
;; file can be checked to line up with the contents of the file (with only the
;; assumption that the disk satisfies block-listp, nothing more - this is
;; what's checked by feasible-file-length-p)
;; i could have replaced the unmake-blocks function with this one, given that
;; its guard is less restrictive (these clauses are a strict subset of those
;; clauses)
;; i opted not to do so because, in my opinion, the guard verification that
;; takes place with the more restrictive guard is valuable - it shows that
;; we're not leaving room for more than (*blocksize* - 1) characters of junk
;; being added anywhere, as long as we can still verify these things with
;; "local" checks (by which i mean, checks that don't refer too much to the
;; disk, which i consider "not local" for these purposes)
(defun
  unmake-blocks-without-feasibility
  (blocks n)
  (declare (xargs :guard (and (block-listp blocks) (natp n))))
  (mbe
   :exec
   (if
    (atom blocks)
    (make-character-list (take n nil))
    (if
     (< n *blocksize*)
     (take n (car blocks))
     (binary-append
      (car blocks)
      (unmake-blocks-without-feasibility (cdr blocks)
                                         (- n *blocksize*)))))
   :logic
   (if
    (atom blocks)
    (make-character-list (take n nil))
    (let ((head (make-character-list (car blocks))))
         (if (or (not (integerp n)) (< n (len head)))
             (take n head)
             (binary-append head
                            (unmake-blocks-without-feasibility
                             (cdr blocks)
                             (- n (len (car blocks))))))))))

(defthm unmake-blocks-without-feasibility-correctness-1
  (character-listp (unmake-blocks-without-feasibility blocks n)))

(defthm unmake-blocks-without-feasibility-correctness-2
  (equal (len (unmake-blocks-without-feasibility blocks n))
         (nfix n)))

(defthm
  unmake-without-feasibility-make-blocks
  (implies
   (and (character-listp text))
   (equal (unmake-blocks-without-feasibility (make-blocks text)
                                             (len text))
          text))
  :hints
  (("subgoal *1/3.2'"
    :in-theory (disable first-n-ac-of-make-character-list)
    :use (:instance first-n-ac-of-make-character-list
                    (i (len text))
                    (l (first-n-ac 8 text nil))
                    (ac nil)))
   ("subgoal *1/3.2'4'"
    :in-theory (disable take-more)
    :use (:instance take-more (i *blocksize*)
                    (l text)
                    (ac1 nil)
                    (ac2 nil)))))

(defund
  l6-file-index-list (file fa-table)
  (declare (xargs :guard (and (l6-regular-file-entry-p file)
                              (fat32-entry-list-p fa-table))))
  (let
      ((first-cluster (l6-regular-file-first-cluster file)))
    (if
        (or (< first-cluster 2) (>= first-cluster (len fa-table)))
        nil
      (list* first-cluster
             (l6-build-index-list fa-table first-cluster nil)))))

(defthm
  l6-file-index-list-correctness-1
  (implies (and (l6-regular-file-entry-p file)
                (fat32-entry-list-p fa-table))
           (fat32-masked-entry-list-p
            (l6-file-index-list file fa-table)))
  :hints (("goal" :in-theory (enable l6-file-index-list))))

;; This function finds a text file given its path and reads a segment of
;; that text file.
(defun
  l6-rdchs (hns fs disk fa-table start n)
  (declare
   (xargs
    :guard (and (symbol-listp hns)
                (l6-fs-p fs)
                (natp start)
                (natp n)
                (block-listp disk)
                (fat32-entry-list-p fa-table))
    :guard-hints
    (("subgoal 2.6"
      :in-theory (e/d (fat32-masked-entry-p)
                      (l6-regular-file-entry-p-correctness-1))
      :use (:instance l6-regular-file-entry-p-correctness-1
                      (entry (l6-stat hns fs disk))))
     ("subgoal 3"
      :in-theory (e/d (fat32-masked-entry-p)
                      (l6-regular-file-entry-p-correctness-1))
      :use (:instance l6-regular-file-entry-p-correctness-1
                      (entry (l6-stat hns fs disk)))))))
  (let
   ((file (l6-stat hns fs disk)))
   (if
    (not (l6-regular-file-entry-p file))
    nil
    (let*
     ((index-list
       (l6-file-index-list file fa-table))
      (file-text
       (coerce (unmake-blocks-without-feasibility
                (fetch-blocks-by-indices disk index-list)
                (l6-regular-file-length file))
               'string))
      (file-length (length file-text))
      (end (+ start n)))
     (if (< file-length end)
         nil
         (subseq file-text start (+ start n)))))))

; This function writes a specified text string to a specified position to a
; text file at a specified path.
(defun
    l6-wrchs
    (hns fs disk fa-table start text)
  (declare
   (xargs
    :guard (and (symbol-listp hns)
                (l6-fs-p fs)
                (natp start)
                (stringp text)
                (block-listp disk)
                (fat32-entry-list-p fa-table)
                (equal (len fa-table) (len disk))
                (<= (len disk) *expt-2-28*)
                (>= (len fa-table) 2))
    :guard-debug t
    :guard-hints
    (("goal" :in-theory (enable l6-file-index-list
                                l6-wrchs-guard-lemma-6))
     ("subgoal 3.4"
      :in-theory
      (disable l6-wrchs-guard-lemma-8
               (:rewrite l6-regular-file-entry-p-correctness-1))
      :use
      ((:instance
        l6-wrchs-guard-lemma-8
        (fa-table
         (update-nth
          (l6-regular-file-first-cluster
           (cdr (assoc-equal (car hns) fs)))
          (fat32-update-lower-28
           (nth (l6-regular-file-first-cluster
                 (cdr (assoc-equal (car hns) fs)))
                fa-table)
           0)
          fa-table))
        (n
         (len
          (make-blocks
           (insert-text
            (first-n-ac
             (l6-regular-file-length
              (cdr (assoc-equal (car hns) fs)))
             (nth (l6-regular-file-first-cluster
                   (cdr (assoc-equal (car hns) fs)))
                  disk)
             nil)
            start text)))))
       (:instance
        (:rewrite l6-regular-file-entry-p-correctness-1)
        (entry (cdr (assoc-equal (car hns) fs))))))
     ("subgoal 3.4.11"
      :in-theory (disable l6-wrchs-guard-lemma-6)
      :use
      (:instance
       l6-wrchs-guard-lemma-6
       (x
        (find-n-free-clusters
         (update-nth
          (l6-regular-file-first-cluster
           (cdr (assoc-equal (car hns) fs)))
          (fat32-update-lower-28
           (nth (l6-regular-file-first-cluster
                 (cdr (assoc-equal (car hns) fs)))
                fa-table)
           0)
          fa-table)
         (len
          (make-blocks
           (insert-text
            (first-n-ac
             (l6-regular-file-length
              (cdr (assoc-equal (car hns) fs)))
             (nth (l6-regular-file-first-cluster
                   (cdr (assoc-equal (car hns) fs)))
                  disk)
             nil)
            start text)))))))
     ("subgoal 3.3"
      :in-theory
      (disable l6-wrchs-guard-lemma-8
               (:rewrite l6-regular-file-entry-p-correctness-1)
               l6-wrchs-guard-lemma-3 l6-wrchs-guard-lemma-6)
      :use
      ((:instance
        l6-wrchs-guard-lemma-8
        (fa-table
         (update-nth
          (l6-regular-file-first-cluster
           (cdr (assoc-equal (car hns) fs)))
          (fat32-update-lower-28
           (nth (l6-regular-file-first-cluster
                 (cdr (assoc-equal (car hns) fs)))
                fa-table)
           0)
          fa-table))
        (n
         (len
          (make-blocks
           (insert-text
            (append
             (nth (l6-regular-file-first-cluster
                   (cdr (assoc-equal (car hns) fs)))
                  disk)
             (unmake-blocks-without-feasibility
              (fetch-blocks-by-indices
               disk
               (l6-build-index-list
                fa-table
                (l6-regular-file-first-cluster
                 (cdr (assoc-equal (car hns) fs)))
                nil))
              (- *blocksize*
                 (l6-regular-file-length
                  (cdr (assoc-equal (car hns) fs))))))
            start text)))))
       (:instance
        (:rewrite l6-regular-file-entry-p-correctness-1)
        (entry (cdr (assoc-equal (car hns) fs))))
       (:instance l6-wrchs-guard-lemma-3
                  (n (l6-regular-file-first-cluster
                      (cdr (assoc-equal (car hns) fs))))
                  (l disk))
       (:instance
        l6-wrchs-guard-lemma-6
        (x
         (find-n-free-clusters
          (update-nth
           (l6-regular-file-first-cluster
            (cdr (assoc-equal (car hns) fs)))
           (fat32-update-lower-28
            (nth (l6-regular-file-first-cluster
                  (cdr (assoc-equal (car hns) fs)))
                 fa-table)
            0)
           fa-table)
          (len
           (make-blocks
            (insert-text
             (append
              (nth (l6-regular-file-first-cluster
                    (cdr (assoc-equal (car hns) fs)))
                   disk)
              (unmake-blocks-without-feasibility
               (fetch-blocks-by-indices
                disk
                (l6-build-index-list
                 fa-table
                 (l6-regular-file-first-cluster
                  (cdr (assoc-equal (car hns) fs)))
                 nil))
               (- *blocksize*
                  (l6-regular-file-length
                   (cdr (assoc-equal (car hns) fs))))))
             start text)))))))))))
  (if (atom hns)
      (mv fs disk fa-table) ;; error - showed up at fs with no name  - so leave fs unchanged
    (if (atom fs)
        (mv nil disk fa-table) ;; error, so leave fs unchanged
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            (mv fs disk fa-table) ;; file-not-found error, so leave fs unchanged
          (if (l6-regular-file-entry-p (cdr sd))
              (if (cdr hns)
                  (mv (cons (cons (car sd) (cdr sd))
                            (delete-assoc (car hns) fs))
                      disk
                      fa-table) ;; error, so leave fs unchanged
                (let* ((old-indices
                        (l6-file-index-list (cdr sd) fa-table))
                       (old-text
                        (unmake-blocks-without-feasibility
                         (fetch-blocks-by-indices disk old-indices)
                         (l6-regular-file-length (cdr sd))))
                       (fa-table-after-free
                        (set-indices-in-fa-table
                         fa-table
                         old-indices
                         (make-list (len old-indices) :initial-element 0)))
                       (new-text (insert-text old-text start text))
                       (new-blocks (make-blocks new-text))
                       (new-indices
                        (find-n-free-clusters fa-table-after-free (len new-blocks))))
                  (if (not (equal (len new-indices) (len new-blocks)))
                      ;; we have an error because of insufficient disk space
                      ;; - so we leave the fs unchanged
                      (mv (cons (cons (car sd) (cdr sd))
                                (delete-assoc (car hns) fs))
                          disk
                          fa-table)
                    (if (consp new-indices)
                        (mv (cons (cons (car sd)
                                        (l6-make-regular-file
                                         (car new-indices)
                                         (len new-text)))
                                  (delete-assoc (car hns) fs))
                            (set-indices disk new-indices new-blocks)
                            (set-indices-in-fa-table fa-table-after-free
                                                     new-indices
                                                     (binary-append
                                                      (cdr new-indices)
                                                      ;; 0 is chosen for now but it has to
                                                      ;; be one of those end of file markers
                                                      (list 0))))
                      (mv (cons (cons (car sd)
                                      (l6-make-regular-file
                                       ;; 0 is chosen for now but it has to
                                       ;; be one of those end of file markers
                                       0
                                       (len new-text)))
                                (delete-assoc (car hns) fs))
                          disk
                          fa-table-after-free)))))
            (mv-let (new-contents new-disk new-fa-table)
              (l6-wrchs (cdr hns) (cdr sd) disk fa-table start text)
              (mv (cons (cons (car sd) new-contents)
                        (delete-assoc (car hns) fs))
                  new-disk
                  new-fa-table))))))))

(defthm
  l6-wrchs-guard-lemma-1
  (implies (fat32-masked-entry-p x)
           (natp x))
  :hints (("goal" :in-theory (enable fat32-masked-entry-p)))
  :rule-classes
  (:forward-chaining
   (:rewrite :corollary (implies (fat32-masked-entry-p x)
                                 (integerp x)))))

(defthm
  l6-wrchs-guard-lemma-2
  (implies (and (fat32-masked-entry-p val)
                (fat32-masked-entry-list-p ac))
           (fat32-masked-entry-list-p (make-list-ac n val ac))))

(defthm l6-wrchs-guard-lemma-3
  (implies (and (block-listp l)
                (natp n)
                (< n (len l)))
           (let ((x (nth n l)))
                (and (character-listp x)
                     (equal (len x) *blocksize*)))))

(defthm
  l6-wrchs-guard-lemma-4
  (implies
   (and
    (block-listp disk)
    (l6-fs-p fs)
    (symbolp name)
    (consp (assoc-equal name fs))
    (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
    (<
     (l6-regular-file-first-cluster (cdr (assoc-equal name fs)))
     (len disk)))
   (member-equal
    (nth
     (l6-regular-file-first-cluster (cdr (assoc-equal name fs)))
     disk)
    disk))
  :hints
  (("goal"
    :in-theory (disable l6-wrchs-guard-lemma-1)
    :use (:instance l6-wrchs-guard-lemma-1
                    (x (l6-regular-file-first-cluster
                        (cdr (assoc-equal name fs))))))))

;; this is daft, but worth a try
;; this should take care of  (EXTRA-INFO '(:GUARD (:BODY L6-WRCHS)) '(<
;; OLD-FIRST-CLUSTER 2))
(defthm
  l6-wrchs-guard-lemma-5
  (implies
   (and (l6-fs-p fs)
        (symbolp name)
        (consp fs)
        (consp (assoc-equal name fs))
        (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
        (<= 2
            (l6-regular-file-first-cluster
             (cdr (assoc-equal name fs)))))
   (rationalp (l6-regular-file-first-cluster
               (cdr (assoc-equal name fs))))))

(defthmd
  l6-wrchs-guard-lemma-6
  (equal (fat32-masked-entry-list-p x)
         (bounded-nat-listp x *expt-2-28*))
  :hints (("goal" :in-theory (enable fat32-masked-entry-p))))

(defthm
  l6-wrchs-guard-lemma-7
  (implies
   (and (<= 2 (len fa-table))
        (<= (len fa-table) *expt-2-28*)
        (fat32-entry-list-p fa-table)
        (stringp text)
        (integerp start)
        (<= 0 start)
        (l6-fs-p fs)
        (symbolp name)
        (consp fs)
        (consp (assoc-equal name fs))
        (l6-regular-file-entry-p (cdr (assoc-equal name fs))))
   (let
       ((found-clusters
         (find-n-free-clusters
          fa-table
          (len
           (make-blocks
            (insert-text
             (make-character-list
              (first-n-ac
               (l6-regular-file-length (cdr (assoc-equal name fs)))
               nil nil))
             start text))))))
     (implies
      (and
       (equal
        (len found-clusters)
        (len
         (make-blocks
          (insert-text
           (make-character-list
            (first-n-ac
             (l6-regular-file-length (cdr (assoc-equal name fs)))
             nil nil))
           start text))))
       (consp found-clusters))
      (and (bounded-nat-listp (cdr found-clusters)
                              *expt-2-28*)
           (fat32-masked-entry-p (car found-clusters))
           (nat-listp found-clusters)))))
  :hints
  (("goal"
    :in-theory (enable l6-wrchs-guard-lemma-6)
    :use
    (:instance
     bounded-nat-listp-correctness-5
     (x (len fa-table))
     (y *expt-2-28*)
     (l
      (find-n-free-clusters
       fa-table
       (len
        (make-blocks
         (insert-text
          (make-character-list
           (first-n-ac
            (l6-regular-file-length (cdr (assoc-equal name fs)))
            nil nil))
          start text)))))))))

(defthm
  l6-wrchs-guard-lemma-8
  (implies (and (fat32-entry-list-p fa-table)
                (natp n)
                (<= (len fa-table) *expt-2-28*)
                (>= (len fa-table) 2))
           (bounded-nat-listp (find-n-free-clusters fa-table n)
                              *expt-2-28*))
  :hints
  (("goal" :use (:instance bounded-nat-listp-correctness-5
                           (l (find-n-free-clusters fa-table n))
                           (x (len fa-table))
                           (y *expt-2-28*)))))

(defthm
  l6-wrchs-guard-lemma-9
  (not (find-n-free-clusters fa-table 0))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters
                              find-n-free-clusters-helper))))

(defthm
  l6-wrchs-guard-lemma-10
  (implies
   (and
    (<= 2 (len disk))
    (<= (len disk) *expt-2-28*)
    (equal (len fa-table) (len disk))
    (fat32-entry-list-p fa-table)
    (block-listp disk)
    (l6-fs-p fs)
    (symbolp name)
    (consp (assoc-equal name fs))
    (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
    (<= 2
        (l6-regular-file-first-cluster
         (cdr (assoc-equal name fs))))
    (<
     (l6-regular-file-first-cluster (cdr (assoc-equal name fs)))
     (len disk)))
   (equal (len (nth (l6-regular-file-first-cluster
                     (cdr (assoc-equal name fs)))
                    disk))
          *blocksize*))
  :hints
  (("goal" :in-theory (disable l6-wrchs-guard-lemma-3)
    :use (:instance l6-wrchs-guard-lemma-3
                    (n (l6-regular-file-first-cluster
                        (cdr (assoc-equal name fs))))
                    (l disk)))))

(defun l6-create
    (hns fs disk fa-table text)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l6-fs-p fs)
                              (stringp text)
                              (block-listp disk)
                              (fat32-entry-list-p fa-table)
                              (equal (len fa-table) (len disk))
                              (<= (len disk) *expt-2-28*)
                              (>= (len fa-table) 2))
                  :guard-hints
                  (("subgoal 1'"
                    :in-theory
                    (disable l6-wrchs-guard-lemma-8)
                    :use
                    ((:instance
                      l6-wrchs-guard-lemma-8
                      (n (len (make-blocks (explode text))))))))))
  (if (atom hns)
      (mv fs disk fa-table) ;; error - showed up at fs with no name  - so leave fs unchanged
    (let ((sd (assoc (car hns) fs)))
      (if (atom sd)
          (if (atom (cdr hns))
              (let* ((blocks (make-blocks (coerce text 'list)))
                     (indices (find-n-free-clusters fa-table (len blocks))))
                (if (not (equal (len indices) (len blocks)))
                    ;; we have an error because of insufficient disk space
                    ;; - so we leave the fs unchanged
                    (mv sd disk fa-table)
                  (if (consp indices)
                      (mv (cons (cons (car hns)
                                      (l6-make-regular-file
                                       (car indices)
                                       (length text)))
                                fs)
                          (set-indices disk indices blocks)
                          (set-indices-in-fa-table fa-table
                                                   indices
                                                   (binary-append
                                                    (cdr indices)
                                                    ;; 0 is chosen for now but it has to
                                                    ;; be one of those end of file markers
                                                    (list 0))))
                    (mv (cons (cons (car hns)
                                    (cons indices
                                          (length text)))
                              fs)
                        disk
                        fa-table))))
            (mv-let (new-fs new-disk new-fa-table)
              (l6-create (cdr hns) nil disk fa-table text)
              (mv (cons (cons (car hns) new-fs) fs) new-disk new-fa-table)))
        (let ((contents (cdr sd)))
          (if (l6-regular-file-entry-p contents)
              (mv (cons (cons (car sd) contents) ;; file already exists, so leave fs unchanged
                        (delete-assoc (car hns) fs))
                  disk
                  fa-table)
            (mv-let (new-fs new-disk new-fa-table)
              (l6-create (cdr hns) contents disk fa-table text)
              (mv (cons (cons (car sd)
                              new-fs)
                        (delete-assoc (car hns) fs))
                  new-disk
                  new-fa-table)))
          )))))

; This function deletes a file or directory given its path.
(defun
    l6-unlink (hns fs fa-table)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l6-fs-p fs)
                              (fat32-entry-list-p fa-table)
                              (<= (len fa-table) *expt-2-28*)
                              (>= (len fa-table) 2))))
  (if
      (atom hns)
      (mv fs fa-table) ;;error case, basically
    (if
        (atom (cdr hns))
        (mv
         (delete-assoc (car hns) fs)
         (if
             (and (consp (assoc (car hns) fs))
                  (l6-regular-file-entry-p (cdr (assoc (car hns) fs))))
             (let* ((old-first-cluster
                     (l6-regular-file-first-cluster (cdr (assoc (car hns) fs))))
                    (old-indices
                     (if
                         (or (< old-first-cluster 2) (>= old-first-cluster
                                                         (len fa-table)))
                         nil
                       (list*
                        old-first-cluster
                        (l6-build-index-list fa-table old-first-cluster nil)))))
               (set-indices-in-fa-table fa-table old-indices
                                        (make-list (len old-indices) :initial-element 0)))
           fa-table))
      (if
          (atom fs)
          (mv nil fa-table)
        (let
            ((sd (assoc (car hns) fs)))
          (if
              (atom sd)
              (mv fs fa-table)
            (let ((contents (cdr sd)))
              (if (l6-regular-file-entry-p contents)
                  (mv fs fa-table) ;; we still have names but we're at a regular file - error
                (mv-let (new-fs new-fa-table)
                  (l6-unlink (cdr hns) contents fa-table)
                  (mv (cons (cons (car sd) new-fs)
                            (delete-assoc (car hns) fs))
                      new-fa-table))))))))))

(defund
  merge-alv (lst1 lst2)
  (declare (xargs :guard (and (boolean-listp lst1)
                              (boolean-listp lst2))))
  (if (atom lst1)
      nil
      (list* (or (car lst1) (car lst2))
             (merge-alv (cdr lst1) (cdr lst2)))))

(defthm merge-alv-correctness-1
  (equal (len (merge-alv lst1 lst2))
         (len lst1))
  :hints (("goal" :in-theory (enable merge-alv))))

(defthm merge-alv-correctness-2
  (implies (equal (len lst1) (len lst2))
           (equal (nth n (merge-alv lst1 lst2))
                  (or (nth n lst1) (nth n lst2))))
  :hints (("goal" :in-theory (enable merge-alv))))

(defthm merge-alv-correctness-3
  (implies (and (boolean-listp lst1)
                (boolean-listp lst2))
           (boolean-listp (merge-alv lst1 lst2)))
  :hints (("goal" :in-theory (enable merge-alv))))

(defun
  l6-to-l4-fs (fs fa-table)
  (declare (xargs :verify-guards nil
                  :guard (and (l6-fs-p fs)
                              (fat32-entry-list-p fa-table)
                              (<= (len fa-table) *expt-2-28*)
                              (>= (len fa-table) 2))))
  (if
   (atom fs)
   (mv fs
       ;; this is for creating a new allocation vector with only the first
       ;; two slots filled in
       (take (len fa-table) (list t t)))
   (let*
    ((directory-or-file-entry (car fs))
     (name (car directory-or-file-entry))
     (entry (cdr directory-or-file-entry)))
    (mv-let
      (tail-fs tail-alv)
      (l6-to-l4-fs (cdr fs) fa-table)
      (if
       (l6-regular-file-entry-p entry)
       (mv
        (list* (cons name
                     (cons (l6-file-index-list entry fa-table)
                           (l6-regular-file-length entry)))
               tail-fs)
        (set-indices-in-alv tail-alv
                            (l6-file-index-list entry fa-table)
                            t))
       (mv-let (head-fs head-alv)
         (l6-to-l4-fs entry fa-table)
         (mv (list* (cons name head-fs) tail-fs)
             (merge-alv head-alv tail-alv))))))))

(defthm l6-to-l4-fs-correctness-1
  (implies (and (l6-fs-p fs)
                (fat32-entry-list-p fa-table))
           (mv-let (l4-fs l4-alv) (l6-to-l4-fs fs fa-table)
             (declare (ignore l4-fs))
                  (boolean-listp l4-alv))))

(verify-guards l6-to-l4-fs)

;; we'll return to this later
(defund l6-list-all-indices (fs fa-table)
  (declare (xargs :guard (and (l6-fs-p fs) (fat32-entry-list-p fa-table))))
  (if (atom fs)
      nil
    (binary-append
     (let* ((directory-or-file-entry (car fs))
            (entry (cdr directory-or-file-entry)))
       (if (l6-regular-file-entry-p entry)
           (let ((index-list (l6-file-index-list entry fa-table)) )
             (if (feasible-file-length-p (len index-list) (l6-regular-file-length entry))
                 index-list
               nil))
         (l6-list-all-indices entry fa-table)))
     (l6-list-all-indices (cdr fs) fa-table))))

(defthm l6-list-all-indices-correctness-1
  (implies (l6-fs-p fs)
           (fat32-masked-entry-list-p (l6-list-all-indices fs fa-table)))
  :hints (("Goal" :in-theory (enable l6-list-all-indices)) ))
