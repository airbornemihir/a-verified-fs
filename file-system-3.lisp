
;  file-system-3.lisp                                  Mihir Mehta

; Here we define the rudiments of a file system with length tracking.  We first
; start with a file-system recognizer, and then we define various file-system
; operations.

(include-book "misc/assert" :dir :system)
(include-book "file-system-2")

;; I don't think blocks are 8 characters long in any system; I simply set this
;; in order to actually get fragmentation without having to make unreasonably
;; large examples.
(defconst *blocksize* 8)

;; This fragments a character-list into blocks that are *blocksize*-character
;; long. If the character-list is not exactly aligned to a block boundary, we
;; fill the space with null characters.
;; It will be used in wrchs.
(defun make-blocks (text)
  (declare (xargs :guard (character-listp text)
                  :measure (len text)))
  (if (atom text)
      nil
    (cons (make-character-list (take *blocksize* text))
          (make-blocks (nthcdr *blocksize* text)))))

;; Characterisation of a disk, which is a list of blocks as described before.
(defun block-listp (block-list)
  (declare (xargs :guard t))
  (if (atom block-list)
      (eq block-list nil)
    (and (character-listp (car block-list))
         (equal (len (car block-list)) *blocksize*)
         (block-listp (cdr block-list)))))

;; Proving that we get a proper block-list out of make-blocks.
(defthm make-blocks-correctness-2
        (implies (character-listp text)
                 (block-listp (make-blocks text))))
;; Lemma
(defthm block-listp-correctness-1
  (implies (block-listp block-list)
           (true-listp block-list)))

;; Lemma
(defthm block-listp-correctness-2
  (implies (and (block-listp block-list1) (block-listp block-list2))
           (block-listp (binary-append block-list1 block-list2))))

;; This function spells out how many characters can be in a file given the
;; number of blocks associated with it. It is kept disabled in order to avoid
;; huge arithmetic-heavy subgoals where they're not wanted.
(defund feasible-file-length-p (index-list-length file-length)
  (declare (xargs :guard (and (natp file-length) (natp index-list-length))))
  (and (> file-length
          (* *blocksize* (- index-list-length 1)))
       (<= file-length
           (* *blocksize* index-list-length))))

;; This is the counterpart of make-blocks that collapses blocks into a
;; character-list of the appropriate length.
;; It will be used in stat and, by extension, in rdchs.
(defun unmake-blocks (blocks n)
  (declare (xargs :guard (and (block-listp blocks)
                              (natp n)
                              (feasible-file-length-p (len blocks) n))
                  :guard-hints (("Goal" :in-theory (enable feasible-file-length-p)) )))
  (if (atom blocks)
      nil
    (if (atom (cdr blocks))
        (take n (car blocks))
      (binary-append (car blocks)
                     (unmake-blocks (cdr blocks) (- n *blocksize*))))))

;; Proving that we get a proper character-list out provided we don't ask for
;; more characters than we have.
(defthm unmake-blocks-correctness-1
  (implies (and (block-listp blocks)
                (natp n)
                (feasible-file-length-p (len blocks) n))
           (character-listp (unmake-blocks blocks n)))
  :hints (("Goal" :in-theory (enable feasible-file-length-p)) ))

(defthm unmake-make-blocks-lemma-1
        (implies (natp n)
                 (iff (consp (nthcdr n l)) (> (len l) n)))
        :hints (("Goal" :induct (nthcdr n l))))

(defthm unmake-make-blocks-lemma-2
  (implies (and (natp n) (>= (len l) n))
           (equal (len (nthcdr n l)) (- (len l) n))))

(encapsulate ()
  (local (include-book "std/lists/repeat" :dir :system))

  ;; Proving that make and unmake are, in a sense, inverse functions of each
  ;; other.
  (defthm unmake-make-blocks
    (implies (and (character-listp text))
             (equal (unmake-blocks (make-blocks text) (len text)) text))
    :hints (("Subgoal *1/3.2" :in-theory (disable unmake-make-blocks-lemma-1)
             :use (:instance unmake-make-blocks-lemma-1 (n *blocksize*) (l
                                                                         text)))
            ("Subgoal *1/3.1'"
             :in-theory (disable already-a-character-list
                                 take-of-too-many)
             :use ((:instance take-of-too-many (x text) (n *blocksize*))
                   (:instance unmake-make-blocks-lemma-1 (n *blocksize*) (l
                                                                          text))))))

  )

;; This is a function that might be needed later.
(defun bounded-nat-listp (l b)
  (if (atom b)
      (eq l nil)
    (and (natp (car l)) (< (car l) b) (bounded-nat-listp (cdr l) b))))

;; This is to be returned when a block is not found. It's full of null
;; characters and is *blocksize* long.
(defconst *nullblock* (make-character-list (take *blocksize* nil)))

;; This function serves to get the specified blocks from a disk. If the block
;; is not found (most likely because of an invalid index) I return a null block
;; as noted above.
(defun fetch-blocks-by-indices (block-list index-list)
  (declare (xargs :guard (and (block-listp block-list)
                              (nat-listp index-list))))
  (if (atom index-list)
      nil
    (let ((tail (fetch-blocks-by-indices block-list (cdr index-list))) )
      (if (>= (car index-list) (len block-list))
          (cons *nullblock* tail)
        (cons (nth (car index-list) block-list)
              tail)
        ))))

;; Prove that a proper block-list is returned.
(defthm fetch-blocks-by-indices-correctness-1
  (implies (and (block-listp block-list) (nat-listp index-list))
           (block-listp (fetch-blocks-by-indices block-list index-list))))

;; Prove that a list of the appropriate length is returned.
(defthm fetch-blocks-by-indices-correctness-2
  (implies (and (block-listp block-list) (nat-listp index-list))
           (equal (len (fetch-blocks-by-indices block-list index-list))
                  (len index-list))))

(defthm
  make-blocks-correctness-1
  (implies (character-listp text)
           (and (< (- (* *blocksize* (len (make-blocks text)))
                      *blocksize*)
                   (len text))
                (not (< (* *blocksize* (len (make-blocks text)))
                        (len text)))))
  :instructions (:induct (:change-goal (main . 2) t)
                         :bash :promote
                         (:claim (character-listp (nthcdr *blocksize* text)))
                         (:casesplit (>= (len text) *blocksize*))
                         :bash :bash (:demote 1)
                         (:dive 1 1)
                         :x
                         :top :s))

;; This function, which is kept disabled, recognises a regular file entry. I am
;; deciding not to make things overly complicated by making getter and setter
;; functions for file entries.
(defund l3-regular-file-entry-p (entry)
  (declare (xargs :guard t))
  (and (consp entry)
       (nat-listp (car entry))
       (natp (cdr entry))
       (feasible-file-length-p (len (car entry)) (cdr entry))))

(defthm l3-regular-file-entry-p-correctness-1
  (implies (l3-regular-file-entry-p entry)
           (and (nat-listp (car entry))
                (natp (cdr entry))
                (feasible-file-length-p (len (car entry)) (cdr entry))))
  :hints (("Goal" :in-theory (enable l3-regular-file-entry-p)) ))

(defthm l3-regular-file-entry-p-correctness-2
  (implies (l3-regular-file-entry-p entry)
           (consp entry))
  :hints (("Goal" :use l3-regular-file-entry-p-correctness-1) ))

; This function defines a valid filesystem. It's an alist where all the cars
; are symbols and all the cdrs are either further filesystems or files,
; separated into text (represented by a nat-list of indices which we use to
; look up an external disk) and metadata (currently, only length).
(defun l3-fs-p (fs)
  (declare (xargs :guard t))
  (if (atom fs)
      (null fs)
    (and (let ((directory-or-file-entry (car fs)))
           (if (atom directory-or-file-entry)
               nil
             (let ((name (car directory-or-file-entry))
                   (entry (cdr directory-or-file-entry)))
               (and (symbolp name)
                    (or (l3-regular-file-entry-p entry)
                        (l3-fs-p entry))))))
         (l3-fs-p (cdr fs)))))
;; this example - which evaluates to t - remains as a counterexample to an
;; erstwhile bug.
;; (defconst *test01* (l3-fs-p '((a  "Mihir" . 5) (b "Warren" . 6) (c))))

(defthm l3-regular-file-entry-p-correctness-3
  (implies (l3-regular-file-entry-p entry)
           (not (l3-fs-p entry)))
  :hints (("Goal" :in-theory (enable l3-regular-file-entry-p)) ))

(defthm alistp-l3-fs-p
  (implies (l3-fs-p fs)
           (alistp fs)))

(defthm l3-fs-p-assoc
  (implies (and (l3-fs-p fs)
                (consp (assoc-equal name fs))
                (not (l3-regular-file-entry-p (cdr (assoc-equal name fs)))))
           (l3-fs-p (cdr (assoc-equal name fs)))))

(assert!
 (l3-fs-p '((a (1 2) . 10) (b (3 4) . 11) (c (a (5 6) . 12) (b (7 8) . 13)))))

(defthm l3-to-l2-fs-guard-lemma-1
  (implies (and (feasible-file-length-p (len blocks) n)
                (block-listp blocks))
           (character-listp (unmake-blocks blocks n)))
  :hints (("Goal" :in-theory (enable feasible-file-length-p)) ))

;; This function transforms an instance of l3 into an equivalent instance of l2.
(defun l3-to-l2-fs (fs disk)
  (declare (xargs :guard (and (l3-fs-p fs) (block-listp disk))
                  :guard-debug t
                  :guard-hints (("Subgoal 2.6" :in-theory (enable feasible-file-length-p)))
                  ))
  (if (atom fs)
      nil
    (cons (let* ((directory-or-file-entry (car fs))
                 (name (car directory-or-file-entry))
                 (entry (cdr directory-or-file-entry)))
            (cons name
                  (if (l3-regular-file-entry-p entry)
                      (cons (coerce (unmake-blocks
                                     (fetch-blocks-by-indices disk (car entry))
                                     (cdr entry)) 'string)
                            (cdr entry))
                    (l3-to-l2-fs entry disk))))
          (l3-to-l2-fs (cdr fs) disk))))

;; This theorem shows the type-correctness of l2-to-l1-fs.
(defthm l3-to-l2-fs-correctness-1
  (implies (and (l3-fs-p fs) (block-listp disk))
           (l2-fs-p (l3-to-l2-fs fs disk))))

;; This function allows a file or directory to be found in a filesystem given a path.
(defun l3-stat (hns fs disk)
  (declare (xargs :guard-debug t
                  :guard (and (symbol-listp hns)
                              (l3-fs-p fs)
                              (block-listp disk))))
  (if (atom hns)
      fs
    (if (atom fs)
        nil
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            nil
          (let ((contents (cdr sd)))
            (if (l3-regular-file-entry-p contents)
                (and (null (cdr hns))
                     (coerce
                      (unmake-blocks (fetch-blocks-by-indices disk (car contents))
                                     (cdr contents))
                      'string))
              (l3-stat (cdr hns) contents disk))))))))

;; (defthm l3-stat-correctness-1-lemma-1
;;   (implies (and (l3-fs-p fs)
;;                 (block-listp disk)
;;                 (consp (cdr (assoc-equal name fs)))
;;                 (nat-listp (cadr (assoc-equal name fs))))
;;            (and (natp (cddr (assoc-equal name fs)))
;;                 (feasible-file-length-p (len (cadr (assoc-equal name fs)))
;;                                         (cddr (assoc-equal name fs))))))

;; (defthm l3-stat-correctness-1-lemma-2
;;   (implies (and (l3-fs-p fs)
;;                 (block-listp disk)
;;                 (consp (cdr (assoc-equal name fs)))
;;                 (nat-listp (cadr (assoc-equal name fs))))
;;            (stringp (cadr (assoc-equal name (l3-to-l2-fs fs disk)))))
;;   :hints ( ("Goal" :use l3-stat-correctness-1-lemma-1)))

(defthm
  l3-stat-correctness-1-lemma-1
  (implies (and (l3-fs-p fs)
                (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (block-listp disk)
                (consp (assoc-equal name fs)))
           (stringp (cadr (assoc-equal name
                                       (l3-to-l2-fs fs disk))))))

(defthm l3-stat-correctness-1-lemma-2
  (implies (and (l3-fs-p fs) (block-listp disk))
           (equal (consp (assoc-equal name (l3-to-l2-fs fs disk)))
                  (consp (assoc-equal name fs)))))

(defthm
  l3-stat-correctness-1-lemma-3
  (implies
   (and (l3-fs-p fs)
        (block-listp disk)
        (consp (assoc-equal name fs))
        (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
   (equal
    (cadr (assoc-equal name (l3-to-l2-fs fs disk)))
    (coerce (unmake-blocks
             (fetch-blocks-by-indices disk (cadr (assoc-equal name fs)))
             (cddr (assoc-equal name fs)))
            'string))))

(defthm l3-stat-correctness-1-lemma-4
  (implies (and (l3-fs-p fs)
                (block-listp disk)
                (l3-fs-p (cdr (assoc-equal name fs))))
           (equal (cdr (assoc-equal name (l3-to-l2-fs fs disk)))
                  (l3-to-l2-fs (cdr (assoc-equal name fs))
                               disk))))

(defthm l3-stat-correctness-1
  (implies (and (symbol-listp hns)
                (l3-fs-p fs)
                (block-listp disk)
                (stringp (l3-stat hns fs disk)))
           (equal (l2-stat hns (l3-to-l2-fs fs disk))
                  (l3-stat hns fs disk)))
  :hints (("Subgoal *1/5.2'"
           :in-theory (disable l3-fs-p-assoc l3-to-l2-fs-correctness-1)
           :use ((:instance l3-to-l2-fs-correctness-1
                            (fs (cdr (assoc-equal (car hns) fs))))
                 (:instance l3-fs-p-assoc (name (car hns)))) ) ))

;; This is simply a useful property of stat.
(defthm l3-stat-of-stat
  (implies (and (symbol-listp inside)
                (symbol-listp outside)
                (l3-stat outside fs disk)
                (l3-fs-p fs)
                (block-listp disk))
           (equal (l3-stat inside (l3-stat outside fs disk) disk)
                  (l3-stat (append outside inside) fs disk)))
  :hints
  (("Goal" :induct (l3-stat outside fs disk))))

;; This function finds a text file given its path and reads a segment of
;; that text file.
(defun l3-rdchs (hns fs disk start n)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l3-fs-p fs)
                              (natp start)
                              (natp n)
                              (block-listp disk))))
  (let ((file (l3-stat hns fs disk)))
    (if (not (stringp file))
        nil
      (let ((file-length (length file))
            (end (+ start n)))
        (if (< file-length end)
            nil
          (subseq file start (+ start n)))))))

; This function deletes a file or directory given its path.

; Note that we don't need to do anything with the disk - the blocks can just
; lie there, forever unreferred to. In a later model we might think about
; re-using the blocks.
(defun l3-unlink (hns fs)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l3-fs-p fs))))
  (if (atom hns)
      fs ;;error case, basically
    (if (atom (cdr hns))
        (delete-assoc (car hns) fs)
      (if (atom fs)
          nil
        (let ((sd (assoc (car hns) fs)))
          (if (atom sd)
              fs
            (let ((contents (cdr sd)))
              (if (l3-regular-file-entry-p contents)
                  fs ;; we still have names but we're at a regular file - error
                (cons (cons (car sd)
                            (l3-unlink (cdr hns) contents))
                      (delete-assoc (car hns) fs))))))))
    ))

;; putting these lemmas on the back burner because we would need to add uniquep
;; to our l3-fs-p definition to make this work
;; (defthm l3-unlink-works-lemma-1 (not (assoc-equal key (delete-assoc-equal key alist))))

;; (defthm l3-unlink-works (implies (l3-fs-p fs) (not (l3-stat hns (l3-unlink hns fs)))))

(defun generate-index-list (disk-length block-list-length)
  (declare (xargs :guard (and (natp disk-length) (natp block-list-length))))
  (if (zp block-list-length)
      nil
    (cons disk-length
          (generate-index-list (1+ disk-length) (1- block-list-length)))))

(defthm
    generate-index-list-correctness-1
    (implies (and (natp disk-length)
                  (natp block-list-length))
             (nat-listp (generate-index-list disk-length block-list-length))))

(defthm
    generate-index-list-correctness-2
    (implies (natp block-list-length)
             (equal (len (generate-index-list disk-length block-list-length))
                    block-list-length)))

(defthm make-blocks-correctness-3
  (implies (and (character-listp cl))
           (feasible-file-length-p (len (make-blocks cl))  (len cl)))
  :hints (("Goal" :in-theory (e/d (feasible-file-length-p) (make-blocks-correctness-1))
           :use (:instance make-blocks-correctness-1 (text cl))) ))

; This function writes a specified text string to a specified position to a
; text file at a specified path.
(defun l3-wrchs (hns fs disk start text)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l3-fs-p fs)
                              (natp start)
                              (stringp text)
                              (block-listp disk))
                  ;; :guard-hints
                  ;; (("Subgoal 1.4" :use (:instance character-listp-coerce (str ()))) )
                  ))
  (if (atom hns)
      (mv fs disk) ;; error - showed up at fs with no name  - so leave fs unchanged
    (if (atom fs)
        (mv nil disk) ;; error, so leave fs unchanged
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            (mv fs disk) ;; file-not-found error, so leave fs unchanged
          (let ((contents (cdr sd)))
            (if (l3-regular-file-entry-p contents)
                (if (cdr hns)
                    (mv (cons (cons (car sd) contents)
                              (delete-assoc (car hns) fs))
                        disk) ;; error, so leave fs unchanged
                  (let* ((oldtext
                          (unmake-blocks
                           (fetch-blocks-by-indices disk (car contents))
                           (cdr contents)))
                         (newtext (insert-text oldtext start text))
                         (newblocks (make-blocks newtext)))
                    (mv (cons (cons (car sd)
                                    (cons (generate-index-list
                                           (len disk)
                                           (len newblocks))
                                          (len newtext)))
                              (delete-assoc (car hns) fs))
                        (binary-append disk newblocks))))
              (mv-let (new-contents new-disk) (l3-wrchs (cdr hns) contents disk start text)
                (mv (cons (cons (car sd) new-contents)
                          (delete-assoc (car hns) fs))
                    new-disk)))
            ))))))

; Mihir, run some example and provide some ASSERT$ events.

(defthm l3-wrchs-returns-fs-lemma-1
  (implies (and (consp (assoc-equal s fs))
                (l3-fs-p fs))
           (and (equal (car (assoc-equal s fs)) s) (symbolp s))))

(defthm l3-wrchs-returns-fs-lemma-2
  (implies (l3-fs-p fs)
           (l3-fs-p (delete-assoc-equal s fs))))

(defthm l3-wrchs-returns-fs-lemma-3
  (implies (and (consp (assoc-equal s fs))
                (l3-fs-p fs)
                (consp (cdr (assoc-equal s fs)))
                (l3-regular-file-entry-p (cdr (assoc-equal s fs))))
           (feasible-file-length-p
            (len (cadr (assoc-equal s fs)))
            (cddr (assoc-equal s fs))))
  :hints ( ("Goal" :induct (assoc-equal s fs))))

(defthm
  l3-wrchs-returns-fs-lemma-4
  (implies
   (and (block-listp disk)
        (character-listp cl))
   (l3-regular-file-entry-p (cons (generate-index-list (len disk)
                                                       (len (make-blocks cl)))
                                  (len cl))))
  :hints (("Goal" :in-theory (enable l3-regular-file-entry-p))))

;; This theorem shows that the property l3-fs-p is preserved by wrchs, and
;; additionally the property block-listp is preseved for the disk.
(defthm l3-wrchs-returns-fs
  (implies (and (l3-fs-p fs)
                (block-listp disk)
                (natp start)
                (stringp text))
           (mv-let (new-fs new-disk)
             (l3-wrchs hns fs disk start text)
             (and (l3-fs-p new-fs) (block-listp new-disk)))))

;; This theorem shows that the property l3-fs-p is preserved by unlink.
(defthm l3-unlink-returns-fs
  (implies (and (l3-fs-p fs))
           (l3-fs-p (l3-unlink hns fs))))

;; The theorems from this point on do not succeed. What they should be and how
;; they should be proved is under consideration; these are relics from the
;; previous model that are kept as an aid to thinking.

(defthm l3-read-after-write-1-lemma-2
  (implies (and (l3-fs-p fs) (stringp text) (stringp (l3-stat hns fs)))
           (stringp (l3-stat hns (l3-wrchs hns fs disk start text)))))

(defthm l3-read-after-write-1-lemma-3
  (implies (l3-rdchs hns fs start n)
           (stringp (l3-stat hns fs))))

(defthm l3-read-after-write-1-lemma-4
  (implies (and (l3-fs-p fs) (stringp text) (stringp (l3-stat hns fs)))
           (equal (l3-stat hns (l3-wrchs hns fs start text))
                  (let* (
                         (end (+ start (length text)))
                         (oldtext (coerce (l3-stat hns fs) 'list))
                         (newtext (append (make-character-list (take start oldtext))
                                          (coerce text 'list)
                                          (nthcdr end oldtext))))
                    (coerce newtext 'string)))))

(defthm l3-read-after-write-1
  (implies (and (l3-fs-p fs)
                (stringp text)
                (symbol-listp hns)
                (natp start)
                (equal n (length text))
                (stringp (l3-stat hns fs)))
           (equal (l3-rdchs hns (l3-wrchs hns fs start text) start n) text)))

;; we want to prove
;; (implies (and (l3-fs-p fs)
;;               (stringp text2)
;;               (symbol-listp hns1)
;;               (symbol-listp hns2)
;;               (not (equal hns1 hns2))
;;               (natp start2)
;;               (stringp (l3-stat hns1 fs)))
;;          (equal (l3-stat hns1 (l3-wrchs hns2 fs start2 text2))
;;                 (l3-stat hns1 fs)))
;; now, let's semi-formally write the cases we want.
;; case 1: (atom hns1) - this will violate the hypothesis
;; (stringp (l3-stat hns1 fs))
;; case 2: (and (consp hns1) (atom fs)) - this will yield nil in both cases
;; case 3: (and (consp hns1) (consp fs) (atom (assoc (car hns1) fs))) - this
;; will yield nil in both cases (might need a lemma)
;; case 4: (and (consp hns1) (consp fs) (consp (assoc (car hns1) fs))
;;              (atom hns2)) - in this case
;; (l3-wrchs hns2 fs start2 text2) will be the same as fs
;; case 5: (and (consp hns1) (consp fs) (consp (assoc (car hns1) fs))
;;              (consp hns2) (not (equal (car hns1) (car hns2)))) - in this
;; case, (assoc (car hns1) (l3-wrchs hns2 fs start2 text2)) =
;; (assoc (car hns1) (delete-assoc (car hns2) fs)) =
;; (assoc (car hns1) fs) and from here on the terms will be equal
;; case 6: (and (consp hns1) (consp fs) (consp (assoc (car hns1) fs))
;;              (consp hns2) (equal (car hns1) (car hns2)) (atom (cdr hns1))) -
;; in this case (consp (cdr hns2)) is implicit because of
;; (not (equal hns1 hns2)) and (stringp (l3-stat hns1 fs)) implies that
;; (l3-wrchs hns2 fs start2 text2) = fs
;; case 7: (and (consp hns1) (consp fs) (consp (assoc (car hns1) fs))
;;              (consp hns2) (equal (car hns1) (car hns2)) (consp (cdr hns1))) -
;; (l3-stat hns1 (l3-wrchs hns2 fs start2 text2)) =
;; (l3-stat hns1 (cons (cons (car hns1)
;;                        (l3-wrchs (cdr hns2) (cdr (assoc (car hns1) fs)) start2 text2))
;;                  (delete-assoc (car hns1) fs)) =
;; (l3-stat (cdr hns1) (l3-wrchs (cdr hns2) (cdr (assoc (car hns1) fs)) start2 text2)) =
;; (l3-stat (cdr hns1) (cdr (assoc (car hns1) fs))) = (induction hypothesis)
;; (l3-stat hns1 fs)

(defthm l3-read-after-write-2-lemma-1
  (implies (l3-fs-p fs)
           (not (stringp (cdr (assoc-equal name fs))))))

(defthm l3-read-after-write-2-lemma-2
  (implies (and (consp hns1)
                (consp fs)
                (consp (assoc-equal (car hns1) fs))
                (l3-fs-p fs)
                (symbolp (car hns1))
                (not (cdr hns1))
                (stringp (l3-stat hns1 fs)))
           (equal (l3-stat hns1 fs) (cadr (assoc (car hns1) fs)))))

(encapsulate
  ()
  (local (defun induction-scheme (hns1 hns2 fs)
           (if (atom hns1)
               fs
             (if (atom fs)
                 nil
               (let ((sd (assoc (car hns2) fs)))
                 (if (atom sd)
                     fs
                   (if (atom hns2)
                       fs
                     (if (not (equal (car hns1) (car hns2)))
                         fs
                       (let ((contents (cdr sd)))
                         (if (atom (cdr hns1))
                             (cons (cons (car sd)
                                         contents)
                                   (delete-assoc (car hns2) fs))
                           (cons (cons (car sd)
                                       (induction-scheme (cdr hns1) (cdr hns2) contents))
                                 (delete-assoc (car hns2) fs)))
                         ))))
                 )))))

  (defthm l3-read-after-write-2-lemma-3
    (implies (and (l3-fs-p fs)
                  (stringp text2)
                  (symbol-listp hns1)
                  (symbol-listp hns2)
                  (not (equal hns1 hns2))
                  (natp start2)
                  (stringp (l3-stat hns1 fs)))
             (equal (l3-stat hns1 (l3-wrchs hns2 fs start2 text2)) (l3-stat hns1 fs)))
    :hints (("Goal"  :induct (induction-scheme hns1 hns2 fs))
            ("Subgoal *1/7.1''" :in-theory (disable alistp-l3-fs-p)
             :use (:instance alistp-l3-fs-p (fs (l3-wrchs (cdr hns2)
                                                    (cdr (assoc-equal (car hns1) fs))
                                                    start2 text2))))))

  )

(defthm l3-read-after-write-2
  (implies (and (l3-fs-p fs)
                (stringp text2)
                (symbol-listp hns1)
                (symbol-listp hns2)
                (not (equal hns1 hns2))
                (natp start1)
                (natp start2)
                (natp n1)
                (stringp (l3-stat hns1 fs)))
           (equal (l3-rdchs hns1 (l3-wrchs hns2 fs start2 text2) start1 n1)
                  (l3-rdchs hns1 fs start1 n1))))

(defun fsck (fs)
  (declare (xargs :guard (l3-fs-p fs)))
  (or (atom fs)
    (and (let ((directory-or-file-entry (car fs)))
           (let ((entry (cdr directory-or-file-entry)))
             (if (and (consp entry) (stringp (car entry)))
                 (equal (length (car entry)) (cdr entry))
               (fsck entry))))
         (fsck (cdr fs)))))

(defthm fsck-after-l3-wrchs-lemma-1
  (implies (and (l3-fs-p fs) (fsck fs))
           (fsck (delete-assoc-equal name fs))))

(defthm fsck-after-l3-wrchs-lemma-2
  (implies (and (l3-fs-p fs) (fsck fs))
           (fsck (cdr (assoc-equal (car hns) fs)))))

(defthm fsck-after-l3-wrchs-lemma-3
  (implies (and (l3-fs-p fs) (consp fs)) (not (stringp (car fs)))))

(defthm fsck-after-l3-wrchs-lemma-4
  (implies (and (consp fs)
                (consp (assoc-equal name fs))
                (l3-fs-p fs)
                (stringp text)
                (fsck fs)
                (consp (cdr (assoc-equal name fs)))
                (stringp (cadr (assoc-equal name fs))))
           (equal (len (coerce (cadr (assoc-equal name fs))
                               'list))
                  (cddr (assoc-equal name fs))))
)

(defthm fsck-after-l3-wrchs
  (implies (and (l3-fs-p fs) (stringp text) (fsck fs))
           (fsck (l3-wrchs hns fs start text))))

(defthm fsck-after-l3-unlink
  (implies (and (l3-fs-p fs) (fsck fs))
           (fsck (l3-unlink hns fs))))

; Find length of file
(defun wc-len (hns fs)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l3-fs-p fs))))
  (let ((file (l3-stat hns fs)))
    (if (not (stringp file))
        nil
      (length file))))

; Prove (list-of-chars-to-string (string-to-chars str))
;       (string-to-chars (list-of-chars-to-string char-list))
; and then, you will be positioned to use either form.
#||From :doc STR::STD/STRINGS/COERCE
  Theorem: <coerce-inverse-1-better>

    (defthm coerce-inverse-1-better
            (equal (coerce (coerce x 'string) 'list)
                   (if (stringp x)
                       nil (make-character-list x))))

  Theorem: <coerce-inverse-2-better>

    (defthm coerce-inverse-2-better
            (equal (coerce (coerce x 'list) 'string)
                   (if (stringp x) x "")))
That takes care of that
||#
; Correspond (or not) with Linux system calls -- the low-level stuff...

; Add file -- or, if you will, create a file with some initial contents

; and so on...

(assign fs '((a "Mihir" . 5) (b "Warren" . 6) (c (a "Mehta" . 5) (b "Hunt" . 4))))

(assign h1 '(a))
(assign h2 '(a b))
(assign h3 '(c b))
(assign h4 '(c))

(l3-stat (@ h1) (@ fs))
(l3-stat (@ h2) (@ fs))
(l3-stat (@ h3) (@ fs))
(l3-stat (@ h4) (@ fs))

(wc-len (@ h1) (@ fs))
(wc-len (@ h2) (@ fs))
(wc-len (@ h3) (@ fs))
(wc-len (@ h4) (@ fs))

(l3-wrchs (@ h1) (@ fs) 1 "athur")
(l3-wrchs (@ h3) (@ fs) 1 "inojosa")
(l3-wrchs (@ h3) (@ fs) 5 "Alvarez")
(l3-wrchs (@ h2) (@ fs) 1 "athur") ;; buggy example

(l3-unlink (@ h1) (@ fs))
(l3-unlink (@ h2) (@ fs))
(l3-unlink (@ h3) (@ fs))
(l3-unlink (@ h4) (@ fs))
