(in-package "ACL2")

;  file-system-4.lisp                                  Mihir Mehta

; Here we define a more complex file system with a disk and an allocation bitmap.
; We first start with a file-system recognizer, and then we define various
; file-system operations.

; Some more information about the proper way to transform an instance of l4 to
; an instance of l3: we need to do a depth-first traversal of the l4 tree and
; append all the disk contents in the order in which they are visited in this
; traversal (for a leaf node - that is, a file - arrival time and departure
; time are the same.) This is, in fact, going to be part of our sanity check -
; when we append all the disk indices we retrieve this way, we should get a set
; of numbers that is unique and corresponds to only blocks marked "not free" in
; the allocation vector. Then, like in the previous model, we can unlink
; l4-fs-p and other conditions which are necessary to make it a valid
; filesystem wrt the disk.

; Why is uniqueness of indices between different text files important? We want
; to avoid strange behaviour caused by a file deletion or overwrite of one of
; the files that exposes the other file's contents to a state of being marked
; "free" in the alv.

; How do we prove uniqueness after a create/write/delete operation? 

; For create, our contention is that all used blocks are marked "not free" in
; the alv (according to the extended l4-fs-p predicate), and the function for
; getting new blocks only returns blocks marked "free", therefore there cannot
; be any overlap between these two sets.

; For delete, the rationale is, removing something from a list that already
; satisfies no-duplicatesp will give us the same thing. This is not going to be
; straightforward because when we get the concatenated list of indices after
; deleting, we will have a contiguous sublist missing which will be hard to
; define.

; In fact, without sorting the files in a directory by name (which we have so
; far avoided doing), we can't make a consistent ordering which will give us
; the nice properties of depth-first traversal we want.

; Anyway, for write, it's going to be more complicated still - our claim is
; that if we re-use anything that was used before, it's fine because we marked
; the blocks as "free" before writing to them and they wouldn't have appeared
; anywhere else because of no-duplicatesp.

; To sum up, we shouldn't try to charge on without proving equivalence to l3
; because that's foolhardy. Yet, it's hard to think of a way to transform l4
; instances to l3 instances - even with sorting of names - in such a way that
; the disks will turn out to be the same in the two circumstances of
; transforming and then writing, or writing and then transforming. I think we
; might just have to start using defun-sk in order to quantify over all
; names. We've known for a while that the time for this was coming.

(include-book "file-system-3")

(defthm mv-nth-replacement
  (equal (mv-nth n (cons a b))
         (if (zp n) a (mv-nth (- n 1) b))))

(in-theory (disable mv-nth))

(defun count-free-blocks (alv)
  (declare (xargs :guard (and (boolean-listp alv))))
  (if (atom alv)
      0
    (if (car alv)
        (count-free-blocks (cdr alv))
      (+ (count-free-blocks (cdr alv)) 1))))

(encapsulate
  ( ((find-n-free-blocks * *) => *) )

  (local
   (defun find-n-free-blocks-helper (alv n start)
     (declare (xargs :guard (and (boolean-listp alv)
                                 (natp n)
                                 (natp start))))
     (if (or (atom alv) (zp n))
         nil
       (if (car alv)
           ;; this block is taken
           (find-n-free-blocks-helper (cdr alv) n (+ start 1))
         ;; this block isn't taken
         (cons start (find-n-free-blocks-helper (cdr alv) (- n 1) (+ start 1)))))))

  (local
   (defthm find-n-free-blocks-helper-correctness-1
     (implies (and (boolean-listp alv)
                   (natp n))
              (<= (len (find-n-free-blocks-helper alv n start)) n))
     :rule-classes (:rewrite :linear)))

  (local
   (defthm find-n-free-blocks-helper-correctness-2
     (implies (and (boolean-listp alv)
                   (natp n)
                   (<= n (count-free-blocks alv)))
              (equal (len (find-n-free-blocks-helper alv n start)) n))))

  (local
   (defthm find-n-free-blocks-helper-correctness-3
     (implies (and (boolean-listp alv)
                   (natp n) (natp start))
              (nat-listp (find-n-free-blocks-helper alv n start)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm find-n-free-blocks-helper-correctness-4
     (implies (and (natp n) (natp start)
                   (member-equal m (find-n-free-blocks-helper alv n start)))
              (<= start m))))

  (local
   (defthm
     find-n-free-blocks-helper-correctness-5
     (implies (and (boolean-listp alv)
                   (natp n)
                   (natp start)
                   (member-equal m
                                 (find-n-free-blocks-helper alv n start)))
              (not (nth (- m start) alv)))
     :hints (("Subgoal *1/6.1'" :in-theory (disable find-n-free-blocks-helper-correctness-4)
              :use (:instance find-n-free-blocks-helper-correctness-4
                              (alv (cdr alv))
                              (start (+ 1 start)))) )))

  (local
   (defthm
     find-n-free-blocks-helper-correctness-6
     (implies (and (natp n) (natp start))
              (no-duplicatesp-equal (find-n-free-blocks-helper alv n start)))
     :hints (("Subgoal *1/9''"
              :in-theory (disable find-n-free-blocks-helper-correctness-4)
              :use (:instance find-n-free-blocks-helper-correctness-4
                              (m start)
                              (alv (cdr alv))
                              (n (+ -1 n))
                              (start (+ 1 start)))))))

  (local
   (defthm find-n-free-blocks-helper-correctness-7
     (implies (and (boolean-listp alv)
                   (natp n) (natp start))
              (bounded-nat-listp
               (find-n-free-blocks-helper alv n start)
               (+ start (len alv))))))

  (local
   (defun find-n-free-blocks (alv n)
     (declare (xargs :guard (and (boolean-listp alv)
                                 (natp n))))
     (find-n-free-blocks-helper alv n 0)))

  ;; Here are some examples showing how this works.
  ;; ACL2 !>(find-n-free-blocks (list t nil t) 1)
  ;; (1)
  ;; ACL2 !>(find-n-free-blocks (list t nil t) 2)
  ;; (1)
  ;; ACL2 !>(find-n-free-blocks (list t nil nil) 2)
  ;; (1 2)

  (defthm find-n-free-blocks-correctness-1
    (implies (and (boolean-listp alv)
                  (natp n))
             (<= (len (find-n-free-blocks alv n)) n))
    :rule-classes (:rewrite :linear))

  (defthm find-n-free-blocks-correctness-2
    (implies (and (boolean-listp alv)
                  (natp n)
                  (<= n (count-free-blocks alv)))
             (equal (len (find-n-free-blocks alv n)) n)))

  (defthm find-n-free-blocks-correctness-3
    (implies (and (boolean-listp alv)
                  (natp n))
             (nat-listp (find-n-free-blocks alv n)))
    :rule-classes (:rewrite :type-prescription))

  (defthm
    find-n-free-blocks-correctness-5
    (implies (and (boolean-listp alv)
                  (natp n)
                  (member-equal m (find-n-free-blocks alv n)))
             (not (nth m alv)))
    :hints
    (("Goal" :in-theory (disable find-n-free-blocks-helper-correctness-5)
      :use (:instance find-n-free-blocks-helper-correctness-5
                      (start 0)))))

  (defthm
    find-n-free-blocks-correctness-6
    (implies (and (natp n))
             (no-duplicatesp-equal (find-n-free-blocks alv n))))

  (defthm find-n-free-blocks-correctness-7
    (implies (and (boolean-listp alv)
                  (natp n))
             (bounded-nat-listp
              (find-n-free-blocks alv n)
              (len alv))))
  )

(defun set-indices (v index-list value-list)
  (declare (xargs :guard (and (true-listp v)
                              (nat-listp index-list)
                              (true-listp value-list)
                              (equal (len index-list) (len value-list)))))
  (if (atom index-list)
      v
    (set-indices (update-nth (car index-list) (car value-list) v)
                        (cdr index-list)
                        (cdr value-list))))

(defthm set-indices-correctness-1
  (implies (and (natp n)
                (nat-listp index-list)
                (not (member-equal n index-list)))
           (equal (nth n (set-indices v index-list value-list))
                  (nth n v))))

(encapsulate
  ( ((set-indices-in-alv * * *) => *) )

  (local (include-book "std/lists/repeat" :dir :system))

  (local
   (defun set-indices-in-alv (alv index-list value)
     (declare (xargs :guard (and (boolean-listp alv)
                                 (bounded-nat-listp index-list (len alv))
                                 (booleanp value))))
     (set-indices alv index-list (repeat (len index-list) value))))

  (defthm
    set-indices-in-alv-correctness-1
    (implies
     (and (boolean-listp alv)
          (booleanp value))
     (boolean-listp (set-indices-in-alv alv index-list value)))
    :rule-classes (:type-prescription :rewrite))

  (defthm
    set-indices-in-alv-correctness-2
    (implies
     (and (boolean-listp alv)
          (booleanp value)
          (bounded-nat-listp index-list (len alv)))
     (equal (len (set-indices-in-alv alv index-list value))
            (len alv))))

  (defthm
    set-indices-in-alv-correctness-3
    (implies
     (and (boolean-listp alv)
          (nat-listp index-list)
          (booleanp value)
          (member-equal n index-list)
          (< n (len alv)))
     (equal (nth n
                 (set-indices-in-alv alv index-list value))
            value)))

  (defthm
    set-indices-in-alv-correctness-4
    (implies
     (and (boolean-listp alv)
          (nat-listp index-list)
          (booleanp value)
          (natp n)
          (not (member-equal n index-list))
          (< n (len alv)))
     (equal (nth n
                 (set-indices-in-alv alv index-list value))
            (nth n alv))))
  )

(defthm set-indices-correctness-2
        (implies (and (true-listp v)
                      (nat-listp index-list)
                      (true-listp value-list)
                      (equal (len index-list)
                             (len value-list))
                      (no-duplicatesp-equal index-list)
                      (natp m)
                      (< m (len index-list)))
                 (equal (nth (nth m index-list)
                             (set-indices v index-list value-list))
                        (nth m value-list))))

;; could be handled differently using repeat... let's see.
(defun indices-marked-p (index-list alv)
  (declare (xargs :guard (and (nat-listp index-list) (boolean-listp alv))))
  (or (atom index-list)
      (and (nth (car index-list) alv) (indices-marked-p (cdr index-list) alv))))

(defthm indices-marked-p-correctness-1
  (implies (and (indices-marked-p index-list alv)
                (equal b (len alv))
                (nat-listp index-list))
           (bounded-nat-listp index-list b)))

(defthm indices-marked-p-correctness-2
  (equal
   (indices-marked-p (binary-append x y) alv)
   (and (indices-marked-p x alv) (indices-marked-p y alv))))

(defthm indices-marked-p-correctness-3
  (implies (and (nat-listp index-list1)
                (nat-listp index-list2)
                (boolean-listp alv)
                (indices-marked-p index-list1 alv)
                (bounded-nat-listp index-list1 (len alv)))
           (indices-marked-p index-list1
                             (set-indices-in-alv alv index-list2 t)))
  :hints (("Subgoal *1/5''"
           :use ((:instance set-indices-in-alv-correctness-3
                            (value t)
                            (n (car index-list1))
                            (index-list index-list2))
                 (:instance set-indices-in-alv-correctness-4
                            (value t)
                            (n (car index-list1))
                            (index-list index-list2)))
           :cases (member-equal (car index-list1)
                                                   index-list2)) ))

(encapsulate
  ()

  (local (defun induction-scheme (l1 l2)
           (if (atom l2)
               l1
             (induction-scheme (binary-append l1 (cons (car l2) nil)) (cdr l2)))))

  (defthm
    indices-marked-p-correctness-4
    (implies (and (boolean-listp alv)
                  (bounded-nat-listp index-list1 (len alv))
                  (bounded-nat-listp index-list2 (len alv)))
             (indices-marked-p
              index-list2
              (set-indices-in-alv alv
                                  (binary-append index-list1 index-list2)
                                  t)))
    :hints (("Goal" :induct (induction-scheme index-list1 index-list2))))

  )

(defthm
  indices-marked-p-correctness-5
  (implies (and (boolean-listp alv)
                (bounded-nat-listp index-list (len alv)))
           (indices-marked-p index-list
                             (set-indices-in-alv alv index-list t)))
  :hints (("Goal" :in-theory (disable indices-marked-p-correctness-4)
           :use (:instance indices-marked-p-correctness-4
                           (index-list2 index-list)
                           (index-list1 nil)))))

(defun l4-regular-file-entry-p (entry)
  (declare (xargs :guard t))
  (l3-regular-file-entry-p entry))

(defun l4-fs-p (fs)
  (declare (xargs :guard t))
  (l3-fs-p fs))

(defun l4-stat (hns fs disk)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l4-fs-p fs)
                              (block-listp disk))))
  (l3-stat hns fs disk))

(defun l4-rdchs (hns fs disk start n)
  (declare (xargs :guard-debug t
                  :guard (and (symbol-listp hns)
                              (l4-fs-p fs)
                              (natp start)
                              (natp n)
                              (block-listp disk))))
  (l3-rdchs hns fs disk start n))

(defun l4-wrchs (hns fs disk alv start text)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l4-fs-p fs)
                              (natp start)
                              (stringp text)
                              (block-listp disk)
                              (boolean-listp alv)
                              (equal (len alv) (len disk)))
                  :guard-debug t))
  (if (atom hns)
      (mv fs disk alv) ;; error - showed up at fs with no name  - so leave fs unchanged
    (if (atom fs)
        (mv nil disk alv) ;; error, so leave fs unchanged
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            (mv fs disk alv) ;; file-not-found error, so leave fs unchanged
          (let ((contents (cdr sd)))
            (if (l3-regular-file-entry-p contents)
                (if (cdr hns)
                    (mv (cons (cons (car sd) contents)
                              (delete-assoc (car hns) fs))
                        disk
                        alv) ;; error, so leave fs unchanged
                  (let* ((old-text
                          (unmake-blocks
                           (fetch-blocks-by-indices disk (car contents))
                           (cdr contents)))
                         (alv-after-free
                          (set-indices-in-alv alv (car contents) nil))
                         (new-text (insert-text old-text start text))
                         (new-blocks (make-blocks new-text))
                         (new-indices
                          (find-n-free-blocks alv-after-free (len new-blocks))))
                    (if (not (equal (len new-indices) (len new-blocks)))
                        ;; we have an error because of insufficient disk space
                        ;; - so we leave the fs unchanged
                        (mv (cons (cons (car sd) contents)
                                  (delete-assoc (car hns) fs))
                            disk
                            alv)
                      (mv (cons (cons (car sd)
                                      (cons new-indices (len new-text)))
                                (delete-assoc (car hns) fs))
                          ;; this (take) means we write as many blocks as we can
                          ;; if we run out of space
                          (set-indices disk new-indices new-blocks)
                          (set-indices-in-alv alv-after-free new-indices t)))))
              (mv-let (new-contents new-disk new-alv)
                (l4-wrchs (cdr hns) contents disk alv start text)
                (mv (cons (cons (car sd) new-contents)
                          (delete-assoc (car hns) fs))
                    new-disk
                    new-alv)))
            ))))))

(defun l4-list-all-indices (fs)
  (declare (xargs :guard (l4-fs-p fs)))
  (if (atom fs)
      nil
    (binary-append
     (let ((directory-or-file-entry (car fs)))
       (let ((entry (cdr directory-or-file-entry)))
         (if (l4-regular-file-entry-p entry)
             (car entry)
           (l4-list-all-indices entry))))
         (l4-list-all-indices (cdr fs))))
  )

(defthm l4-list-all-indices-correctness-1
  (implies (l4-fs-p fs)
   (nat-listp (l4-list-all-indices fs))))

(defun l4-stricter-fs-p (fs alv)
  (declare (xargs :guard t :guard-debug t))
  (and (l4-fs-p fs)
       (boolean-listp alv)
       (let ( (all-indices (l4-list-all-indices fs)))
         (and (no-duplicatesp all-indices)
              (bounded-nat-listp all-indices (len alv))
              (indices-marked-p all-indices alv)))))

(defthm l4-wrchs-returns-fs
  (implies (and (symbol-listp hns)
                (l3-fs-p fs)
                (boolean-listp alv)
                (integerp start)
                (<= 0 start)
                (stringp text)
                (block-listp disk))
           (l3-fs-p (mv-nth 0 (l4-wrchs hns fs disk alv start text))))
  :hints (("Subgoal *1/5'''" :in-theory (enable l3-regular-file-entry-p))
          ("Subgoal *1/6'4'" :in-theory (enable l3-regular-file-entry-p))))

(defthm l4-wrchs-returns-alv
  (implies (and (symbol-listp hns)
                (l3-fs-p fs)
                (boolean-listp alv)
                (integerp start)
                (<= 0 start)
                (stringp text)
                (block-listp disk))
           (boolean-listp (mv-nth 2 (l4-wrchs hns fs disk alv start text)))))

(defthm l4-wrchs-returns-stricter-fs-lemma-1
  (implies (and (consp (assoc-equal name fs))
                (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (boolean-listp alv)
                (indices-marked-p (l4-list-all-indices fs)
                                  alv))
           (indices-marked-p (cadr (assoc-equal name fs))
                             alv)))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-2
  (implies
   (and (l4-fs-p fs)
        (boolean-listp alv)
        (indices-marked-p (l4-list-all-indices fs)
                          alv))
   (indices-marked-p (l4-list-all-indices (delete-assoc-equal name fs))
                     alv)))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-3
  (implies (and (consp (assoc-equal name fs))
                (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
                (l3-fs-p fs)
                (boolean-listp alv)
                (indices-marked-p (l4-list-all-indices fs)
                                  alv))
           (indices-marked-p (l4-list-all-indices (cdr (assoc-equal name fs)))
                             alv)))

;; this should be where the encapsulate begins

(defun l4-collect-all-index-lists (fs)
  (declare (xargs :guard (l4-fs-p fs)))
  (if (atom fs)
      nil
    (let* ((directory-or-file-entry (car fs))
           (entry (cdr directory-or-file-entry))
           (tail (l4-collect-all-index-lists (cdr fs))))
      (if (l4-regular-file-entry-p entry)
          (cons (car entry) tail)
        (binary-append (l4-collect-all-index-lists entry) tail))))
  )

(defthm l4-collect-all-index-lists-correctness-1
  (implies (l3-fs-p fs)
           (true-list-listp (l4-collect-all-index-lists fs))))

(include-book "flatten-lemmas")

;; This theorem shows the equivalence between two ways of listing indices
(defthm l4-collect-all-index-lists-correctness-2
  (implies (l3-fs-p fs)
           (equal (flatten (l4-collect-all-index-lists fs))
                  (l4-list-all-indices fs))))

;; this should be where the encapsulate ends

(defthm l4-wrchs-returns-stricter-fs-lemma-4
  (implies (and (consp (assoc-equal name fs))
                (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (no-duplicatesp-equal (l4-list-all-indices fs)))
           (no-duplicatesp-equal (car (cdr (assoc-equal name fs))))))

(defthm l4-wrchs-returns-stricter-fs-lemma-5
  (implies (and (consp (assoc-equal name fs))
                (l3-fs-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (no-duplicatesp-equal (l4-list-all-indices fs)))
           (no-duplicatesp-equal (l4-list-all-indices (cdr (assoc-equal name fs))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-6
  (implies
   (l3-fs-p fs)
   (subsetp-equal
    (l4-collect-all-index-lists (delete-assoc-equal name fs))
    (l4-collect-all-index-lists fs)))
  :hints (("Subgoal *1/3.2'"
           :in-theory (disable subsetp-of-binary-append-1)
           :use (:instance subsetp-of-binary-append-1
                           (x (cons (cadr (car fs)) nil))
                           (y (l4-collect-all-index-lists (cdr fs)) )))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-7
  (implies (and (consp fs)
                (l3-fs-p fs)
                (not-intersectp-list x (l4-collect-all-index-lists fs)))
           (not-intersectp-list
            x
            (l4-collect-all-index-lists (delete-assoc-equal name fs)))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-8
  (implies (and (l3-fs-p fs)
                (disjoint-list-listp (l4-collect-all-index-lists fs)))
           (disjoint-list-listp
            (l4-collect-all-index-lists (delete-assoc-equal name fs)))))

(defthm l4-wrchs-returns-stricter-fs-lemma-9
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (consp (assoc-equal name fs))
                (l3-fs-p fs))
           (member-equal (cadr (assoc-equal name fs))
                         (l4-collect-all-index-lists fs))))

;; too many hypotheses, because of too many hypotheses in
;; member-intersectp-binary-append
(defthm
  l4-wrchs-returns-stricter-fs-lemma-10
  (implies
   (and
    (l3-fs-p fs1)
    (l3-regular-file-entry-p (cdr (assoc-equal name fs2)))
    (consp (assoc-equal name fs2))
    (l3-fs-p fs2)
    (not (member-intersectp-equal (l4-collect-all-index-lists fs1)
                                  (l4-collect-all-index-lists fs2))))
   (not-intersectp-list (cadr (assoc-equal name fs2))
                        (l4-collect-all-index-lists fs1)))
  :hints
  (("Goal"
    :use (:instance intersectp-member-when-not-member-intersectp
                    (lst1 (l4-collect-all-index-lists fs1))
                    (lst2 (l4-collect-all-index-lists fs2))
                    (x (cadr (assoc-equal name fs2)))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-11
  (implies (and (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
                (consp (assoc-equal name fs))
                (l3-fs-p fs)
                (member-intersectp-equal
                 (l4-collect-all-index-lists (cdr (assoc-equal name fs)))
                 l))
           (member-intersectp-equal l (l4-collect-all-index-lists fs))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-12
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (consp (assoc-equal name fs))
                (l3-fs-p fs)
                (not-intersectp-list l (l4-collect-all-index-lists fs))
                (disjoint-list-listp (l4-collect-all-index-lists fs)))
           (not (intersectp-equal (cadr (assoc-equal name fs))
                                  l)))
  :hints (("Goal" :use (:instance intersectp-is-commutative (y l)
                                  (x (cadr (assoc-equal name fs)))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-13
  (implies (and (consp (assoc-equal name fs))
                (l3-fs-p fs)
                (disjoint-list-listp (l4-collect-all-index-lists fs))
                (not (l3-regular-file-entry-p (cdr (assoc-equal name fs)))))
           (disjoint-list-listp
            (l4-collect-all-index-lists (cdr (assoc-equal name fs))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-14
  (implies (and (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
                (consp (assoc-equal name fs))
                (l3-fs-p fs)
                (not-intersectp-list l (l4-collect-all-index-lists fs)))
           (not-intersectp-list
            l
            (l4-collect-all-index-lists (cdr (assoc-equal name fs))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-15
  (implies
   (and (consp (assoc-equal name fs))
        (l3-fs-p fs)
        (disjoint-list-listp (l4-collect-all-index-lists fs)))
   (disjoint-list-listp
    (if (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
        (cons (cadr (assoc-equal name fs))
              (l4-collect-all-index-lists (delete-assoc-equal name fs)))
      (binary-append
       (l4-collect-all-index-lists (cdr (assoc-equal name fs)))
       (l4-collect-all-index-lists (delete-assoc-equal name fs))))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (consp (assoc-equal name fs))
          (l3-fs-p fs)
          (disjoint-list-listp (l4-collect-all-index-lists fs))
          (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
     (disjoint-list-listp
      (cons (cadr (assoc-equal name fs))
            (l4-collect-all-index-lists (delete-assoc-equal name fs))))))
   (:rewrite
    :corollary
    (implies
     (and (consp (assoc-equal name fs))
          (l3-fs-p fs)
          (disjoint-list-listp (l4-collect-all-index-lists fs))
          (not (l3-regular-file-entry-p (cdr (assoc-equal name fs)))))
     (disjoint-list-listp
      (binary-append
       (l4-collect-all-index-lists (cdr (assoc-equal name fs)))
       (l4-collect-all-index-lists (delete-assoc-equal name fs)))))))
  :hints
  (("Subgoal *1/2.1''"
    :use
    ((:instance
      member-intersectp-is-commutative
      (x (l4-collect-all-index-lists (cdr (assoc-equal name (cdr fs)))))
      (y
       (cons
        (cadr (car fs))
        (l4-collect-all-index-lists (delete-assoc-equal name (cdr fs))))))
     (:instance
      member-intersectp-is-commutative
      (x (l4-collect-all-index-lists (delete-assoc-equal name (cdr fs))))
      (y (l4-collect-all-index-lists
          (cdr (assoc-equal name (cdr fs))))))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-16
  (implies
   (and (not-intersectp-list l (l4-collect-all-index-lists fs))
        (l3-fs-p fs))
   (not-intersectp-list
    l
    (l4-collect-all-index-lists (delete-assoc-equal name fs)))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-17
  (implies
   (and (not-intersectp-list l (l4-collect-all-index-lists fs))
        (l3-fs-p fs))
   (not
    (intersectp-equal
     l
     (flatten (l4-collect-all-index-lists (delete-assoc-equal name fs))))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (and (not-intersectp-list l (l4-collect-all-index-lists fs))
                  (l3-fs-p fs))
             (not (intersectp-equal
                   l
                   (l4-list-all-indices (delete-assoc-equal name fs)))))))
  :hints
  (("Goal" :in-theory (disable not-intersectp-list-correctness-1)
    :use
    (:instance
     not-intersectp-list-correctness-1 (x l)
     (l (l4-collect-all-index-lists (delete-assoc-equal name fs)))))))

(skip-proofs
 (defthm l4-wrchs-returns-stricter-fs-lemma-18
   (implies
    (and (symbol-listp hns)
         (l3-fs-p fs)
         (boolean-listp alv)
         (indices-marked-p (l4-list-all-indices fs)
                           alv)
         (integerp start)
         (<= 0 start)
         (stringp text)
         (block-listp disk)
         (equal (len alv) (len disk))
         (no-duplicatesp-equal (l4-list-all-indices fs)))
    (indices-marked-p
     (l4-list-all-indices (mv-nth 0 (l4-wrchs hns fs disk alv start text)))
     (mv-nth 2
             (l4-wrchs hns fs disk alv start text))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-19
  (implies
   (and (symbol-listp hns)
        (l3-fs-p fs)
        (boolean-listp alv)
        (no-duplicatesp-equal (l4-list-all-indices fs))
        (indices-marked-p (l4-list-all-indices fs)
                          alv)
        (integerp start)
        (<= 0 start)
        (stringp text)
        (block-listp disk)
        (equal (len alv) (len disk)))
   (bounded-nat-listp
    (l4-list-all-indices (mv-nth 0 (l4-wrchs hns fs disk alv start text)))
    (len (mv-nth 2
                 (l4-wrchs hns fs disk alv start text)))))
  :hints
  (("Goal"
    :in-theory (disable l4-list-all-indices-correctness-1
                        indices-marked-p-correctness-1)
    :use
    ((:instance
      indices-marked-p-correctness-1
      (b (len (mv-nth 2
                      (l4-wrchs hns fs disk alv start text))))
      (index-list
       (l4-list-all-indices (mv-nth 0 (l4-wrchs hns fs disk alv start text))))
      (alv (mv-nth 2
                   (l4-wrchs hns fs disk alv start text))))
     (:instance l4-list-all-indices-correctness-1
                (fs (mv-nth 0 (l4-wrchs hns fs disk alv start text))))))))

(defthm
 l4-wrchs-returns-stricter-fs-lemma-20
 (implies
  (and (l3-fs-p fs)
       (not (intersectp-equal l (l4-list-all-indices fs))))
  (not
      (intersectp-equal l
                        (l4-list-all-indices (delete-assoc-equal name fs))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-21
  (implies
   (and (l3-fs-p fs)
        (no-duplicatesp-equal (l4-list-all-indices fs)))
   (no-duplicatesp-equal (l4-list-all-indices (delete-assoc-equal name fs)))))

(defthm if-directory-then-not-file (implies (l3-fs-p fs) (not (l3-regular-file-entry-p fs))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-22
  (implies (and (natp n)
                (indices-marked-p index-list alv)
                (boolean-listp alv)
                (nat-listp index-list))
           (not (intersectp-equal (find-n-free-blocks alv n)
                                  index-list)))
  :hints (("Subgoal *1/1''"
           :use (:instance intersectp-is-commutative (x index-list)
                           (y (find-n-free-blocks alv n))))
          ("Subgoal *1/4''" :use ((:instance intersectp-is-commutative
                                             (x (find-n-free-blocks alv n))
                                             (y index-list))
                                  (:instance intersectp-is-commutative
                                             (x (find-n-free-blocks alv n))
                                             (y (cdr index-list)))))))

(defthm l4-wrchs-returns-stricter-fs-lemma-23
  (implies (and (nat-listp index-list1)
                (nat-listp index-list2)
                (indices-marked-p index-list1 alv)
                (boolean-listp alv)
                (not (intersectp-equal index-list1 index-list2)))
           (indices-marked-p index-list1
                             (set-indices-in-alv alv index-list2 nil))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-24
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (not (intersectp-equal (l4-list-all-indices fs)
                                       l)))
           (not (intersectp-equal l (cadr (assoc-equal name fs)))))
   :hints (("Goal" :in-theory (enable intersectp-is-commutative))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-25
  (implies
   (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
        (l3-fs-p fs)
        (no-duplicatesp-equal (l4-list-all-indices fs)))
   (not (intersectp-equal (l4-list-all-indices (delete-assoc-equal name fs))
                          (cadr (assoc-equal name fs)))))
  :hints (("Goal" :in-theory (enable intersectp-is-commutative))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-26
  (implies (and (character-listp cl)
                (boolean-listp alv)
                (<= (len (make-blocks cl))
                    (count-free-blocks alv)))
           (l3-regular-file-entry-p
            (cons (find-n-free-blocks alv (len (make-blocks cl)))
                  (len cl))))
  :hints (("goal" :in-theory (enable l3-regular-file-entry-p))))

(verify(IMPLIES
 (AND
  (CONSP HNS)
  (CONSP FS)
  (CONSP (ASSOC-EQUAL NAME FS))
  (NOT (L3-REGULAR-FILE-ENTRY-P (CDR (ASSOC-EQUAL NAME FS))))
  (L3-FS-P FS)
  (NO-DUPLICATESP-EQUAL (L4-LIST-ALL-INDICES FS))
  )
 (NOT (INTERSECTP-EQUAL
           (L4-LIST-ALL-INDICES (CDR (ASSOC-EQUAL NAME FS)))
           (L4-LIST-ALL-INDICES (DELETE-ASSOC-EQUAL NAME FS))))))

(skip-proofs
 (defthm
  L4-WRCHS-RETURNS-STRICTER-FS-LEMMA-27
  (IMPLIES
   (AND
    (NO-DUPLICATESP-EQUAL
     (L4-LIST-ALL-INDICES (MV-NTH 0
                                  (L4-WRCHS hns
                                            fs
                                            DISK ALV START TEXT))))
    (SYMBOL-LISTP hns)
    (L3-FS-P FS)
    (BOOLEAN-LISTP ALV)
    (INDICES-MARKED-P (L4-LIST-ALL-INDICES FS)
                      ALV)
    (INTEGERP START)
    (<= 0 START)
    (STRINGP TEXT)
    (BLOCK-LISTP DISK)
    (EQUAL (LEN ALV) (LEN DISK))
    (nat-listp l)
    (INDICES-MARKED-P l
                      ALV)
    (not (INTERSECTP-equal
         (l4-list-all-indices fs)
         l)))
   (not (INTERSECTP-equal
         (l4-list-all-indices (MV-NTH 0
                                      (L4-WRCHS hns
                                                fs
                                                DISK ALV START TEXT)))
         l)))
   :hints (("Subgoal *1/7" :in-theory (enable l3-regular-file-entry-p)))))

(defthm
  L4-WRCHS-RETURNS-STRICTER-FS-LEMMA-28
  (IMPLIES
   (AND (SYMBOL-LISTP HNS)
        (L3-FS-P FS)
        (BOOLEAN-LISTP ALV)
        (NO-DUPLICATESP-EQUAL (L4-LIST-ALL-INDICES FS))
        (INDICES-MARKED-P (L4-LIST-ALL-INDICES FS)
                          ALV)
        (INTEGERP START)
        (<= 0 START)
        (STRINGP TEXT)
        (BLOCK-LISTP DISK)
        (EQUAL (LEN ALV) (LEN DISK)))
   (NO-DUPLICATESP-EQUAL
    (L4-LIST-ALL-INDICES (mv-nth 0 (L4-WRCHS HNS FS DISK ALV START
                                             TEXT)))))
  :hints (("Subgoal *1/6" :in-theory (enable l3-regular-file-entry-p))
          ("Subgoal *1/4" :in-theory (enable intersectp-is-commutative))
          ("Subgoal *1/5" :in-theory (enable intersectp-is-commutative))))

(defthm l4-wrchs-returns-stricter-fs
  (implies (and (symbol-listp hns)
                (l4-stricter-fs-p fs alv)
                (natp start)
                (stringp text)
                (block-listp disk)
                (equal (len alv) (len disk)))
           (mv-let (new-fs new-disk new-alv)
             (l4-wrchs hns fs disk alv start text)
             (declare (ignore new-disk))
             (l4-stricter-fs-p new-fs new-alv))))

(defun l4-to-l3-fs (fs disk)
  (mv fs disk))

(defthmd l4-to-l3-fs-correctness-1
  (implies (and (l4-fs-p fs) (block-listp disk))
           (mv-let (new-fs new-disk) (l4-to-l3-fs fs disk)
             (and (l3-fs-p new-fs) (block-listp new-disk)))))

;; We can't prove that equality keeps holding under this transformation. Thus,
;; we will need to prove something stronger - any read, anywhere, after a create,
;; write or delete operation, preserves the properties we want.

;; We will probably need a new induction scheme.
(defthm l4-wrchs-correctness-1
  (implies (and (L4-STRICTER-FS-P FS ALV)
                (equal (len disk) (len alv))
                (>= (count-free-blocks alv) (len (make-blocks text))))
           (equal (mv-let (new-fs2 new-disk2) (mv-let (new-fs4 new-disk4) (l4-to-l3-fs fs
                                                                                       disk) (l3-wrchs hns new-fs4 new-disk4 start text)) (l3-stat hns1 new-fs2 new-disk2))
                  (mv-let (new-fs3 new-disk3) (mv-let (new-fs5 new-disk5 new-alv5)
                                                (l4-wrchs hns fs disk alv start text)
                                                (declare (ignore new-alv5))
                                                (l4-to-l3-fs new-fs5
                                                             new-disk5))
                    (l3-stat hns1 new-fs3 new-disk3))))
  :hints ( ("Goal''" :induct (and (L4-WRCHS HNS FS DISK ALV START TEXT)
                                (L3-WRCHS HNS FS DISK START TEXT)
                                (L3-STAT HNS1 fs disk)))))

