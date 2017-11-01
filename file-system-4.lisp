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
(include-book "find-n-free-blocks")
(include-book "set-indices")

(defthm mv-nth-replacement
  (equal (mv-nth n (cons a b))
         (if (zp n) a (mv-nth (- n 1) b))))

(in-theory (disable mv-nth))

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

(defund l4-list-all-indices (fs)
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
           (nat-listp (l4-list-all-indices fs)))
  :hints (("Goal" :in-theory (enable l4-list-all-indices)) ))

(defun l4-stricter-fs-p (fs alv)
  (declare (xargs :guard t :guard-debug t))
  (and (l4-fs-p fs)
       (boolean-listp alv)
       (let ( (all-indices (l4-list-all-indices fs)))
         (and (nat-listp all-indices)
              (no-duplicatesp all-indices)
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
                  (l4-list-all-indices fs)))
  :hints (("Goal" :in-theory (enable l4-list-all-indices)) ))

(defthm
  l4-collect-all-index-lists-correctness-3
  (implies
   (l3-fs-p fs)
   (equal (no-duplicatesp-equal (l4-list-all-indices fs))
          (and (disjoint-list-listp (l4-collect-all-index-lists fs))
               (no-duplicates-listp (l4-collect-all-index-lists fs)))))
  :hints
  (("goal" :in-theory (disable flatten-disjoint-lists)
    :use ((:instance flatten-disjoint-lists
                     (l (l4-collect-all-index-lists fs)))))))

(defun indices-marked-listp (l alv)
  (if (atom l)
      (equal l nil)
    (and (indices-marked-p (car l) alv) (indices-marked-listp (cdr l) alv))))

(defthm indices-marked-p-of-flatten
  (implies (true-listp l)
           (equal (indices-marked-p (flatten l) alv)
                  (indices-marked-listp l alv))))

(defthm l4-indices-marked-p-of-list-all-indices
  (implies (l3-fs-p fs)
           (equal (indices-marked-p (l4-list-all-indices fs)
                                    alv)
                  (indices-marked-listp (l4-collect-all-index-lists fs)
                                        alv)))
  :hints (("goal" :in-theory (disable indices-marked-p-of-flatten)
           :use (:instance indices-marked-p-of-flatten
                           (l (l4-collect-all-index-lists fs))))))

(defthm indices-marked-listp-of-binary-append
  (implies (true-listp l1)
   (equal (indices-marked-listp (binary-append l1 l2) alv)
          (and (indices-marked-listp l1 alv)
               (indices-marked-listp l2 alv)))))

;; this should be where the encapsulate ends

(defthm l4-wrchs-returns-stricter-fs-lemma-1
  (implies
   (and
    (consp (assoc-equal name fs))
    (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
    (l3-fs-p fs)
    (disjoint-list-listp (l4-collect-all-index-lists fs)))
   (disjoint-list-listp
    (l4-collect-all-index-lists (cdr (assoc-equal name fs))))))

(defthm l4-wrchs-returns-stricter-fs-lemma-2
  (implies
   (and (consp (assoc-equal name fs))
        (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
        (l3-fs-p fs)
        (indices-marked-listp (l4-collect-all-index-lists fs)
                              alv))
   (indices-marked-listp
    (l4-collect-all-index-lists (cdr (assoc-equal name fs)))
    alv)))

(defthm l4-wrchs-returns-stricter-fs-lemma-3
  (implies
   (and
    (consp (assoc-equal name fs))
    (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
    (l3-fs-p fs)
    (no-duplicates-listp (l4-collect-all-index-lists fs)))
   (no-duplicates-listp
    (l4-collect-all-index-lists (cdr (assoc-equal name fs))))))

(defthm l4-wrchs-returns-stricter-fs-lemma-4
  (implies (member-intersectp-equal l b)
           (member-intersectp-equal l (cons a b))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-5
  (implies
   (and (l3-fs-p fs)
        (not (member-intersectp-equal (l4-collect-all-index-lists fs)
                                      l)))
   (not (member-intersectp-equal
         l
         (l4-collect-all-index-lists (delete-assoc-equal name fs))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-6
  (implies (and (l3-fs-p fs)
                (not-intersectp-list l (l4-collect-all-index-lists fs)))
           (not-intersectp-list
            l
            (l4-collect-all-index-lists (delete-assoc-equal name fs)))))

(defthm l4-wrchs-returns-stricter-fs-lemma-7
  (implies
   (and (l3-fs-p fs)
        (disjoint-list-listp (l4-collect-all-index-lists fs)))
   (disjoint-list-listp
    (l4-collect-all-index-lists (delete-assoc-equal name fs)))))

(defthm l4-wrchs-returns-stricter-fs-lemma-8
  (implies
   (and (l3-fs-p fs)
        (no-duplicates-listp (l4-collect-all-index-lists fs)))
   (no-duplicates-listp
    (l4-collect-all-index-lists (delete-assoc-equal name fs)))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-9
  (implies (and (l3-fs-p fs)
                (boolean-listp alv)
                (indices-marked-listp (l4-collect-all-index-lists fs)
                                      alv))
           (indices-marked-listp
            (l4-collect-all-index-lists (delete-assoc-equal name fs))
            alv)))

(defthm l4-wrchs-returns-stricter-fs-lemma-10
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (boolean-listp alv)
                (indices-marked-listp (l4-collect-all-index-lists fs)
                                      alv))
           (indices-marked-p (cadr (assoc-equal name fs))
                             alv)))

(defthm l4-wrchs-returns-stricter-fs-lemma-11
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (no-duplicates-listp (l4-collect-all-index-lists fs)))
           (no-duplicatesp-equal (cadr (assoc-equal name fs)))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-12
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (not-intersectp-list l (l4-collect-all-index-lists fs)))
           (not (intersectp-equal l (cadr (assoc-equal name fs))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-13
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (not (member-intersectp-equal (l4-collect-all-index-lists fs)
                                              l)))
           (not-intersectp-list (cadr (assoc-equal name fs))
                                l)))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-14
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (disjoint-list-listp (l4-collect-all-index-lists fs)))
           (not-intersectp-list
            (cadr (assoc-equal name fs))
            (l4-collect-all-index-lists (delete-assoc-equal name fs)))))

(defthm l4-wrchs-returns-stricter-fs-lemma-15
  (implies (and (boolean-listp alv)
                (indices-marked-p l alv)
                (natp n))
           (not (intersectp-equal l (find-n-free-blocks alv n)))))

(defthm l4-wrchs-returns-stricter-fs-lemma-16
  (implies (and (natp n)
                (l3-fs-p fs)
                (boolean-listp alv)
                (indices-marked-listp (l4-collect-all-index-lists fs)
                                      alv))
           (not-intersectp-list (find-n-free-blocks alv n)
                                (l4-collect-all-index-lists fs))))

(defthm l4-wrchs-returns-stricter-fs-lemma-17
  (implies (and (boolean-listp alv)
                (nat-listp l)
                (bounded-nat-listp index-list (len alv))
                (indices-marked-p index-list alv)
                (not (intersectp-equal l index-list)))
           (indices-marked-p index-list
                             (set-indices-in-alv alv l nil))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-18
  (implies (and (l3-fs-p fs)
                (nat-listp l)
                (boolean-listp alv)
                (indices-marked-listp (l4-collect-all-index-lists fs)
                                      alv)
                (not-intersectp-list l (l4-collect-all-index-lists fs)))
           (indices-marked-listp (l4-collect-all-index-lists fs)
                                 (set-indices-in-alv alv l nil))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-19
  (implies (and (l3-fs-p fs)
                (nat-listp l)
                (boolean-listp alv)
                (indices-marked-listp (l4-collect-all-index-lists fs)
                                      alv))
           (indices-marked-listp (l4-collect-all-index-lists fs)
                                 (set-indices-in-alv alv l t))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-20
  (implies
   (and (consp (assoc-equal name fs))
        (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
        (l3-fs-p fs)
        (not (member-intersectp-equal l (l4-collect-all-index-lists fs))))
   (not (member-intersectp-equal
         l
         (l4-collect-all-index-lists (cdr (assoc-equal name fs)))))))

(defthm l4-wrchs-returns-stricter-fs-lemma-21
  (implies (and (natp n)
                (boolean-listp alv)
                (indices-marked-listp l alv))
           (not-intersectp-list (find-n-free-blocks alv n)
                                l)))

;; (defthm l4-wrchs-returns-stricter-fs-lemma-22
;;   (implies (and (boolean-listp alv)
;;                 (indices-marked-p l alv)
;;                 (not (intersectp-equal l index-list))
;;                 (nat-listp index-list)
;;                 (bounded-nat-listp l (len alv)))
;;            (indices-marked-p l
;;                              (set-indices-in-alv alv index-list nil))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-22
  (implies (and (boolean-listp alv)
                (nat-listp index-list)
                (true-list-listp l)
                (bounded-nat-listp (flatten l)
                                   (len alv))
                (indices-marked-listp l alv)
                (not-intersectp-list index-list l))
           (indices-marked-listp l
                                 (set-indices-in-alv alv index-list nil)))
  :hints (("Subgoal *1/6" :expand (flatten l))))

(defthm l4-wrchs-returns-stricter-fs-lemma-23
  (implies (and (true-list-listp l)
                (indices-marked-listp l alv)
                (nat-listp (flatten l)))
           (bounded-nat-listp (flatten l) (len alv))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-24
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (boolean-listp alv)
                (indices-marked-listp (l4-collect-all-index-lists fs)
                                      alv))
           (bounded-nat-listp (cadr (assoc-equal name fs))
                              (len alv))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-25
  (implies (and (consp (assoc-equal name fs))
                (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
                (l3-fs-p fs)
                (not-intersectp-list l (l4-collect-all-index-lists fs)))
           (not-intersectp-list
            l
            (l4-collect-all-index-lists (cdr (assoc-equal name fs))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-26
  (implies
   (and
    (l3-fs-p fs)
    (symbol-listp hns)
    (boolean-listp alv)
    (indices-marked-listp (l4-collect-all-index-lists fs)
                          alv)
    (integerp start)
    (<= 0 start)
    (stringp text)
    (block-listp disk)
    (equal (len alv) (len disk))
    (bounded-nat-listp l (len alv))
    (not-intersectp-list l (l4-collect-all-index-lists fs))
    (indices-marked-p l alv))
   (indices-marked-p l
                     (mv-nth 2
                             (l4-wrchs hns fs disk alv start text))))
  :hints
  (("Subgoal *1/5"
    :in-theory (disable indices-marked-p-correctness-3)
    :use
    ((:instance
      indices-marked-p-correctness-3
      (index-list1 l)
      (alv (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs))
                               nil))
      (index-list2
       (find-n-free-blocks
        (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs))
                            nil)
        (len
         (make-blocks
          (insert-text
           (unmake-blocks
            (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs)))
            (cddr (assoc-equal (car hns) fs)))
           start text))))))
     (:instance set-indices-in-alv-correctness-2
                (index-list (cadr (assoc-equal (car hns) fs)))
                (value nil))
     (:instance
      indices-marked-p-correctness-1
      (index-list l)
      (b (len (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs))
                                  nil))))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-27
  (implies
   (and (l3-fs-p fs)
        (symbol-listp hns)
        (boolean-listp alv)
        (indices-marked-listp (l4-collect-all-index-lists fs)
                              alv)
        (integerp start)
        (<= 0 start)
        (stringp text)
        (block-listp disk)
        (equal (len alv) (len disk))
        (bounded-nat-listp (flatten l)
                           (len alv))
        (not (member-intersectp-equal l (l4-collect-all-index-lists fs)))
        (indices-marked-listp l alv)
        (true-list-listp l))
   (indices-marked-listp l
                         (mv-nth 2
                                 (l4-wrchs hns fs disk alv start text))))
  :hints (("Goal" :induct (indices-marked-listp l alv))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-28
  (implies
   (and (l3-fs-p fs)
        (boolean-listp alv)
        (indices-marked-listp (l4-collect-all-index-lists fs)
                              alv))
   (bounded-nat-listp
    (flatten (l4-collect-all-index-lists (delete-assoc-equal (car hns) fs)))
    (len alv)))
  :hints
  (("Goal" :in-theory (disable l4-collect-all-index-lists-correctness-2))
   ("Subgoal *1/2.2'"
    :in-theory (disable indices-marked-p-correctness-1)
    :use
    ((:instance indices-marked-p-correctness-1
                (index-list (flatten (l4-collect-all-index-lists (cdr fs))))
                (b (len alv)))))
   ("Subgoal *1/3.1'"
    :in-theory (disable indices-marked-p-correctness-1)
    :use
    ((:instance
      indices-marked-p-correctness-1
      (index-list (flatten (l4-collect-all-index-lists (cdr (car fs)))))
      (b (len alv)))))
   ("Subgoal *1/3.2'"
    :in-theory (disable indices-marked-p-correctness-1)
    :use
    ((:instance indices-marked-p-correctness-1
                (index-list (flatten (l4-collect-all-index-lists (cdr fs))))
                (b (len alv)))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-29
  (implies
   (and (consp (assoc-equal name fs))
        (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
        (l3-fs-p fs)
        (disjoint-list-listp (l4-collect-all-index-lists fs))
        (no-duplicates-listp (l4-collect-all-index-lists fs)))
   (not (member-intersectp-equal
         (l4-collect-all-index-lists (delete-assoc-equal name fs))
         (l4-collect-all-index-lists (cdr (assoc-equal name fs))))))
  :hints
  (("Subgoal *1/7''"
    :in-theory (disable member-intersectp-is-commutative)
    :use
    (:instance
     member-intersectp-is-commutative
     (x (l4-collect-all-index-lists (cdr (assoc-equal name (cdr fs)))))
     (y
      (cons
       (cadr (car fs))
       (l4-collect-all-index-lists (delete-assoc-equal name
                                                       (cdr fs)))))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-30
  (implies
   (and (symbol-listp hns)
        (l3-fs-p fs)
        (boolean-listp alv)
        (indices-marked-listp (l4-collect-all-index-lists fs)
                              alv)
        (integerp start)
        (<= 0 start)
        (stringp text)
        (block-listp disk)
        (equal (len alv) (len disk))
        (not-intersectp-list l (l4-collect-all-index-lists fs))
        (indices-marked-p l alv)
        (nat-listp l))
   (not-intersectp-list l
                        (l4-collect-all-index-lists
                         (mv-nth 0
                                 (l4-wrchs hns fs disk alv start text)))))
  :hints (("subgoal *1/6.2" :in-theory (enable l3-regular-file-entry-p))
          ("subgoal *1/5.2" :in-theory (enable l3-regular-file-entry-p))
          ("subgoal *1/4.2" :in-theory (enable l3-regular-file-entry-p))
          ("subgoal *1/3.2" :in-theory (enable l3-regular-file-entry-p))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-31
  (implies
   (and (symbol-listp hns)
        (l3-fs-p fs)
        (boolean-listp alv)
        (indices-marked-listp (l4-collect-all-index-lists fs)
                              alv)
        (integerp start)
        (<= 0 start)
        (stringp text)
        (block-listp disk)
        (equal (len alv) (len disk))
        (not (member-intersectp-equal l (l4-collect-all-index-lists fs)))
        (indices-marked-listp l alv)
        (nat-listp (flatten l))
        (true-list-listp l))
   (not (member-intersectp-equal
         l
         (l4-collect-all-index-lists
          (mv-nth 0
                  (l4-wrchs hns fs disk alv start text))))))
  :hints (("Goal" :induct (indices-marked-listp l alv))
          ("Subgoal *1/2" :expand (flatten l))))


(defthm l4-wrchs-returns-stricter-fs-lemma-32
  (implies
   (and (symbol-listp hns)
        (l3-fs-p fs)
        (boolean-listp alv)
        (disjoint-list-listp (l4-collect-all-index-lists fs))
        (no-duplicates-listp (l4-collect-all-index-lists fs))
        (indices-marked-listp (l4-collect-all-index-lists fs)
                              alv)
        (integerp start)
        (<= 0 start)
        (stringp text)
        (block-listp disk)
        (equal (len alv) (len disk)))
   (and
    (indices-marked-listp
     (l4-collect-all-index-lists (mv-nth 0
                                         (l4-wrchs hns fs disk alv start text)))
     (mv-nth 2
             (l4-wrchs hns fs disk alv start text)))
    (disjoint-list-listp (l4-collect-all-index-lists
                          (mv-nth 0
                                  (l4-wrchs hns fs disk alv start text))))))
  :hints (("Goal" :induct t)
          ("Subgoal *1/7.2" :in-theory (disable l4-collect-all-index-lists-correctness-2))
          ("Subgoal *1/7''" :in-theory (disable l4-collect-all-index-lists-correctness-2))
          ("subgoal *1/6" :in-theory (enable l3-regular-file-entry-p))))

;; find a simpler problem that doesn't have all these details, that shows the
;; same kind of issue
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
             (l4-stricter-fs-p new-fs new-alv)))
  :hints (("Subgoal *1/6" :in-theory (enable L3-REGULAR-FILE-ENTRY-P))))

(defun l4-to-l2-fs (fs disk)
  (declare (xargs :guard (and (l4-fs-p fs) (block-listp disk))
                  ))
  (l3-to-l2-fs fs disk))

;; This theorem shows the type-correctness of l4-to-l2-fs.
(defthm l4-to-l2-fs-correctness-1
  (implies (and (l4-fs-p fs) (block-listp disk))
           (l2-fs-p (l4-to-l2-fs fs disk))))

;; This is the first of two theorems showing the equivalence of the l4 and l2
;; versions of stat.
(defthm l4-stat-correctness-1
  (implies (and (symbol-listp hns)
                (l4-fs-p fs)
                (block-listp disk)
                (stringp (l4-stat hns fs disk)))
           (equal (l2-stat hns (l4-to-l2-fs fs disk))
                  (l4-stat hns fs disk))))

;; This is the second of two theorems showing the equivalence of the l4 and l2
;; versions of stat.
(defthm l4-stat-correctness-2
  (implies (and (symbol-listp hns)
                (l4-fs-p fs)
                (block-listp disk)
                (l4-fs-p (l4-stat hns fs disk)))
           (equal (l2-stat hns (l4-to-l2-fs fs disk))
                  (l4-to-l2-fs (l4-stat hns fs disk) disk)))
  )

;; This theorem proves the equivalence of the l4 and l2 versions of rdchs.
(defthm l4-rdchs-correctness-1
  (implies (and (symbol-listp hns)
                (l4-fs-p fs)
                (natp start)
                (natp n)
                (block-listp disk))
           (equal (l2-rdchs hns (l4-to-l2-fs fs disk) start n)
                  (l4-rdchs hns fs disk start n))))

(defthm
  l4-wrchs-correctness-1-lemma-1
  (implies (and (natp key)
                (< key (len block-list))
                (block-listp block-list)
                (nat-listp index-list)
                (not (member-equal key index-list)))
           (equal (fetch-blocks-by-indices (update-nth key val block-list)
                                           index-list)
                  (fetch-blocks-by-indices block-list index-list))))

(defthm l4-wrchs-correctness-1-lemma-2
  (implies (and (l3-regular-file-entry-p (cdr (car fs)))
                (not (member-equal index (l4-list-all-indices fs))))
           (not (member-equal index (cadr (car fs)))))
  :hints (("goal" :in-theory (enable l4-list-all-indices))))

(defthm
  l4-wrchs-correctness-1-lemma-3
  (implies (and (consp fs)
                (l3-fs-p fs)
                (member-equal index (l4-list-all-indices (cdr fs))))
           (member-equal index (l4-list-all-indices fs)))
  :hints (("goal" :expand (l4-list-all-indices fs))))

(defthm
  l4-wrchs-correctness-1-lemma-4
  (implies (and (l3-fs-p fs)
                (consp (car fs))
                (l3-fs-p (cdr (car fs)))
                (member-equal index
                              (l4-list-all-indices (cdr (car fs)))))
           (member-equal index (l4-list-all-indices fs)))
  :hints (("goal" :expand (l4-list-all-indices fs))))

(defthm l4-wrchs-correctness-1-lemma-5
  (implies (and (l3-fs-p fs)
                (boolean-listp alv)
                (stringp text)
                (integerp start)
                (<= 0 start)
                (block-listp disk)
                (<= 0 (count-free-blocks alv))
                (integerp index)
                (<= 0 index)
                (< index (len disk))
                (not (member-equal index (l4-list-all-indices fs))))
           (equal (l3-to-l2-fs fs (update-nth index value disk))
                  (l3-to-l2-fs fs disk))))

;; (verify (IMPLIES (AND
;;                (CONSP INDEX-LIST)
;;                (MEMBER-EQUAL (CAR INDEX-LIST)
;;                              (L4-LIST-ALL-INDICES FS))
;;                (L3-FS-P FS)
;;                (NAT-LISTP (CDR INDEX-LIST)))
;;               (not (NOT-INTERSECTP-LIST INDEX-LIST
;;                                         (L4-COLLECT-ALL-INDEX-LISTS FS))))
;;  :instructions ((prove      :hints (("Goal" :in-theory (enable L4-LIST-ALL-INDICES)) ))))

(defthm l4-wrchs-correctness-1-lemma-6 (IMPLIES (AND
               (CONSP INDEX-LIST)
               (MEMBER-EQUAL (CAR INDEX-LIST)
                             (L4-LIST-ALL-INDICES FS))
               (L3-FS-P FS)
               (NAT-LISTP (CDR INDEX-LIST)))
              (not (NOT-INTERSECTP-LIST INDEX-LIST
                                        (L4-COLLECT-ALL-INDEX-LISTS FS))))
     :hints (("Goal" :in-theory (enable L4-LIST-ALL-INDICES)) ))

;; This theorem shows the equivalence of the l4 and l2 versions of wrchs.
(defthm l4-wrchs-correctness-1
  (implies (and (l4-stricter-fs-p fs alv)
                (stringp text)
                (natp start)
                (symbol-listp hns)
                (block-listp disk)
                (<= (len (make-blocks text)) (count-free-blocks alv)))
           (equal (l2-wrchs hns (l4-to-l2-fs fs disk) start text)
                  (mv-let (new-fs new-disk new-alv)
                    (l4-wrchs hns fs disk alv start text)
                    (declare (ignore new-alv))
                    (l4-to-l2-fs new-fs new-disk))))
  :hints ()
  ;; (("Subgoal *1/8.9'"
  ;;   :in-theory (disable l3-wrchs-returns-fs)
  ;;   :use (:instance l3-wrchs-returns-fs (hns (cdr hns))
  ;;                   (fs (cdr (assoc-equal (car hns) fs)))))
  ;;  ("Subgoal *1/8.1'"
  ;;   :in-theory (disable l3-wrchs-returns-fs l3-fs-p-assoc)
  ;;   :use ((:instance l3-wrchs-returns-fs
  ;;                    (fs (cdr (assoc-equal (car hns) fs)))
  ;;                    (hns (cdr hns)))
  ;;         (:instance l3-fs-p-assoc
  ;;                    (fs (cdr (assoc-equal (car hns) fs))))))
  ;;  ("Subgoal *1/8'''"
  ;;   :in-theory (disable l3-wrchs-returns-fs)
  ;;   :use (:instance l3-wrchs-returns-fs (hns (cdr hns))
  ;;                   (fs (cdr (assoc-equal (car hns) fs))))))
  )

(thm
 (IMPLIES
  (AND
   (L3-FS-P FS)
   (BOOLEAN-LISTP ALV)
   (STRINGP TEXT)
   (INTEGERP START)
   (<= 0 START)
   (BLOCK-LISTP DISK)
   (<= 0 (COUNT-FREE-BLOCKS ALV))
   (not-intersectp-list index-list (L4-COLLECT-ALL-INDEX-LISTS FS))
   (bounded-nat-listp index-list (len disk)))
  (EQUAL
   (L3-TO-L2-FS
    FS
    (SET-INDICES
     DISK
     index-list
     value-list))
   (L3-TO-L2-FS FS DISK)))
 :hints (("Subgoal *1/5''" :in-theory (disable L4-WRCHS-CORRECTNESS-1-LEMMA-5)
          :use (:instance  L4-WRCHS-CORRECTNESS-1-LEMMA-5 (index (car
 index-list)) (value (car value-list)))))) 

(thm (IMPLIES
      (AND (L3-fs-P fs1)
           (EQUAL (L2-WRCHS hns
                            (L3-TO-L2-FS fs1
                                         DISK)
                            START TEXT)
                  (L3-TO-L2-FS (MV-NTH 0
                                       (L4-WRCHS hns
                                                 fs1
                                                 DISK ALV START TEXT))
                               (MV-NTH 1
                                       (L4-WRCHS hns
                                                 fs1
                                                 DISK ALV START TEXT))))
           (L3-FS-P FS2)
           (BOOLEAN-LISTP ALV)
           (DISJOINT-LIST-LISTP (L4-COLLECT-ALL-INDEX-LISTS FS1))
           (NO-DUPLICATES-LISTP (L4-COLLECT-ALL-INDEX-LISTS FS1))
           (INDICES-MARKED-LISTP (L4-COLLECT-ALL-INDEX-LISTS FS1)
                                 ALV)
           (STRINGP TEXT)
           (INTEGERP START)
           (<= 0 START)
           (SYMBOL-LISTP hns)
           (BLOCK-LISTP DISK)
           (<= 0 (COUNT-FREE-BLOCKS ALV))
           (not (member-intersectp-equal (L4-COLLECT-ALL-INDEX-LISTS FS1)
                                         (L4-COLLECT-ALL-INDEX-LISTS FS2))))
      (EQUAL (L3-TO-L2-FS fs2
                          (MV-NTH 1
                                  (L4-WRCHS hns
                                            fs1
                                            DISK ALV START TEXT)))
             (L3-TO-L2-FS fs2
                          DISK))))
