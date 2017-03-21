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
          (natp offset)
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
  (implies (and (nat-listp index-list) (indices-marked-p index-list alv))
           (bounded-nat-listp index-list (len alv))))

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
                    (mv (cons (cons (car sd)
                                    (cons new-indices (len new-text)))
                              (delete-assoc (car hns) fs))
                        ;; this (take) means we write as many blocks as we can
                        ;; if we run out of space
                        (set-indices disk new-indices (take (len new-indices) new-blocks))
                        (set-indices-in-alv alv-after-free new-indices t))))
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
              (indices-marked-p all-indices alv)
              (equal (+ (len all-indices) (count-free-blocks alv)) (len alv))))))
