(in-package "ACL2")

(include-book "hifat-to-lofat-inversion")

(defun non-free-cluster-listp (index-list fa-table)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (bounded-nat-listp index-list (len fa-table)))))
  (or (atom index-list)
      (and (not (equal (fat32-entry-mask (nth (car index-list) fa-table)) 0))
           (non-free-cluster-listp (cdr index-list) fa-table))))

(defun free-cluster-listp (index-list fa-table)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (bounded-nat-listp index-list (len fa-table)))))
  (or (atom index-list)
      (and (equal (fat32-entry-mask (nth (car index-list) fa-table)) 0)
           (free-cluster-listp (cdr index-list) fa-table))))

;; In the subdirectory case, we need to place all the entries (32 bytes each)
;; and two entries (dot and dotdot). The space taken up for these things is
;; determined by the rule len-of-make-clusters, which expresses the length in
;; terms of the greatest integer function.
(defund
  hifat-cluster-count (fs cluster-size)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (integerp cluster-size)
                              (< 0 cluster-size))))
  (b*
      (((unless (consp fs)) 0)
       (head (car fs))
       (contents (m1-file->contents (cdr head))))
    (+
     (hifat-cluster-count (cdr fs)
                          cluster-size)
     (if
      (m1-regular-file-p (cdr head))
      (len (make-clusters contents cluster-size))
      (+ (hifat-cluster-count contents cluster-size)
         ;; This mbe form is here to help make a good type-prescription rule,
         ;; which identifies this thing as a natural number - not just an
         ;; integer. As an aside, I guess the battle over whether 0 is a
         ;; natural number has been lost for a while, since nobody seems to use
         ;; the term "whole number" any more.
         (mbe :exec (floor (+ (* 32 (+ 2 (len contents)))
                              cluster-size -1)
                           cluster-size)
              :logic (nfix (floor (+ (* 32 (+ 2 (len contents)))
                                     cluster-size -1)
                                  cluster-size))))))))

(defthm free-cluster-listp-of-find-n-free-clusters-helper-lemma-1
  (implies (and (free-cluster-listp index-list fa-table)
                (lower-bounded-integer-listp index-list 2)
                (not (member-equal key index-list)))
           (free-cluster-listp index-list
                               (update-nth key val fa-table)))
  :hints (("Goal" :in-theory (disable update-nth))
          ))

(encapsulate
  ()

  (local
   (defun induction-scheme
       (fa-table n start)
     (declare (xargs :measure (nfix (- (len fa-table) start))))
     (if (or (zp n) (not (integerp start)) (<= (len fa-table) start))
         nil
       (if (not (equal (fat32-entry-mask (nth start fa-table))
                       0))
           (induction-scheme fa-table
                             n (+ start 1))
         (cons start
               (induction-scheme fa-table
                                 (- n 1)
                                 (+ start 1)))))))

  (defthm
    free-cluster-listp-of-find-n-free-clusters-helper
    (implies
     (natp start)
     (free-cluster-listp (find-n-free-clusters-helper (nthcdr start fa-table)
                                                      n start)
                         fa-table))
    :hints (("goal" :induct (induction-scheme fa-table n start)
             :in-theory (enable find-n-free-clusters-helper)
             :expand (find-n-free-clusters-helper fa-table n start)))))

(defthm free-cluster-listp-of-find-n-free-clusters
  (free-cluster-listp (find-n-free-clusters fa-table n)
                      fa-table)
  :hints (("goal" :in-theory (enable find-n-free-clusters))))

(defthm count-free-clusters-of-effective-fat-of-place-contents-lemma-1
  (implies
   (and (free-cluster-listp index-list fa-table)
        (bounded-nat-listp index-list (len fa-table))
        (lower-bounded-integer-listp index-list 2)
        (not (member-equal 0 value-list))
        (fat32-masked-entry-list-p value-list)
        (no-duplicatesp-equal index-list)
        (equal (len index-list)
               (len value-list)))
   (equal (count-free-clusters
           (set-indices-in-fa-table fa-table index-list value-list))
          (- (count-free-clusters fa-table)
             (len index-list))))
  :hints
  (("goal" :in-theory (enable set-indices-in-fa-table)
    :induct (set-indices-in-fa-table fa-table index-list value-list))))


(defthmd
  count-free-clusters-of-effective-fat-of-place-contents-lemma-2
  (implies (stringp x)
           (iff (equal (len (explode x)) 0)
                (equal x "")))
  :hints (("goal" :expand (len (explode x)))))

(defthm
  count-free-clusters-of-effective-fat-of-place-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (stringp contents)
        (fat32-masked-entry-p first-cluster)
        (>= first-cluster *ms-first-data-cluster*)
        (< first-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (not (equal (fat32-entry-mask (fati first-cluster fat32-in-memory))
                    0)))
   (equal
    (count-free-clusters
     (effective-fat
      (mv-nth 0
              (place-contents fat32-in-memory dir-ent
                              contents file-length first-cluster))))
    (if (equal (mv-nth 2
                       (place-contents fat32-in-memory dir-ent
                                       contents file-length first-cluster))
               *enospc*)
        (count-free-clusters (effective-fat fat32-in-memory))
      (+ 1
         (count-free-clusters (effective-fat fat32-in-memory))
         (- (len (make-clusters contents
                                (cluster-size fat32-in-memory))))))))
  :hints
  (("goal"
    :in-theory (e/d (place-contents set-indices-in-fa-table
                                    count-free-clusters-of-effective-fat-of-place-contents-lemma-2)
                    ((:rewrite len-of-find-n-free-clusters)))
    :use
    ((:instance find-n-free-clusters-correctness-3
                (n (+ -1
                      (len (make-clusters contents
                                          (cluster-size fat32-in-memory)))))
                (fa-table (effective-fat fat32-in-memory))
                (x 0))
     (:instance (:rewrite len-of-find-n-free-clusters)
                (n (+ -1
                      (len (make-clusters contents
                                          (cluster-size fat32-in-memory)))))
                (fa-table (effective-fat fat32-in-memory))))
    :expand (make-clusters "" (cluster-size fat32-in-memory)))))

(defthm
  hifat-to-lofat-helper-correctness-5-lemma-5
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (equal (mv-nth 2
                       (hifat-to-lofat-helper fat32-in-memory
                                              fs current-dir-first-cluster))
               0))
   (equal
    (count-free-clusters
     (effective-fat
      (mv-nth 0
              (hifat-to-lofat-helper fat32-in-memory
                                     fs current-dir-first-cluster))))
    (- (count-free-clusters (effective-fat fat32-in-memory))
       (hifat-cluster-count fs (cluster-size fat32-in-memory)))))
  :hints
  (("goal"
    :in-theory (e/d (len-of-make-clusters hifat-cluster-count
                     painful-debugging-lemma-14)
                    (floor nth)))))

(encapsulate
  ()

  (local (in-theory (e/d
                     (hifat-cluster-count
                      count-free-clusters-of-effective-fat-of-place-contents-lemma-2
                      painful-debugging-lemma-12)
                     ((:rewrite
                       fati-of-hifat-to-lofat-helper-disjoint)
                      (:rewrite
                       fati-of-hifat-to-lofat-helper-disjoint-lemma-1)
                      (:definition update-nth) floor nth))))

  (defthm
    hifat-to-lofat-helper-correctness-5
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (m1-file-alist-p fs))
     (equal (mv-nth 2
                    (hifat-to-lofat-helper fat32-in-memory
                                           fs current-dir-first-cluster))
            (if (>= (count-free-clusters (effective-fat fat32-in-memory))
                    (hifat-cluster-count fs (cluster-size fat32-in-memory)))
                0 *enospc*)))
    :hints
    (("goal" :induct (hifat-to-lofat-helper fat32-in-memory
                                            fs current-dir-first-cluster)
      :expand ((make-clusters "" (cluster-size fat32-in-memory))
               (hifat-cluster-count fs (cluster-size fat32-in-memory))))
     ("subgoal *1/4" :in-theory (enable len-of-make-clusters)))))
