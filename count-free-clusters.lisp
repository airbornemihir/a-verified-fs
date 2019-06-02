(in-package "ACL2")

(include-book "hifat-to-lofat-inversion")

(defun count-free-clusters-helper (fa-table n)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (natp n)
                              (>= (len fa-table) n))
                  :guard-hints (("Goal" :in-theory (disable nth)) )))
  (if
      (zp n)
      0
    (if
        (not (equal (fat32-entry-mask (nth (- n 1) fa-table)) 0))
        (count-free-clusters-helper fa-table (- n 1))
      (+ 1 (count-free-clusters-helper fa-table (- n 1))))))

(defthm stobj-count-free-clusters-helper-correctness-1
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (>= (count-of-clusters fat32-in-memory) n))
   (equal
    (stobj-count-free-clusters-helper
     fat32-in-memory n)
    (count-free-clusters-helper (nthcdr 2 (effective-fat fat32-in-memory)) n))))

(defthm
  update-nth-of-count-free-clusters-helper-1
  (implies (and (natp n)
                (natp key)
                (not (equal (fat32-entry-mask val) 0)))
           (equal (count-free-clusters-helper (update-nth key val fa-table)
                                              n)
                  (if (and (< key n)
                           (equal (fat32-entry-mask (nth key fa-table))
                                  0))
                      (- (count-free-clusters-helper fa-table n)
                         1)
                      (count-free-clusters-helper fa-table n))))
  :hints (("goal" :in-theory (disable nth update-nth))))

(defthm
  update-nth-of-count-free-clusters-helper-2
  (implies (and (natp n)
                (natp key)
                (equal (fat32-entry-mask val) 0))
           (equal (count-free-clusters-helper (update-nth key val fa-table)
                                              n)
                  (if (and (< key n)
                           (not (equal (fat32-entry-mask (nth key fa-table))
                                       0)))
                      (+ (count-free-clusters-helper fa-table n)
                         1)
                      (count-free-clusters-helper fa-table n))))
  :hints (("goal" :in-theory (disable nth update-nth))))

(defthm count-free-clusters-helper-correctness-1
  (<= (count-free-clusters-helper fa-table n)
      (nfix n))
  :rule-classes :linear)

(defund
  count-free-clusters (fa-table)
  (declare
   (xargs :guard (and (fat32-entry-list-p fa-table)
                      (>= (len fa-table)
                          *ms-first-data-cluster*))
          :guard-hints (("goal" :in-theory (disable nth)))))
  (count-free-clusters-helper
   (nthcdr *ms-first-data-cluster* fa-table)
   (- (len fa-table)
      *ms-first-data-cluster*)))

(defthm
  update-nth-of-count-free-clusters-1
  (implies
   (and (integerp key) (<= *ms-first-data-cluster* key)
        (not (equal (fat32-entry-mask val) 0))
        (< key (len fa-table)))
   (equal (count-free-clusters (update-nth key val fa-table))
          (if
              (equal (fat32-entry-mask (nth key fa-table))
                     0)
              (- (count-free-clusters fa-table) 1)
            (count-free-clusters fa-table))))
  :hints (("goal" :in-theory (enable count-free-clusters))))

(defthm
  update-nth-of-count-free-clusters-2
  (implies
   (and (integerp key) (<= *ms-first-data-cluster* key)
        (equal (fat32-entry-mask val) 0)
        (< key (len fa-table)))
   (equal (count-free-clusters (update-nth key val fa-table))
          (if
              (equal (fat32-entry-mask (nth key fa-table))
                     0)
              (count-free-clusters fa-table)
            (+ (count-free-clusters fa-table) 1))))
  :hints (("goal" :in-theory (enable count-free-clusters))))

(defthm
  count-free-clusters-correctness-1
  (implies (>= (len fa-table)
               *ms-first-data-cluster*)
           (<= (count-free-clusters fa-table)
               (- (len fa-table)
                  *ms-first-data-cluster*)))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable count-free-clusters))))

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
(defun
  hifat-cluster-count (fs cluster-size)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (integerp cluster-size)
                              (< 0 cluster-size))))
  (b* (((unless (consp fs)) 0)
       (head (car fs))
       (contents (m1-file->contents (cdr head))))
    (+ (hifat-cluster-count (cdr fs)
                            cluster-size)
       (if (m1-regular-file-p (cdr head))
           (len (make-clusters contents cluster-size))
           (+ (hifat-cluster-count contents cluster-size)
              (floor (+ (* 32 (+ 2 (len contents)))
                        cluster-size -1)
                     cluster-size))))))

(defthm hifat-cluster-count-correctness-1
  (implies (not (zp cluster-size))
           (<= 0
               (hifat-cluster-count fs cluster-size)))
  :rule-classes :linear
  :hints (("goal" :in-theory (disable floor))))

(defthmd
  len-of-find-n-free-clusters-lemma-1
  (implies
   (consp fa-table)
   (equal
    (len (find-n-free-clusters-helper fa-table n start))
    (if
     (and
      (<
       (len (find-n-free-clusters-helper (take (- (len fa-table) 1) fa-table)
                                         n start))
       (nfix n))
      (equal (fat32-entry-mask (nth (- (len fa-table) 1) fa-table))
             0))
     (+ (len (find-n-free-clusters-helper (take (- (len fa-table) 1) fa-table)
                                          n start))
        1)
     (len (find-n-free-clusters-helper (take (- (len fa-table) 1) fa-table)
                                       n start)))))
  :hints (("goal" :in-theory (enable find-n-free-clusters-helper)
           :induct (find-n-free-clusters-helper fa-table n start)
           :expand (len (cdr fa-table)))))

(defthmd
  len-of-find-n-free-clusters-lemma-2
  (equal (len (find-n-free-clusters-helper (take n2 fa-table)
                                           n1 start))
         (min (count-free-clusters-helper fa-table n2)
              (nfix n1)))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters-helper
                              len-of-find-n-free-clusters-lemma-1))))

(defthm
  find-n-free-clusters-helper-of-true-list-fix
  (equal (find-n-free-clusters-helper (true-list-fix fa-table)
                                      n start)
         (find-n-free-clusters-helper fa-table n start))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters-helper))))

(defthm
  another-len-of-find-n-free-clusters
  (equal (len (find-n-free-clusters fa-table n))
         (min (count-free-clusters fa-table)
              (nfix n)))
  :hints (("goal" :in-theory (e/d (count-free-clusters find-n-free-clusters)
                                  (nthcdr))
           :use (:instance len-of-find-n-free-clusters-lemma-2
                           (n2 (len (nthcdr 2 fa-table)))
                           (fa-table (nthcdr 2 fa-table))
                           (n1 n)
                           (start 2)))))

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

(encapsulate
  ()

  (local
   (defthm
     count-free-clusters-of-effective-fat-of-place-contents-lemma-2
     (implies (stringp x)
              (iff (equal (len (explode x)) 0)
                   (equal x "")))
     :hints (("goal" :expand (len (explode x))))))

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
      :in-theory (e/d (place-contents set-indices-in-fa-table)
                      ((:rewrite another-len-of-find-n-free-clusters)))
      :use
      ((:instance find-n-free-clusters-correctness-3
                  (n (+ -1
                        (len (make-clusters contents
                                            (cluster-size fat32-in-memory)))))
                  (fa-table (effective-fat fat32-in-memory))
                  (x 0))
       (:instance (:rewrite another-len-of-find-n-free-clusters)
                  (n (+ -1
                        (len (make-clusters contents
                                            (cluster-size fat32-in-memory)))))
                  (fa-table (effective-fat fat32-in-memory))))
      :expand (make-clusters "" (cluster-size fat32-in-memory))))
    :otf-flg t))

(defthm
  hifat-to-lofat-helper-correctness-5-lemma-4
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (fat32-masked-entry-p current-dir-first-cluster)
        (equal
         (mv-nth
          2
          (hifat-to-lofat-helper
           fat32-in-memory fs current-dir-first-cluster))
         0))
   (equal
    (count-free-clusters
     (effective-fat
      (mv-nth
       0
       (hifat-to-lofat-helper
        fat32-in-memory fs current-dir-first-cluster))))
    (-
     (count-free-clusters
      (effective-fat fat32-in-memory))
     (hifat-cluster-count fs (cluster-size fat32-in-memory)))))
  :hints (("Goal" :in-theory (e/d (len-of-make-clusters) (floor nth))) ))

(defthm
  hifat-to-lofat-helper-correctness-5
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (fat32-masked-entry-p current-dir-first-cluster))
   (equal
    (mv-nth
     2
     (hifat-to-lofat-helper
      fat32-in-memory fs current-dir-first-cluster))
    (if
        (>= (count-free-clusters (effective-fat fat32-in-memory))
            (hifat-cluster-count fs (cluster-size fat32-in-memory)))
        0
      *enospc*)))
  :hints (("Goal" :in-theory (disable floor nth)) ))
