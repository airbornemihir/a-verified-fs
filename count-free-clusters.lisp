(in-package "ACL2")

(include-book "hifat-to-lofat-inversion")

(defun count-free-clusters-helper (fa-table n)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (natp n)
                              (>= (len fa-table)
                                  (+ *ms-first-data-cluster* n)))
                  :guard-hints (("Goal" :in-theory (disable nth)) )))
  (if
      (zp n)
      0
    (if
        (not (equal (fat32-entry-mask (nth (+ n 1) fa-table)) 0))
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
    (count-free-clusters-helper (effective-fat fat32-in-memory) n))))

(defthm
  update-nth-of-count-free-clusters-helper
  (implies
   (and (natp n)
        (integerp key)
        (>= key *ms-first-data-cluster*)
        (equal (fat32-entry-mask (nth key fa-table))
               0)
        (not (equal (fat32-entry-mask val) 0)))
   (equal
    (count-free-clusters-helper (update-nth key val fa-table)
                                n)
    (if (< key (+ n 2))
        (- (count-free-clusters-helper fa-table n)
           1)
        (count-free-clusters-helper fa-table n))))
  :hints (("goal" :in-theory (disable nth update-nth))))

(defund count-free-clusters (fa-table)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (>= (len fa-table)
                                  *ms-first-data-cluster*))
                  :guard-hints (("Goal" :in-theory (disable nth)) )))
  (count-free-clusters-helper fa-table (- (len fa-table)
                                          *ms-first-data-cluster*)))

(defthm
  update-nth-of-count-free-clusters
  (implies
   (and (integerp key)
        (>= key *ms-first-data-cluster*)
        (equal (fat32-entry-mask (nth key fa-table))
               0)
        (not (equal (fat32-entry-mask val) 0))
        (< key (len fa-table)))
   (equal (count-free-clusters (update-nth key val fa-table))
          (- (count-free-clusters fa-table) 1)))
  :hints (("goal" :in-theory (enable count-free-clusters))))

(defun indices-non-zero-p (index-list fa-table)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (bounded-nat-listp index-list (len fa-table)))))
  (or (atom index-list)
      (and (not (equal (fat32-entry-mask (nth (car index-list) fa-table)) 0))
           (indices-non-zero-p (cdr index-list) fa-table))))

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
