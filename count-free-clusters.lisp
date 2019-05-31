(in-package "ACL2")

(local (include-book "file-system-6"))
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

(defun indices-non-zero-p (index-list fa-table)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (bounded-nat-listp index-list (len fa-table)))))
  (or (atom index-list)
      (and (not (equal (fat32-entry-mask (nth (car index-list) fa-table)) 0))
           (indices-non-zero-p (cdr index-list) fa-table))))

;; In the subdirectory case, we need to place all the entries (32 bytes each)
;; and two entries (dot and dotdot). The space taken up for these things is
;; determined by the rule len-of-make-clusters, which expresses the length in
;; terms of the greates integer function.
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
