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
    (count-free-clusters-helper (effective-fat fat32-in-memory) n)))
  :hints (("Goal" :in-theory (enable)) ))
