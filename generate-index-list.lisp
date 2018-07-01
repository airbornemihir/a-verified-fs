(in-package "ACL2")

;  generate-index-list.lisp                            Mihir Mehta

;; If one's going to append some blocks at the end of the disk, one needs to
;; generate the indices for those blocks - that's what this function does.
(defun
  generate-index-list
  (disk-length block-list-length)
  (declare (xargs :guard (and (natp disk-length)
                              (natp block-list-length))))
  (if (zp block-list-length)
      nil
      (cons disk-length
            (generate-index-list (1+ disk-length)
                                 (1- block-list-length)))))

(defthm
  generate-index-list-correctness-1
  (implies
   (and (natp disk-length)
        (natp block-list-length))
   (nat-listp
    (generate-index-list disk-length block-list-length))))

(defthm
  generate-index-list-correctness-2
  (implies
   (natp block-list-length)
   (equal
    (len (generate-index-list disk-length block-list-length))
    block-list-length)))
