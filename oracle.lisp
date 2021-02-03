(in-package "ACL2")

;  oracle.lisp                                         Mihir Mehta

(include-book "lofat-syscalls")

(defconst *syscall-pwrite* 1)
(defconst *syscall-pread* 2)
(defconst *syscall-open* 3)

(defund lofat-oracle-single-step (fat32$c syscall-num args fd-table file-table)
  (declare (xargs :stobjs fat32$c
                  :guard (and (true-listp args)
                              (fd-table-p fd-table)
                              (lofat-fs-p fat32$c)
                              (file-table-p file-table))
                  :verify-guards nil))
  (cond
   ((equal syscall-num *syscall-pwrite*)
    (b*
        (((mv fat32$c retval errno)
          (lofat-pwrite
           (nth 0 args) ;; fd
           (nth 1 args) ;; buf
           (nth 2 args) ;; offset
           fat32$c fd-table file-table)))
      (mv fat32$c
          "" ;; buf
          retval errno fd-table file-table)))
   ((equal syscall-num *syscall-pread*)
    (b*
        (((mv buf retval errno)
          (lofat-pread
           (nth 0 args) ;; fd
           (nth 1 args) ;; count
           (nth 2 args) ;; offset
           fat32$c fd-table file-table)))
      (mv fat32$c
          buf
          retval errno fd-table file-table)))
   ((equal syscall-num *syscall-open*)
    (b*
        (((mv fd-table file-table fd retval)
          (lofat-pread
           (nth 0 args) ;; fd
           (nth 1 args) ;; count
           (nth 2 args) ;; offset
           fat32$c fd-table file-table)))
      (mv fat32$c
          fd
          retval
          0 ;; errno
          fd-table file-table)))
   (t (mv fat32$c
          "" ;; buf
          0 0 fd-table file-table))))
