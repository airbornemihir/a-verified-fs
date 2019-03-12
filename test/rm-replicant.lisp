(include-book "../file-system-m2")
(include-book "../m1-syscalls")
(include-book "centaur/getopt/top" :dir :system)
(include-book "oslib/argv" :dir :system)

(defoptions rm-opts
  :parents (demo2)
  :tag :demo2

  ((recursive    "Recursively delete a directory"
                 booleanp
                 :rule-classes :type-prescription
                 :alias #\r)))

(defun rm-list (fs r name-list exit-status)
  (b*
      (((when (atom name-list))
        (mv fs exit-status))
       (fat32-pathname
        (pathname-to-fat32-pathname (coerce (car name-list) 'list)))
       ;; It doesn't really matter for these purposes what the errno is. We're
       ;; not trying to match this program for its stderr output.
       ((mv fs retval &)
        (if r
            (m1-unlink-recursive fs fat32-pathname)
          (m1-unlink fs fat32-pathname)))
       (exit-status (if (equal retval 0) exit-status 1)))
    (rm-list fs r (cdr name-list) exit-status)))

(b*
    (((mv argv state)
      (oslib::argv))
     ((mv errmsg opts extra-args) (parse-rm-opts argv))
     ;; Either a parsing error, or no files provided on the command line.
     ((when (or errmsg (atom extra-args)))
      (mv (good-bye 1) fat32-in-memory state))
     ((rm-opts opts) opts)
     ((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-fat32-in-memory
       fat32-in-memory val state))
     ((mv fs &)
      (fat32-in-memory-to-m1-fs fat32-in-memory))
     ((mv fs exit-status)
      (if
          opts.recursive
          (rm-list fs t extra-args 0)
        (rm-list fs nil extra-args 0)))
     ((mv fat32-in-memory &)
      (m1-fs-to-fat32-in-memory fat32-in-memory fs))
     ((mv & val state)
      (getenv$ "RM_OUTPUT" state))
     (state
      (fat32-in-memory-to-disk-image
       fat32-in-memory val state)))
  (mv (good-bye exit-status) fat32-in-memory state))
