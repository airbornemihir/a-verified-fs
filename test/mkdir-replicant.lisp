(include-book "../file-system-m2")
(include-book "centaur/getopt/top" :dir :system)
(include-book "oslib/argv" :dir :system)

(defoptions mkdir-opts
  :parents (demo2)
  :tag :demo2

  ((parents    "no error if existing, make parent directories as needed"
               booleanp
               :rule-classes :type-prescription
               :alias #\p)))

(defun mkdir-list (fs r name-list exit-status)
  (b*
      (((when (atom name-list))
        (mv fs exit-status))
       (fat32-pathname
        (pathname-to-fat32-pathname (coerce (car name-list) 'list)))
       ;; It doesn't really matter for these purposes what the errno is. We're
       ;; not trying to match this program for its stderr output.
       ((mv fs retval &)
        (m1-mkdir fs fat32-pathname))
       (exit-status (if (equal retval 0) exit-status 1)))
    (mkdir-list fs r (cdr name-list) exit-status)))

(b*
    (((mv argv state)
      (oslib::argv))
     ((mv errmsg opts extra-args) (parse-mkdir-opts argv))
     ;; Either a parsing error, or no files provided on the command line.
     ((when (or errmsg (atom extra-args)))
      (mv (good-bye 1) fat32-in-memory state))
     ((mkdir-opts opts) opts)
     ((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-fat32-in-memory
       fat32-in-memory val state))
     ((mv fs &)
      (fat32-in-memory-to-m1-fs fat32-in-memory))
     ((mv fs exit-status)
      (mkdir-list fs nil extra-args 0))
     ((mv fat32-in-memory &)
      (m1-fs-to-fat32-in-memory fat32-in-memory fs))
     ((mv & val state)
      (getenv$ "MKDIR_OUTPUT" state))
     (state
      (fat32-in-memory-to-disk-image
       fat32-in-memory val state)))
  (mv (good-bye exit-status) fat32-in-memory state))
