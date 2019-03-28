(include-book "../test-stuff")
(include-book "oslib/argv" :dir :system)

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
      (disk-image-to-lofat
       fat32-in-memory val state))
     ((mv fs &)
      (lofat-to-m1-fs fat32-in-memory))
     ((mv fs exit-status)
      (if
          opts.recursive
          (rm-list fs t extra-args 0)
        (rm-list fs nil extra-args 0)))
     ((mv fat32-in-memory &)
      (m1-fs-to-lofat fat32-in-memory fs))
     ((mv & val state)
      (getenv$ "RM_OUTPUT" state))
     (state
      (lofat-to-disk-image
       fat32-in-memory val state)))
  (mv (good-bye exit-status) fat32-in-memory state))