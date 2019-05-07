(include-book "../test-stuff")
(include-book "oslib/argv" :dir :system)

(b*
    (((mv argv state)
      (oslib::argv))
     ((mv errmsg & extra-args) (parse-rm-opts argv))
     ;; Either a parsing error, or no files provided on the command line.
     ((when (or errmsg (atom extra-args)))
      (mv (good-bye 1) fat32-in-memory state))
     ((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory val state))
     ((mv fat32-in-memory exit-status)
      (rm-1 fat32-in-memory extra-args))
     ((mv & val state)
      (getenv$ "RM_OUTPUT" state))
     (state
      (lofat-to-disk-image
       fat32-in-memory val state)))
  (mv (good-bye exit-status) fat32-in-memory state))
