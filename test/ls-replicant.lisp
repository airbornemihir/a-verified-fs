(include-book "../test-stuff")
(include-book "oslib/argv" :dir :system)

(b*
    (((mv argv state)
      (oslib::argv))
     ((mv errmsg & extra-args) (parse-ls-opts argv))
     ;; Parsing error.
     ((when errmsg)
      (mv (good-bye 1) fat32-in-memory state))
     ;; ((rm-opts opts) opts)
     ((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory val state))
     (ls-list
      (ls-list fat32-in-memory extra-args))
     (exit-status
      (if (< (len ls-list) (len extra-args)) 2 0)))
  (mv (good-bye exit-status) fat32-in-memory state))
