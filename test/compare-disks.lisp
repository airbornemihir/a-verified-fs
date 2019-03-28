(include-book "../lofat")
(include-book "centaur/getopt/top" :dir :system)
(include-book "oslib/argv" :dir :system)

(b*
    (((mv & val state)
      (getenv$ "REF_INPUT" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory val state))
     ((mv fs-ref &)
      (lofat-to-m1-fs fat32-in-memory))
     ((mv & val state)
      (getenv$ "INPUT" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory val state))
     ((mv fs &)
      (lofat-to-m1-fs fat32-in-memory)))
  (mv
       (good-bye
        (if (m1-dir-equiv fs-ref fs)
            0
          1))
       fat32-in-memory
       state))