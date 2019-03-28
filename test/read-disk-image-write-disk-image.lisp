(include-book "../lofat")

(b*
    (((mv & image-path state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (time$
       (disk-image-to-fat32-in-memory
        fat32-in-memory image-path state)))
     (state
      (time$
       (fat32-in-memory-to-disk-image
        fat32-in-memory image-path state))))
  (mv fat32-in-memory state))
