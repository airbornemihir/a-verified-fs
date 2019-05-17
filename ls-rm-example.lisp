(in-package "ACL2")

(include-book "test-stuff")

(defthm
  lstat-after-unlink
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (m1-bounded-file-alist-p
     (mv-nth
      '0
      (remove-file-by-pathname (mv-nth '0
                                       (lofat-to-hifat fat32-in-memory))
                               pathname)))
    (not
     (<
      (max-entry-count fat32-in-memory)
      (hifat-entry-count
       (mv-nth
        '0
        (remove-file-by-pathname (mv-nth '0
                                         (lofat-to-hifat fat32-in-memory))
                                 pathname)))))
    (equal
     (mv-nth
      '1
      (hifat-to-lofat
       fat32-in-memory
       (mv-nth
        '0
        (remove-file-by-pathname (mv-nth '0
                                         (lofat-to-hifat fat32-in-memory))
                                 pathname))))
     0))
   (b* (((mv fat32-in-memory unlink-errno)
         (lofat-unlink fat32-in-memory pathname))
        ((mv & lstat-errno)
         (lofat-lstat fat32-in-memory pathname)))
     (implies (equal unlink-errno 0)
              (not (equal lstat-errno 0)))))
  :hints (("goal"
           :in-theory (enable lofat-unlink))))
