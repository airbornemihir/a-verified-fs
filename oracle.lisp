(in-package "ACL2")

;  oracle.lisp                                         Mihir Mehta

(include-book "lofat-syscalls")

(fty::defprod lofat-st
              ((fd natp)
               (buf stringp)
               (offset natp)
               (count natp)
               (retval integerp)
               (errno natp)
               (path fat32-filename-list-p)
               (stat struct-stat-p)
               (statfs struct-statfs-p)
               (dirp integerp) ;; This is interesting. We try to mimic the
               ;; NULL-returning behaviour of the actual opendir by making it
               ;; return -1 at precisely those times. That means this cannot be
               ;; assumed to be a natural number.
               (fd-table fd-table-p)
               (file-table file-table-p)
               (dirstream-table dirstream-table-p)))

(defthm lofat-pwrite-correctness-1
  (natp (mv-nth 2
                (lofat-pwrite fd buf
                              offset fat32$c fd-table file-table)))
  :rule-classes :type-prescription
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-pwrite))))

(defthm lofat-mkdir-correctness-1
  (natp (mv-nth 2
                (lofat-mkdir fat32$c (lofat-st->path st))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-mkdir)))
  :rule-classes :type-prescription)

(defthm
  lofat-find-file-correctness-4
  (implies
   (lofat-directory-file-p (mv-nth 0
                                   (lofat-find-file fat32$c d-e-list path)))
   (d-e-list-p
    (lofat-file->contents (mv-nth 0
                                  (lofat-find-file fat32$c d-e-list path)))))
  :hints (("goal" :in-theory (enable lofat-find-file))))

(defthm lofat-opendir-correctness-1
  (and
   (dirstream-table-p (mv-nth 0
                              (lofat-opendir fat32$c dirstream-table path)))
   (integerp (mv-nth 1
                     (lofat-opendir fat32$c dirstream-table path)))
   (integerp (mv-nth 2
                     (lofat-opendir fat32$c dirstream-table path))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-opendir)))
  :rule-classes
  ((:rewrite :corollary
             (dirstream-table-p (mv-nth 0
                                        (lofat-opendir fat32$c dirstream-table path))))
   (:type-prescription
    :corollary
    (integerp (mv-nth 1
                      (lofat-opendir fat32$c dirstream-table path))))
                                        (:type-prescription
    :corollary
    (integerp (mv-nth 2
                      (lofat-opendir fat32$c dirstream-table path))))))

(defthm lofat-remove-file-correctness-3
  (natp (mv-nth 1
                (lofat-remove-file fat32$c root-d-e path)))
  :hints (("goal" :in-theory (enable lofat-remove-file
                                     lofat-remove-file-helper)))
  :rule-classes :type-prescription)

(defthm lofat-unlink-correctness-1
  (and
   (integerp (mv-nth 1
                     (lofat-unlink fat32$c path)))
   (natp (mv-nth 2
                 (lofat-unlink fat32$c path))))
  :hints (("goal" :in-theory (enable lofat-unlink)))
  :rule-classes
  ((:type-prescription
    :corollary
    (integerp (mv-nth 1
                      (lofat-unlink fat32$c path))))
   (:type-prescription
    :corollary
    (natp (mv-nth 2
                  (lofat-unlink fat32$c path))))))

(defthm lofat-lstat-correctness-1
  (and
   (integerp (mv-nth 1 (lofat-lstat fat32$c path)))
   (natp (mv-nth 2 (lofat-lstat fat32$c path))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-lstat)))
  :rule-classes
  ((:type-prescription
    :corollary
    (integerp (mv-nth 1 (lofat-lstat fat32$c path))))
   (:type-prescription
    :corollary
    (natp (mv-nth 2 (lofat-lstat fat32$c path))))))

;; We aren't going to put statfs in this. It'll just make things pointlessly
;; complicated.
(defund lofat-oracle-single-step (fat32$c syscall-sym st)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (lofat-st-p st))
                  :guard-debug t))
  (b*
      ((st (mbe :logic (lofat-st-fix st) :exec st))
       ((when (eq syscall-sym :pwrite))
        (b*
            (((mv fat32$c retval errno)
              (lofat-pwrite
               (lofat-st->fd st)
               (lofat-st->buf st)
               (lofat-st->offset st)
               fat32$c
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv fat32$c
              (change-lofat-st
               st :retval retval :errno errno))))
       ((when (eq syscall-sym :pread))
        (b*
            (((mv buf retval errno)
              (lofat-pread
               (lofat-st->fd st)
               (lofat-st->count st)
               (lofat-st->offset st)
               fat32$c
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv fat32$c
              (change-lofat-st
               st :buf buf :retval retval :errno errno))))
       ((when (eq syscall-sym :open))
        (b*
            (((mv fd-table file-table fd retval)
              (lofat-open
               (lofat-st->path st)
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv fat32$c
              (change-lofat-st
               st :fd fd :retval retval :errno 0 :file-table file-table
               :fd-table fd-table))))
       ((when (eq syscall-sym :lstat))
        (b*
            (((mv stat retval errno)
              (lofat-lstat
               fat32$c
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :stat stat :retval retval :errno errno))))
       ((when (eq syscall-sym :unlink))
        (b*
            (((mv fat32$c retval errno)
              (lofat-unlink
               fat32$c
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :retval retval :errno errno))))
       ((when (eq syscall-sym :truncate))
        (b*
            (((mv fat32$c retval errno)
              (lofat-unlink
               fat32$c
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :retval retval :errno errno))))
       ((when (eq syscall-sym :mkdir))
        (b*
            (((mv fat32$c retval errno)
              (lofat-mkdir
               fat32$c
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :retval retval :errno errno))))
       ((when (eq syscall-sym :opendir))
        (b*
            (((mv dirstream-table dirp retval)
              (lofat-opendir
               fat32$c
               (lofat-st->dirstream-table st)
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :dirstream-table dirstream-table :dirp dirp
               :retval retval :errno 0)))))
    (mv fat32$c st)))
