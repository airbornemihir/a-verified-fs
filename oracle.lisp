(in-package "ACL2")

;  oracle.lisp                                         Mihir Mehta

(include-book "lofat-syscalls")
(include-book "abs-syscalls")

(local (in-theory (disable nth)))

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
               (dir-stream-table dir-stream-table-p)))

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
       ;; ((when (eq syscall-sym :unlink))
       ;;  (b*
       ;;      (((mv fat32$c retval errno)
       ;;        (lofat-unlink
       ;;         fat32$c
       ;;         (lofat-st->path st))))
       ;;    (mv fat32$c
       ;;        (change-lofat-st
       ;;         st :retval retval :errno errno))))
       ;; ((when (eq syscall-sym :truncate))
       ;;  (b*
       ;;      (((mv fat32$c retval errno)
       ;;        (lofat-unlink
       ;;         fat32$c
       ;;         (lofat-st->path st))))
       ;;    (mv fat32$c
       ;;        (change-lofat-st
       ;;         st :retval retval :errno errno))))
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
            (((mv dir-stream-table dirp retval)
              (lofat-opendir
               fat32$c
               (lofat-st->dir-stream-table st)
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :dir-stream-table dir-stream-table :dirp dirp
               :retval retval :errno 0)))))
    (mv fat32$c st)))

;; We aren't going to put statfs in this. It'll just make things pointlessly
;; complicated.
(defund absfat-oracle-single-step (frame syscall-sym st)
  (declare (xargs :guard (and (frame-p frame)
                              (lofat-st-p st)
                              (consp (assoc-equal 0 frame))
                              (no-duplicatesp-equal (strip-cars frame)))
                  :guard-debug t))
  (b*
      ((st (mbe :logic (lofat-st-fix st) :exec st))
       ((when (eq syscall-sym :pwrite))
        (b*
            (((mv frame retval errno)
              (abs-pwrite
               (lofat-st->fd st)
               (lofat-st->buf st)
               (lofat-st->offset st)
               frame
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv frame
              (change-lofat-st
               st :retval retval :errno errno))))
       ((when (eq syscall-sym :pread))
        (b*
            (((mv buf retval errno)
              (abs-pread
               (lofat-st->fd st)
               (lofat-st->count st)
               (lofat-st->offset st)
               frame
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv frame
              (change-lofat-st
               st :buf buf :retval retval :errno errno))))
       ((when (eq syscall-sym :open))
        (b*
            (((mv fd-table file-table fd retval)
              (abs-open
               (lofat-st->path st)
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv frame
              (change-lofat-st
               st :fd fd :retval retval :errno 0 :file-table file-table
               :fd-table fd-table))))
       ((when (eq syscall-sym :lstat))
        (b*
            (((mv stat retval errno)
              (abs-lstat
               frame
               (lofat-st->path st))))
          (mv frame
              (change-lofat-st
               st :stat stat :retval retval :errno errno))))
       ;; ((when (eq syscall-sym :unlink))
       ;;  (b*
       ;;      (((mv fat32$c retval errno)
       ;;        (lofat-unlink
       ;;         fat32$c
       ;;         (lofat-st->path st))))
       ;;    (mv fat32$c
       ;;        (change-lofat-st
       ;;         st :retval retval :errno errno))))
       ;; ((when (eq syscall-sym :truncate))
       ;;  (b*
       ;;      (((mv fat32$c retval errno)
       ;;        (lofat-unlink
       ;;         fat32$c
       ;;         (lofat-st->path st))))
       ;;    (mv fat32$c
       ;;        (change-lofat-st
       ;;         st :retval retval :errno errno))))
       ((when (eq syscall-sym :mkdir))
        (b*
            (((mv frame retval errno)
              (abs-mkdir
               frame
               (lofat-st->path st))))
          (mv frame
              (change-lofat-st
               st :retval retval :errno errno))))
       ;; This is an interesting case! Basically, this command does not modify
       ;; the state of the filesystem but does change the frame.
       ((when (eq syscall-sym :opendir))
        (b*
            (((mv dirp dir-stream-table retval frame)
              (abs-opendir
               frame
               (lofat-st->path st)
               (lofat-st->dir-stream-table st))))
          (mv frame
              (change-lofat-st
               st :dir-stream-table dir-stream-table :dirp dirp
               :retval retval :errno 0)))))
    (mv frame st)))

(defthm
  lofat-mkdir-refinement-lemma-1
  (implies
   (and
    (good-root-d-e-p (pseudo-root-d-e fat32$c)
                     fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (lofat-file-p file)
    (or (and (lofat-regular-file-p file)
             (<= (len (make-clusters (lofat-file->contents file)
                                     (cluster-size fat32$c)))
                 (count-free-clusters (effective-fat fat32$c))))
        (and (equal (lofat-file->contents file) nil)
             (<= 1
                 (count-free-clusters (effective-fat fat32$c)))))
    (not (equal (mv-nth 1
                        (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                          path file))
                28))
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c)))
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                    path file))
          (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                    path file))
          (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     (mv-nth 0
             (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                               path
                               (m1-file d-e (lofat-file->contents file)))))
    (equal
     (mv-nth 1
             (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                               path
                               (m1-file d-e (lofat-file->contents file))))
     (mv-nth 1
             (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                               path file)))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (lofat-to-hifat root-d-e-list)
                           (lofat-place-file-correctness-1))
           :use (:instance lofat-place-file-correctness-1
                           (entry-limit (max-entry-count fat32$c))
                           (root-d-e (pseudo-root-d-e fat32$c))))))

(defthm
  lofat-mkdir-refinement
  (implies
   (and (lofat-fs-p fat32$c)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (lofat-to-hifat fat32$c))
               0)
        (not (equal (mv-nth 0 (lofat-mkdir fat32$c path)) *eio*)))
   (and
    (equal
     (mv-nth
      1
      (lofat-to-hifat (mv-nth 0 (lofat-mkdir fat32$c path))))
     0)
    (equal
     (mv-nth
      0
      (lofat-to-hifat (mv-nth 0 (lofat-mkdir fat32$c path))))
     (mv-nth 0
             (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
                           path)))
    (equal
     (mv-nth 1 (lofat-mkdir fat32$c path))
     (mv-nth 1
             (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
                           path)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (lofat-mkdir)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          make-list-ac-removal
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)))
    :expand
    ((:free (fs) (hifat-find-file fs nil))
     (:free (fs file) (hifat-place-file fs nil file))))))

(thm
 (implies
  (frame-reps-fs frame (lofat-to-hifat fat32$c))
  (frame-reps-fs
   (mv-nth 0 (abs-mkdir frame (lofat-st->path st)))
   (lofat-to-hifat (mv-nth 0
                           (lofat-mkdir fat32$c (lofat-st->path st))))))
 :hints (("goal" :do-not-induct t :in-theory (disable
                                              abs-mkdir-correctness-2
                                              ;; Consider disabling later.
                                              hifat-mkdir)
          :use
          (:instance
           abs-mkdir-correctness-2 (path (lofat-st->path st)))))
 :otf-flg t)

;; How do we prove this? The best way seems to be to open up the definitions of
;; the single-step functions and proceed from there.
(defthm absfat-oracle-single-step-refinement
  (implies
   (frame-reps-fs
    frame
    (lofat-to-hifat fat32$c))
   (frame-reps-fs
    (mv-nth 0 (absfat-oracle-single-step frame syscall-sym st))
    (lofat-to-hifat (mv-nth 0 (lofat-oracle-single-step fat32$c syscall-sym
                                                        st)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable absfat-oracle-single-step
                              lofat-oracle-single-step)))
  :otf-flg t)
