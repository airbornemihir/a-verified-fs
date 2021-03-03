(in-package "ACL2")

;  oracle.lisp                                         Mihir Mehta

(include-book "lofat-syscalls")
(include-book "abs-syscalls")

(local (in-theory (disable nth make-list-ac-removal last
                           make-list-ac)))

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

;; Counterexample, but for regular files which we aren't really thinking about
(thm
 (implies
  (and
   (lofat-fs-p fat32$c)
   (fat32-filename-list-p path)
   (not
    (equal
     (mv-nth
      1
      (find-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (car path)))
     0))
   (equal (mv-nth 1
                  (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                    path file))
          0)
   (equal (mv-nth 1
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
          0)
   (no-duplicatesp-equal (mv-nth 0
                                 (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
   (lofat-regular-file-p file)
   (< 0
      (len (explode (lofat-file->contents file)))))
  (and
   (hifat-equiv
    (mv-nth 0
            (lofat-to-hifat
             (mv-nth 0
                     (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                       path file))))
    (mv-nth
     0
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path file))
      (place-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (d-e-set-first-cluster-file-size
        (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                   nil)
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        (len (explode (lofat-file->contents file)))))
      (max-entry-count fat32$c))))
   (hifat-equiv
    (mv-nth
     0
     (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                       path
                       (make-m1-file :d-e (lofat-file->d-e file)
                                     :contents (lofat-file->contents file))))
    (mv-nth
     0
     (hifat-place-file
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c)))
      path
      (m1-file (lofat-file->d-e file)
               (lofat-file->contents file)))))))
 :hints
 (("goal"
   :do-not-induct t
   :in-theory
   (e/d (lofat-to-hifat root-d-e-list hifat-place-file)
        ((:rewrite hifat-to-lofat-inversion-lemma-2)
         (:rewrite absfat-subsetp-transitivity-lemma-7)
         (:rewrite abs-directory-file-p-when-m1-file-p)
         (:rewrite m1-regular-file-p-correctness-1)
         (:definition find-d-e)
         (:rewrite str::consp-of-explode)
         (:rewrite abs-mkdir-correctness-lemma-228)
         (:rewrite str::explode-when-not-stringp)
         (:rewrite hifat-find-file-correctness-1-lemma-1)
         (:rewrite nfix-when-zp)
         (:rewrite abs-directory-file-p-correctness-1)
         (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2)
         (:rewrite lofat-find-file-correctness-lemma-2)
         (:rewrite d-e-p-of-car-when-d-e-list-p)
         (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
         (:linear m1-regular-file-p-correctness-2)
         (:rewrite lofat-pread-refinement-lemma-1)
         (:definition member-intersectp-equal)
         (:rewrite lofat-find-file-correctness-lemma-1)
         (:definition assoc-equal)))
   :restrict ((not-intersectp-list-when-subsetp-1
               ((y (mv-nth 0
                           (d-e-cc fat32$c
                                   (pseudo-root-d-e fat32$c))))))))))

;; This was a counterexample.
;; (thm
;;  (implies
;;   (and
;;    (lofat-fs-p fat32$c)
;;    (fat32-filename-list-p path)
;;    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
;;           0)
;;    (consp (cdr path))
;;    (equal
;;     (mv-nth 1
;;             (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
;;                               path
;;                               '((d-e 0 0 0 0 0 0 0 0 0 0 0 16
;;                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                                 (contents))))
;;     0)
;;    (equal (mv-nth 1
;;                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
;;           0)
;;    (no-duplicatesp-equal (mv-nth 0
;;                                  (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
;;    (<= 1
;;        (count-free-clusters (effective-fat fat32$c)))
;;    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
;;       (max-entry-count fat32$c))
;;    (not (m1-directory-file-p
;;          (mv-nth 0
;;                  (lofat-find-file fat32$c
;;                                   (mv-nth 0 (root-d-e-list fat32$c))
;;                                   (dirname path)))))
;;    (lofat-directory-file-p
;;     (mv-nth 0
;;             (lofat-find-file fat32$c
;;                              (mv-nth 0 (root-d-e-list fat32$c))
;;                              (dirname path))))
;;    (equal (mv-nth 1
;;                   (lofat-find-file fat32$c
;;                                    (mv-nth 0 (root-d-e-list fat32$c))
;;                                    (dirname path)))
;;           0)
;;    (not (equal (mv-nth 1
;;                        (lofat-find-file fat32$c
;;                                         (mv-nth 0 (root-d-e-list fat32$c))
;;                                         path))
;;                0)))
;;   (and (equal (mv-nth 1 (lofat-mkdir fat32$c path))
;;               -1)
;;        (equal (mv-nth 1
;;                       (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
;;                                    path))
;;               0)))
;;  :hints
;;  (("goal" :do-not-induct t
;;    :in-theory
;;    (e/d (lofat-mkdir)
;;         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
;;          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)))
;;    :expand ((:free (fs) (hifat-find-file fs nil))
;;             (:free (fs file)
;;                    (hifat-place-file fs nil file))))))

(defthm
  absfat-oracle-single-step-refinement-lemma-1
  (implies
   (frame-reps-fs frame
                  (mv-nth 0 (lofat-to-hifat fat32$c)))
   (frame-reps-fs (mv-nth 0 (abs-mkdir frame (lofat-st->path st)))
                  (mv-nth 0
                          (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
                                       (lofat-st->path st)))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable abs-mkdir-correctness-2 hifat-mkdir)
           :use (:instance abs-mkdir-correctness-2
                           (path (lofat-st->path st))))))

(defthm
  absfat-oracle-single-step-refinement-lemma-2
  (implies
   (frame-reps-fs frame
                  (mv-nth 0 (lofat-to-hifat fat32$c)))
   (frame-reps-fs (mv-nth 0
                          (abs-pwrite (lofat-st->fd st)
                                      (lofat-st->buf st)
                                      (lofat-st->offset st)
                                      frame
                                      (lofat-st->fd-table st)
                                      (lofat-st->file-table st)))
                  (mv-nth 0
                          (hifat-pwrite (lofat-st->fd st)
                                        (lofat-st->buf st)
                                        (lofat-st->offset st)
                                        (mv-nth 0 (lofat-to-hifat fat32$c))
                                        (lofat-st->fd-table st)
                                        (lofat-st->file-table st)))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable abs-pwrite-correctness-1 hifat-pwrite)
           :use (:instance abs-pwrite-correctness-1
                           (fd (lofat-st->fd st))
                           (buf (lofat-st->buf st))
                           (offset (lofat-st->offset st))
                           (fd-table (lofat-st->fd-table st))
                           (file-table (lofat-st->file-table st))))))

;; I have this single-step property relating two representations of
;; my FAT32 filesystem, AbsFAT and LoFAT. The very next thing I want to do are
;; derive from this a multi-step property for when multiple steps are executed,
;; which is a refinement relation. Towards that end, I will need to define an
;; interpreter which processes a sequence of system calls, and induct on the
;; length of that sequence to apply this single-step property to the induction
;; case.
;;
;; My problem, however, is that this single-step property has too many
;; hypotheses. Currently, there are four hypotheses, and as you can see,
;; hypotheses 1 and 2 are invariants. However, hypotheses 3 and 4 are not,
;; because they ensure that
;; we are not facing certain kinds of running-out-of-space errors in
;; LoFAT. There is not really an equivalent concept of "running out of space"
;; in AbsFAT, because it is a more abstract model and does not get into the
;; byte level as much as LoFAT does. That means there isn't a way to ensure
;; the same kind of running-out-of-space behaviour in AbsFAT, which would allow
;; us to make these hypotheses invariants - there is simply no way in AbsFAT to
;; draw out this information about how much space is available.
;;
;; This seems to present two ways to proceed:
;;
;; - Make a predicate which takes as arguments the current state of LoFAT
;; (i.e. the stobj fat32$c and the auxiliary state st) and the list of
;; instructions, and returns true or false depending on whether hypotheses 3
;; and 4 are preserved as invariants throughout the execution. Use this as a
;; hypothesis for the multi-step relation so that the induction hypothesis
;; becomes strong enough to allow this single-step relation to be used. This
;; seems clunky because I expect to spend a lot of time messing around with
;; this new predicate holds in subgoals when I'm using this multi-step relation
;; for code proofs.
;;
;; - Make some kind of intermediate model between LoFAT and AbsFAT, which does
;; take space issues into account. This, too, seems clunky because AbsFAT is
;; designed to simplify reasoning about sequences of instructions and I will
;; potentially give up some of that if I have to reason about a new model.
;;
;; So, coming to the main questions: is there a third option which is better?
;; Should I just pick one of these two and go with it until I actually start
;; doing a code proof and run into difficulties? Or is one of these two
;; obviously better, despite me not being able to see it yet? It's worth noting
;; that I also want to reason about instructions being executed concurrently,
;; i.e. not necessarily in parallel in the plet sense, but definitely in the
;; sense of single-core concurrency where multiple threads of instructions each
;; get their turn in an arbitrary order to execute one instruction at a
;; time. I expect this to exacerbate any bad decisions I make now, which is why
;; I'm hoping to get this right before I go too far.
(defthm
  absfat-oracle-single-step-refinement
  (implies
   (and
    ;; Hypothesis 1
    (lofat-fs-p fat32$c)
    ;; Hypothesis 2
    (equal (mv-nth '1 (lofat-to-hifat fat32$c))
           '0)
    ;; Hypothesis 3
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    ;; Hypothesis 4
    (not
     (equal (lofat-st->errno
             (mv-nth 1
                     (lofat-oracle-single-step fat32$c syscall-sym st)))
            *enospc*))
    ;; Predicate relating AbsFAT and LoFAT.
    (frame-reps-fs frame
                   (mv-nth 0 (lofat-to-hifat fat32$c))))
   (and
    ;; Hypothesis 1
    (lofat-fs-p (mv-nth 0
                        (lofat-oracle-single-step fat32$c syscall-sym st)))
    ;; Hypothesis 2
    (equal
     (mv-nth '1
             (lofat-to-hifat
              (mv-nth 0
                      (lofat-oracle-single-step fat32$c syscall-sym st))))
     '0)
    ;; Predicate relating AbsFAT and LoFAT.
    (frame-reps-fs
     (mv-nth 0
             (absfat-oracle-single-step frame syscall-sym st))
     (mv-nth
      0
      (lofat-to-hifat
       (mv-nth 0
               (lofat-oracle-single-step fat32$c syscall-sym st)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (absfat-oracle-single-step lofat-oracle-single-step)
                    (hifat-mkdir hifat-pwrite)))))

;; Move later.
(defthm
  hifat-pwrite-correctness-lemma-1
  (implies
   (true-equiv d-e1 d-e2)
   (equal
    (mv-nth 1
            (hifat-place-file fs path (m1-file d-e1 contents)))
    (mv-nth
     1
     (hifat-place-file fs path (m1-file d-e2 contents)))))
  :hints (("goal" :in-theory (enable hifat-place-file)))
  :rule-classes :congruence)

;; Move later.
(defthm
  hifat-pwrite-correctness-2
  (implies
   (hifat-equiv fs1 fs2)
   (equal
    (mv-nth
     1
     (hifat-pwrite fd buf offset fs1 fd-table file-table))
    (mv-nth 1
            (hifat-pwrite fd
                          buf offset fs2 fd-table file-table))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-no-dups-p)))
  :rule-classes :congruence)

(defthm
  hifat-pwrite-correctness-3
  (and
   (integerp
    (mv-nth
     1
     (hifat-pwrite fd buf offset fs1 fd-table file-table)))
   (natp
    (mv-nth
     2
     (hifat-pwrite fd buf offset fs1 fd-table file-table))))
  :rule-classes
  ((:type-prescription
    :corollary
    (integerp
     (mv-nth
      1
      (hifat-pwrite fd buf offset fs1 fd-table file-table))))
   (:type-prescription
    :corollary
    (natp
     (mv-nth
      2
      (hifat-pwrite fd buf offset fs1 fd-table file-table))))))

;; Move later.
(defthm
  hifat-pwrite-correctness-4
  (implies
   (hifat-equiv fs1 fs2)
   (equal
    (mv-nth
     2
     (hifat-pwrite fd buf offset fs1 fd-table file-table))
    (mv-nth 2
            (hifat-pwrite fd
                          buf offset fs2 fd-table file-table))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-no-dups-p)))
  :rule-classes :congruence)

;; Move later.
(defthm
  hifat-mkdir-correctness-2
  (implies
   (hifat-equiv fs1 fs2)
   (equal
    (mv-nth
     1
     (hifat-mkdir fs1 path))
    (mv-nth 1
            (hifat-mkdir fs2 path))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-no-dups-p)))
  :rule-classes :congruence)

;; Move later.
(defthm
  hifat-mkdir-correctness-3
  (and (integerp (mv-nth 1 (hifat-mkdir fs path)))
       (natp (mv-nth 2 (hifat-mkdir fs path))))
  :rule-classes
  ((:type-prescription :corollary (integerp (mv-nth 1 (hifat-mkdir fs path))))
   (:type-prescription
    :corollary (natp (mv-nth 2 (hifat-mkdir fs path))))))

;; Move later.
(defthm
  hifat-mkdir-correctness-4
  (implies
   (hifat-equiv fs1 fs2)
   (equal
    (mv-nth
     2
     (hifat-mkdir fs1 path))
    (mv-nth 2
            (hifat-mkdir fs2 path))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-no-dups-p)))
  :rule-classes :congruence)

(defthmd abs-open-correctness-2
  (equal (lofat-open path fd-table file-table)
         (abs-open path fd-table file-table))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-open abs-open))))

(defcong hifat-equiv equal
  (hifat-pread fd count offset fs fd-table file-table)
  4
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-pread))))

(defthm
  lofat-opendir-correctness-lemma-1
  (implies
   (and (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0))
   (equal
    (lofat-directory-file-p (mv-nth 0
                                    (lofat-find-file fat32$c d-e-list path)))
    (m1-directory-file-p
     (mv-nth
      0
      (hifat-find-file
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
       path)))))
  :hints (("goal" :induct (lofat-find-file fat32$c d-e-list path)
           :in-theory (enable lofat-find-file hifat-find-file))))

;; Replaces one of the corollaries of lofat-find-file-correctness-2.
(defthm
  lofat-find-file-correctness-5
  (implies
   (and (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0))
   (equal
    (mv-nth 1
            (lofat-find-file fat32$c d-e-list path))
    (mv-nth 1
            (hifat-find-file
             (mv-nth 0
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
             path))))
  :hints
  (("goal"
    :in-theory (enable hifat-find-file)
    :induct
    (mv
     (mv-nth
      0
      (hifat-find-file
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
       path))
     (mv-nth 0
             (lofat-find-file fat32$c d-e-list path)))
    :expand (lofat-to-hifat-helper fat32$c nil entry-limit))))

;; Move later.
(defthm
  hifat-lstat-correctness-3
  (and (integerp (mv-nth 1 (hifat-lstat fs path)))
       (natp (mv-nth 2 (hifat-lstat fs path))))
  :hints (("Goal" :in-theory (enable hifat-lstat)))
  :rule-classes
  ((:type-prescription :corollary (integerp (mv-nth 1 (hifat-lstat fs path))))
   (:type-prescription :corollary (natp (mv-nth 2 (hifat-lstat fs path))))))

(defthm
  hifat-opendir-correctness-1
  (integerp (mv-nth 2
                    (hifat-opendir fs path dir-stream-table)))
  :hints (("goal" :in-theory (enable hifat-opendir)))
  :rule-classes :type-prescription)

(defthm hifat-opendir-correctness-lemma-1
  (implies (and (set-equiv x y)
                (no-duplicatesp-equal x)
                (no-duplicatesp-equal y)
                (true-listp x)
                (true-listp y))
           (equal (equal (<<-sort x) (<<-sort y))
                  t))
  :hints (("goal" :do-not-induct t
           :in-theory (disable common-<<-sort-for-perms)
           :use common-<<-sort-for-perms)))

(defthm
  hifat-opendir-correctness-lemma-2
  (implies (and (hifat-equiv fs1 fs2)
                (fat32-filename-list-p (strip-cars fs1))
                (fat32-filename-list-p (strip-cars fs2)))
           (equal (set-equiv (strip-cars fs1)
                             (strip-cars fs2))
                  t))
  :hints
  (("goal" :in-theory (disable hifat-equiv-implies-set-equiv-strip-cars-1)
    :use hifat-equiv-implies-set-equiv-strip-cars-1)))

(defthmd
  lofat-opendir-correctness-2
  (implies (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                  0)
           (and
            (equal (mv-nth 1
                           (lofat-opendir fat32$c dir-stream-table path))
                   (mv-nth 0
                           (hifat-opendir (mv-nth 0 (lofat-to-hifat fat32$c))
                                          path dir-stream-table)))
            (equal (mv-nth 2
                           (lofat-opendir fat32$c dir-stream-table path))
                   (mv-nth 2
                           (hifat-opendir (mv-nth 0 (lofat-to-hifat fat32$c))
                                          path dir-stream-table)))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (lofat-opendir hifat-opendir lofat-to-hifat)
                           (lofat-pread-refinement-lemma-2)))))

(defthm
  lofat-opendir-correctness-lemma-2
  (implies
   (and (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0))
   (equal
    (strip-cars (mv-nth 0
                        (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
    (names-from-d-e-list d-e-list)))
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper
                                     names-from-d-e-list))))

(thm
 (implies
  (and
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
      fat32$c
      root-d-e-list
      entry-limit2))
    0)
   (lofat-directory-file-p
    (mv-nth 0
            (lofat-find-file fat32$c
                             root-d-e-list
                             path))))
  (equal
   (mv-nth
    3
    (lofat-to-hifat-helper
     fat32$c
     (lofat-file->contents
      (mv-nth 0
              (lofat-find-file fat32$c
                               root-d-e-list
                               path)))
     entry-limit1))
   0)))

(verify
 (implies
  (and
   (<= 2
       (fat32-entry-mask (bpb_rootclus fat32$c)))
   (equal (mv-nth 1
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
          0)
   (no-duplicatesp-equal
    (mv-nth 0
            (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
   (<= (len (mv-nth 0 (root-d-e-list fat32$c)))
       65534)
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
    (mv-nth 2
            (lofat-to-hifat-helper fat32$c
                                   (mv-nth 0 (root-d-e-list fat32$c))
                                   (max-entry-count fat32$c))))
   (equal
    (mv-nth 3
            (lofat-to-hifat-helper fat32$c
                                   (mv-nth 0 (root-d-e-list fat32$c))
                                   (max-entry-count fat32$c)))
    0)
   (lofat-fs-p fat32$c)
   (m1-directory-file-p
    (mv-nth
     0
     (hifat-find-file
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c
                                     (mv-nth 0 (root-d-e-list fat32$c))
                                     (max-entry-count fat32$c)))
      path)))
   (equal
    (mv-nth
     1
     (hifat-find-file
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c
                                     (mv-nth 0 (root-d-e-list fat32$c))
                                     (max-entry-count fat32$c)))
      path))
    0))
  (equal
   (<<-sort
    (strip-cars
     (m1-file->contents
      (mv-nth
       0
       (hifat-find-file
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c
                                       (mv-nth 0 (root-d-e-list fat32$c))
                                       (max-entry-count fat32$c)))
        path)))))
   (<<-sort
    (names-from-d-e-list
     (lofat-file->contents
      (mv-nth 0
              (lofat-find-file fat32$c
                               (mv-nth 0 (root-d-e-list fat32$c))
                               path)))))))
 :instructions
 ((:bash
   ("goal" :do-not-induct t
    :in-theory (disable (:rewrite lofat-find-file-correctness-2)
                        lofat-pread-refinement-lemma-2)
    :use (:instance (:rewrite lofat-find-file-correctness-2)
                    (entry-limit (max-entry-count fat32$c))
                    (path path)
                    (d-e-list (mv-nth 0 (root-d-e-list fat32$c)))
                    (fat32$c fat32$c))))
  (:dive 1 1 1)
  := :up
  (:claim
   (and
    (useful-d-e-list-p
     (lofat-file->contents
      (mv-nth 0
              (lofat-find-file fat32$c
                               (mv-nth 0 (root-d-e-list fat32$c))
                               path))))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (lofat-file->contents
        (mv-nth 0
                (lofat-find-file fat32$c
                                 (mv-nth 0 (root-d-e-list fat32$c))
                                 path)))
       (max-entry-count fat32$c)))
     0))
   :hints :none)
  (:rewrite lofat-opendir-correctness-lemma-2)
  :top :bash
  (:bash
   ("goal" :do-not-induct t
    :in-theory (disable (:rewrite lofat-find-file-correctness-2)
                        lofat-pread-refinement-lemma-2)))
  (:dive 1)))

(thm
 (implies (and
           (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                  0)
           (lofat-fs-p fat32$c)
           (useful-d-e-list-p (mv-nth 0 (root-d-e-list fat32$c))))
           (equal (mv-nth 0
                          (lofat-opendir fat32$c dir-stream-table path))
                  (mv-nth 1
                          (hifat-opendir (mv-nth 0 (lofat-to-hifat fat32$c))
                                         path dir-stream-table))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (lofat-opendir hifat-opendir lofat-to-hifat)
                           (lofat-pread-refinement-lemma-2)))))

(encapsulate
  ()

  (local
   (defthm
     lemma
     (implies
      (hifat-equiv fs1 fs2)
      (equal
       (hifat-opendir fs1 path dir-stream-table)
       (hifat-opendir fs2 path dir-stream-table)))
     :hints (("goal" :in-theory (enable hifat-opendir)
              :expand
              ((:with
                fat32-filename-list-fix-when-fat32-filename-list-p
                (fat32-filename-list-fix
                 (<<-sort
                  (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs2
                                                                            path)))))))
               (:with
                (:rewrite fat32-filename-list-p-of-<<-sort-when-fat32-filename-list-p)
                (fat32-filename-list-p
                 (<<-sort
                  (strip-cars
                   (m1-file->contents (mv-nth 0 (hifat-find-file fs2 path)))))))
               (:with
                (:rewrite fat32-filename-list-p-of-strip-cars-when-m1-file-alist-p)
                (fat32-filename-list-p
                 (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs2
                                                                           path))))))
               (:with
                (:rewrite m1-file-alist-p-of-m1-file->contents)
                (m1-file-alist-p
                 (m1-file->contents (mv-nth 0 (hifat-find-file fs2 path)))))
               (:with
                (:rewrite hifat-opendir-correctness-lemma-1)
                (equal
                 (<<-sort
                  (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs2 path)))))
                 (<<-sort
                  (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs1
                                                                            path)))))))
               (:with
                (:rewrite no-duplicatesp-of-strip-cars-when-hifat-no-dups-p)
                (no-duplicatesp-equal
                 (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs2
                                                                           path))))))
               (:with
                hifat-opendir-correctness-lemma-2
                (set-equiv
                 (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs1 path))))
                 (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs2
                                                                           path)))))))))
     :rule-classes :congruence))

  ;; Move later.
  (defcong
    hifat-equiv equal
    (hifat-opendir fs path dir-stream-table)
    1))

(defthmd
  absfat-oracle-multi-step-refinement-lemma-2
  (implies
   (and t
        ;; hypothesis 1
        (lofat-fs-p fat32$c)
        ;; hypothesis 2
        (equal (mv-nth '1 (lofat-to-hifat fat32$c))
               '0)
        ;; hypothesis 3
        (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
           (max-entry-count fat32$c))
        ;; hypothesis 4
        (not
         (equal (lofat-st->errno
                 (mv-nth 1
                         (lofat-oracle-single-step fat32$c syscall-sym st)))
                *enospc*))
        ;; predicate relating absfat and lofat.
        (frame-reps-fs frame
                       (mv-nth 0 (lofat-to-hifat fat32$c))))
   (equal
    (mv-nth 1
            (absfat-oracle-single-step frame syscall-sym st))
    (mv-nth 1
            (lofat-oracle-single-step fat32$c syscall-sym st))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (absfat-oracle-single-step lofat-oracle-single-step
                                               abs-open-correctness-2
                                               abs-opendir-correctness-2
                                               lofat-opendir-correctness-2)
                    (hifat-mkdir hifat-pwrite))))
  :otf-flg t)

(defund lofat-oracle-multi-step (fat32$c syscall-sym-list st)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (lofat-st-p st))
                  :verify-guards nil))
  (b*
      (((when (atom syscall-sym-list)) (mv fat32$c st))
       ((mv fat32$c st) (lofat-oracle-single-step fat32$c (car syscall-sym-list) st)))
    (lofat-oracle-multi-step fat32$c (cdr syscall-sym-list) st)))

(defund absfat-oracle-multi-step (frame syscall-sym-list st)
  (declare (xargs :guard (and (frame-p frame)
                              (lofat-st-p st)
                              (consp (assoc-equal 0 frame))
                              (no-duplicatesp-equal (strip-cars frame)))
                  :guard-debug t
                  :verify-guards nil))
  (b*
      (((when (atom syscall-sym-list)) (mv frame st))
       ((mv frame st) (absfat-oracle-single-step frame (car syscall-sym-list) st)))
    (absfat-oracle-multi-step frame (cdr syscall-sym-list) st)))

(defund good-lofat-oracle-steps-p-helper (fat32$c syscall-sym-list st)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (lofat-st-p st))
                  :verify-guards nil
                  :measure (len syscall-sym-list)))
  (b*
      (((when (atom syscall-sym-list)) (mv t fat32$c))
       ((mv fs &) (lofat-to-hifat fat32$c))
       ((unless
            (< (hifat-entry-count fs)
               (max-entry-count fat32$c)))
        (mv nil fat32$c))
       ((mv fat32$c st)
        (lofat-oracle-single-step fat32$c (car syscall-sym-list)
                                  st))
       ((when
            (equal (lofat-st->errno
                    st)
                   *enospc*))
        (mv nil fat32$c)))
    (good-lofat-oracle-steps-p-helper fat32$c (cdr syscall-sym-list) st)))

(defthm
  lofat-oracle-multi-step-of-append
  (equal
   (lofat-oracle-multi-step fat32$c (append x y)
                            st)
   (lofat-oracle-multi-step (mv-nth 0
                                    (lofat-oracle-multi-step fat32$c x st))
                            y
                            (mv-nth 1
                                    (lofat-oracle-multi-step fat32$c x st))))
  :hints (("goal" :in-theory (enable lofat-oracle-multi-step append))))

(defthm
  good-lofat-oracle-steps-p-helper-of-append
  (equal (mv-nth 0
                 (good-lofat-oracle-steps-p-helper fat32$c (append x y)
                                                   st))
         (and (mv-nth 0
                      (good-lofat-oracle-steps-p-helper fat32$c x st))
              (mv-nth 0
                      (good-lofat-oracle-steps-p-helper
                       (mv-nth 0
                               (lofat-oracle-multi-step fat32$c x st))
                       y
                       (mv-nth 1
                               (lofat-oracle-multi-step fat32$c x st))))))
  :hints (("goal" :in-theory (enable good-lofat-oracle-steps-p-helper
                                     lofat-oracle-multi-step append))))

(defthm
  absfat-oracle-multi-step-of-append
  (equal
   (absfat-oracle-multi-step frame (append x y)
                            st)
   (absfat-oracle-multi-step (mv-nth 0
                                    (absfat-oracle-multi-step frame x st))
                            y
                            (mv-nth 1
                                    (absfat-oracle-multi-step frame x st))))
  :hints (("goal" :in-theory (enable absfat-oracle-multi-step append))))

(encapsulate
  ()

  (local
   (defun-nx
     induction-scheme (fat32$c frame st syscall-sym-list)
     (declare (xargs :stobjs fat32$c
                     :verify-guards nil
                     :measure (len syscall-sym-list)))
     (cond
      ((and
        (not (atom syscall-sym-list))
        (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
           (max-entry-count fat32$c))
        (not
         (equal
          (lofat-st->errno
           (mv-nth 1
                   (lofat-oracle-single-step fat32$c (car syscall-sym-list)
                                             st)))
          28)))
       (induction-scheme
        (mv-nth 0
                (lofat-oracle-single-step fat32$c (car syscall-sym-list)
                                          st))
        (mv-nth 0
                (absfat-oracle-single-step frame (car syscall-sym-list)
                                           st))
        (mv-nth 1
                (lofat-oracle-single-step fat32$c (car syscall-sym-list)
                                          st))
        (cdr syscall-sym-list)))
      (t
       (mv fat32$c frame st syscall-sym-list)))))

  (local (include-book "std/basic/inductions" :dir :system))

  (defthm
    absfat-oracle-multi-step-refinement-lemma-1
    (implies
     (and
      (lofat-fs-p fat32$c)
      (equal (mv-nth '1 (lofat-to-hifat fat32$c))
             '0)
      (mv-nth 0
              (good-lofat-oracle-steps-p-helper
               fat32$c (take n syscall-sym-list) st))
      (frame-reps-fs frame
                     (mv-nth 0 (lofat-to-hifat fat32$c)))
      (<= (nfix n) (len syscall-sym-list)))
     (and
      (lofat-fs-p (mv-nth 0
                          (lofat-oracle-multi-step
                           fat32$c (take n syscall-sym-list) st)))
      (equal
       (mv-nth '1
               (lofat-to-hifat
                (mv-nth 0
                        (lofat-oracle-multi-step
                         fat32$c (take n syscall-sym-list) st))))
       '0)
      (frame-reps-fs
       (mv-nth 0
               (absfat-oracle-multi-step
                frame (take n syscall-sym-list) st))
       (mv-nth
        0
        (lofat-to-hifat
         (mv-nth 0
                 (lofat-oracle-multi-step
                  fat32$c (take n syscall-sym-list) st)))))))
    :hints
    (("goal"
      :in-theory (e/d (absfat-oracle-multi-step lofat-oracle-multi-step
                                                good-lofat-oracle-steps-p-helper)
                      (hifat-mkdir hifat-pwrite take
                                   append-of-take-and-cons))
      :induct
      (dec-induct n)
      :expand
      (:with
       take-as-append-and-nth
       (take n syscall-sym-list))))))
