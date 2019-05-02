(in-package "ACL2")

(include-book "lofat-syscalls")
(include-book "centaur/getopt/top" :dir :system)

(defoptions mkdir-opts
  :parents (demo2)
  :tag :demo2
  ((parents    "no error if existing, make parent directories as needed"
               booleanp
               :rule-classes :type-prescription
               :alias #\p)))

(defun mkdir-list (fs name-list exit-status)
  (b*
      (((when (atom name-list))
        (mv fs exit-status))
       (fat32-pathname
        (pathname-to-fat32-pathname (coerce (car name-list) 'list)))
       ;; It doesn't really matter for these purposes what the errno is. We're
       ;; not trying to match this program for its stderr output.
       ((mv fs retval &)
        (hifat-mkdir fs fat32-pathname))
       (exit-status (if (equal retval 0) exit-status 1)))
    (mkdir-list fs (cdr name-list) exit-status)))

(defoptions rm-opts
  :parents (demo2)
  :tag :demo2
  ((recursive    "Recursively delete a directory"
                 booleanp
                 :rule-classes :type-prescription
                 :alias #\r)))

(defun rm-list (fs r name-list exit-status)
  (declare (xargs :guard
                  (and
                   (m1-file-alist-p fs)
                   (STRING-listp NAME-LIST))))
  (b*
      (((when (atom name-list))
        (mv
         (mbe :logic (m1-file-alist-fix fs) :exec fs)
         exit-status))
       (fat32-pathname
        (pathname-to-fat32-pathname (coerce (car name-list) 'list)))
       ;; It doesn't really matter for these purposes what the errno is. We're
       ;; not trying to match this program for its stderr output.
       ((mv fs retval &)
        (if (not (fat32-filename-list-p fat32-pathname))
            (mv fs 1 *enoent*)
          (if r
              (hifat-unlink-recursive fs fat32-pathname)
            (hifat-unlink fs fat32-pathname))))
       (exit-status (if (equal retval 0) exit-status 1)))
    (rm-list fs r (cdr name-list) exit-status)))

(defthm
  rm-1-guard-lemma-1
  (m1-file-alist-p
   (mv-nth 0 (rm-list fs r name-list exit-status)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite hifat-subsetp-transitive)
                        (:definition pathname-to-fat32-pathname)
                        (:definition name-to-fat32-name)
                        (:definition hifat-subsetp)))))

(defund
  rm-1
  (fat32-in-memory pathnames recursive-p)
  (declare (xargs :guard (and (lofat-fs-p fat32-in-memory)
                              (string-listp pathnames))
                  :stobjs fat32-in-memory))
  (b* (((mv fs &)
        (lofat-to-hifat fat32-in-memory))
       ((mv fs exit-status)
        (if recursive-p (rm-list fs t pathnames 0)
            (rm-list fs nil pathnames 0)))
       ((mv fat32-in-memory &)
        (hifat-to-lofat fat32-in-memory fs)))
    (mv fat32-in-memory exit-status)))

(defoptions rmdir-opts
  :parents (demo2)
  :tag :demo2
  ((parents    "no error if existing, make parent directories as needed"
               booleanp
               :rule-classes :type-prescription
               :alias #\p)))

(defun rmdir-list (fs name-list exit-status)
  (b*
      (((when (atom name-list))
        (mv fs exit-status))
       (fat32-pathname
        (pathname-to-fat32-pathname (coerce (car name-list) 'list)))
       ;; It doesn't really matter for these purposes what the errno is. We're
       ;; not trying to match this program for its stderr output.
       ((mv fs retval &)
        (hifat-rmdir fs fat32-pathname))
       (exit-status (if (equal retval 0) exit-status 1)))
    (rmdir-list fs (cdr name-list) exit-status)))

(defoptions wc-opts
  :parents (demo2)
  :tag :demo2
  ((bytes    "Count bytes"
             booleanp
             :rule-classes :type-prescription
             :alias #\c)
   (lines "Count lines"
          booleanp
          :rule-classes :type-prescription
          :alias #\l)
   (words "Count words"
          booleanp
          :rule-classes :type-prescription
          :alias #\w)))

(defun
  wc-helper
  (text nl nw nc beginning-of-word-p pos)
  (declare (xargs :measure (nfix (- (length text) pos))
                  :guard (and (stringp text)
                              (natp pos)
                              (natp nc)
                              (natp nw)
                              (natp nl)
                              (<= pos (length text)))))
  (if (zp (- (length text) pos))
      (mv nl nw nc)
      (b* ((c (char text pos))
           (nc (+ nc 1))
           (nl (if (equal c #\newline) (+ nl 1) nl))
           ((mv beginning-of-word-p nw)
            (if (or (equal c #\space)
                    (equal c #\newline)
                    (equal c #\tab))
                (mv t nw)
                (if beginning-of-word-p (mv nil (+ nw 1))
                    (mv beginning-of-word-p nw)))))
        (wc-helper text nl
                   nw nc beginning-of-word-p (+ pos 1)))))

(defund wc-1 (fat32-in-memory pathname)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (stringp pathname)
                (lofat-fs-p fat32-in-memory))
    :guard-hints
    (("goal" :in-theory
      (enable lofat-open lofat-lstat)))))
  (b*
      ((fat32-pathname (pathname-to-fat32-pathname (coerce pathname 'list)))
       ;; It would be nice to eliminate this check by proving a theorem, but
       ;; it's not at all simple to ensure that a string given to us is free of
       ;; filenames indicating deleted files and such which are not allowed in
       ;; a pathname satisfying fat32-filename-list-p.
       ((unless (fat32-filename-list-p fat32-pathname))
        (mv 0 0 0 1))
       ((mv val error-code &)
        (lofat-lstat fat32-in-memory fat32-pathname))
       ((unless (equal error-code 0))
        (mv 0 0 0 error-code))
       (file-length (struct-stat->st_size val))
       ((mv fd-table file-table fd &)
        (lofat-open fat32-pathname fat32-in-memory nil nil))
       ((mv file-text file-read-length &)
        (lofat-pread
         fd file-length 0 fat32-in-memory fd-table file-table))
       ((unless (equal file-read-length file-length))
        (mv 0 0 0 1))
       ((mv nl nw nc)
        (wc-helper file-text 0 0 0 t 0)))
    (mv nl nw nc 0)))

(defthm
  wc-after-rm-lemma-1
  (implies
   (not
    (equal
     (mv-nth
      1
      (lofat-lstat
       fat32-in-memory
       (pathname-to-fat32-pathname (coerce pathname 'list))))
     0))
   (not (equal (mv-nth 3 (wc-1 fat32-in-memory pathname))
               0)))
  :hints (("goal" :in-theory (enable wc-1))))

(defthm
  wc-after-rm-lemma-2
  (implies
   (equal
    (mv-nth
     1
     (find-file-by-pathname fs
                            (pathname-to-fat32-pathname (explode pathname))))
    *enoent*)
   (equal
    (mv-nth
     1
     (find-file-by-pathname (mv-nth 0
                                    (rm-list fs nil pathnames exit-status))
                            (pathname-to-fat32-pathname (explode pathname))))
    *enoent*))
  :hints (("goal" :induct (rm-list fs nil pathnames exit-status)
           :in-theory (disable (:definition pathname-to-fat32-pathname)
                               (:definition name-to-fat32-name)
                               (:linear len-of-member-equal)
                               (:definition take-redefinition)))))

(defthm
  wc-after-rm-lemma-3
  (implies (m1-regular-file-p
            (mv-nth 0 (find-file-by-pathname fs pathname)))
           (equal (mv-nth 1 (find-file-by-pathname fs pathname))
                  0)))

(defthm wc-after-rm-lemma-4
  (fat32-filename-list-prefixp x x))

(defthm
  wc-after-rm-lemma-6
  (implies (m1-regular-file-p (mv-nth 0 (find-file-by-pathname fs pathname)))
           (equal (mv-nth 1 (remove-file-by-pathname fs pathname))
                  0)))

(defthm
  wc-after-rm-lemma-5
  (implies
   (and
    (m1-regular-file-p
     (mv-nth 0
             (find-file-by-pathname
              fs
              (pathname-to-fat32-pathname (explode pathname)))))
    (member-equal pathname pathnames)
    (fat32-filename-list-p (pathname-to-fat32-pathname (explode pathname))))
   (equal
    (mv-nth
     1
     (find-file-by-pathname (mv-nth 0
                                    (rm-list fs nil pathnames exit-status))
                            (pathname-to-fat32-pathname (explode pathname))))
    *enoent*))
  :hints (("goal" :induct (rm-list fs nil pathnames exit-status)
           :in-theory (disable (:definition pathname-to-fat32-pathname)
                               (:definition name-to-fat32-name)
                               (:linear len-of-member-equal)
                               (:definition take-redefinition)))))

(defthm
  wc-after-rm
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (m1-bounded-file-alist-p
     (mv-nth '0
             (rm-list (mv-nth '0
                              (lofat-to-hifat fat32-in-memory))
                      'nil
                      pathnames '0)))
    (m1-file-no-dups-p
     (mv-nth '0
             (rm-list (mv-nth '0
                              (lofat-to-hifat fat32-in-memory))
                      'nil
                      pathnames '0)))
    (not
     (<
      (max-entry-count fat32-in-memory)
      (m1-entry-count
       (mv-nth
        '0
        (rm-list (mv-nth '0
                         (lofat-to-hifat fat32-in-memory))
                 'nil
                 pathnames '0)))))
    (equal
     (mv-nth
      '1
      (hifat-to-lofat
       fat32-in-memory
       (mv-nth
        '0
        (rm-list (mv-nth '0
                         (lofat-to-hifat fat32-in-memory))
                 'nil
                 pathnames '0))))
     0)
    (m1-file-no-dups-p
     (mv-nth
      0
      (lofat-to-hifat
       (mv-nth
        0
        (hifat-to-lofat
         fat32-in-memory
         (mv-nth
          0
          (rm-list (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                   nil pathnames 0)))))))
    (m1-regular-file-p
     (mv-nth
      0
      (find-file-by-pathname
       (mv-nth 0 (lofat-to-hifat fat32-in-memory))
       (pathname-to-fat32-pathname (explode pathname))))))
   (b*
       (((mv fat32-in-memory &)
         (rm-1 fat32-in-memory pathnames nil)))
     (implies
      (and (member-equal pathname pathnames)
           (stringp pathname)
           (fat32-filename-list-p
            (pathname-to-fat32-pathname (explode pathname))))
      (not (equal (mv-nth 3 (wc-1 fat32-in-memory pathname))
                  0)))))
  :hints
  (("goal"
    :in-theory
    (e/d (rm-1 wc-1)
         (find-file-by-pathname-correctness-3-lemma-7
          wc-after-rm-lemma-5
          (:definition pathname-to-fat32-pathname)
          (:definition name-to-fat32-name)))
    :do-not-induct t
    :expand
    (:with
     lofat-pread-refinement
     (:free (fd count offset
                fat32-in-memory fd-table file-table)
            (lofat-pread fd count offset
                         fat32-in-memory fd-table file-table)))
    :use
    ((:instance
      find-file-by-pathname-correctness-3-lemma-7
      (pathname (pathname-to-fat32-pathname (explode pathname)))
      (m1-file-alist2
       (mv-nth
        0
        (lofat-to-hifat
         (mv-nth
          0
          (hifat-to-lofat
           fat32-in-memory
           (mv-nth
            0
            (rm-list (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                     nil pathnames 0)))))))
      (m1-file-alist1
       (mv-nth
        0
        (rm-list (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                 nil pathnames 0))))
     (:instance
      wc-after-rm-lemma-5
      (exit-status 0)
      (fs (mv-nth 0
                  (lofat-to-hifat fat32-in-memory))))))))

(defoptions ls-opts
  :parents (demo2)
  :tag :demo2
  ((directory    "Recursively delete a directory"
                 booleanp
                 :rule-classes :type-prescription
                 :alias #\d)))

(defun ls-list (fat32-in-memory name-list)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and
                          (lofat-fs-p fat32-in-memory) (string-listp name-list))))
  (b*
      (((when (atom name-list)) nil)
       (fat32-pathname
        (pathname-to-fat32-pathname (coerce (car name-list) 'list)))
       ;; It doesn't really matter for these purposes what the errno is. We're
       ;; not trying to match this program for its stderr output.
       ((unless
            (fat32-filename-list-p fat32-pathname))
        (ls-list fat32-in-memory (cdr name-list)))
       ((mv & retval &)
        (lofat-lstat fat32-in-memory fat32-pathname)))
    (if
        (equal retval 0)
        (cons (car name-list) (ls-list fat32-in-memory (cdr name-list)))
      (ls-list fat32-in-memory (cdr name-list)))))

(defthm ls-list-correctness-1
  (<= (len (ls-list fat32-in-memory name-list))
      (len name-list))
  :rule-classes :linear)

(defthmd
  ls-list-correctness-2
  (implies
   (not (equal (mv-nth 1
                       (lofat-lstat fat32-in-memory pathname))
               0))
   (equal (mv-nth 1
                  (lofat-lstat fat32-in-memory pathname))
          -1))
  :hints (("goal" :in-theory (enable lofat-lstat))))

(defthm
  ls-list-correctness-3
  (implies
   (and
    (member-equal pathname name-list)
    (equal (len (ls-list fat32-in-memory name-list))
           (len name-list)))
    (and
     (fat32-filename-list-p
      (pathname-to-fat32-pathname (explode pathname)))
     (equal
      (mv-nth
       1
       (lofat-lstat
        fat32-in-memory
        (pathname-to-fat32-pathname (explode pathname))))
      0))))

(defthm
  ls-after-rm-lemma-1
  (implies
   (and
    (equal
     (len
      (ls-list
       (mv-nth
        0
        (hifat-to-lofat
         fat32-in-memory
         (mv-nth 0
                 (rm-list (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                          nil rm-pathnames 0))))
       ls-pathnames))
     (len ls-pathnames))
    (fat32-filename-list-p
     (pathname-to-fat32-pathname
      (explode (nth 0
                    (intersection-equal ls-pathnames rm-pathnames)))))
    (member-equal (nth 0
                       (intersection-equal ls-pathnames rm-pathnames))
                  rm-pathnames)
    (lofat-fs-p fat32-in-memory)
    (string-listp rm-pathnames))
   (not
    (equal
     (mv-nth
      1
      (lofat-lstat
       (mv-nth
        0
        (hifat-to-lofat
         fat32-in-memory
         (mv-nth 0
                 (rm-list (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                          nil rm-pathnames 0))))
       (pathname-to-fat32-pathname
        (explode (nth 0
                      (intersection-equal ls-pathnames rm-pathnames))))))
     0)))
  :hints (("Goal" :in-theory (e/d (lofat-lstat) (nth)) :do-not-induct t) ))

(defthm
  ls-after-rm
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (string-listp rm-pathnames)
    ;; (m1-bounded-file-alist-p
    ;;  (mv-nth '0
    ;;          (rm-list (mv-nth '0
    ;;                           (lofat-to-hifat fat32-in-memory))
    ;;                   'nil
    ;;                   pathnames '0)))
    ;; (m1-file-no-dups-p
    ;;  (mv-nth '0
    ;;          (rm-list (mv-nth '0
    ;;                           (lofat-to-hifat fat32-in-memory))
    ;;                   'nil
    ;;                   pathnames '0)))
    ;; (not
    ;;  (<
    ;;   (max-entry-count fat32-in-memory)
    ;;   (m1-entry-count
    ;;    (mv-nth
    ;;     '0
    ;;     (rm-list (mv-nth '0
    ;;                      (lofat-to-hifat fat32-in-memory))
    ;;              'nil
    ;;              pathnames '0)))))
    ;; (equal
    ;;  (mv-nth
    ;;   '1
    ;;   (hifat-to-lofat
    ;;    fat32-in-memory
    ;;    (mv-nth
    ;;     '0
    ;;     (rm-list (mv-nth '0
    ;;                      (lofat-to-hifat fat32-in-memory))
    ;;              'nil
    ;;              pathnames '0))))
    ;;  0)
    ;; (m1-file-no-dups-p
    ;;  (mv-nth
    ;;   0
    ;;   (lofat-to-hifat
    ;;    (mv-nth
    ;;     0
    ;;     (hifat-to-lofat
    ;;      fat32-in-memory
    ;;      (mv-nth
    ;;       0
    ;;       (rm-list (mv-nth 0 (lofat-to-hifat fat32-in-memory))
    ;;                nil pathnames 0)))))))
    ;; (m1-regular-file-p
    ;;  (mv-nth
    ;;   0
    ;;   (find-file-by-pathname
    ;;    (mv-nth 0 (lofat-to-hifat fat32-in-memory))
    ;;    (pathname-to-fat32-pathname (explode pathname)))))
    )
   (b*
       (((mv fat32-in-memory &)
         (rm-1 fat32-in-memory rm-pathnames nil)))
     (implies
      (and (< 0 (len (intersection-equal ls-pathnames rm-pathnames))))
      (< (len (ls-list fat32-in-memory ls-pathnames)) (len ls-pathnames)))))
  :hints
  (("goal"
    :in-theory
    (e/d (rm-1)
         (ls-list-correctness-3 nth
                                (:rewrite member-equal-nth)))
    :do-not-induct t
    :use
    ((:instance
      ls-list-correctness-3
      (pathname (nth 0 (intersection-equal ls-pathnames rm-pathnames)))
      (fat32-in-memory
       (mv-nth 0
               (hifat-to-lofat
                fat32-in-memory
                (mv-nth 0
                        (rm-list (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                                 nil rm-pathnames 0)))))
      (name-list ls-pathnames))
     (:instance
      (:rewrite member-equal-nth)
      (l (intersection-equal ls-pathnames rm-pathnames))
      (n 0))))))

(defun compare-disks (image-path1 image-path2 fat32-in-memory state)
  (declare (xargs :stobjs (fat32-in-memory state)
                  :guard-debug t
                  :guard (and (fat32-in-memoryp fat32-in-memory)
                              (stringp image-path1)
                              (stringp image-path2))
                  :guard-hints (("Goal" :in-theory (disable
                                                    read-file-into-string2)) )))
  (b*
      (((mv fat32-in-memory error-code1)
        (disk-image-to-lofat
         fat32-in-memory image-path1 state))
       ((mv fs-ref error-code2)
        (if
            (not (equal error-code1 0))
            (mv nil *EIO*)
          (lofat-to-hifat fat32-in-memory)))
       ((mv fat32-in-memory error-code3)
        (disk-image-to-lofat
         fat32-in-memory image-path2 state))
       ((mv fs error-code4)
        (if
            (or (not (equal error-code1 0)) (not (equal error-code3 0)))
            (mv nil *EIO*)
          (lofat-to-hifat fat32-in-memory)))
       ((unless (or (equal error-code1 0) (equal error-code3 0)))
        (mv t fat32-in-memory))
       ((unless (and (equal error-code1 0) (equal error-code3 0)))
        (mv nil fat32-in-memory))
       ((unless (or (equal error-code2 0) (equal error-code4 0)))
        (mv t fat32-in-memory))
       ((unless (and (equal error-code2 0) (equal error-code4 0)))
        (mv nil fat32-in-memory))
       ((unless (hifat-equiv fs-ref fs))
        (mv nil fat32-in-memory)))
    (mv t fat32-in-memory)))

(defthm
  compare-disks-correctness-1-lemma-1
  (implies
   (not (stringp str))
   (not (equal (mv-nth 1 (string-to-lofat-nx str))
               0)))
  :hints (("goal" :in-theory (enable string-to-lofat string-to-lofat-nx))))

(defthm
  compare-disks-correctness-1
  (let*
      ((str1 (read-file-into-string image-path1))
       (str2 (read-file-into-string image-path2)))
    (implies
     (fat32-in-memoryp fat32-in-memory)
     (equal
      (mv-nth 0
              (compare-disks image-path1
                             image-path2 fat32-in-memory state))
      (eqfat str1 str2))))
  :hints
  (("goal"
    :in-theory
    (e/d (eqfat string-to-lofat-ignore-lemma-14
                lofat-equiv)
         (read-file-into-string2 (:e string-to-lofat-nx)))
    :expand (hide (string-to-lofat-nx nil)))))

