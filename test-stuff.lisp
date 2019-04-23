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
  (b*
      (((when (atom name-list))
        (mv fs exit-status))
       (fat32-pathname
        (pathname-to-fat32-pathname (coerce (car name-list) 'list)))
       ;; It doesn't really matter for these purposes what the errno is. We're
       ;; not trying to match this program for its stderr output.
       ((mv fs retval &)
        (if r
            (hifat-unlink-recursive fs fat32-pathname)
          (hifat-unlink fs fat32-pathname)))
       (exit-status (if (equal retval 0) exit-status 1)))
    (rm-list fs r (cdr name-list) exit-status)))

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

(defthm
  wc-guard-lemma-1
  (implies (lofat-regular-file-p file)
           (not (lofat-directory-file-p file)))
  :hints (("goal" :in-theory (enable lofat-directory-file-p
                                     lofat-regular-file-p))))

(defun wc-1 (fat32-in-memory pathname)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (stringp pathname) (lofat-fs-p fat32-in-memory))
                  :guard-debug t))
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

