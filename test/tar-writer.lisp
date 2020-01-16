(include-book "../tar-stuff")

(local (in-theory (disable mod ceiling floor)))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defund
    tar-len-encode-helper (len n)
    (declare (xargs :guard (and (natp len) (natp n))))
    (if
     (zp n)
     nil
     (cons (code-char (+ (mod len 8) (char-code #\0)))
           (tar-len-encode-helper (floor len 8) (- n 1))))))

(defthm
  len-of-tar-len-encode-helper
  (equal (len (tar-len-encode-helper len n))
         (nfix n))
  :hints (("goal" :in-theory (enable tar-len-encode-helper))))

(defthm
  character-listp-of-tar-len-encode-helper
  (character-listp (tar-len-encode-helper len n))
  :hints (("goal" :in-theory (enable tar-len-encode-helper))))

(defund tar-len-encode (len)
  ;; It would be folly to stipulate that the length has to be less than 8^11,
  ;; and then keep struggling with every new guard proof.
  (declare (xargs :guard (natp len)
                  :guard-hints (("Goal" :in-theory (enable
                                                    tar-len-encode-helper)) )))
  (coerce (revappend (tar-len-encode-helper len 11) (list (code-char 0)))
          'string))

(defthm length-of-tar-len-encode
  (equal (len (explode (tar-len-encode len))) 12)
  :hints (("Goal" :in-theory (enable tar-len-encode)) ))

(defund
  tar-header-block (pathname len typeflag)
  (declare
   (xargs :guard (and (characterp typeflag)
                      (stringp pathname)
                      (>= 100 (length pathname))
                      (natp len))
          :guard-hints
          (("goal" :in-theory (disable make-list-ac-removal)))))
  (let ((pathname (mbe :exec pathname
                       :logic (str-fix pathname))))
       (concatenate
        'string
        pathname
        (coerce (make-list (- 124 (length pathname))
                           :initial-element (code-char 0))
                'string)
        (tar-len-encode len)
        (coerce (make-list (- 155 136)
                           :initial-element (code-char 0))
                'string)
        (string (mbe :exec typeflag
                     :logic (char-fix typeflag)))
        (coerce (make-list (- 512 156)
                           :initial-element (code-char 0))
                'string))))

(defthm
  length-of-tar-header-block
  (implies (>= 100 (length (str-fix pathname)))
           (equal (len (explode (tar-header-block pathname len typeflag)))
                  512))
  :hints (("goal" :in-theory (enable tar-header-block))))

(defund tar-reg-file-string (fat32-in-memory pathname)
  (declare (xargs :guard (and (lofat-fs-p fat32-in-memory)
                              (stringp pathname))
                  :stobjs fat32-in-memory
                  :guard-debug t
                  :guard-hints (("Goal" :in-theory (disable MAKE-LIST-AC-REMOVAL)) )
                  :verify-guards nil))
  (b*
      ((fat32-pathname (pathname-to-fat32-pathname (coerce pathname 'list)))
       ((unless (fat32-filename-list-p fat32-pathname)) "")
       ((mv val & &) (lofat-lstat fat32-in-memory fat32-pathname))
       (file-length (struct-stat->st_size val))
       ((mv fd-table file-table fd &)
        (lofat-open fat32-pathname nil nil))
       ((unless (>= fd 0)) "")
       ((mv contents & &)
        (lofat-pread
         fd file-length 0 fat32-in-memory fd-table file-table))
       (len (length contents))
       (first-block
        (tar-header-block pathname len *tar-regtype*)))
    (concatenate
     'string
     first-block
     contents
     (coerce
      (make-list
       (- (* 512 (ceiling len 512)) len) :initial-element
       (code-char 0))
      'string))))

(defund
  tar-dir-ent-list-string
  (fat32-in-memory pathname dir-ent-list)
  (declare
   (xargs
    :guard (and (lofat-fs-p fat32-in-memory)
                (useful-dir-ent-list-p dir-ent-list)
                (stringp pathname))
    :stobjs fat32-in-memory
    :guard-debug t
    :guard-hints
    (("goal"
      :in-theory (e/d (lofat-to-hifat-helper
                       lofat-to-hifat-helper-correctness-4)
                      (make-list-ac-removal))))
    :verify-guards nil
    :measure
    (mv-nth
     1
     (lofat-to-hifat-helper fat32-in-memory dir-ent-list
                            (max-entry-count fat32-in-memory)))
    :hints
    (("goal"
      :expand
      (lofat-to-hifat-helper fat32-in-memory dir-ent-list
                             (max-entry-count fat32-in-memory))
      :in-theory
      (enable lofat-to-hifat-helper-correctness-4)))))
  (b*
      (((unless
         (mbe :exec (consp dir-ent-list)
              :logic (and (consp dir-ent-list)
                          (useful-dir-ent-list-p dir-ent-list))))
        "")
       ((mv & & & error-code)
        (lofat-to-hifat-helper fat32-in-memory dir-ent-list
                               (max-entry-count fat32-in-memory)))
       ((unless (zp error-code)) "")
       (head (car dir-ent-list))
       (head-pathname
        (concatenate
         'string pathname "/"
         (coerce
          (fat32-name-to-name (coerce (dir-ent-filename head) 'list))
          'string)))
       ((unless (dir-ent-directory-p head))
        (concatenate
         'string
         (tar-reg-file-string fat32-in-memory head-pathname)
         (tar-dir-ent-list-string fat32-in-memory
                                  pathname (cdr dir-ent-list))))
       ((mv head-clusterchain-contents &)
        (dir-ent-clusterchain-contents fat32-in-memory head)))
    (concatenate
     'string
     (tar-header-block head-pathname 0 *tar-dirtype*)
     (tar-dir-ent-list-string
      fat32-in-memory head-pathname
      (make-dir-ent-list head-clusterchain-contents))
     (tar-dir-ent-list-string fat32-in-memory
                              pathname (cdr dir-ent-list)))))

(b*
    (((mv & disk-image-location state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory disk-image-location state))
     ((mv & input-pathname state)
      (getenv$ "TAR_INPUT" state))
     ((mv & val state)
      (getenv$ "TAR_OUTPUT" state))
     (output-pathname (pathname-to-fat32-pathname (coerce val 'list)))
     ((mv root-dir-ent-list &) (root-dir-ent-list fat32-in-memory))
     ((mv file error-code)
      (lofat-find-file fat32-in-memory root-dir-ent-list
                       (pathname-to-fat32-pathname (coerce input-pathname 'list))))
     ((unless (zp error-code))
      (mv fat32-in-memory state))
     (file-text
      (if
          (lofat-regular-file-p file)
          (tar-reg-file-string fat32-in-memory input-pathname)
        (concatenate
         'string
         (tar-header-block input-pathname 0 *tar-dirtype*)
         (tar-dir-ent-list-string
          fat32-in-memory input-pathname (lofat-file->contents file)))))
     ((mv fd-table file-table fd &)
      (lofat-open output-pathname nil nil))
     ((mv fat32-in-memory & &)
      (lofat-pwrite fd file-text 0 fat32-in-memory fd-table file-table))
     ((mv state &)
      (lofat-to-disk-image
       fat32-in-memory disk-image-location state)))
  (mv fat32-in-memory state))
