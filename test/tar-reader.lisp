(include-book "../test-stuff")
(local (defconst *REGTYPE* #\0))
(local (defconst *DIRTYPE* #\5))

(local
 (in-theory (disable nth update-nth ceiling floor mod true-listp take member-equal)))

(defund tar-len-decode-helper (rev-char-list)
  (declare (xargs :guard (character-listp rev-char-list)))
  (if (atom rev-char-list)
      0
      (+ (nfix (- (char-code (car rev-char-list))
                  (char-code #\0)))
         (* 8
            (tar-len-decode-helper (cdr rev-char-list))))))

(defund
  tar-len-decode (string)
  (declare
   (xargs :guard (stringp string)
          :guard-hints
          (("goal" :in-theory (disable reverse-removal)))))
  (tar-len-decode-helper (reverse (coerce string 'list))))

(defund process-block-sequence (file-text state)
  (declare (xargs :stobjs state
                  :measure (length file-text)
                  :guard (and (state-p state) (stringp file-text)
                              (open-output-channel-p *standard-co* :character state))
                  :guard-debug t))
  (b*
      (((unless (mbe :exec (>= (length file-text) 512)
                     :logic (and (stringp file-text) (>= (length file-text) 512))))
        state)
       (first-block (subseq file-text 0 512))
       ((when (equal first-block
                     (coerce (make-list 512 :initial-element (code-char 0))
                             'string)))
        (process-block-sequence
         (subseq file-text 512 nil) state))
       (first-block-name (subseq first-block 0 100))
       (state (princ$ "File with name " *standard-co* state))
       (state (princ$ first-block-name *standard-co* state))
       (first-block-typeflag (char first-block 156))
       (state (princ$
               (cond ((equal first-block-typeflag *REGTYPE*)
                      " is a regular file")
                     ((equal first-block-typeflag *DIRTYPE*)
                      " is a directory file")
                     (t " is other than a regular or directory file"))
               *standard-co* state))
       (state (princ$ ", has length " *standard-co* state))
       (first-block-length (tar-len-decode (subseq first-block 124 135)))
       (state (princ$ first-block-length *standard-co* state))
       (state (princ$ ", has contents:" *standard-co* state))
       (state (newline *standard-co* state))
       (state (princ$ (subseq file-text 512
                              (min (+ 512 first-block-length) (length file-text)))
                      *standard-co* state))
       (state (newline *standard-co* state)))
    (process-block-sequence
     (subseq file-text (min (+ 512
                               (* 512 (ceiling first-block-length 512)))
                            (length file-text))
             nil)
     state)))

(b*
    (((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory val state))
     ((mv & val state)
      (getenv$ "TAR_INPUT" state))
     (fat32-pathname (pathname-to-fat32-pathname (coerce val 'list)))
     ((mv val error-code &)
      (lofat-lstat fat32-in-memory fat32-pathname))
     ((unless (equal error-code 0))
      (mv fat32-in-memory state))
     (file-length (struct-stat->st_size val))
     ((mv fd-table file-table fd &)
      (lofat-open fat32-pathname fat32-in-memory nil nil))
     ((mv file-text file-read-length &)
      (lofat-pread
       fd file-length 0 fat32-in-memory fd-table file-table))
     ((unless (equal file-read-length file-length))
      (mv fat32-in-memory state))
     (state (process-block-sequence file-text state)))
  (mv fat32-in-memory state))
