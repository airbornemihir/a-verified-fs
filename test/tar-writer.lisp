(include-book "../tar-stuff")

(local (in-theory (disable mod ceiling floor)))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defund
    tar-len-encode-helper (len)
    (declare (xargs :guard (natp len)
                    :measure (nfix len)))
    (if
     (zp len)
     nil
     (cons (code-char (+ (mod len 8) (char-code #\0)))
           (tar-len-encode-helper (floor len 8))))))

(defund tar-len-encode (len)
  ;; It would be folly to stipulate that the length has to be less than 8^11,
  ;; and then keep struggling with every new guard proof.
  (declare (xargs :guard (natp len)
                  :guard-hints (("Goal" :in-theory (enable tar-len-encode-helper)) )))
  (coerce (append (make-list (nfix (- 11 (len (tar-len-encode-helper len))))
                             :initial-element #\0)
                  (revappend (tar-len-encode-helper len) (list (code-char 0))))
          'string))

(b*
    (((mv & disk-image-location state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory disk-image-location state))
     ((mv & val state)
      (getenv$ "TAR_INPUT" state))
     (input-pathname (pathname-to-fat32-pathname (coerce val 'list)))
     ((mv & val state)
      (getenv$ "TAR_OUTPUT" state))
     (output-pathname (pathname-to-fat32-pathname (coerce val 'list))))
  (mv fat32-in-memory state))
