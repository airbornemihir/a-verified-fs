(include-book "file-system-5")
(include-book "std/lists/repeat" :dir :system)
(defconst *test02-fs* (cons (cons :vmlinuz (l5-make-regular-file
                                            nil 0 t t t t 0)) nil))
; 524288 (that is, 2^19) is the highest size for which this works without a
; segmentation fault
; also, the timing information isn't very helpful
(defconst *test02-disk* (repeat 524288 *nullblock*))
(defconst *test02-alv* (repeat 524288 t))
(time$
 (mv-let (new-fs new-disk new-alv)
   (l5-wrchs '(:vmlinuz) *test02-fs* *test02-disk* *test02-alv* 0 (coerce (flatten
                                                                        (repeat
                                                                         4096
                                                                         (coerce
                                                                          "X3GCtIIL"
                                                                          'list)))
                                                                       'string)
             0)
   (and (null new-fs) (null new-disk) (null new-alv))
   ))
(time$
 (mv-let (new-fs new-disk new-alv)
   (l5-wrchs '(:vmlinuz) *test02-fs* *test02-disk* *test02-alv* 0 (coerce (flatten
                                                                        (repeat
                                                                         16384
                                                                         (coerce
                                                                          "X3GCtIIL"
                                                                          'list)))
                                                                       'string)
             0)
   (and (null new-fs) (null new-disk) (null new-alv))
   ))
(time$
 (mv-let (new-fs new-disk new-alv)
   (l5-wrchs '(:vmlinuz) *test02-fs* *test02-disk* *test02-alv* 0 (coerce (flatten
                                                                        (repeat
                                                                         65536
                                                                         (coerce
                                                                          "X3GCtIIL"
                                                                          'list)))
                                                                       'string)
             0)
   (and (null new-fs) (null new-disk) (null new-alv))
   ))
(time$
 (mv-let (new-fs new-disk new-alv)
   (l5-wrchs '(:vmlinuz) *test02-fs* *test02-disk* *test02-alv* 0 (coerce (flatten
                                                                        (repeat
                                                                         262144
                                                                         (coerce
                                                                          "X3GCtIIL"
                                                                          'list)))
                                                                       'string)
             0)
   (and (null new-fs) (null new-disk) (null new-alv))
   ))
(time$
 (mv-let (new-fs new-disk new-alv)
   (l5-wrchs '(:vmlinuz) *test02-fs* *test02-disk* *test02-alv* 0 (coerce (flatten
                                                                        (repeat
                                                                         1048576
                                                                         (coerce
                                                                          "X3GCtIIL"
                                                                          'list)))
                                                                       'string)
             0)
   (and (null new-fs) (null new-disk) (null new-alv))
   ))
(good-bye)
