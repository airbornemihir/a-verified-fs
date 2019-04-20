(include-book "../lofat")

(profile 'disk-image-to-lofat)
(profile 'lofat-to-disk-image)

(b*
    (((mv & image-path state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (time$
       (disk-image-to-lofat
        fat32-in-memory image-path state)
       :msg "The execution of ~xf took ~st seconds of real ~
                   time and ~sc seconds of run time (cpu time), and ~
                   allocated ~sa bytes.  In an unrelated note, bar ~
                   currently has the value ~x0.~%"
       :args nil))
     (state
      (time$
       (lofat-to-disk-image
        fat32-in-memory image-path state)
       :msg "The execution of ~xf took ~st seconds of real ~
                   time and ~sc seconds of run time (cpu time), and ~
                   allocated ~sa bytes.  In an unrelated note, bar ~
                   currently has the value ~x0.~%"
       :args nil)))
  (mv fat32-in-memory state))

(memsum)
