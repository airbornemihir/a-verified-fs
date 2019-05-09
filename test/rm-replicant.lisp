(include-book "../test-stuff")
(include-book "oslib/argv" :dir :system)

(defun rm-2 (fat32-in-memory state disk-path output-path rm-pathnames)
  (declare (xargs :stobjs (state fat32-in-memory)
                  :guard (fat32-in-memoryp fat32-in-memory)))
  (mbe :logic
       (b*
           ((disk-image-string (read-file-into-string disk-path))
            ((mv fat32-in-memory disk-image-string exit-status)
             (rm-1 fat32-in-memory disk-image-string rm-pathnames))
            ((mv channel state)
             (open-output-channel output-path
                                  :character state))
            (state
             (princ$ disk-image-string channel state))
            (state (close-output-channel channel state)))
         (mv fat32-in-memory state exit-status))
       :exec
       (b*
           (((mv fat32-in-memory &)
             (disk-image-to-lofat
              fat32-in-memory disk-path state))
            ((mv fs &)
             (lofat-to-hifat fat32-in-memory))
            ((mv fs exit-status)
             (rm-list fs rm-pathnames 0))
            ((mv fat32-in-memory &)
             (hifat-to-lofat fat32-in-memory fs))
            (state
             (lofat-to-disk-image
              fat32-in-memory output-path state)))
         (mv fat32-in-memory state exit-status))))

(b*
    (((mv argv state)
      (oslib::argv))
     ((mv errmsg & extra-args) (parse-rm-opts argv))
     ;; Either a parsing error, or no files provided on the command line.
     ((when (or errmsg (atom extra-args)))
      (mv (good-bye 1) fat32-in-memory state))
     ((mv & disk-path state)
      (getenv$ "DISK" state))
     ((mv & output-path state)
      (getenv$ "RM_OUTPUT" state))
     ((mv fat32-in-memory state exit-status)
      (rm-2 fat32-in-memory state disk-path output-path)))
  (mv (good-bye exit-status) fat32-in-memory state))
