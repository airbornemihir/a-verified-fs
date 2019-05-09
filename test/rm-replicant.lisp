(include-book "../test-stuff")
(include-book "oslib/argv" :dir :system)

;; (defthm rm-2-guard-lemma-1
;;   (implies
;;    (and
;;     (stringp disk-path)
;;     (string-listp rm-pathnames)
;;     (lofat-fs-p fat32-in-memory)
;;     (state-p1 state))
;;    (equal
;;     (mv-nth 1
;;             (rm-1 fat32-in-memory nil rm-pathnames))
;;     (lofat-to-string
;;      (mv-nth
;;       0
;;       (hifat-to-lofat
;;        (mv-nth 0 (string-to-lofat fat32-in-memory nil))
;;        (mv-nth
;;         0
;;         (rm-list
;;          (mv-nth
;;           0
;;           (lofat-to-hifat (mv-nth 0
;;                                   (string-to-lofat fat32-in-memory nil))))
;;          rm-pathnames 0)))))))
;;   :hints (("Goal" :in-theory (enable rm-1)) ))

(defthm
  rm-2-guard-lemma-1
  (implies
   (not (equal (mv-nth 1 (rm-list fs name-list exit-status))
               exit-status))
   (equal (mv-nth 1 (rm-list fs name-list exit-status))
          1)))

(defun rm-2 (fat32-in-memory state disk-path output-path rm-pathnames)
  (declare (xargs :stobjs (state fat32-in-memory)
                  :guard (and (fat32-in-memoryp fat32-in-memory)
                              (string-listp rm-pathnames)
                              (stringp disk-path)
                              (stringp output-path)
                              (state-p state))
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (e/d (rm-1) (read-file-into-string2))) )))
  (mbe :logic
       (b*
           ((disk-image-string (read-file-into-string disk-path))
            ((mv fat32-in-memory disk-image-string exit-status)
             (rm-1 fat32-in-memory disk-image-string rm-pathnames))
            ((unless (equal exit-status 0)) (mv fat32-in-memory state 1))
            ((mv channel state)
             (open-output-channel output-path
                                  :character state))
            ((when (null channel)) (mv fat32-in-memory state 1))
            (state
             (princ$ disk-image-string channel state))
            (state (close-output-channel channel state)))
         (mv fat32-in-memory state exit-status))
       :exec
       (b*
           (((mv fat32-in-memory error-code)
             (disk-image-to-lofat
              fat32-in-memory disk-path state))
            ((unless (equal error-code 0))
             (mv fat32-in-memory state 1))
            ((mv fs &)
             (lofat-to-hifat fat32-in-memory))
            ((mv fs exit-status)
             (rm-list fs rm-pathnames 0))
            ((mv fat32-in-memory &)
             (hifat-to-lofat fat32-in-memory fs))
            ((unless (equal exit-status 0)) (mv fat32-in-memory state 1))
            ((mv state error-code)
             (lofat-to-disk-image
              fat32-in-memory output-path state))
            (exit-status (if (equal error-code 0) exit-status 1)))
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
      (rm-2 fat32-in-memory state disk-path output-path extra-args)))
  (mv (good-bye exit-status) fat32-in-memory state))
