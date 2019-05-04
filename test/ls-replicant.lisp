(include-book "../test-stuff")
(include-book "oslib/argv" :dir :system)

(defun ls-output (prefix ls-list channel state)
  (declare (xargs :stobjs state :verify-guards nil))
  (if
      (atom ls-list)
      state
    (b*
        ((state (princ$ (concatenate 'string prefix (car ls-list)) channel state))
         (state (newline channel state)))
      (ls-output prefix (cdr ls-list) channel state))))

(b*
    (((mv argv state)
      (oslib::argv))
     ((mv errmsg & extra-args) (parse-ls-opts argv))
     ;; Parsing error.
     ((when errmsg)
      (mv (good-bye 1) fat32-in-memory state))
     ;; ((rm-opts opts) opts)
     ((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory val state))
     (ls-list
      (ls-list fat32-in-memory extra-args))
     (exit-status
      (if (< (len ls-list) (len extra-args)) 2 0))
     ((mv & prefix state)
      (getenv$ "LS_PREFIX" state))
     ((mv & val state)
      (getenv$ "LS_OUTPUT" state))
     ((mv channel state)
      (open-output-channel val :character state))
     (state (ls-output prefix ls-list channel state))
     (state (close-output-channel channel state)))
  (mv (good-bye exit-status) fat32-in-memory state))
