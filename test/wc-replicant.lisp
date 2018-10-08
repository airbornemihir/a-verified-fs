(include-book "../file-system-m2")

(b*
    (((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (slurp-disk-image
       fat32-in-memory val state))
     ((mv & val state)
      (getenv$ "WC_OUTPUT" state))
     ((mv channel state)
      (open-output-channel val :character state))
     ((mv & val state)
      (getenv$ "WC_INPUT" state))
     ((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory
                                 (bpb_rootclus fat32-in-memory)
                                 (ash 1 21)))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory dir-contents 40))
     ((mv val error-code &)
      (m1-lstat
       fs (pathname-to-fat32-pathname (coerce val 'list))))
     ((unless (equal error-code 0))
       (mv fat32-in-memory state))
     (state
        (princ$
         (struct-stat->st_size val)
         channel state))
     (state
        (newline channel state))
     (state
      (close-output-channel channel state)))
  (mv fat32-in-memory state))
