(include-book "../file-system-m2")

(defun
    all-following-cluster-contents
    (fat32-in-memory current-cluster file-size)
  (declare (xargs :stobjs (fat32-in-memory)
                  :verify-guards nil))
  (let*
      ((cluster-size (* (bpb_bytspersec fat32-in-memory)
                        (bpb_secperclus fat32-in-memory)))
       (data-region-index (* (nfix (- current-cluster 2))
                             cluster-size)))
    (if
        (or (zp file-size) (zp cluster-size))
        ""
      (string-append
       (nats=>string
        (rev (get-dir-ent-helper fat32-in-memory data-region-index
                                 (min file-size cluster-size))))
       (all-following-cluster-contents
        fat32-in-memory (fati current-cluster fat32-in-memory)
        (nfix (- file-size cluster-size)))))))

(defun
  get-dir-ent-contents
  (fat32-in-memory data-region-index)
  (declare (xargs :stobjs (fat32-in-memory)
                  :verify-guards nil))
  (let*
   ((dir-ent (get-dir-ent fat32-in-memory data-region-index))
    (first-cluster (dir-ent-first-cluster dir-ent))
    (file-size (dir-ent-file-size dir-ent)))
   (all-following-cluster-contents
    fat32-in-memory first-cluster file-size)))

(b*
    (((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (slurp-disk-image
       fat32-in-memory val state))
     ((mv & val state)
      (getenv$ "CAT_OUTPUT" state))
     ((mv channel state)
      (open-output-channel val :character state))
     (state
      (princ$
       (get-dir-ent-contents
        fat32-in-memory 0)
       channel state))
     (state
      (close-output-channel channel state)))
  (mv fat32-in-memory state))
