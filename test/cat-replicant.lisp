(include-book "../file-system-m2")

(defun
  get-dir-ent-first-cluster-contents
  (fat32-in-memory data-region-index)
  (declare (xargs :stobjs (fat32-in-memory)
                  :verify-guards nil))
  (let*
   ((dir-ent (get-dir-ent fat32-in-memory data-region-index))
    (first-cluster (dir-ent-first-cluster dir-ent))
    (cluster-size (* (bpb_bytspersec fat32-in-memory)
                     (bpb_secperclus fat32-in-memory)))
    (file-size (dir-ent-file-size dir-ent))
    (data-region-index (* (nfix (- first-cluster 2))
                          cluster-size)))
   (nats=>string
    (rev (get-dir-ent-helper fat32-in-memory data-region-index
                             (min file-size cluster-size))))))

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
       (get-dir-ent-first-cluster-contents
        fat32-in-memory 0)
       channel state))
     (state
      (close-output-channel channel state)))
  (mv fat32-in-memory state))
