(include-book "../file-system-m2")

(defun
    get-clusterchain-contents
    (fat32-in-memory clusterchain file-size)
  (declare (xargs :stobjs (fat32-in-memory)
                  :verify-guards nil))
  (if
      (atom clusterchain)
      nil
    (let*
        ((cluster-size (* (bpb_bytspersec fat32-in-memory)
                          (bpb_secperclus fat32-in-memory)))
         (masked-current-cluster (car clusterchain))
         (data-region-index (* (nfix (- masked-current-cluster 2))
                               cluster-size)))
      (append
       (rev (get-dir-ent-helper fat32-in-memory data-region-index
                                (min file-size cluster-size)))
       (get-clusterchain-contents
        fat32-in-memory (cdr clusterchain)
        (nfix (- file-size cluster-size)))))))

(defun get-dir-ent-matching-name
    (fat32-in-memory data-region-index dir-size str)
  (declare (xargs :stobjs (fat32-in-memory)
                  :verify-guards nil
                  :measure (acl2-count dir-size)))
  (if
      (zp dir-size)
      nil
    (let*
        ((dir-ent (get-dir-ent fat32-in-memory data-region-index)))
      (if
          (equal str (nats=>string (subseq dir-ent 0 11)))
          dir-ent
        (get-dir-ent-matching-name
         fat32-in-memory
         (+ data-region-index *ms-dir-ent-length*)
         (nfix (- dir-size *ms-dir-ent-length*))
         str)))))

(defun
  get-dir-ent-contents
  (fat32-in-memory dir-ent)
  (declare (xargs :stobjs (fat32-in-memory)
                  :verify-guards nil))
  (b*
   ((first-cluster (dir-ent-first-cluster dir-ent))
    (file-size (dir-ent-file-size dir-ent))
    ((mv clusterchain error-code)
     (get-clusterchain
      fat32-in-memory (fat32-entry-mask first-cluster) file-size)))
   (if (equal error-code 0)
       (mv (get-clusterchain-contents
            fat32-in-memory clusterchain file-size)
           0)
     (mv "" error-code))))

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
     ((mv & val state)
      (getenv$ "CAT_INPUT" state))
     ((mv contents error-code)
      (get-dir-ent-contents
       fat32-in-memory
       (get-dir-ent-matching-name
        fat32-in-memory 0 1024 val)))
     (state
      (if
          (not (equal error-code 0))
          state
        (princ$
         (nats=>string contents)
         channel state)))
     (state
      (close-output-channel channel state)))
  (mv fat32-in-memory state))
