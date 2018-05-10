(include-book "../file-system-m2")

(defun
  get-dir-ent-first-cluster-contents
  (fat32-in-memory data-region-index)
  (declare (xargs :stobjs (fat32-in-memory)
                  :verify-guards nil))
  (let*
   ((dir-ent (get-dir-ent fat32-in-memory data-region-index))
    (first-cluster (combine32u (nth 21 dir-ent)
                               (nth 20 dir-ent)
                               (nth 27 dir-ent)
                               (nth 26 dir-ent)))
    (cluster-size (* (bpb_bytspersec fat32-in-memory)
                     (bpb_secperclus fat32-in-memory)))
    (file-size (combine32u (nth 31 dir-ent)
                           (nth 30 dir-ent)
                           (nth 29 dir-ent)
                           (nth 28 dir-ent)))
    (data-region-index (* (nfix (- first-cluster 2))
                          cluster-size)))
   (nats=>string
    (rev (get-dir-ent-helper fat32-in-memory data-region-index
                             (min file-size cluster-size))))))

(time$ (slurp-disk-image
        fat32-in-memory "disk1.raw" state))

(mv-let
  (channel state)
  (open-output-channel "output.txt" :character state)
  (pprogn
   (princ$
    (get-dir-ent-first-cluster-contents
     fat32-in-memory 0)
    channel state)
   (close-output-channel channel state)))
