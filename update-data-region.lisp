(in-package "ACL2")

;  update-data-region.lisp                              Mihir Mehta

; This is optimised code for updating the data region from a string, along with
; necessary basic definitions.

(include-book "fat32-in-memory")
(include-book "cluster-listp")
(include-book "flatten-lemmas")

;; These are some rules from other books which are either interacting badly
;; with the theory I've built up so far, or else causing a lot of unnecessary
;; frames and tries.
(local
 (in-theory (disable take-of-too-many take-of-len-free make-list-ac-removal
                     revappend-removal str::hex-digit-listp-of-cons
                     loghead logtail)))

(local
 (in-theory (disable nth update-nth floor mod true-listp)))

;; At some point, the following theorem has to be moved to
;; file-system-lemmas.lisp.
(defthmd take-of-nthcdr
  (equal (take n1 (nthcdr n2 l))
         (nthcdr n2 (take (+ (nfix n1) (nfix n2)) l))))

(local (include-book "arithmetic-3/top" :dir :system))

(defund
  cluster-size (fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (fat32-in-memoryp fat32-in-memory)))
  (* (bpb_secperclus fat32-in-memory)
     (bpb_bytspersec fat32-in-memory)))

(defthm natp-of-cluster-size
  (implies (fat32-in-memoryp fat32-in-memory)
           (natp (cluster-size fat32-in-memory)))
  :hints (("goal" :in-theory (enable fat32-in-memoryp cluster-size
                                     bpb_bytspersec bpb_secperclus)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (fat32-in-memoryp fat32-in-memory)
                           (integerp (cluster-size fat32-in-memory))))
                 (:rewrite
                  :corollary
                  (implies (fat32-in-memoryp fat32-in-memory)
                           (rationalp (cluster-size fat32-in-memory))))
                 (:linear
                  :corollary
                  (implies (fat32-in-memoryp fat32-in-memory)
                           (<= 0 (cluster-size fat32-in-memory))))
                 (:rewrite
                  :corollary
                  (implies (fat32-in-memoryp fat32-in-memory)
                           (equal
                           (nfix (cluster-size fat32-in-memory))
                           (cluster-size fat32-in-memory))))))

(defthm
  cluster-size-of-update-nth
  (implies
   (not (member-equal key
                      (list *bpb_secperclus* *bpb_bytspersec*)))
   (equal (cluster-size (update-nth key val fat32-in-memory))
          (cluster-size fat32-in-memory)))
  :hints (("goal" :in-theory (enable cluster-size))))

(defthm
  cluster-size-of-resize-data-region
  (equal (cluster-size (resize-data-region i fat32-in-memory))
         (cluster-size fat32-in-memory))
  :hints (("goal" :in-theory (enable resize-data-region))))

(defthm
  cluster-size-of-resize-fat
  (equal (cluster-size (resize-fat i fat32-in-memory))
         (cluster-size fat32-in-memory))
  :hints (("goal" :in-theory (enable resize-fat))))

(defund
  count-of-clusters (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (and (fat32-in-memoryp fat32-in-memory)
                      (>= (bpb_secperclus fat32-in-memory) 1))
          :guard-debug t))
  (floor (- (bpb_totsec32 fat32-in-memory)
            (+ (bpb_rsvdseccnt fat32-in-memory)
               (* (bpb_numfats fat32-in-memory)
                  (bpb_fatsz32 fat32-in-memory))))
         (bpb_secperclus fat32-in-memory)))

(defthm
  count-of-clusters-of-resize-fat
  (equal (count-of-clusters (resize-fat i fat32-in-memory))
         (count-of-clusters fat32-in-memory))
  :hints (("goal" :in-theory (enable count-of-clusters))))

(defthm
  count-of-clusters-of-update-nth
  (implies
   (not (member key
                (list *bpb_totsec32*
                      *bpb_rsvdseccnt* *bpb_numfats*
                      *bpb_fatsz32* *bpb_secperclus*)))
   (equal
    (count-of-clusters (update-nth key val fat32-in-memory))
    (count-of-clusters fat32-in-memory)))
  :hints (("goal" :in-theory (enable count-of-clusters))))

(defthm
  count-of-clusters-of-update-data-regioni
  (equal
   (count-of-clusters (update-data-regioni i v fat32-in-memory))
   (count-of-clusters fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni))))

(defun
  stobj-cluster-listp-helper
  (fat32-in-memory n)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (fat32-in-memoryp fat32-in-memory)
                (natp n)
                (<= n (data-region-length fat32-in-memory)))
    :guard-hints
    (("goal" :in-theory (disable fat32-in-memoryp)))))
  (or
   (zp n)
   (let
    ((current-cluster
      (data-regioni (- (data-region-length fat32-in-memory)
                       n)
                    fat32-in-memory)))
    (and
     (cluster-p current-cluster
                (cluster-size fat32-in-memory))
     (stobj-cluster-listp-helper fat32-in-memory (- n 1))))))

(defthm
  stobj-cluster-listp-helper-correctness-1
  (implies
   (and (natp n)
        (<= n (data-region-length fat32-in-memory)))
   (equal
    (stobj-cluster-listp-helper fat32-in-memory n)
    (cluster-listp
     (nthcdr
      (- (data-region-length fat32-in-memory)
         n)
      (true-list-fix (nth *data-regioni* fat32-in-memory)))
     (cluster-size fat32-in-memory))))
  :hints
  (("goal"
    :in-theory (enable data-regioni data-region-length
                       nth nthcdr-when->=-n-len-l)
    :induct (stobj-cluster-listp-helper fat32-in-memory n)
    :expand
    ((true-list-fix (nth *data-regioni* fat32-in-memory))
     (cluster-listp
      (nthcdr
       (+ (- n)
          (len (nth *data-regioni* fat32-in-memory)))
       (true-list-fix (nth *data-regioni* fat32-in-memory)))
      (cluster-size fat32-in-memory))
     (cluster-listp
      (nthcdr
       (+ (- n)
          (len (cdr (nth *data-regioni* fat32-in-memory))))
       (true-list-fix
        (cdr (nth *data-regioni* fat32-in-memory))))
      (cluster-size fat32-in-memory)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (natp n)
          (<= n (data-region-length fat32-in-memory))
          (fat32-in-memoryp fat32-in-memory))
     (equal (stobj-cluster-listp-helper fat32-in-memory n)
            (cluster-listp
             (nthcdr (- (data-region-length fat32-in-memory)
                        n)
                     (nth *data-regioni* fat32-in-memory))
             (cluster-size fat32-in-memory))))
    :hints (("goal" :in-theory (enable fat32-in-memoryp))))))

(defund
  fat-entry-count (fat32-in-memory)
  (declare (xargs :guard (fat32-in-memoryp fat32-in-memory)
                  :stobjs fat32-in-memory))
  (floor (* (bpb_fatsz32 fat32-in-memory)
            (bpb_bytspersec fat32-in-memory))
         4))

(defthm
  fat-entry-count-of-update-nth
  (implies
   (not (member-equal key
                      (list *bpb_fatsz32* *bpb_bytspersec*)))
   (equal (fat-entry-count (update-nth key val fat32-in-memory))
          (fat-entry-count fat32-in-memory)))
  :hints
  (("goal" :in-theory (enable fat-entry-count
                              bpb_bytspersec bpb_fatsz32))))

(defthm
  fat-entry-count-of-resize-data-region
  (equal (fat-entry-count
          (resize-data-region i fat32-in-memory))
         (fat-entry-count fat32-in-memory))
  :hints (("goal" :in-theory (enable resize-data-region))))

(defthm
  fat32-entry-p-of-bpb_rootclus-when-fat32-in-memoryp
  (implies (fat32-in-memoryp fat32-in-memory)
           (fat32-entry-p (bpb_rootclus fat32-in-memory)))
  :hints (("goal" :in-theory (enable fat32-entry-p))))

(encapsulate
  ()

  (local
   (defthm
     lofat-fs-p-guard-lemma-2
     (implies (and
               (fat32-in-memoryp fat32-in-memory)
               (>= (bpb_bytspersec fat32-in-memory) *ms-min-bytes-per-sector*)
               (>= (bpb_secperclus fat32-in-memory) 1))
              (not (equal (cluster-size fat32-in-memory)
                          0)))
     :hints (("goal" :in-theory (enable cluster-size)))))

  (defund lofat-fs-p (fat32-in-memory)
    (declare (xargs :stobjs fat32-in-memory :guard t))
    (and (fat32-in-memoryp fat32-in-memory)
         (>= (bpb_bytspersec fat32-in-memory)
             *ms-min-bytes-per-sector*)
         (>= (bpb_secperclus fat32-in-memory) 1)
         (>= (count-of-clusters fat32-in-memory)
             *ms-min-count-of-clusters*)
         (<= (+ *ms-first-data-cluster*
                (count-of-clusters fat32-in-memory))
             *ms-bad-cluster*)
         (>= (bpb_rsvdseccnt fat32-in-memory) 1)
         (>= (bpb_numfats fat32-in-memory) 1)
         (>= (bpb_fatsz32 fat32-in-memory) 1)
         ;; These constraints on bpb_rootclus aren't in the spec, but they are
         ;; clearly implied
         (>= (fat32-entry-mask (bpb_rootclus fat32-in-memory))
             *ms-first-data-cluster*)
         (< (fat32-entry-mask (bpb_rootclus fat32-in-memory))
            (+ *ms-first-data-cluster*
               (count-of-clusters fat32-in-memory)))
         (<= (+ (count-of-clusters fat32-in-memory)
                *ms-first-data-cluster*)
             (fat-entry-count fat32-in-memory))
         ;; The spec (page 9) imposes both hard and soft limits on the legal
         ;; values of the cluster size, limiting it to being a power of 2 from
         ;; 512 through 32768. The following two clauses, however, are less
         ;; stringent - they allow values of cluster size which are powers of 2
         ;; going up to 2097152, although the lower bound of 512 is retained
         ;; thanks to the lower bounds on bpb_bytspersec and bpb_secperclus
         ;; above.
         (equal (mod (cluster-size fat32-in-memory)
                     *ms-dir-ent-length*)
                0)
         (equal (mod *ms-max-dir-size*
                     (cluster-size fat32-in-memory))
                0)
         ;; Some array properties in addition to the scalar properties
         (stobj-cluster-listp-helper
          fat32-in-memory
          (data-region-length fat32-in-memory))
         (equal (data-region-length fat32-in-memory)
                (count-of-clusters fat32-in-memory))
         (equal (* 4 (fat-length fat32-in-memory))
                (* (bpb_fatsz32 fat32-in-memory)
                   (bpb_bytspersec fat32-in-memory)))))

  (local
   (defthm
     lofat-fs-p-guard-lemma-3
     (implies (and (fat32-in-memoryp fat32-in-memory)
                   (< 0 (bpb_bytspersec fat32-in-memory)))
              (< (fat-entry-count fat32-in-memory)
                 (ash 1 48)))
     :rule-classes ()
     :hints (("goal"
              :do-not-induct t
              :in-theory
              (enable fat32-in-memoryp fat-entry-count
                      bpb_bytspersec bpb_fatsz32)))))

  (defthm
    lofat-fs-p-correctness-1
    (implies (lofat-fs-p fat32-in-memory)
             (and (fat32-in-memoryp fat32-in-memory)
                  (integerp (cluster-size fat32-in-memory))
                  (>= (cluster-size fat32-in-memory)
                      *ms-min-bytes-per-sector*)
                  (>= (count-of-clusters fat32-in-memory)
                      *ms-min-count-of-clusters*)
                  (equal (mod (cluster-size fat32-in-memory)
                              *ms-dir-ent-length*)
                         0)
                  (equal (mod *ms-max-dir-size*
                              (cluster-size fat32-in-memory))
                         0)
                  (<= (+ *ms-first-data-cluster*
                         (count-of-clusters fat32-in-memory))
                      *ms-bad-cluster*)
                  (>= (bpb_secperclus fat32-in-memory) 1)
                  (>= (bpb_rsvdseccnt fat32-in-memory) 1)
                  (>= (bpb_numfats fat32-in-memory) 1)
                  (>= (bpb_fatsz32 fat32-in-memory) 1)
                  (>= (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                      *ms-first-data-cluster*)
                  ;; There was a bug here, which we fixed - previously,
                  ;; bpb_rootclus was only allowed to point at clusters up to
                  ;; but not including (count-of-clusters fat32-in-memory),
                  ;; which causes two clusters (up to but not including
                  ;; (+ 2 (count-of-clusters fat32-in-memory))) to be left out.
                  (< (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                     (+ *ms-first-data-cluster*
                        (count-of-clusters fat32-in-memory)))
                  (>= (bpb_bytspersec fat32-in-memory)
                      *ms-min-bytes-per-sector*)
                  (equal (data-region-length fat32-in-memory)
                         (count-of-clusters fat32-in-memory))
                  (<= (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*)
                      (fat-length fat32-in-memory))
                  (equal (fat-length fat32-in-memory)
                         (fat-entry-count fat32-in-memory))
                  ;; This also represents a fixed bug - earlier, we were going
                  ;; to return an error for all filesystems with fat-length
                  ;; greater than *ms-bad-cluster*. The upper limit is actually
                  ;; (ash 1 28) - only slightly greater than *ms-bad-cluster* -
                  ;; derived from bpb_fatsz32 being up to (ash 1 16) and
                  ;; bpb_bytspersec being up to 4096.
                  (< (fat-entry-count fat32-in-memory)
                     (ash 1 48))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (lofat-fs-p cluster-size fat-entry-count)
       (fat32-in-memoryp))
      :use
      lofat-fs-p-guard-lemma-3))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (lofat-fs-p fat32-in-memory)
               (and (fat32-in-memoryp fat32-in-memory)
                    (integerp (cluster-size fat32-in-memory))
                    (equal (mod (cluster-size fat32-in-memory)
                                *ms-dir-ent-length*)
                           0)
                    (equal (mod *ms-max-dir-size*
                                (cluster-size fat32-in-memory))
                           0)
                    (equal (data-region-length fat32-in-memory)
                           (count-of-clusters fat32-in-memory))
                    (equal (fat-length fat32-in-memory)
                           (fat-entry-count fat32-in-memory)))))
     (:forward-chaining
      :corollary
      (implies (lofat-fs-p fat32-in-memory)
               (integerp (cluster-size fat32-in-memory))))
     (:linear
      :corollary
      (implies
       (lofat-fs-p fat32-in-memory)
       (and (>= (cluster-size fat32-in-memory)
                *ms-min-bytes-per-sector*)
            (>= (count-of-clusters fat32-in-memory)
                *ms-min-count-of-clusters*)
            (<= (+ *ms-first-data-cluster*
                   (count-of-clusters fat32-in-memory))
                *ms-bad-cluster*)
            (>= (bpb_secperclus fat32-in-memory) 1)
            (>= (bpb_rsvdseccnt fat32-in-memory) 1)
            (>= (bpb_numfats fat32-in-memory) 1)
            (>= (bpb_fatsz32 fat32-in-memory) 1)
            (>= (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                *ms-first-data-cluster*)
            (< (fat32-entry-mask (bpb_rootclus fat32-in-memory))
               (+ *ms-first-data-cluster*
                  (count-of-clusters fat32-in-memory)))
            (>= (bpb_bytspersec fat32-in-memory)
                *ms-min-bytes-per-sector*)
            (>= (* (cluster-size fat32-in-memory)
                   (count-of-clusters fat32-in-memory))
                (* *ms-min-bytes-per-sector*
                   *ms-min-count-of-clusters*))
            (<= (+ (count-of-clusters fat32-in-memory)
                   *ms-first-data-cluster*)
                (fat-entry-count fat32-in-memory))
            (< (fat-entry-count fat32-in-memory)
               (ash 1 48))))))))

(defthm
  fati-when-lofat-fs-p
  (implies (and (lofat-fs-p fat32-in-memory)
                (< (nfix i) (fat-length fat32-in-memory)))
           (fat32-entry-p (fati i fat32-in-memory)))
  :hints (("goal" :in-theory (enable lofat-fs-p
                                     fat32-in-memoryp fati fat-length))))

(defthm
  cluster-size-of-update-fati
  (equal (cluster-size (update-fati i v fat32-in-memory))
         (cluster-size fat32-in-memory))
  :hints
  (("goal" :in-theory (enable cluster-size update-fati))))

(defthm
  count-of-clusters-of-update-fati
  (equal (count-of-clusters (update-fati i v fat32-in-memory))
         (count-of-clusters fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable count-of-clusters update-fati bpb_totsec32))))

;; Before disabling, this function used to cause 11030904 frames and 95410
;; tries in this book; after disabling those numbers are 4919970 and 33324
;; respectively.
(defthmd
  lofat-fs-p-of-update-fati
  (implies (and (lofat-fs-p fat32-in-memory)
                (< i (fat-length fat32-in-memory)))
           (equal
            (lofat-fs-p
             (update-fati i v fat32-in-memory))
            (fat32-entry-p v)))
  :hints
  (("goal"
    :in-theory (e/d (lofat-fs-p
                     fat32-in-memoryp
                     update-fati fat-length count-of-clusters
                     data-region-length)
                    (cluster-size-of-update-fati))
    :use cluster-size-of-update-fati)))

(defthm
  data-regioni-when-lofat-fs-p
  (implies (and (lofat-fs-p fat32-in-memory)
                (< (nfix i)
                   (data-region-length fat32-in-memory)))
           (cluster-p (data-regioni i fat32-in-memory)
                      (cluster-size fat32-in-memory)))
  :hints
  (("goal" :in-theory (e/d (lofat-fs-p
                            fat32-in-memoryp
                            data-regioni data-region-length)
                           (unsigned-byte-p))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (< (nfix i)
             (data-region-length fat32-in-memory)))
     (and
      (stringp (data-regioni i fat32-in-memory))
      (equal (len (explode (data-regioni i fat32-in-memory)))
             (cluster-size fat32-in-memory))))
    :hints (("goal" :in-theory (enable cluster-p))))))

(defthm
  cluster-size-of-update-data-regioni
  (equal
   (cluster-size (update-data-regioni i v fat32-in-memory))
   (cluster-size fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable cluster-size update-data-regioni))))

(defthm
  lofat-fs-p-of-update-data-regioni
  (implies (and (lofat-fs-p fat32-in-memory)
                (< i (data-region-length fat32-in-memory)))
           (equal
            (lofat-fs-p
             (update-data-regioni i v fat32-in-memory))
            (cluster-p v (cluster-size fat32-in-memory))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (lofat-fs-p
                     fat32-in-memoryp
                     update-data-regioni
                     data-region-length count-of-clusters
                     fat-length)
                    (cluster-size-of-update-data-regioni))
    :use
    cluster-size-of-update-data-regioni)))

(defun
    update-data-region
    (fat32-in-memory str len)
  (declare
   (xargs
    :guard (and (stringp str)
                (natp len)
                (<= len
                    (data-region-length fat32-in-memory))
                (>= (length str)
                    (* (- (data-region-length fat32-in-memory)
                          len)
                       (cluster-size fat32-in-memory)))
                (<= len
                    (- *ms-bad-cluster*
                       *ms-first-data-cluster*)))
    :stobjs fat32-in-memory
    :measure (nfix len)))
  (b*
      ((len (the (unsigned-byte 28) len))
       ((when (zp len)) (mv fat32-in-memory 0))
       (cluster-size (cluster-size fat32-in-memory))
       (index (- (data-region-length fat32-in-memory)
                 len)))
    (if
        (<= (* (+ index 1) cluster-size)
            (length str))
        (b*
            ((current-cluster (subseq str (* index cluster-size)
                                      (* (+ index 1) cluster-size)))
             (fat32-in-memory
              (update-data-regioni
               index current-cluster fat32-in-memory)))
          (update-data-region
           fat32-in-memory
           str (the (unsigned-byte 28) (- len 1))))
      (b*
          ((current-cluster (subseq str (* index cluster-size) nil))
           (fat32-in-memory
            (update-data-regioni
             index current-cluster fat32-in-memory)))
        (mv fat32-in-memory *eio*)))))

(defun
    update-data-region-from-disk-image
    (fat32-in-memory len state tmp_init image-path)
  (declare
   (xargs
    :guard
    (and (natp tmp_init)
         (stringp image-path)
         (stringp (read-file-into-string image-path))
         (natp len)
         (<= len
             (data-region-length fat32-in-memory))
         (>= (length (read-file-into-string image-path))
             (+ tmp_init
                (* (- (data-region-length fat32-in-memory)
                      len)
                   (cluster-size fat32-in-memory))))
         (<= len
             (- *ms-bad-cluster*
                *ms-first-data-cluster*)))
    :stobjs (fat32-in-memory state)
    :measure (nfix len)))
  (b*
      ((len (the (unsigned-byte 28) len))
       ((when (zp len)) (mv fat32-in-memory 0))
       (cluster-size (cluster-size fat32-in-memory))
       (index (- (data-region-length fat32-in-memory)
                 len))
       (fat32-in-memory
        (update-data-regioni
         index
         (read-file-into-string
          image-path
          :start (+ tmp_init (* index cluster-size))
          :bytes cluster-size)
         fat32-in-memory)))
    (if (equal (length (data-regioni index fat32-in-memory))
               cluster-size)
        (update-data-region-from-disk-image
         fat32-in-memory
         (the (unsigned-byte 28) (- len 1))
         state tmp_init image-path)
      (mv fat32-in-memory *eio*))))

(defthm
  update-data-region-from-disk-image-correctness-1
  (implies
   (and (natp tmp_init)
        (<= len
            (data-region-length fat32-in-memory))
        (>= (length (read-file-into-string image-path))
            (+ tmp_init
               (* (- (data-region-length fat32-in-memory)
                     len)
                  (cluster-size fat32-in-memory))))
        (not (zp (cluster-size fat32-in-memory))))
   (equal (update-data-region-from-disk-image fat32-in-memory
                                              len state tmp_init image-path)
          (update-data-region fat32-in-memory
                              (subseq (read-file-into-string image-path)
                                      tmp_init nil)
                              len)))
  :hints
  (("goal"
    :induct (update-data-region-from-disk-image fat32-in-memory
                                                len state tmp_init image-path)
    :in-theory (e/d (take-of-nthcdr nthcdr-when->=-n-len-l
                                    by-slice-you-mean-the-whole-cake-2)
                    nil)
    :expand (:free (fat32-in-memory str)
                   (update-data-region fat32-in-memory str len)))))

(defthm
  fat32-in-memoryp-of-update-data-regioni
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal
    (fat32-in-memoryp (update-data-regioni i v fat32-in-memory))
    (and (stringp v)
         (<= (nfix i)
             (data-region-length fat32-in-memory)))))
  :hints
  (("goal"
    :in-theory (enable fat32-in-memoryp update-data-regioni
                       data-region-length))))

(defthm
  fat32-in-memoryp-of-update-data-region
  (implies (and (fat32-in-memoryp fat32-in-memory)
                (stringp str))
           (fat32-in-memoryp
            (mv-nth 0
                    (update-data-region fat32-in-memory str len)))))

(defthm
  bpb_bytspersec-of-update-data-region
  (equal
   (bpb_bytspersec (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_bytspersec fat32-in-memory)))

(defthm
  bpb_secperclus-of-update-data-region
  (equal
   (bpb_secperclus (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_secperclus fat32-in-memory)))

(defthm
  bpb_rsvdseccnt-of-update-data-region
  (equal
   (bpb_rsvdseccnt (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_rsvdseccnt fat32-in-memory)))

(defthm
  bpb_totsec32-of-update-data-region
  (equal
   (bpb_totsec32 (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_totsec32 fat32-in-memory)))

(defthm
  bpb_fatsz32-of-update-data-region
  (equal
   (bpb_fatsz32 (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_fatsz32 fat32-in-memory)))

(defthm
  bpb_numfats-of-update-data-region
  (equal
   (bpb_numfats (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_numfats fat32-in-memory)))

(defthm
  bpb_rootclus-of-update-data-region
  (equal
   (bpb_rootclus (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_rootclus fat32-in-memory)))

(defthm
  fat-length-of-update-data-region
  (equal
   (fat-length (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (fat-length fat32-in-memory)))

(defthm
  fat-entry-count-of-update-data-region
  (equal (fat-entry-count
          (mv-nth 0 (update-data-region fat32-in-memory str len)))
         (fat-entry-count fat32-in-memory))
  :hints (("goal" :in-theory (enable fat-entry-count))))

(defthm
  data-region-length-of-update-data-region
  (implies
   (<= len
       (data-region-length fat32-in-memory))
   (equal (data-region-length
           (mv-nth 0 (update-data-region fat32-in-memory str len)))
          (data-region-length fat32-in-memory)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (<= len
         (data-region-length fat32-in-memory))
     (equal
      (consp (nth *data-regioni*
                  (mv-nth 0 (update-data-region fat32-in-memory str len))))
      (consp (nth *data-regioni* fat32-in-memory))))
    :hints
    (("goal"
      :in-theory (enable data-region-length)
      :do-not-induct t
      :expand
      ((len (nth *data-regioni*
                 (mv-nth 0 (update-data-region fat32-in-memory str len))))
       (len (nth *data-regioni* fat32-in-memory))))))))

(defthmd
  update-data-region-correctness-2
  (equal
   (update-data-region fat32-in-memory str len)
   (mv (mv-nth 0
               (update-data-region fat32-in-memory str len))
       (mv-nth 1
               (update-data-region fat32-in-memory str len)))))

(encapsulate
  ()

  (set-default-hints
   '((nonlinearp-default-hint stable-under-simplificationp
                              hist pspv)))

  (defthm update-data-region-alt-lemma-4
    (implies (and (not (zp len))
                  (< (len (explode str))
                     (+ (cluster-size fat32-in-memory)
                        (* -1 len (cluster-size fat32-in-memory))
                        (* (cluster-size fat32-in-memory)
                           (len (nth *data-regioni* fat32-in-memory)))))
                  (< 0 (cluster-size fat32-in-memory)))
             (< (len (explode str))
                (* (cluster-size fat32-in-memory)
                   (len (nth *data-regioni* fat32-in-memory)))))
    :rule-classes :linear)

  (defthm
    update-data-region-correctness-1
    (implies (and (natp len)
                  (<= len
                      (data-region-length fat32-in-memory))
                  (>= (length str)
                      (* (- (data-region-length fat32-in-memory)
                            len)
                         (cluster-size fat32-in-memory))))
             (iff
              (equal (mv-nth 1
                             (update-data-region fat32-in-memory str len))
                     0)
              (>= (length str)
                  (* (data-region-length fat32-in-memory)
                     (cluster-size fat32-in-memory)))))))

(encapsulate
  ()
  
  (local
   (defthm
     update-data-region-alt-lemma-1
     (equal (update-nth *data-regioni* val
                        (update-data-regioni i v fat32-in-memory))
            (update-nth *data-regioni* val fat32-in-memory))
     :hints (("goal" :in-theory (enable update-data-regioni)))))

  (local
   (defthm
     update-data-region-alt-lemma-2
     (implies (fat32-in-memoryp fat32-in-memory)
              (and
               (true-listp (nth *data-regioni* fat32-in-memory))
               (equal
                (update-nth *data-regioni*
                            (nth *data-regioni* fat32-in-memory)
                            fat32-in-memory)
                fat32-in-memory)))
     :hints (("goal" :in-theory (enable fat32-in-memoryp)))))

  (local
   (defthm
     update-data-region-alt-lemma-3
     (equal
      (nth *data-regioni*
           (update-data-regioni i v fat32-in-memory))
      (update-nth i v
                  (nth *data-regioni* fat32-in-memory)))
     :hints (("goal" :in-theory (enable update-data-regioni)) )))

  (defthmd
    update-data-region-alt
    (implies
     (and (stringp str)
          (natp len)
          (>= (data-region-length fat32-in-memory)
              len)
          (fat32-in-memoryp fat32-in-memory)
          (< 0 (cluster-size fat32-in-memory))
          (>= (length str)
              (* (data-region-length fat32-in-memory)
                 (cluster-size fat32-in-memory))))
     (equal
      (update-data-region fat32-in-memory str len)
      (mv
       (update-nth
        *data-regioni*
        (append
         (take (- (data-region-length fat32-in-memory)
                  len)
               (nth *data-regioni* fat32-in-memory))
         (make-clusters
          (subseq str
                  (* (- (data-region-length fat32-in-memory)
                        len)
                     (cluster-size fat32-in-memory))
                  (* (data-region-length fat32-in-memory)
                     (cluster-size fat32-in-memory)))
          (cluster-size fat32-in-memory)))
        fat32-in-memory)
       0)))
    :hints
    (("goal"
      :in-theory
      (e/d (data-region-length make-clusters
                               remember-that-time-with-update-nth
                               by-slice-you-mean-the-whole-cake-2
                               take-of-nthcdr)
           (append take take-redefinition))
      :induct (update-data-region fat32-in-memory str len)))))

(defthm
  cluster-listp-after-update-data-region
  (implies
   (and
    (fat32-in-memoryp fat32-in-memory)
    (stringp str)
    (natp len)
    (>= (len (explode str))
        (* (cluster-size fat32-in-memory)
           (data-region-length fat32-in-memory)))
    (< 0 (cluster-size fat32-in-memory))
    (cluster-listp (take (- (data-region-length fat32-in-memory)
                            len)
                         (nth *data-regioni* fat32-in-memory))
                   (cluster-size fat32-in-memory))
    (>= (data-region-length fat32-in-memory)
        len))
   (cluster-listp
    (nth *data-regioni*
         (mv-nth 0
                 (update-data-region fat32-in-memory str len)))
    (cluster-size fat32-in-memory)))
  :hints (("goal" :use update-data-region-alt))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (fat32-in-memoryp fat32-in-memory)
          (stringp str)
          (natp len)
          (>= (len (explode str))
              (* (cluster-size fat32-in-memory)
                 (data-region-length fat32-in-memory)))
          (< 0 (cluster-size fat32-in-memory))
          (cluster-listp
           (take (- (data-region-length fat32-in-memory)
                    len)
                 (nth *data-regioni* fat32-in-memory))
           cluster-size)
          (>= (data-region-length fat32-in-memory)
              len)
          (equal cluster-size
                 (cluster-size fat32-in-memory)))
     (cluster-listp
      (nth
       *data-regioni*
       (mv-nth 0
               (update-data-region fat32-in-memory str len)))
      cluster-size))
    :hints
    (("goal"
      :in-theory (e/d (fat32-in-memoryp)
                      (fat32-in-memoryp-of-update-data-region))
      :use fat32-in-memoryp-of-update-data-region
      :do-not-induct t)))))
