(in-package "ACL2")

;  lofat.lisp                                           Mihir Mehta

; This is a stobj model of the FAT32 filesystem.

(include-book "hifat-to-lofat-inversion")

;; These are some rules from other books which are either interacting badly
;; with the theory I've built up so far, or else causing a lot of unnecessary
;; frames and tries.
(local
 (in-theory (disable take-of-too-many make-list-ac-removal
                     revappend-removal str::hex-digit-listp-of-cons
                     loghead logtail)))

(local
 (in-theory (disable nth update-nth floor mod true-listp)))

(defconst *initialbytcnt* 16)

(defund get-initial-bytes (str)
  (declare (xargs :guard (and (stringp str)
                              (>= (length str) *initialbytcnt*))))
  (string=>nats (subseq str 0 *initialbytcnt*)))

(defthm
  len-of-get-initial-bytes
  (implies (stringp str)
           (equal (len (get-initial-bytes str))
                  *initialbytcnt*))
  :hints (("goal" :in-theory (enable get-initial-bytes))))

(defthm
  unsigned-byte-listp-of-get-initial-bytes
  (unsigned-byte-listp 8 (get-initial-bytes str))
  :hints (("goal" :in-theory (enable get-initial-bytes))))

(defthm
  nth-of-get-initial-bytes
  (equal (integerp (nth n (get-initial-bytes str)))
         (< (nfix n)
            (len (get-initial-bytes str))))
  :hints (("goal" :in-theory (enable get-initial-bytes
                                     consp-of-string=>nats)))
  :rule-classes
  (:rewrite
   (:linear :corollary (implies (< (nfix n)
                                   (len (get-initial-bytes str)))
                                (<= 0 (nth n (get-initial-bytes str))))
            :hints (("goal" :in-theory (enable get-initial-bytes))))
   (:type-prescription
    :corollary (or (integerp (nth n (get-initial-bytes str)))
                   (equal (nth n (get-initial-bytes str))
                          nil))
    :hints (("goal" :in-theory (enable get-initial-bytes))))))

(defund
  get-remaining-rsvdbyts (str)
  (declare
   (xargs
    :guard
    (and
     (stringp str)
     (>= (length str) *initialbytcnt*)
     (<= (* (combine16u (nth 12 (get-initial-bytes str))
                        (nth 11 (get-initial-bytes str)))
            (combine16u (nth 15 (get-initial-bytes str))
                        (nth 14 (get-initial-bytes str))))
         (length str))
     (<= *initialbytcnt*
         (* (combine16u (nth 12 (get-initial-bytes str))
                        (nth 11 (get-initial-bytes str)))
            (combine16u (nth 15 (get-initial-bytes str))
                        (nth 14 (get-initial-bytes str))))))))
  (b*
      ((initial-bytes (get-initial-bytes str))
       (tmp_bytspersec (combine16u (nth (+ 11 1) initial-bytes)
                                   (nth (+ 11 0) initial-bytes)))
       (tmp_rsvdseccnt (combine16u (nth (+ 14 1) initial-bytes)
                                   (nth (+ 14 0) initial-bytes)))
       (tmp_rsvdbytcnt (* tmp_rsvdseccnt tmp_bytspersec)))
    (string=>nats (subseq str *initialbytcnt* tmp_rsvdbytcnt))))

(defthm
  len-of-get-remaining-rsvdbyts
  (implies
   (stringp str)
   (equal
    (len (get-remaining-rsvdbyts str))
    (nfix
     (-
      (* (combine16u (nth 12 (get-initial-bytes str))
                     (nth 11 (get-initial-bytes str)))
         (combine16u (nth 15 (get-initial-bytes str))
                     (nth 14 (get-initial-bytes str))))
      *initialbytcnt*))))
  :hints (("goal" :in-theory (enable get-remaining-rsvdbyts))))

(defthm
  consp-of-get-remaining-rsvdbyts
  (implies
   (stringp str)
   (iff
    (consp (get-remaining-rsvdbyts str))
    (not (zp
          (-
           (* (combine16u (nth 12 (get-initial-bytes str))
                          (nth 11 (get-initial-bytes str)))
              (combine16u (nth 15 (get-initial-bytes str))
                          (nth 14 (get-initial-bytes str))))
           *initialbytcnt*)))))
  :hints (("goal" :in-theory (disable
                              len-of-get-remaining-rsvdbyts)
           :use len-of-get-remaining-rsvdbyts
           :expand (len (get-remaining-rsvdbyts str)))))

(defthm
  unsigned-byte-listp-of-get-remaining-rsvdbyts
  (unsigned-byte-listp 8 (get-remaining-rsvdbyts str))
  :hints (("goal" :in-theory (enable get-remaining-rsvdbyts)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (integer-listp (get-remaining-rsvdbyts str))
    :hints
    (("goal"
      :in-theory
      (enable integer-listp-when-unsigned-byte-listp))))))

(defthm nth-of-get-remaining-rsvdbyts
  (and (equal (unsigned-byte-p 8 (nth n (get-remaining-rsvdbyts str)))
              (< (nfix n)
                 (len (get-remaining-rsvdbyts str))))
       (not (complex-rationalp (nth n (get-remaining-rsvdbyts str)))))
  :hints (("goal" :in-theory (enable get-remaining-rsvdbyts
                                     consp-of-string=>nats))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (local
   (defthm read-reserved-area-guard-lemma-2
     (implies (and (unsigned-byte-listp 8 l)
                   (natp n)
                   (< n (len l)))
              (rationalp (nth n l)))
     :hints (("Goal" :in-theory (enable nth)) )))

  (defund
      read-reserved-area (fat32-in-memory str)
    (declare
     (xargs
      :guard (and (stringp str)
                  (>= (length str) *initialbytcnt*)
                  (fat32-in-memoryp fat32-in-memory))
      :guard-hints
      (("goal"
        :in-theory (e/d (cluster-size) (unsigned-byte-p))))
      :stobjs (fat32-in-memory)))
    (b*
        (;; We want to do this unconditionally, in order to prove a strong linear
         ;; rule.
         (fat32-in-memory
          (update-bpb_secperclus 1
                                 fat32-in-memory))
         ;; This too needs to be unconditional.
         (fat32-in-memory
          (update-bpb_rsvdseccnt 1
                                 fat32-in-memory))
         ;; This too needs to be unconditional.
         (fat32-in-memory
          (update-bpb_numfats 1
                              fat32-in-memory))
         ;; I feel weird about stipulating this, but the FAT size has to be at
         ;; least 1 sector if we're going to have at least 65525 clusters of
         ;; data, as required by the FAT32 specification on page 15.
         (fat32-in-memory
          (update-bpb_fatsz32 1
                              fat32-in-memory))
         ;; This needs to be at least 512, per the spec.
         (fat32-in-memory
          (update-bpb_bytspersec 512
                                 fat32-in-memory))
         ((unless (mbt (and (stringp str) (>= (length str) *initialbytcnt*))))
          (mv fat32-in-memory *EIO*))
         (initial-bytes
          (get-initial-bytes str))
         (tmp_bytspersec (combine16u (nth (+ 11 1) initial-bytes)
                                     (nth (+ 11 0) initial-bytes)))
         (tmp_rsvdseccnt (combine16u (nth (+ 14 1) initial-bytes)
                                     (nth (+ 14 0) initial-bytes)))
         (tmp_rsvdbytcnt (* tmp_rsvdseccnt tmp_bytspersec))
         ((unless (and (>= tmp_bytspersec 512)
                       (>= tmp_rsvdseccnt 1)
                       (>= tmp_rsvdbytcnt *initialbytcnt*)
                       (>= (length str) tmp_rsvdbytcnt)))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bs_jmpboot (subseq initial-bytes 0 3) fat32-in-memory))
         (fat32-in-memory
          (update-bs_oemname (subseq initial-bytes 3 11) fat32-in-memory))
         (fat32-in-memory
          (update-bpb_bytspersec tmp_bytspersec fat32-in-memory))
         (tmp_secperclus (nth 13 initial-bytes))
         ;; this is actually a proxy for testing membership in the set {1, 2, 4,
         ;; 8, 16, 32, 64, 128}
         ((unless (>= tmp_secperclus 1))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bpb_secperclus tmp_secperclus
                                 fat32-in-memory))
         ((unless (and
                   (equal (mod (cluster-size fat32-in-memory)
                               *ms-dir-ent-length*)
                          0)
                   (equal (mod *ms-max-dir-size*
                               (cluster-size fat32-in-memory))
                          0)))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bpb_rsvdseccnt tmp_rsvdseccnt fat32-in-memory))
         (remaining-rsvdbyts
          (get-remaining-rsvdbyts str))
         (tmp_numfats (nth (- 16 *initialbytcnt*) remaining-rsvdbyts))
         ((unless (and (mbt (integerp tmp_numfats)) (>= tmp_numfats 1)))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bpb_numfats tmp_numfats
                              fat32-in-memory))
         (fat32-in-memory
          (update-bpb_rootentcnt
           (combine16u (nth (+ 17 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 17 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_totsec16
           (combine16u (nth (+ 19 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 19 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_media (nth (- 21 *initialbytcnt*) remaining-rsvdbyts)
                            fat32-in-memory))
         (fat32-in-memory
          (update-bpb_fatsz16
           (combine16u (nth (+ 22 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 22 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_secpertrk
           (combine16u (nth (+ 24 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 24 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_numheads
           (combine16u (nth (+ 26 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 26 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_hiddsec
           (combine32u (nth (+ 28 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 28 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 28 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 28 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_totsec32
           (combine32u (nth (+ 32 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 32 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 32 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 32 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         ;; fat32-specific stuff
         (tmp_fatsz32
          (combine32u (nth (+ 36 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                      (nth (+ 36 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                      (nth (+ 36 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                      (nth (+ 36 0 (- *initialbytcnt*)) remaining-rsvdbyts)))
         ((unless (>= tmp_fatsz32 1))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bpb_fatsz32
           tmp_fatsz32
           fat32-in-memory))
         ((unless
              (and
               (>= (count-of-clusters fat32-in-memory)
                   *ms-min-count-of-clusters*)
               (<= (+ (count-of-clusters fat32-in-memory)
                      *ms-first-data-cluster*)
                   (fat-entry-count fat32-in-memory))))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bpb_extflags
           (combine16u (nth (+ 40 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 40 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_fsver_minor (nth (- 42 *initialbytcnt*) remaining-rsvdbyts)
                                  fat32-in-memory))
         (fat32-in-memory
          (update-bpb_fsver_major (nth (- 43 *initialbytcnt*) remaining-rsvdbyts)
                                  fat32-in-memory))
         (fat32-in-memory
          (update-bpb_rootclus
           (combine32u (nth (+ 44 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 44 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 44 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 44 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         ((unless
              (and
               (>= (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                   *ms-first-data-cluster*)
               (< (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                  (+ *ms-first-data-cluster*
                     (count-of-clusters fat32-in-memory)))))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bpb_fsinfo
           (combine16u (nth (+ 48 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 48 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_bkbootsec
           (combine16u (nth (+ 50 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 50 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_reserved (subseq remaining-rsvdbyts
                                       (+ 52 (- *initialbytcnt*) 0)
                                       (+ 52 (- *initialbytcnt*) 12))
                               fat32-in-memory))
         (fat32-in-memory
          (update-bs_drvnum (nth (- 64 *initialbytcnt*) remaining-rsvdbyts)
                            fat32-in-memory))
         (fat32-in-memory
          (update-bs_reserved1 (nth (- 65 *initialbytcnt*) remaining-rsvdbyts)
                               fat32-in-memory))
         (fat32-in-memory
          (update-bs_bootsig (nth (- 66 *initialbytcnt*) remaining-rsvdbyts)
                             fat32-in-memory))
         (fat32-in-memory
          (update-bs_volid
           (combine32u (nth (+ 67 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 67 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 67 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 67 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bs_vollab (subseq remaining-rsvdbyts
                                    (+ 71 (- *initialbytcnt*) 0)
                                    (+ 71 (- *initialbytcnt*) 11))
                            fat32-in-memory))
         (fat32-in-memory
          (update-bs_filsystype (subseq remaining-rsvdbyts
                                        (+ 82 (- *initialbytcnt*) 0)
                                        (+ 82 (- *initialbytcnt*) 8))
                                fat32-in-memory)))
      (mv fat32-in-memory 0))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    read-reserved-area-correctness-1-lemma-1
    (implies
     (and (>= (length str) *initialbytcnt*)
          (>= (combine16u (nth 12 (get-initial-bytes (str-fix str)))
                          (nth 11 (get-initial-bytes (str-fix str))))
              512)
          (>= (combine16u (nth 15 (get-initial-bytes (str-fix str)))
                          (nth 14 (get-initial-bytes (str-fix str))))
              1))
     (equal
      (get-initial-bytes
       (implode (take (* (combine16u (nth 12 (get-initial-bytes str))
                                     (nth 11 (get-initial-bytes str)))
                         (combine16u (nth 15 (get-initial-bytes str))
                                     (nth 14 (get-initial-bytes str))))
                      (explode str))))
      (get-initial-bytes str)))
    :hints (("goal" :in-theory (enable get-initial-bytes))))

  (defthm
    read-reserved-area-correctness-1-lemma-2
    (implies
     (and (>= (length str) *initialbytcnt*)
          (>= (combine16u (nth 12 (get-initial-bytes (str-fix str)))
                          (nth 11 (get-initial-bytes (str-fix str))))
              512)
          (>= (combine16u (nth 15 (get-initial-bytes (str-fix str)))
                          (nth 14 (get-initial-bytes (str-fix str))))
              1)
          (<= (* (combine16u (nth 15 (get-initial-bytes (str-fix str)))
                             (nth 14 (get-initial-bytes (str-fix str))))
                 (combine16u (nth 12 (get-initial-bytes (str-fix str)))
                             (nth 11 (get-initial-bytes (str-fix str)))))
              (length (str-fix str))))
     (equal
      (get-remaining-rsvdbyts
       (implode (take (* (combine16u (nth 12 (get-initial-bytes str))
                                     (nth 11 (get-initial-bytes str)))
                         (combine16u (nth 15 (get-initial-bytes str))
                                     (nth 14 (get-initial-bytes str))))
                      (explode str))))
      (get-remaining-rsvdbyts str)))
    :hints (("goal" :in-theory (enable get-remaining-rsvdbyts take-of-nthcdr)
             :do-not-induct t))))

(defthm
  read-reserved-area-correctness-1
  (implies
   (and (>= (length str) *initialbytcnt*)
        (>= (combine16u (char-code (nth 12 (explode str)))
                        (char-code (nth 11 (explode str))))
            512)
        (>= (combine16u (char-code (nth 15 (explode str)))
                        (char-code (nth 14 (explode str))))
            1)
        (<= (* (combine16u (char-code (nth 15 (explode str)))
                           (char-code (nth 14 (explode str))))
               (combine16u (char-code (nth 12 (explode str)))
                           (char-code (nth 11 (explode str)))))
            (length str)))
   (equal
    (read-reserved-area fat32-in-memory
                        (subseq str 0
                                (* (combine16u (char-code (nth 15 (explode str)))
                                               (char-code (nth 14 (explode str))))
                                   (combine16u (char-code (nth 12 (explode str)))
                                               (char-code (nth 11 (explode str)))))))
    (read-reserved-area fat32-in-memory str)))
  :hints
  (("goal"
    :in-theory (e/d (read-reserved-area get-initial-bytes
                                        fat-entry-count count-of-clusters
                                        cluster-size take-of-nthcdr)
                    (read-reserved-area-correctness-1-lemma-1
                     read-reserved-area-correctness-1-lemma-2))
    :use (read-reserved-area-correctness-1-lemma-1
          read-reserved-area-correctness-1-lemma-2))))

(defun
  update-fat (fat32-in-memory str pos)
  (declare
   (xargs :guard (and (stringp str)
                      (unsigned-byte-p 48 pos)
                      (<= (* pos 4) (length str))
                      (equal (length str)
                             (* (fat-length fat32-in-memory) 4)))
          :guard-hints
          (("goal" :in-theory (e/d (fat-length update-fati)
                                   (fat32-in-memoryp))))
          :stobjs fat32-in-memory))
  (b*
      ((pos (the (unsigned-byte 48) pos)))
    (if
     (zp pos)
     fat32-in-memory
     (b*
         ((ch-word
           (the
            (unsigned-byte 32)
            (combine32u (char-code (char str
                                         (the (unsigned-byte 50)
                                              (- (* pos 4) 1))))
                        (char-code (char str
                                         (the (unsigned-byte 50)
                                              (- (* pos 4) 2))))
                        (char-code (char str
                                         (the (unsigned-byte 50)
                                              (- (* pos 4) 3))))
                        (char-code (char str
                                         (the (unsigned-byte 50)
                                              (- (* pos 4) 4)))))))
          (fat32-in-memory (update-fati (- pos 1)
                                        ch-word fat32-in-memory)))
       (update-fat fat32-in-memory str
                   (the (unsigned-byte 48) (- pos 1)))))))

(defthm
  nth-of-update-fat
  (implies (not (equal (nfix n) *fati*))
           (equal (nth n (update-fat fat32-in-memory str pos))
                  (nth n fat32-in-memory)))
  :hints (("goal" :in-theory (enable update-fat update-fati))))

(defthm bpb_secperclus-of-update-fat
  (equal (bpb_secperclus
          (update-fat fat32-in-memory str pos))
         (bpb_secperclus fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_secperclus)) ))

(defthm bpb_fatsz32-of-update-fat
  (equal (bpb_fatsz32
          (update-fat fat32-in-memory str pos))
         (bpb_fatsz32 fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_fatsz32)) ))

(defthm bpb_numfats-of-update-fat
  (equal (bpb_numfats
          (update-fat fat32-in-memory str pos))
         (bpb_numfats fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_numfats)) ))

(defthm bpb_rsvdseccnt-of-update-fat
  (equal (bpb_rsvdseccnt
          (update-fat fat32-in-memory str pos))
         (bpb_rsvdseccnt fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_rsvdseccnt)) ))

(defthm bpb_totsec32-of-update-fat
  (equal (bpb_totsec32
          (update-fat fat32-in-memory str pos))
         (bpb_totsec32 fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_totsec32)) ))

(defthm bpb_bytspersec-of-update-fat
  (equal (bpb_bytspersec
          (update-fat fat32-in-memory str pos))
         (bpb_bytspersec fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_bytspersec)) ))

(defthm count-of-clusters-of-update-fat
  (equal (count-of-clusters
          (update-fat fat32-in-memory str pos))
         (count-of-clusters fat32-in-memory))
  :hints (("Goal" :in-theory (enable count-of-clusters)) ))

(defthm cluster-size-of-update-fat
  (equal (cluster-size
          (update-fat fat32-in-memory str pos))
         (cluster-size fat32-in-memory))
  :hints (("Goal" :in-theory (enable cluster-size)) ))

(defthm
  data-region-length-of-update-fat
  (equal (data-region-length
          (update-fat fat32-in-memory str pos))
         (data-region-length fat32-in-memory))
  :hints (("goal" :in-theory (enable data-region-length))))

(defthm fat32-in-memoryp-of-update-fat
  (implies (and (<= (* pos 4) (length str))
                (equal (length str)
                       (* (fat-length fat32-in-memory) 4))
                (fat32-in-memoryp fat32-in-memory))
           (fat32-in-memoryp (update-fat fat32-in-memory str pos))))

(defthm
  fat-entry-count-of-update-fat
  (equal (fat-entry-count
          (update-fat fat32-in-memory str pos))
         (fat-entry-count fat32-in-memory))
  :hints (("goal" :in-theory (enable fat-entry-count))))

(defthm
  bpb_rootclus-of-update-fat
  (equal
   (bpb_rootclus (update-fat fat32-in-memory str pos))
   (bpb_rootclus fat32-in-memory)))

(defthm
  fat-length-of-update-fat
  (implies (and (<= (* pos 4) (length str))
                (equal (length str)
                       (* (fat-length fat32-in-memory) 4)))
           (equal (fat-length (update-fat fat32-in-memory str pos))
                  (fat-length fat32-in-memory))))

(defthm
  bpb_secperclus-of-read-reserved-area
  (and
   (implies
    (stringp str)
    (>=
     (bpb_secperclus
      (mv-nth 0
              (read-reserved-area fat32-in-memory str)))
     1))
   (natp
    (bpb_secperclus
     (mv-nth 0
             (read-reserved-area fat32-in-memory str)))))
  :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (read-reserved-area) (subseq))))
  :rule-classes
  ((:linear
    :corollary
    (<= 1
        (bpb_secperclus
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str))))
    :hints
    (("goal" :do-not-induct t
      :in-theory (e/d (read-reserved-area) (subseq)))))
   (:rewrite
    :corollary
    (integerp
     (bpb_secperclus
      (mv-nth 0
              (read-reserved-area fat32-in-memory str))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (read-reserved-area) (subseq)))))
   (:type-prescription
    :corollary
    (natp
     (bpb_secperclus
      (mv-nth 0
              (read-reserved-area fat32-in-memory str))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (read-reserved-area) (subseq)))))))

(defthm
  bpb_rsvdseccnt-of-read-reserved-area
  (and
   (integerp
    (bpb_rsvdseccnt
     (mv-nth
      0
      (read-reserved-area fat32-in-memory str))))
   (<= 1
       (bpb_rsvdseccnt
        (mv-nth
         0
         (read-reserved-area fat32-in-memory str)))))
  :rule-classes
  ((:linear
    :corollary
    (<= 1
        (bpb_rsvdseccnt
         (mv-nth
          0
          (read-reserved-area fat32-in-memory str)))))
   (:rewrite
    :corollary
    (integerp
     (bpb_rsvdseccnt
      (mv-nth
       0
       (read-reserved-area fat32-in-memory str)))))
   (:type-prescription
    :corollary
    (natp
     (bpb_rsvdseccnt
      (mv-nth
       0
       (read-reserved-area fat32-in-memory str))))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (read-reserved-area) (subseq)))))

(defthm
  bpb_numfats-of-read-reserved-area
  (and
   (<= 1
       (bpb_numfats
        (mv-nth
         0
         (read-reserved-area fat32-in-memory str))))
   (integerp
    (bpb_numfats
     (mv-nth
      0
      (read-reserved-area fat32-in-memory str)))))
  :rule-classes
  ((:linear
    :corollary
    (<= 1
        (bpb_numfats
         (mv-nth
          0
          (read-reserved-area fat32-in-memory str)))))
   (:rewrite
    :corollary
    (integerp
     (bpb_numfats
      (mv-nth
       0
       (read-reserved-area fat32-in-memory str)))))
   (:type-prescription
    :corollary
    (natp
     (bpb_numfats
      (mv-nth
       0
       (read-reserved-area fat32-in-memory str))))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (read-reserved-area) (subseq)))))

(defthm
  bpb_fatsz32-of-read-reserved-area
  (and
   (<= 1
       (bpb_fatsz32
        (mv-nth
         0
         (read-reserved-area fat32-in-memory str))))
   (integerp
    (bpb_fatsz32
     (mv-nth
      0
      (read-reserved-area fat32-in-memory str)))))
  :rule-classes
  ((:linear
    :corollary
    (<= 1
        (bpb_fatsz32
         (mv-nth
          0
          (read-reserved-area fat32-in-memory str)))))
   (:rewrite
    :corollary
    (integerp
     (bpb_fatsz32
      (mv-nth
       0
       (read-reserved-area fat32-in-memory str)))))
   (:type-prescription
    :corollary
    (natp
     (bpb_fatsz32
      (mv-nth
       0
       (read-reserved-area fat32-in-memory str))))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (read-reserved-area) (subseq)))))

(defthm
  bpb_bytspersec-of-read-reserved-area
  (and
   (integerp
    (bpb_bytspersec
     (mv-nth 0
             (read-reserved-area fat32-in-memory str))))
   (<= *ms-min-bytes-per-sector*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area fat32-in-memory str))))
   (< (bpb_bytspersec
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))
      (ash 1 16)))
  :rule-classes
  ((:linear
    :corollary
    (and
     (<= *ms-min-bytes-per-sector*
         (bpb_bytspersec
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str))))
     (< (bpb_bytspersec
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str)))
        (ash 1 16))))
   (:rewrite
    :corollary
    (integerp
     (bpb_bytspersec
      (mv-nth 0
              (read-reserved-area fat32-in-memory str)))))
   (:type-prescription
    :corollary
    (natp
     (bpb_bytspersec
      (mv-nth 0
              (read-reserved-area fat32-in-memory str))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (read-reserved-area) (subseq unsigned-byte-p))
    :use
    ((:instance
      (:theorem (implies (unsigned-byte-p 16 x)
                         (< x (ash 1 16))))
      (x (combine16u
          (nth 12 (get-initial-bytes (str-fix str)))
          (nth 11
               (get-initial-bytes (str-fix str))))))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    cluster-size-of-read-reserved-area
    (natp
    (- (cluster-size
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str)))
       *ms-min-bytes-per-sector*))
    :rule-classes
    ((:linear
      :corollary
      (<= *ms-min-bytes-per-sector*
          (cluster-size
           (mv-nth 0
                   (read-reserved-area fat32-in-memory str)))))
     (:rewrite
      :corollary
      (integerp
       (cluster-size
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))))
     (:type-prescription
      :corollary
      (natp
       (cluster-size
        (mv-nth 0
                (read-reserved-area fat32-in-memory str))))))
    :hints
    (("goal"
      :in-theory (e/d (cluster-size read-reserved-area)
                      (bpb_bytspersec-of-read-reserved-area
                       bpb_secperclus-of-read-reserved-area))
      :use (bpb_bytspersec-of-read-reserved-area
            bpb_secperclus-of-read-reserved-area))))

  (defthm
    fat-entry-count-of-read-reserved-area
    (implies
     (equal (mv-nth 1
                    (read-reserved-area fat32-in-memory str))
            0)
     (and
      (<= 512
          (fat-entry-count
           (mv-nth 0
                   (read-reserved-area fat32-in-memory str))))
      (< (fat-entry-count
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str)))
         (ash 1 48))))
    :rule-classes :linear
    :hints
    (("goal"
      :in-theory (e/d (fat-entry-count read-reserved-area)
                      ((:rewrite combine16u-unsigned-byte)
                       (:rewrite combine32u-unsigned-byte)))
      :use
      ((:instance
        (:rewrite combine16u-unsigned-byte)
        (a0 (nth 11 (get-initial-bytes (str-fix str))))
        (a1 (nth 12 (get-initial-bytes (str-fix str)))))
       (:instance
        (:rewrite combine32u-unsigned-byte)
        (a0 (nth 20
                 (get-remaining-rsvdbyts (str-fix str))))
        (a1 (nth 21
                 (get-remaining-rsvdbyts (str-fix str))))
        (a2 (nth 22
                 (get-remaining-rsvdbyts (str-fix str))))
        (a3 (nth 23
                 (get-remaining-rsvdbyts (str-fix str))))))))))

(defthm
  count-of-clusters-of-read-reserved-area
  (implies
   (equal (mv-nth 1
                  (read-reserved-area fat32-in-memory str))
          0)
   (and
    (<= *ms-min-count-of-clusters*
        (count-of-clusters
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str))))
    (integerp
     (count-of-clusters
      (mv-nth 0
              (read-reserved-area fat32-in-memory str))))))
  :rule-classes
  ((:linear
    :corollary
    (implies
     (equal (mv-nth 1
                    (read-reserved-area fat32-in-memory str))
            0)
     (<= *ms-min-count-of-clusters*
         (count-of-clusters
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str))))))
   (:rewrite
    :corollary
    (implies
     (equal (mv-nth 1
                    (read-reserved-area fat32-in-memory str))
            0)
     (integerp
      (count-of-clusters
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))))))
  :hints (("goal" :in-theory (enable count-of-clusters read-reserved-area))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    fat32-in-memoryp-of-read-reserved-area
    (implies
     (fat32-in-memoryp fat32-in-memory)
     (fat32-in-memoryp (mv-nth 0
                               (read-reserved-area fat32-in-memory str))))
    :hints (("goal" :in-theory (enable read-reserved-area))))

  (defund
    string-to-lofat (fat32-in-memory str)
    (declare
     (xargs
      :guard (and (stringp str)
                  (>= (length str) *initialbytcnt*)
                  (fat32-in-memoryp fat32-in-memory))
      :guard-hints
      (("goal"
        :in-theory (enable cluster-size count-of-clusters)))
      :stobjs fat32-in-memory))
    (b*
        (((mv fat32-in-memory error-code)
          (read-reserved-area fat32-in-memory str))
         ((unless (equal error-code 0))
          (mv fat32-in-memory error-code))
         (fat-read-size (fat-entry-count fat32-in-memory))
         ;; The expression below should eventually be replaced by
         ;; fat-entry-count, but that is going to open a can of worms...
         ((unless (integerp (/ (* (bpb_fatsz32 fat32-in-memory)
                                  (bpb_bytspersec fat32-in-memory))
                               4)))
          (mv fat32-in-memory *eio*))
         (data-byte-count (* (count-of-clusters fat32-in-memory)
                             (cluster-size fat32-in-memory)))
         ((unless (> data-byte-count 0))
          (mv fat32-in-memory *eio*))
         (tmp_bytspersec (bpb_bytspersec fat32-in-memory))
         (tmp_init (* tmp_bytspersec
                      (+ (bpb_rsvdseccnt fat32-in-memory)
                         (* (bpb_numfats fat32-in-memory)
                            (bpb_fatsz32 fat32-in-memory)))))
         (fat32-in-memory (resize-fat fat-read-size fat32-in-memory))
         ((unless (and (<= (+ (* (bpb_rsvdseccnt fat32-in-memory)
                                 (bpb_bytspersec fat32-in-memory))
                              (* fat-read-size 4))
                           (length str))
                       (unsigned-byte-p 48 fat-read-size)))
          (mv fat32-in-memory *eio*))
         (fat32-in-memory
          (update-fat fat32-in-memory
                      (subseq str
                              (* (bpb_rsvdseccnt fat32-in-memory)
                                 (bpb_bytspersec fat32-in-memory))
                              (+ (* (bpb_rsvdseccnt fat32-in-memory)
                                    (bpb_bytspersec fat32-in-memory))
                                 (* fat-read-size 4)))
                      fat-read-size))
         (fat32-in-memory
          (resize-data-region (count-of-clusters fat32-in-memory)
                              fat32-in-memory))
         ((unless (and (<= (data-region-length fat32-in-memory)
                           (- *ms-bad-cluster*
                              *ms-first-data-cluster*))
                       (>= (length str) tmp_init)))
          (mv fat32-in-memory *eio*))
         (data-region-string (subseq str tmp_init nil)))
      (update-data-region fat32-in-memory data-region-string
                          (data-region-length fat32-in-memory)))))

(defthmd
  string-to-lofat-correctness-1
  (equal
   (string-to-lofat fat32-in-memory str)
   (mv
    (mv-nth 0
            (string-to-lofat fat32-in-memory str))
    (mv-nth 1
            (string-to-lofat fat32-in-memory str))))
  :hints
  (("goal"
    :in-theory (e/d (string-to-lofat)
                    (subseq))
    :use
    (:instance
     update-data-region-correctness-2
     (fat32-in-memory
      (resize-data-region
       (count-of-clusters
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (update-fat
        (resize-fat
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str)))
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str)))
        (subseq
         str
         (*
          (bpb_bytspersec
           (mv-nth 0
                   (read-reserved-area fat32-in-memory str)))
          (bpb_rsvdseccnt
           (mv-nth 0
                   (read-reserved-area fat32-in-memory str))))
         (+
          (*
           4
           (fat-entry-count
            (mv-nth 0
                    (read-reserved-area fat32-in-memory str))))
          (*
           (bpb_bytspersec
            (mv-nth 0
                    (read-reserved-area fat32-in-memory str)))
           (bpb_rsvdseccnt
            (mv-nth
             0
             (read-reserved-area fat32-in-memory str))))))
        (fat-entry-count
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str))))))
     (str
      (subseq
       str
       (+
        (*
         (bpb_bytspersec
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str)))
         (bpb_rsvdseccnt
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str))))
        (*
         (bpb_bytspersec
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str)))
         (bpb_fatsz32
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str)))
         (bpb_numfats
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str)))))
       nil))
     (len
      (count-of-clusters
       (mv-nth 0
               (read-reserved-area fat32-in-memory str))))))))

(defthm
  disk-image-to-lofat-guard-lemma-1
  (iff
   (< (len (explode (read-file-into-string2
                     image-path 0 *initialbytcnt* state)))
      *initialbytcnt*)
   (<
    (len
     (explode (read-file-into-string2 image-path 0 nil state)))
    *initialbytcnt*))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (<=
      *initialbytcnt*
      (len
       (explode
        (read-file-into-string2 image-path 0 nil state))))
     (equal
      (len (explode (read-file-into-string2
                     image-path 0 *initialbytcnt* state)))
      *initialbytcnt*)))))

(defthm
  disk-image-to-lofat-guard-lemma-3
  (equal
   (read-reserved-area
    (update-bpb_bytspersec
     512
     (update-bpb_fatsz32
      1
      (update-bpb_numfats
       1
       (update-bpb_rsvdseccnt
        1
        (update-bpb_secperclus 1 fat32-in-memory)))))
    str)
   (read-reserved-area fat32-in-memory str))
  :hints (("Goal" :in-theory (enable read-reserved-area)) ))

(defthm
  disk-image-to-lofat-guard-lemma-9
  (implies
   (< (nfix n) 16)
   (equal
    (nth
     n
     (explode (read-file-into-string2 image-path 0 16 state)))
    (nth
     n
     (explode
      (read-file-into-string2 image-path 0 nil state)))))
  :hints (("goal" :in-theory (enable nth))))

(defthm
  disk-image-to-lofat-guard-lemma-4
  (implies
   (equal
    (mv-nth
     1
     (read-reserved-area fat32-in-memory
                         (read-file-into-string2 image-path 0 nil state)))
    0)
   (and
    (equal
     (combine16u
      (char-code
       (nth 12
            (explode (read-file-into-string2 image-path 0 nil state))))
      (char-code
       (nth 11
            (explode (read-file-into-string2 image-path 0 nil state)))))
     (bpb_bytspersec
      (mv-nth
       0
       (read-reserved-area fat32-in-memory
                           (read-file-into-string2 image-path 0 nil state)))))
    (equal
     (combine16u
      (char-code
       (nth 15
            (explode (read-file-into-string2 image-path 0 nil state))))
      (char-code
       (nth 14
            (explode (read-file-into-string2 image-path 0 nil state)))))
     (bpb_rsvdseccnt
      (mv-nth
       0
       (read-reserved-area fat32-in-memory
                           (read-file-into-string2 image-path 0 nil state)))))))
  :hints (("Goal" :in-theory (enable read-reserved-area get-initial-bytes)) ))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    disk-image-to-lofat-guard-lemma-5
    (implies
     (equal (mv-nth 1
                    (read-reserved-area fat32-in-memory str))
            0)
     (<=
      (* *ms-min-bytes-per-sector*
         *ms-min-count-of-clusters*)
      (*
       (cluster-size
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (count-of-clusters
        (mv-nth 0
                (read-reserved-area fat32-in-memory str))))))
    :rule-classes :linear
    :hints
    (("goal"
      :in-theory (disable cluster-size-of-read-reserved-area
                          count-of-clusters-of-read-reserved-area
                          read-reserved-area)
      :use (cluster-size-of-read-reserved-area
            count-of-clusters-of-read-reserved-area))))

  (defthm
    disk-image-to-lofat-guard-lemma-15
    (iff
     (integerp
      (*
       (bpb_fatsz32
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))
       1/4
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))))
     (integerp
      (*
       1/4
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))
       (bpb_fatsz32
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))))))

  (defthm
    disk-image-to-lofat-guard-lemma-22
    (implies
     (and
      (integerp
       (*
        1/4
        (bpb_bytspersec
         (mv-nth
          0
          (read-reserved-area fat32-in-memory
                              str)))
        (bpb_fatsz32
         (mv-nth 0
                 (read-reserved-area
                  fat32-in-memory
                  str))))))
     (<=
      (* 4
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   str))))
      (*
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area fat32-in-memory
                             str)))
       (bpb_fatsz32
        (mv-nth
         0
         (read-reserved-area fat32-in-memory
                             str)))
       (bpb_numfats
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 str))))))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable fat-entry-count)) )))

(defthm
  disk-image-to-lofat-guard-lemma-6
  (implies
   (<=
    16
    (len
     (explode (read-file-into-string2 image-path 0 16 state))))
   (stringp
    (read-file-into-string2
     image-path 16
     (+
      -16
      (*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))))
     state))))

(defthm
  disk-image-to-lofat-guard-lemma-7
  (implies
   (<= 16
       (len (explode (read-file-into-string2 image-path 0 16 state))))
   (stringp
    (read-file-into-string2
     image-path 16
     (+
      -16
      (*
       (combine16u
        (char-code
         (nth 12
              (explode (read-file-into-string2 image-path 0 nil state))))
        (char-code
         (nth 11
              (explode (read-file-into-string2 image-path 0 nil state)))))
       (combine16u
        (char-code
         (nth 15
              (explode (read-file-into-string2 image-path 0 nil state))))
        (char-code
         (nth 14
              (explode (read-file-into-string2 image-path 0 nil state)))))))
     state)))
  :hints (("goal" :in-theory (enable read-reserved-area))))

(defthm
  disk-image-to-lofat-guard-lemma-8
  (implies
   (< (combine16u (char-code (nth 15 (explode str)))
                  (char-code (nth 14 (explode str))))
      1)
   (equal
    (read-reserved-area fat32-in-memory str)
    (mv
     (update-bpb_bytspersec
      512
      (update-bpb_fatsz32
       1
       (update-bpb_numfats
        1
        (update-bpb_rsvdseccnt 1
                               (update-bpb_secperclus 1 fat32-in-memory)))))
     *eio*)))
  :hints (("goal" :in-theory (enable read-reserved-area get-initial-bytes))))

(defthm
  disk-image-to-lofat-guard-lemma-10
  (implies
   (equal
    (mv-nth
     1
     (read-reserved-area
      fat32-in-memory
      (read-file-into-string2 image-path 0 nil state)))
    0)
   (equal
    (len
     (explode
      (read-file-into-string2
       image-path 16
       (+
        -16
        (*
         (bpb_bytspersec
          (mv-nth
           0
           (read-reserved-area
            fat32-in-memory
            (read-file-into-string2 image-path 0 nil state))))
         (bpb_rsvdseccnt
          (mv-nth
           0
           (read-reserved-area
            fat32-in-memory
            (read-file-into-string2 image-path 0 nil state))))))
       state)))
    (+
     -16
     (*
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state))))
      (bpb_rsvdseccnt
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state))))))))
  :hints (("goal" :in-theory (enable read-reserved-area))))

(defthm
  disk-image-to-lofat-guard-lemma-11
  (implies
   (<
    (len
     (explode
      (read-file-into-string2
       image-path 16
       (+
        -16
        (*
         (combine16u
          (char-code
           (nth 12
                (explode (read-file-into-string2 image-path 0 nil state))))
          (char-code
           (nth 11
                (explode (read-file-into-string2 image-path 0 nil state)))))
         (combine16u
          (char-code
           (nth 15
                (explode (read-file-into-string2 image-path 0 nil state))))
          (char-code
           (nth 14
                (explode (read-file-into-string2 image-path 0 nil state)))))))
       state)))
    (+
     -16
     (*
      (combine16u
       (char-code
        (nth 12
             (explode (read-file-into-string2 image-path 0 nil state))))
       (char-code
        (nth 11
             (explode (read-file-into-string2 image-path 0 nil state)))))
      (combine16u
       (char-code
        (nth 15
             (explode (read-file-into-string2 image-path 0 nil state))))
       (char-code
        (nth 14
             (explode (read-file-into-string2 image-path 0 nil state))))))))
   (equal
    (read-reserved-area
     fat32-in-memory
     (read-file-into-string2 image-path 0 nil state))
    (mv
     (update-bpb_bytspersec
      512
      (update-bpb_fatsz32
       1
       (update-bpb_numfats
        1
        (update-bpb_rsvdseccnt 1
                               (update-bpb_secperclus 1 fat32-in-memory)))))
     *EIO*)))
  :hints (("goal" :in-theory (enable get-initial-bytes read-reserved-area))))

(defthmd
  disk-image-to-lofat-guard-lemma-12
  (implies
   (< (combine16u (char-code (nth 12 (explode str)))
                  (char-code (nth 11 (explode str))))
      512)
   (equal
    (read-reserved-area fat32-in-memory str)
    (mv
     (update-bpb_bytspersec
      512
      (update-bpb_fatsz32
       1
       (update-bpb_numfats
        1
        (update-bpb_rsvdseccnt 1
                               (update-bpb_secperclus 1 fat32-in-memory)))))
     *eio*)))
  :hints (("goal" :in-theory (enable read-reserved-area get-initial-bytes))))

(defthm
  disk-image-to-lofat-guard-lemma-13
  (implies
   (and
    (<= 16
        (len (explode (read-file-into-string2 image-path 0 16 state))))
    (>=
     (combine16u
      (char-code
       (nth 12
            (explode (read-file-into-string2 image-path 0 nil state))))
      (char-code
       (nth 11
            (explode (read-file-into-string2 image-path 0 nil state)))))
     512)
    (>=
     (combine16u
      (char-code
       (nth 15
            (explode (read-file-into-string2 image-path 0 nil state))))
      (char-code
       (nth 14
            (explode (read-file-into-string2 image-path 0 nil state)))))
     1))
   (equal
    (read-reserved-area
     fat32-in-memory
     (read-file-into-string2
      image-path 0
      (*
       (combine16u
        (char-code
         (nth 12
              (explode (read-file-into-string2 image-path 0 nil state))))
        (char-code
         (nth 11
              (explode (read-file-into-string2 image-path 0 nil state)))))
       (combine16u
        (char-code
         (nth 15
              (explode (read-file-into-string2 image-path 0 nil state))))
        (char-code
         (nth 14
              (explode (read-file-into-string2 image-path 0 nil state))))))
      state))
    (read-reserved-area fat32-in-memory
                        (read-file-into-string2 image-path 0 nil state))))
  :hints
  (("goal"
    :in-theory (disable read-reserved-area-correctness-1)
    :use (:instance read-reserved-area-correctness-1
                    (str (read-file-into-string2 image-path 0 nil state))))))

(defthm
  disk-image-to-lofat-guard-lemma-14
  (implies
   (equal
    (mv-nth
     1
     (read-reserved-area fat32-in-memory
                         (read-file-into-string2 image-path 0 nil state)))
    0)
   (equal
    (read-reserved-area
     fat32-in-memory
     (read-file-into-string2
      image-path 0
      (*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state)))))
      state))
    (read-reserved-area fat32-in-memory
                        (read-file-into-string2 image-path 0 nil state))))
  :hints
  (("goal"
    :in-theory (e/d (read-reserved-area)
                    (disk-image-to-lofat-guard-lemma-13))
    :use disk-image-to-lofat-guard-lemma-13)))

;; Accumulated-persistence suggests disabling this rule, but really it only
;; gets tried in the main lemma, where we have to leave it enabled anyway. So
;; we might as well skip (or at least shrink) that one in-theory hint.
(defthm
  disk-image-to-lofat-guard-lemma-16
  (implies
   (< (* (combine16u (char-code (nth 12 (explode str)))
                     (char-code (nth 11 (explode str))))
         (combine16u (char-code (nth 15 (explode str)))
                     (char-code (nth 14 (explode str)))))
      16)
   (equal
    (read-reserved-area fat32-in-memory str)
    (mv
     (update-bpb_bytspersec
      512
      (update-bpb_fatsz32
       1
       (update-bpb_numfats
        1
        (update-bpb_rsvdseccnt 1
                               (update-bpb_secperclus 1 fat32-in-memory)))))
     *eio*)))
  :hints (("goal" :in-theory (enable read-reserved-area get-initial-bytes))))

(defthm
  disk-image-to-lofat-guard-lemma-17
  (implies
   (equal
    (mv-nth
     1
     (read-reserved-area fat32-in-memory
                         (read-file-into-string2 image-path 0 nil state)))
    0)
   (iff
    (<
     (len
      (explode
       (read-file-into-string2
        image-path
        (*
         (bpb_bytspersec
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state))))
         (bpb_rsvdseccnt
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
        (*
         4
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
        state)))
     (*
      4
      (fat-entry-count
       (mv-nth
        0
        (read-reserved-area fat32-in-memory
                            (read-file-into-string2 image-path 0 nil state))))))
    (<
     (len (explode (read-file-into-string2 image-path 0 nil state)))
     (+
      (* 4
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
      (*
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area fat32-in-memory
                             (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))))))))

(defthm
  disk-image-to-lofat-guard-lemma-19
  (implies
   (and
    (equal
     (mv-nth
      1
      (read-reserved-area
       fat32-in-memory
       (read-file-into-string2 image-path 0 nil state)))
     0)
    (<=
     (+
      (*
       4
       (fat-entry-count
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state)))))
      (*
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))))
     (len
      (explode
       (read-file-into-string2 image-path 0 nil state)))))
   (equal
    (read-file-into-string2
     image-path
     (*
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state))))
      (bpb_rsvdseccnt
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state)))))
     (*
      4
      (fat-entry-count
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state)))))
     state)
    (implode
     (take
      (*
       4
       (fat-entry-count
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state)))))
      (nthcdr
       (*
        (bpb_bytspersec
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state))))
        (bpb_rsvdseccnt
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state)))))
       (explode
        (read-file-into-string2 image-path 0 nil state)))))))
  :hints
  (("goal"
    :in-theory (enable take-of-nthcdr)
    :use
    (:theorem
     (equal
      (+
       (len
        (explode
         (mv-nth
          0
          (read-file-into-string1
           (mv-nth 0
                   (open-input-channel image-path
                                       :character state))
           (mv-nth 1
                   (open-input-channel image-path
                                       :character state))
           nil 1152921504606846975))))
       (*
        4
        (fat-entry-count
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (mv-nth
            0
            (read-file-into-string1
             (mv-nth 0
                     (open-input-channel image-path
                                         :character state))
             (mv-nth 1
                     (open-input-channel image-path
                                         :character state))
             nil 1152921504606846975))))))
       (*
        -4
        (fat-entry-count
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (mv-nth
            0
            (read-file-into-string1
             (mv-nth 0
                     (open-input-channel image-path
                                         :character state))
             (mv-nth 1
                     (open-input-channel image-path
                                         :character state))
             nil 1152921504606846975)))))))
      (len
       (explode
        (mv-nth
         0
         (read-file-into-string1
          (mv-nth 0
                  (open-input-channel image-path
                                      :character state))
          (mv-nth 1
                  (open-input-channel image-path
                                      :character state))
          nil 1152921504606846975)))))))))

(defthm
  disk-image-to-lofat-guard-lemma-21
  (equal
   (+
    (-
     (*
      4
      (fat-entry-count
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))))
    (* (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area fat32-in-memory str))))
    (-
     (*
      (bpb_bytspersec
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))
      (bpb_rsvdseccnt
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))))
    (* (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_fatsz32
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_numfats
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))))
   (+
    (-
     (*
      4
      (fat-entry-count
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))))
    (*
     (bpb_bytspersec
      (mv-nth 0
              (read-reserved-area fat32-in-memory str)))
     (bpb_fatsz32
      (mv-nth 0
              (read-reserved-area fat32-in-memory str)))
     (bpb_numfats
      (mv-nth 0
              (read-reserved-area fat32-in-memory str)))))))

(defthm
  disk-image-to-lofat-guard-lemma-25
  (implies
   (stringp (read-file-into-string2 image-path 0 nil state))
   (iff
    (stringp
     (read-file-into-string2
      image-path
      (+
       (*
        4
        (fat-entry-count
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state)))))
       (*
        (bpb_bytspersec
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state))))
        (bpb_rsvdseccnt
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state))))))
      (+
       (-
        (*
         4
         (fat-entry-count
          (mv-nth
           0
           (read-reserved-area
            fat32-in-memory
            (read-file-into-string2 image-path 0 nil state))))))
       (*
        (bpb_bytspersec
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state))))
        (bpb_fatsz32
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state))))
        (bpb_numfats
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state))))))
      state))
    (<=
     (+
      (*
       4
       (fat-entry-count
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state)))))
      (*
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))))
     (length
      (read-file-into-string2 image-path 0 nil state))))))

(defthm
  disk-image-to-lofat-guard-lemma-27
  (implies
   (and
    (<=
     0
     (+
      (* 4
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
      (*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state)))))))
    (<=
     (+
      (* 4
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
      (*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))))
     (len (explode (read-file-into-string2 image-path 0 nil state)))))
   (iff
    (<
     (len
      (explode
       (read-file-into-string2
        image-path
        (+
         (*
          4
          (fat-entry-count
           (mv-nth 0
                   (read-reserved-area
                    fat32-in-memory
                    (read-file-into-string2 image-path 0 nil state)))))
         (*
          (bpb_bytspersec
           (mv-nth 0
                   (read-reserved-area
                    fat32-in-memory
                    (read-file-into-string2 image-path 0 nil state))))
          (bpb_rsvdseccnt
           (mv-nth 0
                   (read-reserved-area
                    fat32-in-memory
                    (read-file-into-string2 image-path 0 nil state))))))
        (+
         (-
          (*
           4
           (fat-entry-count
            (mv-nth 0
                    (read-reserved-area
                     fat32-in-memory
                     (read-file-into-string2 image-path 0 nil state))))))
         (*
          (bpb_bytspersec
           (mv-nth 0
                   (read-reserved-area
                    fat32-in-memory
                    (read-file-into-string2 image-path 0 nil state))))
          (bpb_fatsz32
           (mv-nth 0
                   (read-reserved-area
                    fat32-in-memory
                    (read-file-into-string2 image-path 0 nil state))))
          (bpb_numfats
           (mv-nth 0
                   (read-reserved-area
                    fat32-in-memory
                    (read-file-into-string2 image-path 0 nil state))))))
        state)))
     (+
      (-
       (*
        4
        (fat-entry-count
         (mv-nth 0
                 (read-reserved-area
                  fat32-in-memory
                  (read-file-into-string2 image-path 0 nil state))))))
      (*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_fatsz32
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_numfats
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state)))))))
    (<
     (len (explode (read-file-into-string2 image-path 0 nil state)))
     (+
      (* (bpb_bytspersec
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state))))
         (bpb_rsvdseccnt
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
      (*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_fatsz32
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_numfats
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))))))))

(defthm
  disk-image-to-lofat-guard-lemma-28
  (implies
   (stringp (read-file-into-string2 image-path 0 nil state))
   (iff
    (stringp
     (read-file-into-string2
      image-path
      (*
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state)))))
      (*
       4
       (fat-entry-count
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state)))))
      state))
    (<=
     (*
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state))))
      (bpb_rsvdseccnt
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state)))))
     (len
      (explode
       (read-file-into-string2 image-path 0 nil state)))))))

(defthm
  disk-image-to-lofat-guard-lemma-29
  (implies
   (and
    (stringp (read-file-into-string2 image-path 0 nil state))
    (equal
     (len
      (explode
       (read-file-into-string2
        image-path
        (*
         (bpb_bytspersec
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state))))
         (bpb_rsvdseccnt
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
        (*
         4
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
        state)))
     (* 4
        (fat-entry-count
         (mv-nth 0
                 (read-reserved-area
                  fat32-in-memory
                  (read-file-into-string2 image-path 0 nil state))))))
    (>=
     (len
      (explode
       (read-file-into-string2 image-path 0 nil state)))
     (*
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state))))
      (bpb_rsvdseccnt
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state)))))))
   (<=
    (+
     (* 4
        (fat-entry-count
         (mv-nth 0
                 (read-reserved-area
                  fat32-in-memory
                  (read-file-into-string2 image-path 0 nil state)))))
     (*
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area fat32-in-memory
                            (read-file-into-string2 image-path 0 nil state))))
      (bpb_rsvdseccnt
       (mv-nth 0
               (read-reserved-area
                fat32-in-memory
                (read-file-into-string2 image-path 0 nil state))))))
    (len (explode (read-file-into-string2 image-path 0 nil state)))))
  :rule-classes :linear)

(defthm
  disk-image-to-lofat-guard-lemma-30
  (implies
   (or (not (stringp str))
       (> *initialbytcnt* (len (explode str))))
   (equal
    (read-reserved-area fat32-in-memory str)
    (mv
     (update-bpb_bytspersec
      512
      (update-bpb_fatsz32
       1
       (update-bpb_numfats
        1
        (update-bpb_rsvdseccnt
         1
         (update-bpb_secperclus 1 fat32-in-memory)))))
     *eio*)))
  :hints (("goal" :in-theory (enable read-reserved-area))))

(defthm
  disk-image-to-lofat-guard-lemma-31
  (iff
   (stringp (read-file-into-string2 image-path 0 16 state))
   (stringp (read-file-into-string2 image-path 0 nil state))))

(defthm
  disk-image-to-lofat-guard-lemma-32
  (implies
   (<
    (*
     (bpb_bytspersec
      (mv-nth
       0
       (read-reserved-area
        fat32-in-memory
        (read-file-into-string2 image-path 0 nil state))))
     (bpb_rsvdseccnt
      (mv-nth
       0
       (read-reserved-area
        fat32-in-memory
        (read-file-into-string2 image-path 0 nil state)))))
    16)
   (equal
    (read-reserved-area
     fat32-in-memory
     (read-file-into-string2 image-path 0 nil state))
    (mv
     (update-bpb_bytspersec
      512
      (update-bpb_fatsz32
       1
       (update-bpb_numfats
        1
        (update-bpb_rsvdseccnt
         1
         (update-bpb_secperclus 1 fat32-in-memory)))))
     *eio*)))
  :hints (("goal" :in-theory (enable read-reserved-area))))

(defun
  disk-image-to-lofat
  (fat32-in-memory image-path state)
  (declare
   (xargs
    :guard (and (stringp image-path)
                (fat32-in-memoryp fat32-in-memory))
    :guard-hints
    (("goal"
      :in-theory
      (e/d (string-to-lofat
            disk-image-to-lofat-guard-lemma-12)
           (string-append
            read-file-into-string2
            ;; The following came from accumulated-persistence results.
            (:rewrite str::explode-when-not-stringp)
            (:definition update-fat)
            (:rewrite nth-of-make-character-list)))))
    :stobjs (fat32-in-memory state)))
  ;; The idea behind this MBE is that slurping in the whole string at once is
  ;; causing inefficiencies in terms of memory allocated for all these subseq
  ;; operations. For instance, for one disk image of size 64 MB with 69441
  ;; clusters, each subseq operation allocated 4,112 bytes and the whole
  ;; update-data-region operation allocated 496,573,872 bytes. This is several
  ;; times the size of the disk, and is probably the reason why we can't
  ;; execute for disks of size 300 MB or more.
  (mbe
   ;; It's a good idea to keep the spec simple.
   :logic (b* ((str (read-file-into-string image-path)))
            (string-to-lofat fat32-in-memory str))
   ;; This b* form pretty closely follows the structure of
   ;; string-to-lofat.
   :exec
   (b*
       ((initial-bytes-str
         (read-file-into-string image-path
                                :bytes *initialbytcnt*))
        (fat32-in-memory (update-bpb_secperclus 1 fat32-in-memory))
        (fat32-in-memory (update-bpb_rsvdseccnt 1 fat32-in-memory))
        (fat32-in-memory (update-bpb_numfats 1 fat32-in-memory))
        (fat32-in-memory (update-bpb_fatsz32 1 fat32-in-memory))
        (fat32-in-memory
         (update-bpb_bytspersec 512 fat32-in-memory))
        ((unless (and (stringp initial-bytes-str)
                      (>= (length initial-bytes-str)
                          *initialbytcnt*)))
         (mv fat32-in-memory *EIO*))
        (tmp_bytspersec
         (combine16u (char-code (char initial-bytes-str 12))
                     (char-code (char initial-bytes-str 11))))
        (tmp_rsvdseccnt
         (combine16u (char-code (char initial-bytes-str 15))
                     (char-code (char initial-bytes-str 14))))
        (tmp_rsvdbytcnt (* tmp_rsvdseccnt tmp_bytspersec))
        ((unless (and (>= tmp_bytspersec 512)
                      (>= tmp_rsvdseccnt 1)
                      (>= tmp_rsvdbytcnt *initialbytcnt*)))
         (mv fat32-in-memory *EIO*))
        (remaining-rsvdbyts-str
         (read-file-into-string
          image-path
          :start *initialbytcnt*
          :bytes (- tmp_rsvdbytcnt *initialbytcnt*)))
        ((unless (and (stringp remaining-rsvdbyts-str)
                      (>= (length remaining-rsvdbyts-str)
                          (- tmp_rsvdbytcnt *initialbytcnt*))))
         (mv fat32-in-memory *EIO*))
        ((mv fat32-in-memory error-code)
         (read-reserved-area
          fat32-in-memory
          (string-append initial-bytes-str
                         remaining-rsvdbyts-str)))
        ((unless (equal error-code 0))
         (mv fat32-in-memory error-code))
        (fat-read-size (fat-entry-count fat32-in-memory))
        ((unless (integerp (/ (* (bpb_fatsz32 fat32-in-memory)
                                 (bpb_bytspersec fat32-in-memory))
                              4)))
         (mv fat32-in-memory *EIO*))
        (data-byte-count (* (count-of-clusters fat32-in-memory)
                            (cluster-size fat32-in-memory)))
        ((unless (> data-byte-count 0))
         (mv fat32-in-memory *EIO*))
        (tmp_bytspersec (bpb_bytspersec fat32-in-memory))
        (tmp_init (* tmp_bytspersec
                     (+ (bpb_rsvdseccnt fat32-in-memory)
                        (* (bpb_numfats fat32-in-memory)
                           (bpb_fatsz32 fat32-in-memory)))))
        (fat32-in-memory
         (resize-fat fat-read-size fat32-in-memory))
        (fat-string
         (read-file-into-string image-path
                                :start tmp_rsvdbytcnt
                                :bytes (* fat-read-size 4)))
        ((unless (and (<= (* fat-read-size 4)
                          (length fat-string))
                      (unsigned-byte-p 48 fat-read-size)))
         (mv fat32-in-memory *EIO*))
        (fat32-in-memory (update-fat fat32-in-memory
                                     fat-string fat-read-size))
        (fat32-in-memory
         (resize-data-region (count-of-clusters fat32-in-memory)
                             fat32-in-memory))
        ;; This test doesn't accomplish much other than getting the extra
        ;; copies of the file allocation table out of the way.
        ((unless
             (and
              (<= (data-region-length fat32-in-memory)
                  (- *ms-bad-cluster*
                     *ms-first-data-cluster*))
              (>=
               (length
                (read-file-into-string
                 image-path
                 :start (+ tmp_rsvdbytcnt (* fat-read-size 4))
                 :bytes (- tmp_init
                           (+ tmp_rsvdbytcnt (* fat-read-size 4)))))
               (- tmp_init
                  (+ tmp_rsvdbytcnt (* fat-read-size 4))))))
         (mv fat32-in-memory *EIO*)))
     (update-data-region-from-disk-image
      fat32-in-memory
      (data-region-length fat32-in-memory)
      state
      tmp_init
      image-path))))

(defun
    stobj-fa-table-to-string-helper
    (fat32-in-memory length ac)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (natp length)
                (<= length (fat-length fat32-in-memory)))
    :guard-hints
    (("goal"
      :in-theory
      (e/d
       (fat32-entry-p)
       (unsigned-byte-p fati-when-lofat-fs-p))
      :use (:instance fati-when-lofat-fs-p
                      (i (+ -1 length)))))))
  (if
      (zp length)
      ac
    (let ((current (fati (- length 1) fat32-in-memory)))
      (stobj-fa-table-to-string-helper
       fat32-in-memory (- length 1)
       (list*
        (code-char (loghead 8             current ))
        (code-char (loghead 8 (logtail  8 current)))
        (code-char (loghead 8 (logtail 16 current)))
        (code-char            (logtail 24 current))
        ac)))))

(defthm
  character-listp-of-stobj-fa-table-to-string-helper
  (equal
   (character-listp
    (stobj-fa-table-to-string-helper fat32-in-memory length ac))
   (character-listp ac)))

(defthm
  len-of-stobj-fa-table-to-string-helper
  (equal
   (len
    (stobj-fa-table-to-string-helper
     fat32-in-memory length ac))
   (+ (len ac) (* 4 (nfix length)))))

(defund
    stobj-fa-table-to-string
    (fat32-in-memory)
    (declare
     (xargs
      :stobjs fat32-in-memory
      :guard (lofat-fs-p fat32-in-memory)))
    (coerce
     (stobj-fa-table-to-string-helper
      fat32-in-memory (fat-length fat32-in-memory) nil)
     'string))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    reserved-area-string-guard-lemma-1
    (implies (lofat-fs-p fat32-in-memory)
             (natp (- (* (bpb_bytspersec fat32-in-memory)
                         (bpb_rsvdseccnt fat32-in-memory))
                      90)))
    :rule-classes
    ((:linear
      :corollary
      (implies (lofat-fs-p fat32-in-memory)
               (<= 90
                   (* (bpb_bytspersec fat32-in-memory)
                      (bpb_rsvdseccnt fat32-in-memory)))))
     (:rewrite
      :corollary
      (implies (lofat-fs-p fat32-in-memory)
               (integerp (* (bpb_bytspersec fat32-in-memory)
                            (bpb_rsvdseccnt fat32-in-memory)))))
     (:rewrite
      :corollary
      (implies (lofat-fs-p fat32-in-memory)
               (integerp (- (* (bpb_bytspersec fat32-in-memory)
                               (bpb_rsvdseccnt fat32-in-memory)))))))
    :hints (("goal" :in-theory (e/d (lofat-fs-p)
                                    (fat32-in-memoryp))))))

(defthm
  reserved-area-string-guard-lemma-2
  (implies (and (lofat-fs-p fat32-in-memory)
                (natp i)
                (< i (fat-length fat32-in-memory)))
           (and (integerp (fati i fat32-in-memory))
                (<= 0 (fati i fat32-in-memory))
                (< (fati i fat32-in-memory) 4294967296)))
  :rule-classes
  ((:rewrite
    :corollary (implies (and (lofat-fs-p fat32-in-memory)
                             (natp i)
                             (< i (fat-length fat32-in-memory)))
                        (integerp (fati i fat32-in-memory))))
   (:linear
    :corollary (implies (and (lofat-fs-p fat32-in-memory)
                             (natp i)
                             (< i (fat-length fat32-in-memory)))
                        (and (<= 0 (fati i fat32-in-memory))
                             (< (fati i fat32-in-memory)
                                4294967296)))))
  :hints
  (("goal"
    :in-theory
    (e/d (lofat-fs-p fat32-entry-p)
         (fati fati-when-lofat-fs-p))
    :use fati-when-lofat-fs-p)))

(encapsulate
  ()

  (local
   (defthm
     reserved-area-string-guard-lemma-3
     (implies (and (logtail-guard size i)
                   (unsigned-byte-p (+ size 8) i))
              (and (integerp (logtail size i))
                   (<= 0 (logtail size i))
                   (< (logtail size i) 256)))
     :rule-classes
     ((:rewrite
       :corollary
       (implies (and (logtail-guard size i)
                     (unsigned-byte-p (+ size 8) i))
                (integerp (logtail size i))))
      (:linear
       :corollary
       (implies (and (logtail-guard size i)
                     (unsigned-byte-p (+ size 8) i))
                (and (<= 0 (logtail size i))
                     (< (logtail size i) 256)))))
     :hints
     (("goal" :in-theory (disable logtail-unsigned-byte-p)
       :use (:instance logtail-unsigned-byte-p (size1 8))))))

  (defund reserved-area-chars (fat32-in-memory)
    (declare (xargs :stobjs fat32-in-memory
                    :guard (lofat-fs-p fat32-in-memory)
                    :guard-hints (("Goal"
                                   :do-not-induct t
                                   :in-theory (disable bs_vollabi
                                                       bs_jmpbooti
                                                       bs_oemnamei
                                                       bs_filsystypei
                                                       bpb_reservedi
                                                       reserved-area-string-guard-lemma-2)
                                   :use
                                   reserved-area-string-guard-lemma-2))))
    (append
     ;; initial bytes
     (list (code-char (bs_jmpbooti 0 fat32-in-memory))
           (code-char (bs_jmpbooti 1 fat32-in-memory))
           (code-char (bs_jmpbooti 2 fat32-in-memory)))
     (list (code-char (bs_oemnamei 0 fat32-in-memory))
           (code-char (bs_oemnamei 1 fat32-in-memory))
           (code-char (bs_oemnamei 2 fat32-in-memory))
           (code-char (bs_oemnamei 3 fat32-in-memory))
           (code-char (bs_oemnamei 4 fat32-in-memory))
           (code-char (bs_oemnamei 5 fat32-in-memory))
           (code-char (bs_oemnamei 6 fat32-in-memory))
           (code-char (bs_oemnamei 7 fat32-in-memory)))
     (list (code-char (loghead 8 (bpb_bytspersec fat32-in-memory)))
           (code-char (logtail 8 (bpb_bytspersec fat32-in-memory)))
           (code-char (bpb_secperclus fat32-in-memory))
           (code-char (loghead 8 (bpb_rsvdseccnt fat32-in-memory)))
           (code-char (logtail 8 (bpb_rsvdseccnt fat32-in-memory))))
     ;; remaining reserved bytes
     (list (code-char (bpb_numfats fat32-in-memory))
           (code-char (loghead 8 (bpb_rootentcnt fat32-in-memory)))
           (code-char (logtail 8 (bpb_rootentcnt fat32-in-memory)))
           (code-char (loghead 8 (bpb_totsec16 fat32-in-memory)))
           (code-char (logtail 8 (bpb_totsec16 fat32-in-memory)))
           (code-char (bpb_media fat32-in-memory))
           (code-char (loghead 8 (bpb_fatsz16 fat32-in-memory)))
           (code-char (logtail 8 (bpb_fatsz16 fat32-in-memory)))
           (code-char (loghead 8 (bpb_secpertrk fat32-in-memory)))
           (code-char (logtail 8 (bpb_secpertrk fat32-in-memory)))
           (code-char (loghead 8 (bpb_numheads fat32-in-memory)))
           (code-char (logtail 8 (bpb_numheads fat32-in-memory)))
           (code-char (loghead 8             (bpb_hiddsec fat32-in-memory) ))
           (code-char (loghead 8 (logtail  8 (bpb_hiddsec fat32-in-memory))))
           (code-char (loghead 8 (logtail 16 (bpb_hiddsec fat32-in-memory))))
           (code-char            (logtail 24 (bpb_hiddsec fat32-in-memory)) )
           (code-char (loghead 8             (bpb_totsec32 fat32-in-memory) ))
           (code-char (loghead 8 (logtail  8 (bpb_totsec32 fat32-in-memory))))
           (code-char (loghead 8 (logtail 16 (bpb_totsec32 fat32-in-memory))))
           (code-char            (logtail 24 (bpb_totsec32 fat32-in-memory)) )
           (code-char (loghead 8             (bpb_fatsz32 fat32-in-memory) ))
           (code-char (loghead 8 (logtail  8 (bpb_fatsz32 fat32-in-memory))))
           (code-char (loghead 8 (logtail 16 (bpb_fatsz32 fat32-in-memory))))
           (code-char            (logtail 24 (bpb_fatsz32 fat32-in-memory)) )
           (code-char (loghead 8 (bpb_extflags fat32-in-memory)))
           (code-char (logtail 8 (bpb_extflags fat32-in-memory)))
           (code-char (bpb_fsver_minor fat32-in-memory))
           (code-char (bpb_fsver_major fat32-in-memory))
           (code-char (loghead 8             (bpb_rootclus fat32-in-memory) ))
           (code-char (loghead 8 (logtail  8 (bpb_rootclus fat32-in-memory))))
           (code-char (loghead 8 (logtail 16 (bpb_rootclus fat32-in-memory))))
           (code-char            (logtail 24 (bpb_rootclus fat32-in-memory)) )
           (code-char (loghead 8 (bpb_fsinfo fat32-in-memory)))
           (code-char (logtail 8 (bpb_fsinfo fat32-in-memory)))
           (code-char (loghead 8 (bpb_bkbootsec fat32-in-memory)))
           (code-char (logtail 8 (bpb_bkbootsec fat32-in-memory))))
     (list (code-char (bpb_reservedi  0 fat32-in-memory))
           (code-char (bpb_reservedi  1 fat32-in-memory))
           (code-char (bpb_reservedi  2 fat32-in-memory))
           (code-char (bpb_reservedi  3 fat32-in-memory))
           (code-char (bpb_reservedi  4 fat32-in-memory))
           (code-char (bpb_reservedi  5 fat32-in-memory))
           (code-char (bpb_reservedi  6 fat32-in-memory))
           (code-char (bpb_reservedi  7 fat32-in-memory))
           (code-char (bpb_reservedi  8 fat32-in-memory))
           (code-char (bpb_reservedi  9 fat32-in-memory))
           (code-char (bpb_reservedi 10 fat32-in-memory))
           (code-char (bpb_reservedi 11 fat32-in-memory)))
     (list (code-char (bs_drvnum fat32-in-memory))
           (code-char (bs_reserved1 fat32-in-memory))
           (code-char (bs_bootsig fat32-in-memory))
           (code-char (loghead 8             (bs_volid fat32-in-memory) ))
           (code-char (loghead 8 (logtail  8 (bs_volid fat32-in-memory))))
           (code-char (loghead 8 (logtail 16 (bs_volid fat32-in-memory))))
           (code-char            (logtail 24 (bs_volid fat32-in-memory)) ))
     (list (code-char (bs_vollabi  0 fat32-in-memory))
           (code-char (bs_vollabi  1 fat32-in-memory))
           (code-char (bs_vollabi  2 fat32-in-memory))
           (code-char (bs_vollabi  3 fat32-in-memory))
           (code-char (bs_vollabi  4 fat32-in-memory))
           (code-char (bs_vollabi  5 fat32-in-memory))
           (code-char (bs_vollabi  6 fat32-in-memory))
           (code-char (bs_vollabi  7 fat32-in-memory))
           (code-char (bs_vollabi  8 fat32-in-memory))
           (code-char (bs_vollabi  9 fat32-in-memory))
           (code-char (bs_vollabi 10 fat32-in-memory)))
     (list (code-char (bs_filsystypei 0 fat32-in-memory))
           (code-char (bs_filsystypei 1 fat32-in-memory))
           (code-char (bs_filsystypei 2 fat32-in-memory))
           (code-char (bs_filsystypei 3 fat32-in-memory))
           (code-char (bs_filsystypei 4 fat32-in-memory))
           (code-char (bs_filsystypei 5 fat32-in-memory))
           (code-char (bs_filsystypei 6 fat32-in-memory))
           (code-char (bs_filsystypei 7 fat32-in-memory)))
     (make-list
      (- (* (bpb_rsvdseccnt fat32-in-memory) (bpb_bytspersec fat32-in-memory)) 90)
      :initial-element (code-char 0)))))

(defthm character-listp-of-reserved-area-chars
  (character-listp (reserved-area-chars fat32-in-memory))
  :hints (("Goal" :in-theory (enable reserved-area-chars))))

(defthm
  len-of-reserved-area-chars
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal (len (reserved-area-chars fat32-in-memory))
          (* (bpb_rsvdseccnt fat32-in-memory)
             (bpb_bytspersec fat32-in-memory))))
  :hints (("goal" :in-theory (enable reserved-area-chars))))

(defund
  reserved-area-string (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (lofat-fs-p fat32-in-memory)))
  (implode (reserved-area-chars fat32-in-memory)))

(defthm
  length-of-reserved-area-string
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal (len (explode (reserved-area-string fat32-in-memory)))
          (* (bpb_rsvdseccnt fat32-in-memory)
             (bpb_bytspersec fat32-in-memory))))
  :hints (("goal" :in-theory (enable reserved-area-string))))

;; This seems like the only way...
;; There is an automatic way to do this proof, but I can't recall it.
(defthm
  nth-of-explode-of-reserved-area-string
  (equal
   (nth n
        (explode (reserved-area-string fat32-in-memory)))
   (nth
    n
    (append
     (list (code-char (bs_jmpbooti 0 fat32-in-memory))
           (code-char (bs_jmpbooti 1 fat32-in-memory))
           (code-char (bs_jmpbooti 2 fat32-in-memory)))
     (list (code-char (bs_oemnamei 0 fat32-in-memory))
           (code-char (bs_oemnamei 1 fat32-in-memory))
           (code-char (bs_oemnamei 2 fat32-in-memory))
           (code-char (bs_oemnamei 3 fat32-in-memory))
           (code-char (bs_oemnamei 4 fat32-in-memory))
           (code-char (bs_oemnamei 5 fat32-in-memory))
           (code-char (bs_oemnamei 6 fat32-in-memory))
           (code-char (bs_oemnamei 7 fat32-in-memory)))
     (list (code-char (loghead 8 (bpb_bytspersec fat32-in-memory)))
           (code-char (logtail 8 (bpb_bytspersec fat32-in-memory)))
           (code-char (bpb_secperclus fat32-in-memory))
           (code-char (loghead 8 (bpb_rsvdseccnt fat32-in-memory)))
           (code-char (logtail 8 (bpb_rsvdseccnt fat32-in-memory))))
     (list (code-char (bpb_numfats fat32-in-memory))
           (code-char (loghead 8 (bpb_rootentcnt fat32-in-memory)))
           (code-char (logtail 8 (bpb_rootentcnt fat32-in-memory)))
           (code-char (loghead 8 (bpb_totsec16 fat32-in-memory)))
           (code-char (logtail 8 (bpb_totsec16 fat32-in-memory)))
           (code-char (bpb_media fat32-in-memory))
           (code-char (loghead 8 (bpb_fatsz16 fat32-in-memory)))
           (code-char (logtail 8 (bpb_fatsz16 fat32-in-memory)))
           (code-char (loghead 8 (bpb_secpertrk fat32-in-memory)))
           (code-char (logtail 8 (bpb_secpertrk fat32-in-memory)))
           (code-char (loghead 8 (bpb_numheads fat32-in-memory)))
           (code-char (logtail 8 (bpb_numheads fat32-in-memory)))
           (code-char (loghead 8 (bpb_hiddsec fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bpb_hiddsec fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bpb_hiddsec fat32-in-memory))))
           (code-char (logtail 24 (bpb_hiddsec fat32-in-memory)))
           (code-char (loghead 8 (bpb_totsec32 fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bpb_totsec32 fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bpb_totsec32 fat32-in-memory))))
           (code-char (logtail 24 (bpb_totsec32 fat32-in-memory)))
           (code-char (loghead 8 (bpb_fatsz32 fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bpb_fatsz32 fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bpb_fatsz32 fat32-in-memory))))
           (code-char (logtail 24 (bpb_fatsz32 fat32-in-memory)))
           (code-char (loghead 8 (bpb_extflags fat32-in-memory)))
           (code-char (logtail 8 (bpb_extflags fat32-in-memory)))
           (code-char (bpb_fsver_minor fat32-in-memory))
           (code-char (bpb_fsver_major fat32-in-memory))
           (code-char (loghead 8 (bpb_rootclus fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bpb_rootclus fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bpb_rootclus fat32-in-memory))))
           (code-char (logtail 24 (bpb_rootclus fat32-in-memory)))
           (code-char (loghead 8 (bpb_fsinfo fat32-in-memory)))
           (code-char (logtail 8 (bpb_fsinfo fat32-in-memory)))
           (code-char (loghead 8 (bpb_bkbootsec fat32-in-memory)))
           (code-char (logtail 8 (bpb_bkbootsec fat32-in-memory))))
     (list (code-char (bpb_reservedi 0 fat32-in-memory))
           (code-char (bpb_reservedi 1 fat32-in-memory))
           (code-char (bpb_reservedi 2 fat32-in-memory))
           (code-char (bpb_reservedi 3 fat32-in-memory))
           (code-char (bpb_reservedi 4 fat32-in-memory))
           (code-char (bpb_reservedi 5 fat32-in-memory))
           (code-char (bpb_reservedi 6 fat32-in-memory))
           (code-char (bpb_reservedi 7 fat32-in-memory))
           (code-char (bpb_reservedi 8 fat32-in-memory))
           (code-char (bpb_reservedi 9 fat32-in-memory))
           (code-char (bpb_reservedi 10 fat32-in-memory))
           (code-char (bpb_reservedi 11 fat32-in-memory)))
     (list (code-char (bs_drvnum fat32-in-memory))
           (code-char (bs_reserved1 fat32-in-memory))
           (code-char (bs_bootsig fat32-in-memory))
           (code-char (loghead 8 (bs_volid fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bs_volid fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bs_volid fat32-in-memory))))
           (code-char (logtail 24 (bs_volid fat32-in-memory))))
     (list (code-char (bs_vollabi 0 fat32-in-memory))
           (code-char (bs_vollabi 1 fat32-in-memory))
           (code-char (bs_vollabi 2 fat32-in-memory))
           (code-char (bs_vollabi 3 fat32-in-memory))
           (code-char (bs_vollabi 4 fat32-in-memory))
           (code-char (bs_vollabi 5 fat32-in-memory))
           (code-char (bs_vollabi 6 fat32-in-memory))
           (code-char (bs_vollabi 7 fat32-in-memory))
           (code-char (bs_vollabi 8 fat32-in-memory))
           (code-char (bs_vollabi 9 fat32-in-memory))
           (code-char (bs_vollabi 10 fat32-in-memory)))
     (list (code-char (bs_filsystypei 0 fat32-in-memory))
           (code-char (bs_filsystypei 1 fat32-in-memory))
           (code-char (bs_filsystypei 2 fat32-in-memory))
           (code-char (bs_filsystypei 3 fat32-in-memory))
           (code-char (bs_filsystypei 4 fat32-in-memory))
           (code-char (bs_filsystypei 5 fat32-in-memory))
           (code-char (bs_filsystypei 6 fat32-in-memory))
           (code-char (bs_filsystypei 7 fat32-in-memory)))
     (make-list (- (* (bpb_rsvdseccnt fat32-in-memory)
                      (bpb_bytspersec fat32-in-memory))
                   90)
                :initial-element (code-char 0)))))
  :instructions ((:dive 1 2 1)
                 :x
                 :up (:rewrite str::explode-of-implode)
                 :s (:rewrite str::make-character-list-when-character-listp)
                 :x :top
                 :bash :bash))

;; A bit of explanation is in order here - this function recurs on n, which is
;; instantiated with (bpb_numfats fat32-in-memory) in
;; lofat-to-string. stobj-fa-table-to-string, in contrast, generates
;; one copy of the FAT string from the fat32-in-memory instance, and does all
;; the part-select heavy lifting.
(defund
  make-fat-string-ac
  (n fat32-in-memory ac)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (natp n)
                (stringp ac))))
  (b* (((when (zp n)) ac)
       (fa-table-string
        (stobj-fa-table-to-string fat32-in-memory)))
    (make-fat-string-ac (1- n)
                        fat32-in-memory
                        (concatenate 'string
                                     fa-table-string ac))))

(defthm
  length-of-stobj-fa-table-to-string
  (equal
   (len
    (explode (stobj-fa-table-to-string fat32-in-memory)))
   (* (fat-length fat32-in-memory) 4))
  :hints (("goal" :in-theory (enable stobj-fa-table-to-string))))

(defthm
  length-of-make-fat-string-ac
  (equal
   (len (explode (make-fat-string-ac n fat32-in-memory ac)))
   (+ (* (nfix n)
         (fat-length fat32-in-memory)
         4)
      (len (explode ac))))
  :hints (("Goal" :in-theory (enable make-fat-string-ac))))

(defun
    data-region-string-helper
    (fat32-in-memory len ac)
  (declare
   (xargs
    :stobjs (fat32-in-memory)
    :guard (and (natp len)
                (lofat-fs-p fat32-in-memory)
                (<= len
                    (data-region-length fat32-in-memory))
                (character-listp ac))))
  (if
      (zp len)
      (mbe :exec ac
           :logic (make-character-list ac))
    (data-region-string-helper
     fat32-in-memory (- len 1)
     (append
      (mbe :exec (coerce (data-regioni (- len 1) fat32-in-memory)
                         'list)
           :logic (take (cluster-size fat32-in-memory)
                        (coerce (data-regioni (- len 1) fat32-in-memory)
                                'list)))
      ac))))

(defthm
  character-listp-of-data-region-string-helper
  (character-listp
   (data-region-string-helper fat32-in-memory len ac))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (equal
     (make-character-list
      (data-region-string-helper fat32-in-memory len ac))
     (data-region-string-helper fat32-in-memory len ac)))
   (:type-prescription
    :corollary
    (true-listp
     (data-region-string-helper fat32-in-memory len ac)))))

(defthm
  len-of-data-region-string-helper
  (equal
   (len (data-region-string-helper fat32-in-memory len ac))
   (+ (len ac)
      (* (nfix len)
         (nfix (cluster-size fat32-in-memory))))))

;; Later
;; (thm
;;  (implies
;;   (and (natp len)
;;        (lofat-fs-p fat32-in-memory)
;;        (<= len
;;            (data-region-length fat32-in-memory))
;;        (character-listp ac))
;;   (equal
;;    (make-clusters
;;     (implode
;;      (data-region-string-helper
;;       fat32-in-memory len ac))
;;     (cluster-size fat32-in-memory))
;;    (append
;;     (take
;;      len
;;      (nth *data-regioni* fat32-in-memory))
;;     (make-clusters
;;      (implode ac)
;;      (cluster-size fat32-in-memory)))))
;;  :hints (("Goal" :in-theory (enable make-clusters remember-that-time-with-update-nth
;;                                     append-of-take-and-cons)
;;           :induct
;;           (data-region-string-helper fat32-in-memory len ac))
;;          ("Subgoal *1/2.2"
;;           :expand
;;           (make-clusters
;;            (implode (append (take (cluster-size fat32-in-memory)
;;                                   (explode (data-regioni (+ -1 len)
;;                                                          fat32-in-memory)))
;;                             ac))
;;            (cluster-size fat32-in-memory))
;;           :use
;;           (:theorem
;;            (equal
;;             (+ (CLUSTER-SIZE FAT32-IN-MEMORY)
;;                (- (CLUSTER-SIZE FAT32-IN-MEMORY))
;;                (LEN AC))
;;             (len ac))))))

(defun
    princ$-data-region-string-helper
    (fat32-in-memory len channel state)
  (declare
   (xargs
    :stobjs (fat32-in-memory state)
    :guard (and (natp len)
                (lofat-fs-p fat32-in-memory)
                (<= len
                    (data-region-length fat32-in-memory))
                (symbolp channel)
                (open-output-channel-p channel
                                       :character state))
    :verify-guards nil))
  (b*
      (((when (zp len)) state)
       (state
        (princ$-data-region-string-helper
         fat32-in-memory (- len 1)
         channel
         state)))
    (princ$ (data-regioni (- len 1) fat32-in-memory) channel state)))

(defthm
  princ$-data-region-string-helper-guard-lemma-1
  (implies
   (and (open-output-channel-p1 channel
                                :character state)
        (symbolp channel)
        (state-p1 state))
   (and
    (open-output-channel-p1
     channel
     :character
     (princ$-data-region-string-helper fat32-in-memory len channel state))
    (state-p1
     (princ$-data-region-string-helper fat32-in-memory len channel state))))
  :hints
  (("goal"
    :induct
    (princ$-data-region-string-helper fat32-in-memory len channel state))))

(verify-guards
  princ$-data-region-string-helper)

(defthm
  data-region-string-helper-of-binary-append
  (implies
   (and (natp len)
        (lofat-fs-p fat32-in-memory)
        (<= len
            (data-region-length fat32-in-memory))
        (character-listp ac1)
        (character-listp ac2))
   (equal
    (data-region-string-helper fat32-in-memory
                               len (binary-append ac1 ac2))
    (binary-append
     (data-region-string-helper fat32-in-memory len ac1)
     ac2))))

(defthm
  princ$-data-region-string-helper-correctness-1
  (implies
   (and (natp len)
        (lofat-fs-p fat32-in-memory)
        (<= len
            (data-region-length fat32-in-memory))
        (character-listp ac))
   (equal
    (princ$
     (coerce (data-region-string-helper fat32-in-memory len ac)
             'string)
     channel state)
    (princ$ (coerce ac 'string)
            channel
            (princ$-data-region-string-helper
             fat32-in-memory len channel state)))))

(defund
  lofat-to-string
  (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (lofat-fs-p fat32-in-memory)))
  (b* ((reserved-area-string
        (reserved-area-string fat32-in-memory))
       (fat-string
        (make-fat-string-ac (bpb_numfats fat32-in-memory)
                            fat32-in-memory ""))
       (data-region-string
        (coerce (data-region-string-helper
                 fat32-in-memory
                 (data-region-length fat32-in-memory)
                 nil)
                'string)))
    (concatenate 'string
                 reserved-area-string
                 fat-string data-region-string)))

(defthm
  length-of-lofat-to-string-lemma-1
  (implies (lofat-fs-p fat32-in-memory)
           (and
           (equal (nfix (bpb_numfats fat32-in-memory))
                  (bpb_numfats fat32-in-memory))
           (equal (nfix (count-of-clusters fat32-in-memory))
                  (count-of-clusters fat32-in-memory))))
  :hints (("goal" :in-theory (enable lofat-fs-p
                                     fat32-in-memoryp
                                     bpb_numfats))))

(defthm
  length-of-lofat-to-string
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal
    (len
     (explode (lofat-to-string fat32-in-memory)))
    (+ (* (bpb_rsvdseccnt fat32-in-memory)
          (bpb_bytspersec fat32-in-memory))
       (* (bpb_numfats fat32-in-memory)
          (fat-length fat32-in-memory)
          4)
       (* (cluster-size fat32-in-memory)
          (data-region-length fat32-in-memory)))))
  :hints
  (("goal" :in-theory (e/d (lofat-to-string) (nfix)))))

(defun
  lofat-to-disk-image
  (fat32-in-memory image-path state)
  (declare
   (xargs
    :stobjs (fat32-in-memory state)
    :guard (and (state-p state)
                (stringp image-path)
                (lofat-fs-p fat32-in-memory))
    :guard-hints
    (("goal"
      :in-theory
      (e/d (lofat-to-string)
           (princ$-of-princ$
            princ$-data-region-string-helper-correctness-1))
      :use
      ((:instance
        princ$-of-princ$
        (state
         (mv-nth '1
                 (open-output-channel image-path ':character
                                      state)))
        (x (reserved-area-string fat32-in-memory))
        (channel
         (mv-nth '0
                 (open-output-channel image-path ':character
                                      state)))
        (y (make-fat-string-ac (bpb_numfats fat32-in-memory)
                               fat32-in-memory '"")))
       (:instance
        princ$-of-princ$
        (state
         (mv-nth '1
                 (open-output-channel image-path ':character
                                      state)))
        (x
         (string-append
          (reserved-area-string fat32-in-memory)
          (make-fat-string-ac (bpb_numfats fat32-in-memory)
                              fat32-in-memory "")))
        (channel
         (mv-nth '0
                 (open-output-channel image-path ':character
                                      state)))
        (y (implode$inline
            (data-region-string-helper
             fat32-in-memory
             (data-region-length fat32-in-memory)
             'nil))))
       (:instance
        princ$-data-region-string-helper-correctness-1
        (ac nil)
        (len (data-region-length fat32-in-memory))
        (state
         (princ$
          (implode
           (append
            (explode (reserved-area-string fat32-in-memory))
            (explode
             (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                 fat32-in-memory ""))))
          (mv-nth 0
                  (open-output-channel image-path
                                       :character state))
          (mv-nth 1
                  (open-output-channel image-path
                                       :character state))))
        (channel
         (mv-nth 0
                 (open-output-channel image-path
                                      :character state)))))))))
  (b*
      (((mv channel state)
        (open-output-channel image-path
                             :character state))
       ((when (null channel)) (mv state *EIO*))
       (state
        (mbe
         :logic (princ$ (lofat-to-string fat32-in-memory)
                        channel state)
         :exec
         (b*
             ((state (princ$ (reserved-area-string fat32-in-memory)
                             channel state))
              (state
               (princ$
                (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                    fat32-in-memory "")
                channel state))
              (state (princ$-data-region-string-helper
                      fat32-in-memory
                      (data-region-length fat32-in-memory)
                      channel state)))
           (princ$ "" channel state))))
       (state (close-output-channel channel state)))
    (mv state 0)))

(defthm
  lofat-to-string-inversion-lemma-1
  (implies
   (and (< (nfix n)
           (* (bpb_rsvdseccnt fat32-in-memory)
              (bpb_bytspersec fat32-in-memory)))
        (lofat-fs-p fat32-in-memory))
   (equal
    (nth
     n
     (append
      (explode (reserved-area-string fat32-in-memory))
      (explode (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                   fat32-in-memory ""))
      (data-region-string-helper
       fat32-in-memory
       (count-of-clusters fat32-in-memory)
       nil)))
    (nth n
         (explode (reserved-area-string fat32-in-memory))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    lofat-to-string-inversion-lemma-2
    (implies (fat32-in-memoryp fat32-in-memory)
             (>= (+ (data-region-length fat32-in-memory)
                    (* (bpb_bytspersec fat32-in-memory)
                       (bpb_rsvdseccnt fat32-in-memory))
                    (* (bpb_numfats fat32-in-memory)
                       4 (fat-length fat32-in-memory)))
                 (* (bpb_bytspersec fat32-in-memory)
                    (bpb_rsvdseccnt fat32-in-memory))))
    :hints
    (("goal" :in-theory (enable bpb_numfats fat32-in-memoryp)))
    :rule-classes :linear)

  (defthm
    lofat-to-string-inversion-lemma-3
    (implies (equal (* (bpb_fatsz32 fat32-in-memory)
                       1/4 (bpb_bytspersec fat32-in-memory))
                    (fat-length fat32-in-memory))
             (equal (* (bpb_bytspersec fat32-in-memory)
                       (bpb_fatsz32 fat32-in-memory)
                       (bpb_numfats fat32-in-memory))
                    (* (bpb_numfats fat32-in-memory)
                       4 (fat-length fat32-in-memory))))))

(encapsulate
  ()

  (local
   (in-theory (e/d (lofat-to-string get-initial-bytes get-remaining-rsvdbyts)
                   (;; the splitter-note suggests these could usefully be
                    ;; disabled
                    nth-of-append nthcdr-of-append take-of-append))))

  (defthm
    lofat-to-string-inversion-lemma-4
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth 11
            (get-initial-bytes
             (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_bytspersec fat32-in-memory)))
      (equal
       (nth 12
            (get-initial-bytes
             (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_bytspersec fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-5
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth 13
           (get-initial-bytes
            (lofat-to-string fat32-in-memory)))
      (bpb_secperclus fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-6
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth 14
            (get-initial-bytes
             (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_rsvdseccnt fat32-in-memory)))
      (equal
       (nth 15
            (get-initial-bytes
             (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_rsvdseccnt fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-7
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth 0
           (get-remaining-rsvdbyts
            (lofat-to-string fat32-in-memory)))
      (bpb_numfats fat32-in-memory)))
    :hints
    (("goal" :in-theory (e/d (string=>nats) (nth)))))

  (defthm
    lofat-to-string-inversion-lemma-8
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        1
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_rootentcnt fat32-in-memory)))
      (equal
       (nth
        2
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_rootentcnt fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-9
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        3
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_totsec16 fat32-in-memory)))
      (equal
       (nth
        4
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_totsec16 fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-10
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth
       5
       (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
      (bpb_media fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-11
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        6
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_fatsz16 fat32-in-memory)))
      (equal
       (nth
        7
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_fatsz16 fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-12
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        8
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_secpertrk fat32-in-memory)))
      (equal
       (nth
        9
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_secpertrk fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-13
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        10
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_numheads fat32-in-memory)))
      (equal
       (nth
        11
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_numheads fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-14
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        12
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_hiddsec fat32-in-memory)))
      (equal
       (nth
        13
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bpb_hiddsec fat32-in-memory))))
      (equal
       (nth
        14
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_hiddsec fat32-in-memory))))
      (equal
       (nth
        15
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 24 (bpb_hiddsec fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-15
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        16
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_totsec32 fat32-in-memory)))
      (equal
       (nth
        17
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bpb_totsec32 fat32-in-memory))))
      (equal
       (nth
        18
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_totsec32 fat32-in-memory))))
      (equal
       (nth
        19
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 24 (bpb_totsec32 fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-16
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        20
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_fatsz32 fat32-in-memory)))
      (equal
       (nth
        21
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail 8 (bpb_fatsz32 fat32-in-memory))))
      (equal
       (nth
        22
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_fatsz32 fat32-in-memory))))
      (equal
       (nth
        23
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 24 (bpb_fatsz32 fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-17
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        24
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_extflags fat32-in-memory)))
      (equal
       (nth
        25
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_extflags fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-18
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth
       26
       (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
      (bpb_fsver_minor fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-19
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth
       27
       (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
      (bpb_fsver_major fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-20
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        28
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_rootclus fat32-in-memory)))
      (equal
       (nth
        29
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bpb_rootclus fat32-in-memory))))
      (equal
       (nth
        30
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_rootclus fat32-in-memory))))
      (equal
       (nth
        31
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 24 (bpb_rootclus fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-21
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        32
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_fsinfo fat32-in-memory)))
      (equal
       (nth
        33
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_fsinfo fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-22
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        34
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_bkbootsec fat32-in-memory)))
      (equal
       (nth
        35
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_bkbootsec fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-23
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth
       48
       (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
      (bs_drvnum fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-24
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth
       49
       (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
      (bs_reserved1 fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-25
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth
       50
       (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
      (bs_bootsig fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-26
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        51
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bs_volid fat32-in-memory)))
      (equal
       (nth
        52
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bs_volid fat32-in-memory))))
      (equal
       (nth
        53
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bs_volid fat32-in-memory))))
      (equal
       (nth
        54
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 24 (bs_volid fat32-in-memory)))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    lofat-to-string-inversion-lemma-27
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (natp index)
          (< index
             (data-region-length fat32-in-memory)))
     (equal
      (take
       (cluster-size fat32-in-memory)
       (nthcdr
        (* (cluster-size fat32-in-memory) index)
        (data-region-string-helper fat32-in-memory len ac)))
      (if (< index (nfix len))
          (coerce (data-regioni index fat32-in-memory)
                  'list)
        (take (cluster-size fat32-in-memory)
              (nthcdr (* (cluster-size fat32-in-memory)
                         (- index (nfix len)))
                      (make-character-list ac)))))))

  (defthm
    lofat-to-string-inversion-lemma-29
    (implies (and (fat32-in-memoryp fat32-in-memory)
                  (<= 512 (bpb_bytspersec fat32-in-memory))
                  (<= 1 (bpb_secperclus fat32-in-memory))
                  (> (+ (- (bpb_rsvdseccnt fat32-in-memory))
                        (bpb_totsec32 fat32-in-memory)
                        (- (* (bpb_fatsz32 fat32-in-memory)
                              (bpb_numfats fat32-in-memory))))
                     (bpb_secperclus fat32-in-memory)))
             (> (* (bpb_bytspersec fat32-in-memory)
                   (bpb_secperclus fat32-in-memory)
                   (floor (+ (- (bpb_rsvdseccnt fat32-in-memory))
                             (bpb_totsec32 fat32-in-memory)
                             (- (* (bpb_fatsz32 fat32-in-memory)
                                   (bpb_numfats fat32-in-memory))))
                          (bpb_secperclus fat32-in-memory)))
                0))
    :rule-classes :linear
    :hints
    (("goal" :in-theory (disable painful-debugging-lemma-15)
      :use (:instance painful-debugging-lemma-15
                      (i (+ (- (bpb_rsvdseccnt fat32-in-memory))
                            (bpb_totsec32 fat32-in-memory)
                            (- (* (bpb_fatsz32 fat32-in-memory)
                                  (bpb_numfats fat32-in-memory)))))
                      (j (bpb_secperclus fat32-in-memory))))))

  (defthm lofat-to-string-inversion-lemma-31
    (implies (lofat-fs-p fat32-in-memory)
             (<=
              (* 4 (fat-length fat32-in-memory))
              (* (bpb_numfats fat32-in-memory)
                 4 (fat-length fat32-in-memory))))
    :rule-classes :linear)

  (defthm lofat-to-string-inversion-lemma-32
    (implies (and (not (zp len))
                  (< (* (cluster-size fat32-in-memory)
                        (count-of-clusters fat32-in-memory))
                     (+ (cluster-size fat32-in-memory)
                        (* (cluster-size fat32-in-memory)
                           (count-of-clusters fat32-in-memory))
                        (* (cluster-size fat32-in-memory)
                           (- len))))
                  (lofat-fs-p fat32-in-memory))
             (< (count-of-clusters fat32-in-memory)
                len))
    :rule-classes :linear))

(defthm
  lofat-to-string-inversion-lemma-28
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (natp len)
        (<= len
            (data-region-length fat32-in-memory)))
   (equal (update-data-region
           fat32-in-memory
           (implode (data-region-string-helper
                     fat32-in-memory
                     (count-of-clusters fat32-in-memory)
                     nil))
           len)
          (mv
           fat32-in-memory
           0)))
  :hints
  (("goal" :in-theory (disable data-region-string-helper)
    :induct
    (update-data-region
     fat32-in-memory
     (implode (data-region-string-helper fat32-in-memory
                                         (count-of-clusters fat32-in-memory)
                                         nil))
     len))
   ("subgoal *1/2"
    :in-theory
    (disable lofat-to-string-inversion-lemma-27)
    :use
    (:instance lofat-to-string-inversion-lemma-27
               (index (- (count-of-clusters fat32-in-memory)
                         len))
               (len (count-of-clusters fat32-in-memory))
               (ac nil)))))

(defthm
  lofat-to-string-inversion-lemma-35
  (implies
   (and (natp n2)
        (< n2 (* 4 (fat-length fat32-in-memory)))
        (not (zp n1)))
   (equal
    (nth n2
         (explode (make-fat-string-ac n1 fat32-in-memory ac)))
    (nth n2
         (explode (stobj-fa-table-to-string
                   fat32-in-memory)))))
  :hints (("Goal" :in-theory (enable make-fat-string-ac))))

(defthm
  lofat-to-string-inversion-lemma-36
  (implies
   (fat32-entry-p current)
   (equal
    (unsigned-byte-p 8
                     (nth n
                          (list (loghead 8 current)
                                (loghead 8 (logtail 8 current))
                                (loghead 8 (logtail 16 current))
                                (logtail 24 current))))
    (< (nfix n) 4)))
  :hints (("goal" :in-theory (e/d (fat32-entry-p)
                                  (unsigned-byte-p))))
  :rule-classes
  ((:linear
    :corollary
    (implies
     (and (fat32-entry-p current)
          (< (nfix n) 4))
     (and (<= 0
              (nth n
                   (list (loghead 8 current)
                         (loghead 8 (logtail 8 current))
                         (loghead 8 (logtail 16 current))
                         (logtail 24 current))))
          (< (nth n
                  (list (loghead 8 current)
                        (loghead 8 (logtail 8 current))
                        (loghead 8 (logtail 16 current))
                        (logtail 24 current)))
             256))))
   (:rewrite
    :corollary
    (implies
     (and (fat32-entry-p current)
          (< (nfix n) 4))
     (integerp (nth n
                    (list (loghead 8 current)
                          (loghead 8 (logtail 8 current))
                          (loghead 8 (logtail 16 current))
                          (logtail 24 current))))))))

(defthm
  lofat-to-string-inversion-lemma-37
  (implies (and (integerp pos)
                (integerp length)
                (<= pos length))
           (and (iff (< (+ -1 (* 4 pos)) (+ -4 (* 4 length)))
                     (not (equal pos length)))
                (iff (< (+ -2 (* 4 pos)) (+ -4 (* 4 length)))
                     (not (equal pos length)))
                (iff (< (+ -3 (* 4 pos)) (+ -4 (* 4 length)))
                     (not (equal pos length)))
                (iff (< (+ -4 (* 4 pos)) (+ -4 (* 4 length)))
                     (not (equal pos length))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    lofat-to-string-inversion-lemma-38
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (not (zp pos))
          (natp length))
     (and
      (equal (nth (+ -1 (* 4 pos))
                  (stobj-fa-table-to-string-helper fat32-in-memory
                                                   length
                                                   ac))
             (if (zp (- pos length))
                 (code-char (logtail 24 (fati (+ -1 pos) fat32-in-memory)))
               (nth (+ -1 (* 4 (- pos length))) ac)))
      (equal (nth (+ -2 (* 4 pos))
                  (stobj-fa-table-to-string-helper fat32-in-memory
                                                   length
                                                   ac))
             (if (zp (- pos length))
                 (code-char (loghead 8
                                     (logtail 16
                                              (fati (+ -1 pos) fat32-in-memory))))
               (nth (+ -2 (* 4 (- pos length))) ac)))
      (equal (nth (+ -3 (* 4 pos))
                  (stobj-fa-table-to-string-helper fat32-in-memory
                                                   length
                                                   ac))
             (if (zp (- pos length))
                 (code-char (loghead 8
                                     (logtail 8 (fati (+ -1 pos) fat32-in-memory))))
               (nth (+ -3 (* 4 (- pos length))) ac)))
      (equal (nth (+ -4 (* 4 pos))
                  (stobj-fa-table-to-string-helper fat32-in-memory
                                                   length
                                                   ac))
             (if (zp (- pos length))
                 (code-char (loghead 8 (fati (+ -1 pos) fat32-in-memory)))
               (nth (+ -4 (* 4 (- pos length))) ac)))))
    :hints (("goal"
             :induct
             (stobj-fa-table-to-string-helper fat32-in-memory
                                              length
                                              ac)
              :expand (:free (n x y) (nth n (cons x y)))))))

(defthm
  lofat-to-string-inversion-lemma-39
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (not (zp pos))
        (<= pos (fat-length fat32-in-memory)))
   (and
    (equal
     (nth
      (+ -1 (* 4 pos))
      (explode
       (stobj-fa-table-to-string fat32-in-memory)))
     (code-char (logtail 24 (fati (- pos 1) fat32-in-memory))))
    (equal
     (nth
      (+ -2 (* 4 pos))
      (explode
       (stobj-fa-table-to-string fat32-in-memory)))
     (code-char
      (loghead 8
               (logtail 16 (fati (- pos 1) fat32-in-memory)))))
    (equal
     (nth
      (+ -3 (* 4 pos))
      (explode
       (stobj-fa-table-to-string fat32-in-memory)))
     (code-char
      (loghead 8
               (logtail 8 (fati (- pos 1) fat32-in-memory)))))
    (equal
     (nth
      (+ -4 (* 4 pos))
      (explode
       (stobj-fa-table-to-string fat32-in-memory)))
     (code-char (loghead 8 (fati (- pos 1) fat32-in-memory))))))
  :hints (("goal" :in-theory (enable stobj-fa-table-to-string))))

(defthm
  lofat-to-string-inversion-lemma-41
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (not (zp pos))
        (<= pos (fat-length fat32-in-memory)))
   (equal (update-fat
           fat32-in-memory
           (make-fat-string-ac (bpb_numfats fat32-in-memory)
                               fat32-in-memory "")
           pos)
          fat32-in-memory))
  :hints
  (("goal"
    :induct
    (update-fat
     fat32-in-memory
     (make-fat-string-ac (bpb_numfats fat32-in-memory)
                         fat32-in-memory "")
     pos))
   ("subgoal *1/3"
    :in-theory
    (disable lofat-to-string-inversion-lemma-39)
    :use (:instance lofat-to-string-inversion-lemma-39
                    (pos 1)))))

(defthm
  lofat-to-string-inversion-lemma-50
  (implies (lofat-fs-p fat32-in-memory)
           (> (* (bpb_numfats fat32-in-memory)
                 4 (fat-entry-count fat32-in-memory))
              0))
  :hints
  (("goal" :in-theory
    (disable lofat-fs-p-correctness-1)
    :use lofat-fs-p-correctness-1))
  :rule-classes :linear)

(encapsulate
  ()

  (local (in-theory (disable bs_jmpbooti update-bs_jmpbooti
                             bs_oemnamei bpb_reservedi bs_vollabi
                             bs_filsystypei)))

  (defthm
    lofat-to-string-inversion-lemma-42
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (chars=>nats (explode (reserved-area-string fat32-in-memory)))
      (append
       ;; initial bytes
       (list (bs_jmpbooti 0 fat32-in-memory)
             (bs_jmpbooti 1 fat32-in-memory)
             (bs_jmpbooti 2 fat32-in-memory))
       (list (bs_oemnamei 0 fat32-in-memory)
             (bs_oemnamei 1 fat32-in-memory)
             (bs_oemnamei 2 fat32-in-memory)
             (bs_oemnamei 3 fat32-in-memory)
             (bs_oemnamei 4 fat32-in-memory)
             (bs_oemnamei 5 fat32-in-memory)
             (bs_oemnamei 6 fat32-in-memory)
             (bs_oemnamei 7 fat32-in-memory))
       (list (loghead 8 (bpb_bytspersec fat32-in-memory))
             (logtail 8 (bpb_bytspersec fat32-in-memory))
             (bpb_secperclus fat32-in-memory)
             (loghead 8 (bpb_rsvdseccnt fat32-in-memory))
             (logtail 8 (bpb_rsvdseccnt fat32-in-memory)))
       ;; remaining reserved bytes
       (list (bpb_numfats fat32-in-memory)
             (loghead 8 (bpb_rootentcnt fat32-in-memory))
             (logtail 8 (bpb_rootentcnt fat32-in-memory))
             (loghead 8 (bpb_totsec16 fat32-in-memory))
             (logtail 8 (bpb_totsec16 fat32-in-memory))
             (bpb_media fat32-in-memory)
             (loghead 8 (bpb_fatsz16 fat32-in-memory))
             (logtail 8 (bpb_fatsz16 fat32-in-memory))
             (loghead 8 (bpb_secpertrk fat32-in-memory))
             (logtail 8 (bpb_secpertrk fat32-in-memory))
             (loghead 8 (bpb_numheads fat32-in-memory))
             (logtail 8 (bpb_numheads fat32-in-memory))
             (loghead 8             (bpb_hiddsec fat32-in-memory) )
             (loghead 8 (logtail  8 (bpb_hiddsec fat32-in-memory)))
             (loghead 8 (logtail 16 (bpb_hiddsec fat32-in-memory)))
             (logtail 24 (bpb_hiddsec fat32-in-memory) )
             (loghead 8             (bpb_totsec32 fat32-in-memory) )
             (loghead 8 (logtail  8 (bpb_totsec32 fat32-in-memory)))
             (loghead 8 (logtail 16 (bpb_totsec32 fat32-in-memory)))
             (logtail 24 (bpb_totsec32 fat32-in-memory) )
             (loghead 8             (bpb_fatsz32 fat32-in-memory) )
             (loghead 8 (logtail  8 (bpb_fatsz32 fat32-in-memory)))
             (loghead 8 (logtail 16 (bpb_fatsz32 fat32-in-memory)))
             (logtail 24 (bpb_fatsz32 fat32-in-memory) )
             (loghead 8 (bpb_extflags fat32-in-memory))
             (logtail 8 (bpb_extflags fat32-in-memory))
             (bpb_fsver_minor fat32-in-memory)
             (bpb_fsver_major fat32-in-memory)
             (loghead 8             (bpb_rootclus fat32-in-memory) )
             (loghead 8 (logtail  8 (bpb_rootclus fat32-in-memory)))
             (loghead 8 (logtail 16 (bpb_rootclus fat32-in-memory)))
             (logtail 24 (bpb_rootclus fat32-in-memory) )
             (loghead 8 (bpb_fsinfo fat32-in-memory))
             (logtail 8 (bpb_fsinfo fat32-in-memory))
             (loghead 8 (bpb_bkbootsec fat32-in-memory))
             (logtail 8 (bpb_bkbootsec fat32-in-memory)))
       (list (bpb_reservedi  0 fat32-in-memory)
             (bpb_reservedi  1 fat32-in-memory)
             (bpb_reservedi  2 fat32-in-memory)
             (bpb_reservedi  3 fat32-in-memory)
             (bpb_reservedi  4 fat32-in-memory)
             (bpb_reservedi  5 fat32-in-memory)
             (bpb_reservedi  6 fat32-in-memory)
             (bpb_reservedi  7 fat32-in-memory)
             (bpb_reservedi  8 fat32-in-memory)
             (bpb_reservedi  9 fat32-in-memory)
             (bpb_reservedi 10 fat32-in-memory)
             (bpb_reservedi 11 fat32-in-memory))
       (list (bs_drvnum fat32-in-memory)
             (bs_reserved1 fat32-in-memory)
             (bs_bootsig fat32-in-memory)
             (loghead 8             (bs_volid fat32-in-memory) )
             (loghead 8 (logtail  8 (bs_volid fat32-in-memory)))
             (loghead 8 (logtail 16 (bs_volid fat32-in-memory)))
             (logtail 24 (bs_volid fat32-in-memory) ))
       (list (bs_vollabi  0 fat32-in-memory)
             (bs_vollabi  1 fat32-in-memory)
             (bs_vollabi  2 fat32-in-memory)
             (bs_vollabi  3 fat32-in-memory)
             (bs_vollabi  4 fat32-in-memory)
             (bs_vollabi  5 fat32-in-memory)
             (bs_vollabi  6 fat32-in-memory)
             (bs_vollabi  7 fat32-in-memory)
             (bs_vollabi  8 fat32-in-memory)
             (bs_vollabi  9 fat32-in-memory)
             (bs_vollabi 10 fat32-in-memory))
       (list (bs_filsystypei 0 fat32-in-memory)
             (bs_filsystypei 1 fat32-in-memory)
             (bs_filsystypei 2 fat32-in-memory)
             (bs_filsystypei 3 fat32-in-memory)
             (bs_filsystypei 4 fat32-in-memory)
             (bs_filsystypei 5 fat32-in-memory)
             (bs_filsystypei 6 fat32-in-memory)
             (bs_filsystypei 7 fat32-in-memory))
       (make-list
        (- (* (bpb_rsvdseccnt fat32-in-memory) (bpb_bytspersec fat32-in-memory)) 90)
        :initial-element 0))))
    :hints (("Goal" :in-theory (e/d (chars=>nats reserved-area-string
                                                 reserved-area-chars)
                                    (unsigned-byte-p)))))

  (local (in-theory (enable chars=>nats-of-take get-initial-bytes
                            lofat-to-string)))

  (defthm
    lofat-to-string-inversion-lemma-43
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (update-bs_jmpboot
       (take 3
             (get-initial-bytes
              (lofat-to-string fat32-in-memory)))
       fat32-in-memory)
      fat32-in-memory)))

  (defthm
    lofat-to-string-inversion-lemma-44
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (update-bs_oemname
       (take
        8
        (nthcdr
         3
         (get-initial-bytes
          (lofat-to-string fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory)))

  (local (in-theory (enable chars=>nats-of-nthcdr get-remaining-rsvdbyts)))

  (defthm
    lofat-to-string-inversion-lemma-45
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (update-bs_vollab
       (take
        11
        (nthcdr
         55
         (get-remaining-rsvdbyts
          (lofat-to-string fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory)))

  (defthm
    lofat-to-string-inversion-lemma-46
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (update-bs_filsystype
       (take
        8
        (nthcdr
         66
         (get-remaining-rsvdbyts
          (lofat-to-string fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory)))

  ;; Kinda wish we could have made use of update_bpb_reserved-alt for this
  ;; theorem, and then done the same kind of thing elsewhere.
  (defthm
    lofat-to-string-inversion-lemma-40
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (update-bpb_reserved
       (take 12
             (nthcdr 36
                     (get-remaining-rsvdbyts
                      (lofat-to-string fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory))))

(defthm
  lofat-to-string-inversion-lemma-47
  (implies
   (and (natp n2)
        (zp (+ n2
               (- (* 4 (fat-length fat32-in-memory)))))
        (not (zp n1)))
   (equal
    (take n2
          (explode (make-fat-string-ac n1 fat32-in-memory ac)))
    (take n2
          (explode (stobj-fa-table-to-string
                    fat32-in-memory)))))
  :hints
  (("goal" :in-theory (enable make-fat-string-ac))))

(defthm
  lofat-to-string-inversion-lemma-48
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (not (zp pos))
        (<= pos (fat-length fat32-in-memory)))
   (equal (update-fat
           fat32-in-memory
           (stobj-fa-table-to-string fat32-in-memory)
           pos)
          fat32-in-memory))
  :hints
  (("goal"
    :induct
    (update-fat
     fat32-in-memory
     (stobj-fa-table-to-string fat32-in-memory)
     pos))))

(defthm
  lofat-to-string-inversion-lemma-49
  (equal
   (nthcdr
    n
    (explode (lofat-to-string fat32-in-memory)))
   (if
    (<= (nfix n)
        (len (explode (reserved-area-string fat32-in-memory))))
    (append
     (nthcdr n
             (explode (reserved-area-string fat32-in-memory)))
     (explode (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                  fat32-in-memory ""))
     (data-region-string-helper
      fat32-in-memory
      (data-region-length fat32-in-memory)
      nil))
    (nthcdr
     (- n
        (len (explode (reserved-area-string fat32-in-memory))))
     (append
      (explode (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                   fat32-in-memory ""))
      (data-region-string-helper
       fat32-in-memory
       (data-region-length fat32-in-memory)
       nil)))))
  :hints
  (("goal" :in-theory
    (e/d (lofat-to-string)
         (fat32-in-memoryp
          length-of-reserved-area-string
          nth-of-explode-of-reserved-area-string)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthmd
    lofat-to-string-inversion-lemma-51
    (implies (lofat-fs-p fat32-in-memory)
             (equal (* (bpb_fatsz32 fat32-in-memory)
                       1/4 (bpb_bytspersec fat32-in-memory))
                    (fat-entry-count fat32-in-memory)))
    :hints
    (("goal" :in-theory (enable lofat-fs-p)
      :use fat-entry-count))))

(defthm
  lofat-to-string-inversion-lemma-52
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal (take (+ (* 4 (fat-entry-count fat32-in-memory))
                   (- (* (bpb_numfats fat32-in-memory)
                         4 (fat-entry-count fat32-in-memory))))
                (data-region-string-helper
                 fat32-in-memory
                 (count-of-clusters fat32-in-memory)
                 nil))
          nil))
  :hints
  (("goal" :in-theory
    (disable lofat-fs-p-correctness-1)
    :use lofat-fs-p-correctness-1)))

(defthm
  lofat-to-string-inversion
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal (string-to-lofat
           fat32-in-memory
           (lofat-to-string fat32-in-memory))
          (mv fat32-in-memory 0)))
  :hints
  (("goal"
    :in-theory
    (e/d (string-to-lofat
          painful-debugging-lemma-4
          painful-debugging-lemma-5
          lofat-to-string-inversion-lemma-51
          cluster-size read-reserved-area
          update-data-region-alt)
         (lofat-fs-p-correctness-1))
    :use lofat-fs-p-correctness-1)))

(defund-nx string-to-lofat-nx (str)
  (string-to-lofat (create-fat32-in-memory) str))

(defund-nx
  eqfat (str1 str2)
  (b*
      (((mv fat32-in-memory1 error-code1)
        (string-to-lofat-nx str1))
       (good1 (and (stringp str1) (equal error-code1 0)))
       ((mv fat32-in-memory2 error-code2)
        (string-to-lofat-nx str2))
       (good2 (and (stringp str2) (equal error-code2 0)))
       ((unless (and good1 good2))
        (and (not good1) (not good2))))
    (lofat-equiv fat32-in-memory1 fat32-in-memory2)))

(defequiv
  eqfat
  :hints (("goal" :in-theory (enable eqfat))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    lofat-fs-p-of-string-to-lofat-lemma-1
    (implies
     (and
      (<= 512
          (combine16u (nth 12 (get-initial-bytes str))
                      (nth 11 (get-initial-bytes str))))
      (<= 1 (nth 13 (get-initial-bytes str)))
      (<
       0
       (* (nth 13 (get-initial-bytes str))
          (combine16u (nth 12 (get-initial-bytes str))
                      (nth 11 (get-initial-bytes str)))
          (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                   (nth 14 (get-initial-bytes str))))
                    (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                (nth 18 (get-remaining-rsvdbyts str))
                                (nth 17 (get-remaining-rsvdbyts str))
                                (nth 16 (get-remaining-rsvdbyts str)))
                    (- (* (nth 0 (get-remaining-rsvdbyts str))
                          (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                      (nth 22 (get-remaining-rsvdbyts str))
                                      (nth 21 (get-remaining-rsvdbyts str))
                                      (nth 20 (get-remaining-rsvdbyts str))))))
                 (nth 13 (get-initial-bytes str))))))
     (not
      (< (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                  (nth 14 (get-initial-bytes str))))
                   (combine32u (nth 19 (get-remaining-rsvdbyts str))
                               (nth 18 (get-remaining-rsvdbyts str))
                               (nth 17 (get-remaining-rsvdbyts str))
                               (nth 16 (get-remaining-rsvdbyts str)))
                   (- (* (nth 0 (get-remaining-rsvdbyts str))
                         (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                     (nth 22 (get-remaining-rsvdbyts str))
                                     (nth 21 (get-remaining-rsvdbyts str))
                                     (nth 20 (get-remaining-rsvdbyts str))))))
                (nth 13 (get-initial-bytes str)))
         0))))

  (defthm
    lofat-fs-p-of-string-to-lofat-lemma-2
    (implies
     (and (<= 512
              (combine16u (nth 12 (get-initial-bytes str))
                          (nth 11 (get-initial-bytes str))))
          (<= 1
              (combine16u (nth 15 (get-initial-bytes str))
                          (nth 14 (get-initial-bytes str)))))
     (and
      (<= 512
          (* (combine16u (nth 12 (get-initial-bytes str))
                         (nth 11 (get-initial-bytes str)))
             (combine16u (nth 15 (get-initial-bytes str))
                         (nth 14 (get-initial-bytes str)))))
      (equal
       (nfix
        (binary-+
         '-16
         (binary-*
          (combine16u$inline (nth '12 (get-initial-bytes str))
                             (nth '11 (get-initial-bytes str)))
          (combine16u$inline
           (nth '15 (get-initial-bytes str))
           (nth '14 (get-initial-bytes str))))))
       (binary-+
        '-16
        (binary-*
         (combine16u$inline (nth '12 (get-initial-bytes str))
                            (nth '11 (get-initial-bytes str)))
         (combine16u$inline
          (nth '15 (get-initial-bytes str))
          (nth '14 (get-initial-bytes str))))))))
    :rule-classes
    ((:linear
      :corollary
      (implies
       (and (<= 512
                (combine16u (nth 12 (get-initial-bytes str))
                            (nth 11 (get-initial-bytes str))))
            (<= 1
                (combine16u (nth 15 (get-initial-bytes str))
                            (nth 14 (get-initial-bytes str)))))
       (<= 512
           (* (combine16u (nth 12 (get-initial-bytes str))
                          (nth 11 (get-initial-bytes str)))
              (combine16u (nth 15 (get-initial-bytes str))
                          (nth 14 (get-initial-bytes str)))))))
     (:rewrite
      :corollary
      (implies
       (and (<= 512
                (combine16u (nth 12 (get-initial-bytes str))
                            (nth 11 (get-initial-bytes str))))
            (<= 1
                (combine16u (nth 15 (get-initial-bytes str))
                            (nth 14 (get-initial-bytes str)))))
       (equal
        (nfix
         (binary-+
          '-16
          (binary-*
           (combine16u$inline (nth '12 (get-initial-bytes str))
                              (nth '11 (get-initial-bytes str)))
           (combine16u$inline
            (nth '15 (get-initial-bytes str))
            (nth '14 (get-initial-bytes str))))))
        (binary-+
         '-16
         (binary-*
          (combine16u$inline (nth '12 (get-initial-bytes str))
                             (nth '11 (get-initial-bytes str)))
          (combine16u$inline
           (nth '15 (get-initial-bytes str))
           (nth '14
                (get-initial-bytes str))))))))))

  (defthm
    lofat-fs-p-of-string-to-lofat-lemma-3
    (implies
     (integerp (* 1/4
                  (combine16u (nth 12 (get-initial-bytes str))
                              (nth 11 (get-initial-bytes str)))
                  (combine32u (nth 23 (get-remaining-rsvdbyts str))
                              (nth 22 (get-remaining-rsvdbyts str))
                              (nth 21 (get-remaining-rsvdbyts str))
                              (nth 20 (get-remaining-rsvdbyts str)))))
     (equal (* 4
               (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                     (nth 11 (get-initial-bytes str)))
                         (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                     (nth 22 (get-remaining-rsvdbyts str))
                                     (nth 21 (get-remaining-rsvdbyts str))
                                     (nth 20 (get-remaining-rsvdbyts str))))
                      4))
            (* (combine16u (nth 12 (get-initial-bytes str))
                           (nth 11 (get-initial-bytes str)))
               (combine32u (nth 23 (get-remaining-rsvdbyts str))
                           (nth 22 (get-remaining-rsvdbyts str))
                           (nth 21 (get-remaining-rsvdbyts str))
                           (nth 20 (get-remaining-rsvdbyts str)))))))

  (defthm
    lofat-fs-p-of-string-to-lofat-lemma-4
    (implies
     (<= 1 (nth 0 (get-remaining-rsvdbyts str)))
     (not
      (<
       (binary-+
        (binary-* (combine16u$inline (nth '12 (get-initial-bytes str))
                                     (nth '11 (get-initial-bytes str)))
                  (combine16u$inline (nth '15 (get-initial-bytes str))
                                     (nth '14 (get-initial-bytes str))))
        (binary-*
         (combine16u$inline (nth '12 (get-initial-bytes str))
                            (nth '11 (get-initial-bytes str)))
         (binary-* (nth '0 (get-remaining-rsvdbyts str))
                   (combine32u$inline (nth '23 (get-remaining-rsvdbyts str))
                                      (nth '22 (get-remaining-rsvdbyts str))
                                      (nth '21 (get-remaining-rsvdbyts str))
                                      (nth '20
                                           (get-remaining-rsvdbyts str))))))
       0))))

  (defthm
    lofat-fs-p-of-string-to-lofat-lemma-6
    (implies
     (and (<= 512
              (combine16u (nth 12 (get-initial-bytes str))
                          (nth 11 (get-initial-bytes str))))
          (<= 1 (nth 13 (get-initial-bytes str))))
     (< '0
        (binary-* (nth '13 (get-initial-bytes str))
                  (combine16u$inline (nth '12 (get-initial-bytes str))
                                     (nth '11 (get-initial-bytes str))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (enable string-to-lofat count-of-clusters
                         cluster-size fat-entry-count
                         lofat-fs-p
                         painful-debugging-lemma-1
                         painful-debugging-lemma-2
                         painful-debugging-lemma-3)))))

(defthm
  lofat-fs-p-of-string-to-lofat-lemma-5
  (implies (and (<= (nfix i)
                    (data-region-length fat32-in-memory))
                (cluster-listp (nth *data-regioni* fat32-in-memory)
                               cluster-size))
           (cluster-listp (nth *data-regioni*
                               (resize-data-region i fat32-in-memory))
                          cluster-size))
  :hints (("goal" :in-theory (enable data-region-length
                                     resize-data-region))))

(defthm
  lofat-fs-p-of-string-to-lofat
  (implies (and (equal (mv-nth 1 (string-to-lofat fat32-in-memory str))
                       0)
                (fat32-in-memoryp fat32-in-memory))
           (lofat-fs-p (mv-nth 0
                               (string-to-lofat fat32-in-memory str))))
  :hints (("goal" :in-theory (enable string-to-lofat
                                     count-of-clusters cluster-size
                                     fat-entry-count read-reserved-area
                                     lofat-fs-p painful-debugging-lemma-1
                                     painful-debugging-lemma-2
                                     painful-debugging-lemma-3))))

(defund
  update-fat-aux (fa-table str pos)
  (if
   (zp pos)
   fa-table
   (let*
    ((ch-word
      (combine32u (char-code (char str (+ -1 (* pos 4))))
                  (char-code (char str (+ -2 (* pos 4))))
                  (char-code (char str (+ -3 (* pos 4))))
                  (char-code (char str (+ -4 (* pos 4))))))
     (fa-table (update-nth (+ -1 pos)
                           ch-word fa-table)))
    (update-fat-aux fa-table str (+ -1 pos)))))

(defthm
  nth-of-update-fat-aux
  (implies
   (integerp pos)
   (equal
    (nth n (update-fat-aux fa-table str pos))
    (if (< (nfix n) (nfix pos))
        (combine32u (char-code (char str (+ 3 (* (nfix n) 4))))
                    (char-code (char str (+ 2 (* (nfix n) 4))))
                    (char-code (char str (+ 1 (* (nfix n) 4))))
                    (char-code (char str (+ 0 (* (nfix n) 4)))))
        (nth n fa-table))))
  :hints (("goal" :in-theory (enable update-fat-aux)
           :induct (update-fat-aux fa-table str pos))
          ("subgoal *1/2.6'"
           :use (:theorem (implies (integerp pos)
                                   (iff (equal 0 (+ -1 pos))
                                        (equal pos 1)))))
          ("subgoal *1/2.1'"
           :use (:theorem (implies (integerp pos)
                                   (iff (equal 0 (+ -1 pos))
                                        (equal pos 1)))))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme
       (fa-table1 fa-table2 pos str)
     (if
         (zp pos)
         (mv fa-table1 fa-table2 pos str)
       (induction-scheme
        (update-nth
         (+ -1 pos)
         (combine32u (char-code (char str (+ -1 (* pos 4))))
                     (char-code (char str (+ -2 (* pos 4))))
                     (char-code (char str (+ -3 (* pos 4))))
                     (char-code (char str (+ -4 (* pos 4)))))
         fa-table1)
        (update-nth
         (+ -1 pos)
         (combine32u (char-code (char str (+ -1 (* pos 4))))
                     (char-code (char str (+ -2 (* pos 4))))
                     (char-code (char str (+ -3 (* pos 4))))
                     (char-code (char str (+ -4 (* pos 4)))))
         fa-table2)
        (+ -1 pos)
        str))))

  (defthmd
    take-of-update-fat-aux
    (equal (take pos (update-fat-aux fa-table1 str pos))
           (take pos (update-fat-aux fa-table2 str pos)))
    :hints
    (("goal"
      :induct (induction-scheme fa-table1 fa-table2 pos str)
      :in-theory (e/d (update-fat-aux)
                      (equal-of-append-repeat
                       (:rewrite append-of-take-and-cons)))
      :expand (update-fat-aux fa-table2 str pos))
     ("subgoal *1/2"
      :use
      ((:instance
        (:rewrite append-of-take-and-cons)
        (y nil)
        (x (combine32u
            (char-code (nth (+ -1 (* 4 pos)) (explode str)))
            (char-code (nth (+ -2 (* 4 pos)) (explode str)))
            (char-code (nth (+ -3 (* 4 pos)) (explode str)))
            (char-code (nth (+ -4 (* 4 pos)) (explode str)))))
        (l
         (update-fat-aux
          (update-nth
           (+ -1 pos)
           (combine32u
            (char-code (nth (+ -1 (* 4 pos)) (explode str)))
            (char-code (nth (+ -2 (* 4 pos)) (explode str)))
            (char-code (nth (+ -3 (* 4 pos)) (explode str)))
            (char-code (nth (+ -4 (* 4 pos)) (explode str))))
           fa-table1)
          str (+ -1 pos)))
        (n (+ -1 pos)))
       (:instance
        (:rewrite append-of-take-and-cons)
        (y nil)
        (x (combine32u
            (char-code (nth (+ -1 (* 4 pos)) (explode str)))
            (char-code (nth (+ -2 (* 4 pos)) (explode str)))
            (char-code (nth (+ -3 (* 4 pos)) (explode str)))
            (char-code (nth (+ -4 (* 4 pos)) (explode str)))))
        (l
         (update-fat-aux
          (update-nth
           (+ -1 pos)
           (combine32u
            (char-code (nth (+ -1 (* 4 pos)) (explode str)))
            (char-code (nth (+ -2 (* 4 pos)) (explode str)))
            (char-code (nth (+ -3 (* 4 pos)) (explode str)))
            (char-code (nth (+ -4 (* 4 pos)) (explode str))))
           fa-table2)
          str (+ -1 pos)))
        (n (+ -1 pos))))))))

(defthm len-of-update-fat-aux
  (equal (len (update-fat-aux fa-table str pos))
         (max (nfix pos) (len fa-table)))
  :hints (("goal" :in-theory (enable update-fat-aux))))

(defthm
  true-list-fix-of-update-fat-aux
  (implies
   (true-listp fa-table)
   (equal (true-list-fix (update-fat-aux fa-table str pos))
          (update-fat-aux fa-table str pos)))
  :hints (("goal" :in-theory (enable update-fat-aux))))

(defthmd
  update-fat-alt
  (equal
   (update-fat fat32-in-memory str pos)
   (if (zp pos)
       fat32-in-memory
       (update-nth *fati*
                   (update-fat-aux (nth *fati* fat32-in-memory)
                                   str pos)
                   fat32-in-memory)))
  :hints
  (("goal" :in-theory (enable update-fat-aux update-fati)
    :induct (update-fat fat32-in-memory str pos))))

(encapsulate
  ()

  (local
   (defthm
     string-to-lofat-ignore-lemma-1
     (implies
      (and
       (stringp str)
       (equal
        (mv-nth 1
                (string-to-lofat fat32-in-memory str))
        0)
       (fat32-in-memoryp fat32-in-memory))
      (and
       (true-listp
        (mv-nth 0
                (string-to-lofat fat32-in-memory str)))
       (equal
        (len
         (mv-nth 0
                 (string-to-lofat fat32-in-memory str)))
        30)))
     :hints
     (("goal"
       :in-theory
       (e/d
        (lofat-fs-p fat32-in-memoryp)
        (lofat-fs-p-of-string-to-lofat))
       :use
       lofat-fs-p-of-string-to-lofat))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-2
     (implies
      (and (stringp str)
           (natp len)
           (>= (data-region-length fat32-in-memory)
               len)
           (fat32-in-memoryp fat32-in-memory)
           (< 0 (cluster-size fat32-in-memory))
           (>= (length str)
               (* (- (data-region-length fat32-in-memory)
                     len)
                  (cluster-size fat32-in-memory)))
           (equal
            (mv-nth
             1
             (update-data-region fat32-in-memory str len))
            0))
      (equal
       (nth
        *data-regioni*
        (mv-nth
         0
         (update-data-region fat32-in-memory str len)))
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
         (cluster-size fat32-in-memory)))))
     :hints
     (("goal"
       :in-theory (disable update-data-region-correctness-1)
       :do-not-induct t
       :use
       (update-data-region-alt
        update-data-region-correctness-1)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-3
     (implies
      (not
       (equal fat32-in-memory (create-fat32-in-memory)))
      (equal
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area (create-fat32-in-memory)
                                    str)))))
     :hints (("goal" :in-theory (e/d (read-reserved-area)
                                     (create-fat32-in-memory))))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-4
     (implies
      (not
       (equal fat32-in-memory (create-fat32-in-memory)))
      (equal
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area (create-fat32-in-memory)
                                    str)))))
     :hints (("goal" :in-theory (enable read-reserved-area
                                        cluster-size
                                        count-of-clusters
                                        fat-entry-count)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-5
     (implies
      (not
       (equal fat32-in-memory (create-fat32-in-memory)))
      (equal
       (bpb_fatsz32
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_fatsz32
        (mv-nth 0
                (read-reserved-area (create-fat32-in-memory)
                                    str)))))
     :hints (("goal" :in-theory (enable read-reserved-area
                                        count-of-clusters
                                        fat-entry-count
                                        cluster-size)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-6
     (implies
      (not
       (equal fat32-in-memory (create-fat32-in-memory)))
      (equal
       (bpb_numfats
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_numfats
        (mv-nth 0
                (read-reserved-area (create-fat32-in-memory)
                                    str)))))
     :hints (("goal" :in-theory (enable read-reserved-area
                                        count-of-clusters
                                        fat-entry-count
                                        cluster-size)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-7
     (implies
      (and
       (not
        (equal fat32-in-memory (create-fat32-in-memory)))
       (equal
        (mv-nth 1
                (read-reserved-area fat32-in-memory str))
        0))
      (equal
       (bpb_totsec32
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_totsec32
        (mv-nth 0
                (read-reserved-area (create-fat32-in-memory)
                                    str)))))
     :hints (("goal" :in-theory (enable read-reserved-area
                                        count-of-clusters
                                        fat-entry-count
                                        cluster-size)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-8
     (implies
      (not
       (equal fat32-in-memory (create-fat32-in-memory)))
      (equal
       (bpb_secperclus
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_secperclus
        (mv-nth 0
                (read-reserved-area (create-fat32-in-memory)
                                    str)))))
     :hints (("goal" :in-theory (enable read-reserved-area
                                        count-of-clusters
                                        fat-entry-count
                                        cluster-size)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-9
     (implies
      (not
       (equal fat32-in-memory (create-fat32-in-memory)))
      (equal
       (mv-nth 1
               (read-reserved-area fat32-in-memory str))
       (mv-nth 1
               (read-reserved-area (create-fat32-in-memory)
                                   str))))
     :hints (("goal" :in-theory (enable read-reserved-area
                                        count-of-clusters
                                        fat-entry-count
                                        cluster-size)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-10
     (< '0
        (binary-*
         (bpb_bytspersec (mv-nth 0
                                 (read-reserved-area fat32-in-memory str)))
         (bpb_secperclus (mv-nth 0
                                 (read-reserved-area fat32-in-memory str)))))
     :rule-classes :linear
     :hints (("goal" :in-theory (e/d (read-reserved-area cluster-size))))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-11
     (implies
      (not (equal n *data-regioni*))
      (equal
       (nth n
            (mv-nth 0
                    (update-data-region fat32-in-memory str len)))
       (nth n fat32-in-memory)))
     :hints (("goal" :in-theory (enable update-data-regioni)))))

  (local
   (defthm string-to-lofat-ignore-lemma-12
     (equal (nth *fati*
                 (mv-nth 0
                         (read-reserved-area fat32-in-memory str)))
            (nth *fati* fat32-in-memory))
     :hints (("Goal" :in-theory (enable read-reserved-area)) )))

  (defthmd
    string-to-lofat-ignore-lemma-13
    (implies (and (equal (data-region-length fat32-in-memory1)
                         (data-region-length fat32-in-memory2))
                  (equal (cluster-size fat32-in-memory1)
                         (cluster-size fat32-in-memory2)))
             (equal (mv-nth 1
                            (update-data-region fat32-in-memory1 str len))
                    (mv-nth 1
                            (update-data-region fat32-in-memory2 str len))))
    :hints
    (("goal" :induct (mv (update-data-region fat32-in-memory1 str len)
                         (update-data-region fat32-in-memory2 str len)))))

  (defthmd
    string-to-lofat-ignore-lemma-14
     (equal (mv-nth 1
                    (string-to-lofat fat32-in-memory str))
            (mv-nth 1
                    (string-to-lofat-nx str)))
    :hints
    (("goal"
      :in-theory
      (enable string-to-lofat read-reserved-area
              update-data-region-alt cluster-size
              count-of-clusters fat-entry-count string-to-lofat-nx)
      :use
      (:instance
       (:rewrite string-to-lofat-ignore-lemma-13)
       (len
        (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                 (nth 14 (get-initial-bytes str))))
                  (combine32u (nth 19 (get-remaining-rsvdbyts str))
                              (nth 18 (get-remaining-rsvdbyts str))
                              (nth 17 (get-remaining-rsvdbyts str))
                              (nth 16 (get-remaining-rsvdbyts str)))
                  (- (* (nth 0 (get-remaining-rsvdbyts str))
                        (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                    (nth 22 (get-remaining-rsvdbyts str))
                                    (nth 21 (get-remaining-rsvdbyts str))
                                    (nth 20 (get-remaining-rsvdbyts str))))))
               (nth 13 (get-initial-bytes str))))
       (str
        (implode
         (take
          (+ (len (explode str))
             (- (* (combine16u (nth 12 (get-initial-bytes str))
                               (nth 11 (get-initial-bytes str)))
                   (combine16u (nth 15 (get-initial-bytes str))
                               (nth 14 (get-initial-bytes str)))))
             (- (* (combine16u (nth 12 (get-initial-bytes str))
                               (nth 11 (get-initial-bytes str)))
                   (nth 0 (get-remaining-rsvdbyts str))
                   (combine32u (nth 23 (get-remaining-rsvdbyts str))
                               (nth 22 (get-remaining-rsvdbyts str))
                               (nth 21 (get-remaining-rsvdbyts str))
                               (nth 20 (get-remaining-rsvdbyts str))))))
          (nthcdr (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                    (nth 11 (get-initial-bytes str)))
                        (combine16u (nth 15 (get-initial-bytes str))
                                    (nth 14 (get-initial-bytes str))))
                     (* (combine16u (nth 12 (get-initial-bytes str))
                                    (nth 11 (get-initial-bytes str)))
                        (nth 0 (get-remaining-rsvdbyts str))
                        (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                    (nth 22 (get-remaining-rsvdbyts str))
                                    (nth 21 (get-remaining-rsvdbyts str))
                                    (nth 20 (get-remaining-rsvdbyts str)))))
                  (explode str)))))
       (fat32-in-memory1
        (resize-data-region
         (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                  (nth 14 (get-initial-bytes str))))
                   (combine32u (nth 19 (get-remaining-rsvdbyts str))
                               (nth 18 (get-remaining-rsvdbyts str))
                               (nth 17 (get-remaining-rsvdbyts str))
                               (nth 16 (get-remaining-rsvdbyts str)))
                   (- (* (nth 0 (get-remaining-rsvdbyts str))
                         (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                     (nth 22 (get-remaining-rsvdbyts str))
                                     (nth 21 (get-remaining-rsvdbyts str))
                                     (nth 20 (get-remaining-rsvdbyts str))))))
                (nth 13 (get-initial-bytes str)))
         (update-fat
          (update-bs_filsystype
           (take 8
                 (nthcdr 66 (get-remaining-rsvdbyts str)))
           (update-bs_vollab
            (take 11
                  (nthcdr 55 (get-remaining-rsvdbyts str)))
            (update-bs_volid
             (combine32u (nth 54 (get-remaining-rsvdbyts str))
                         (nth 53 (get-remaining-rsvdbyts str))
                         (nth 52 (get-remaining-rsvdbyts str))
                         (nth 51 (get-remaining-rsvdbyts str)))
             (update-bs_bootsig
              (nth 50 (get-remaining-rsvdbyts str))
              (update-bs_reserved1
               (nth 49 (get-remaining-rsvdbyts str))
               (update-bs_drvnum
                (nth 48 (get-remaining-rsvdbyts str))
                (update-bpb_reserved
                 (take 12
                       (nthcdr 36 (get-remaining-rsvdbyts str)))
                 (update-bpb_bkbootsec
                  (combine16u (nth 35 (get-remaining-rsvdbyts str))
                              (nth 34 (get-remaining-rsvdbyts str)))
                  (update-bpb_fsinfo
                   (combine16u (nth 33 (get-remaining-rsvdbyts str))
                               (nth 32 (get-remaining-rsvdbyts str)))
                   (update-bpb_rootclus
                    (combine32u (nth 31 (get-remaining-rsvdbyts str))
                                (nth 30 (get-remaining-rsvdbyts str))
                                (nth 29 (get-remaining-rsvdbyts str))
                                (nth 28 (get-remaining-rsvdbyts str)))
                    (update-bpb_fsver_major
                     (nth 27 (get-remaining-rsvdbyts str))
                     (update-bpb_fsver_minor
                      (nth 26 (get-remaining-rsvdbyts str))
                      (update-bpb_extflags
                       (combine16u (nth 25 (get-remaining-rsvdbyts str))
                                   (nth 24 (get-remaining-rsvdbyts str)))
                       (update-bpb_totsec32
                        (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                    (nth 18 (get-remaining-rsvdbyts str))
                                    (nth 17 (get-remaining-rsvdbyts str))
                                    (nth 16 (get-remaining-rsvdbyts str)))
                        (update-bpb_hiddsec
                         (combine32u (nth 15 (get-remaining-rsvdbyts str))
                                     (nth 14 (get-remaining-rsvdbyts str))
                                     (nth 13 (get-remaining-rsvdbyts str))
                                     (nth 12 (get-remaining-rsvdbyts str)))
                         (update-bpb_numheads
                          (combine16u (nth 11 (get-remaining-rsvdbyts str))
                                      (nth 10 (get-remaining-rsvdbyts str)))
                          (update-bpb_secpertrk
                           (combine16u (nth 9 (get-remaining-rsvdbyts str))
                                       (nth 8 (get-remaining-rsvdbyts str)))
                           (update-bpb_fatsz16
                            (combine16u (nth 7 (get-remaining-rsvdbyts str))
                                        (nth 6 (get-remaining-rsvdbyts str)))
                            (update-bpb_media
                             (nth 5 (get-remaining-rsvdbyts str))
                             (update-bpb_totsec16
                              (combine16u (nth 4 (get-remaining-rsvdbyts str))
                                          (nth 3 (get-remaining-rsvdbyts str)))
                              (update-bpb_rootentcnt
                               (combine16u (nth 2 (get-remaining-rsvdbyts str))
                                           (nth 1 (get-remaining-rsvdbyts str)))
                               (update-bs_oemname
                                (take 8 (nthcdr 3 (get-initial-bytes str)))
                                (update-bs_jmpboot
                                 (take 3 (get-initial-bytes str))
                                 (update-bpb_bytspersec
                                  (combine16u (nth 12 (get-initial-bytes str))
                                              (nth 11 (get-initial-bytes str)))
                                  (update-bpb_fatsz32
                                   (combine32u
                                    (nth 23 (get-remaining-rsvdbyts str))
                                    (nth 22 (get-remaining-rsvdbyts str))
                                    (nth 21 (get-remaining-rsvdbyts str))
                                    (nth 20 (get-remaining-rsvdbyts str)))
                                   (update-bpb_numfats
                                    (nth 0 (get-remaining-rsvdbyts str))
                                    (update-bpb_rsvdseccnt
                                     (combine16u
                                      (nth 15 (get-initial-bytes str))
                                      (nth 14 (get-initial-bytes str)))
                                     (update-bpb_secperclus
                                      (nth 13 (get-initial-bytes str))
                                      (resize-fat
                                       (floor
                                        (*
                                         (combine16u
                                          (nth 12 (get-initial-bytes str))
                                          (nth 11 (get-initial-bytes str)))
                                         (combine32u
                                          (nth 23 (get-remaining-rsvdbyts str))
                                          (nth 22 (get-remaining-rsvdbyts str))
                                          (nth 21 (get-remaining-rsvdbyts str))
                                          (nth
                                           20 (get-remaining-rsvdbyts str))))
                                        4)
                                       fat32-in-memory)))))))))))))))))))))))))))))
          (implode
           (take (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                   (nth 11 (get-initial-bytes str)))
                       (combine16u (nth 15 (get-initial-bytes str))
                                   (nth 14 (get-initial-bytes str))))
                    (- (* (combine16u (nth 12 (get-initial-bytes str))
                                      (nth 11 (get-initial-bytes str)))
                          (combine16u (nth 15 (get-initial-bytes str))
                                      (nth 14 (get-initial-bytes str)))))
                    (* (combine16u (nth 12 (get-initial-bytes str))
                                   (nth 11 (get-initial-bytes str)))
                       (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                   (nth 22 (get-remaining-rsvdbyts str))
                                   (nth 21 (get-remaining-rsvdbyts str))
                                   (nth 20 (get-remaining-rsvdbyts str)))))
                 (nthcdr (* (combine16u (nth 12 (get-initial-bytes str))
                                        (nth 11 (get-initial-bytes str)))
                            (combine16u (nth 15 (get-initial-bytes str))
                                        (nth 14 (get-initial-bytes str))))
                         (explode str))))
          (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                (nth 11 (get-initial-bytes str)))
                    (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                (nth 22 (get-remaining-rsvdbyts str))
                                (nth 21 (get-remaining-rsvdbyts str))
                                (nth 20 (get-remaining-rsvdbyts str))))
                 4))))
       (fat32-in-memory2
        (resize-data-region
         (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                  (nth 14 (get-initial-bytes str))))
                   (combine32u (nth 19 (get-remaining-rsvdbyts str))
                               (nth 18 (get-remaining-rsvdbyts str))
                               (nth 17 (get-remaining-rsvdbyts str))
                               (nth 16 (get-remaining-rsvdbyts str)))
                   (- (* (nth 0 (get-remaining-rsvdbyts str))
                         (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                     (nth 22 (get-remaining-rsvdbyts str))
                                     (nth 21 (get-remaining-rsvdbyts str))
                                     (nth 20 (get-remaining-rsvdbyts str))))))
                (nth 13 (get-initial-bytes str)))
         (update-fat
          (update-bs_filsystype
           (take 8
                 (nthcdr 66 (get-remaining-rsvdbyts str)))
           (update-bs_vollab
            (take 11
                  (nthcdr 55 (get-remaining-rsvdbyts str)))
            (update-bs_volid
             (combine32u (nth 54 (get-remaining-rsvdbyts str))
                         (nth 53 (get-remaining-rsvdbyts str))
                         (nth 52 (get-remaining-rsvdbyts str))
                         (nth 51 (get-remaining-rsvdbyts str)))
             (update-bs_bootsig
              (nth 50 (get-remaining-rsvdbyts str))
              (update-bs_reserved1
               (nth 49 (get-remaining-rsvdbyts str))
               (update-bs_drvnum
                (nth 48 (get-remaining-rsvdbyts str))
                (update-bpb_reserved
                 (take 12
                       (nthcdr 36 (get-remaining-rsvdbyts str)))
                 (update-bpb_bkbootsec
                  (combine16u (nth 35 (get-remaining-rsvdbyts str))
                              (nth 34 (get-remaining-rsvdbyts str)))
                  (update-bpb_fsinfo
                   (combine16u (nth 33 (get-remaining-rsvdbyts str))
                               (nth 32 (get-remaining-rsvdbyts str)))
                   (update-bpb_rootclus
                    (combine32u (nth 31 (get-remaining-rsvdbyts str))
                                (nth 30 (get-remaining-rsvdbyts str))
                                (nth 29 (get-remaining-rsvdbyts str))
                                (nth 28 (get-remaining-rsvdbyts str)))
                    (update-bpb_fsver_major
                     (nth 27 (get-remaining-rsvdbyts str))
                     (update-bpb_fsver_minor
                      (nth 26 (get-remaining-rsvdbyts str))
                      (update-bpb_extflags
                       (combine16u (nth 25 (get-remaining-rsvdbyts str))
                                   (nth 24 (get-remaining-rsvdbyts str)))
                       (update-bpb_totsec32
                        (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                    (nth 18 (get-remaining-rsvdbyts str))
                                    (nth 17 (get-remaining-rsvdbyts str))
                                    (nth 16 (get-remaining-rsvdbyts str)))
                        (update-bpb_hiddsec
                         (combine32u (nth 15 (get-remaining-rsvdbyts str))
                                     (nth 14 (get-remaining-rsvdbyts str))
                                     (nth 13 (get-remaining-rsvdbyts str))
                                     (nth 12 (get-remaining-rsvdbyts str)))
                         (update-bpb_numheads
                          (combine16u (nth 11 (get-remaining-rsvdbyts str))
                                      (nth 10 (get-remaining-rsvdbyts str)))
                          (update-bpb_secpertrk
                           (combine16u (nth 9 (get-remaining-rsvdbyts str))
                                       (nth 8 (get-remaining-rsvdbyts str)))
                           (update-bpb_fatsz16
                            (combine16u (nth 7 (get-remaining-rsvdbyts str))
                                        (nth 6 (get-remaining-rsvdbyts str)))
                            (update-bpb_media
                             (nth 5 (get-remaining-rsvdbyts str))
                             (update-bpb_totsec16
                              (combine16u (nth 4 (get-remaining-rsvdbyts str))
                                          (nth 3 (get-remaining-rsvdbyts str)))
                              (update-bpb_rootentcnt
                               (combine16u (nth 2 (get-remaining-rsvdbyts str))
                                           (nth 1 (get-remaining-rsvdbyts str)))
                               (update-bs_oemname
                                (take 8 (nthcdr 3 (get-initial-bytes str)))
                                (update-bs_jmpboot
                                 (take 3 (get-initial-bytes str))
                                 (update-bpb_bytspersec
                                  (combine16u (nth 12 (get-initial-bytes str))
                                              (nth 11 (get-initial-bytes str)))
                                  (update-bpb_fatsz32
                                   (combine32u
                                    (nth 23 (get-remaining-rsvdbyts str))
                                    (nth 22 (get-remaining-rsvdbyts str))
                                    (nth 21 (get-remaining-rsvdbyts str))
                                    (nth 20 (get-remaining-rsvdbyts str)))
                                   (update-bpb_numfats
                                    (nth 0 (get-remaining-rsvdbyts str))
                                    (update-bpb_rsvdseccnt
                                     (combine16u
                                      (nth 15 (get-initial-bytes str))
                                      (nth 14 (get-initial-bytes str)))
                                     (update-bpb_secperclus
                                      (nth 13 (get-initial-bytes str))
                                      (resize-fat
                                       (floor
                                        (*
                                         (combine16u
                                          (nth 12 (get-initial-bytes str))
                                          (nth 11 (get-initial-bytes str)))
                                         (combine32u
                                          (nth 23 (get-remaining-rsvdbyts str))
                                          (nth 22 (get-remaining-rsvdbyts str))
                                          (nth 21 (get-remaining-rsvdbyts str))
                                          (nth
                                           20 (get-remaining-rsvdbyts str))))
                                        4)
                                       (create-fat32-in-memory))))))))))))))))))))))))))))))
          (implode
           (take (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                   (nth 11 (get-initial-bytes str)))
                       (combine16u (nth 15 (get-initial-bytes str))
                                   (nth 14 (get-initial-bytes str))))
                    (- (* (combine16u (nth 12 (get-initial-bytes str))
                                      (nth 11 (get-initial-bytes str)))
                          (combine16u (nth 15 (get-initial-bytes str))
                                      (nth 14 (get-initial-bytes str)))))
                    (* (combine16u (nth 12 (get-initial-bytes str))
                                   (nth 11 (get-initial-bytes str)))
                       (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                   (nth 22 (get-remaining-rsvdbyts str))
                                   (nth 21 (get-remaining-rsvdbyts str))
                                   (nth 20 (get-remaining-rsvdbyts str)))))
                 (nthcdr (* (combine16u (nth 12 (get-initial-bytes str))
                                        (nth 11 (get-initial-bytes str)))
                            (combine16u (nth 15 (get-initial-bytes str))
                                        (nth 14 (get-initial-bytes str))))
                         (explode str))))
          (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                (nth 11 (get-initial-bytes str)))
                    (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                (nth 22 (get-remaining-rsvdbyts str))
                                (nth 21 (get-remaining-rsvdbyts str))
                                (nth 20 (get-remaining-rsvdbyts str))))
                 4))))))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-16
     (equal
      (nth *fati*
           (update-fat fat32-in-memory str pos))
      (if (zp pos)
          (nth *fati* fat32-in-memory)
        (update-fat-aux (nth *fati* fat32-in-memory)
                        str pos)))
     :hints
     (("goal" :use update-fat-alt))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-17
     (implies
      (and
       (not (equal fat32-in-memory (create-fat32-in-memory)))
       (<=
        (+ 2
           (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                    (nth 14 (get-initial-bytes str))))
                     (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                 (nth 18 (get-remaining-rsvdbyts str))
                                 (nth 17 (get-remaining-rsvdbyts str))
                                 (nth 16 (get-remaining-rsvdbyts str)))
                     (- (* (nth 0 (get-remaining-rsvdbyts str))
                           (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                       (nth 22 (get-remaining-rsvdbyts str))
                                       (nth 21 (get-remaining-rsvdbyts str))
                                       (nth 20 (get-remaining-rsvdbyts str))))))
                  (nth 13 (get-initial-bytes str))))
        (floor (* (combine16u (nth 12 (get-initial-bytes str))
                              (nth 11 (get-initial-bytes str)))
                  (combine32u (nth 23 (get-remaining-rsvdbyts str))
                              (nth 22 (get-remaining-rsvdbyts str))
                              (nth 21 (get-remaining-rsvdbyts str))
                              (nth 20 (get-remaining-rsvdbyts str))))
               4))
       (<
        (fat32-entry-mask (combine32u (nth 31 (get-remaining-rsvdbyts str))
                                      (nth 30 (get-remaining-rsvdbyts str))
                                      (nth 29 (get-remaining-rsvdbyts str))
                                      (nth 28 (get-remaining-rsvdbyts str))))
        (+ 2
           (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                    (nth 14 (get-initial-bytes str))))
                     (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                 (nth 18 (get-remaining-rsvdbyts str))
                                 (nth 17 (get-remaining-rsvdbyts str))
                                 (nth 16 (get-remaining-rsvdbyts str)))
                     (- (* (nth 0 (get-remaining-rsvdbyts str))
                           (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                       (nth 22 (get-remaining-rsvdbyts str))
                                       (nth 21 (get-remaining-rsvdbyts str))
                                       (nth 20 (get-remaining-rsvdbyts str))))))
                  (nth 13 (get-initial-bytes str)))))
       (<= (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                    (nth 14 (get-initial-bytes str))))
                     (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                 (nth 18 (get-remaining-rsvdbyts str))
                                 (nth 17 (get-remaining-rsvdbyts str))
                                 (nth 16 (get-remaining-rsvdbyts str)))
                     (- (* (nth 0 (get-remaining-rsvdbyts str))
                           (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                       (nth 22 (get-remaining-rsvdbyts str))
                                       (nth 21 (get-remaining-rsvdbyts str))
                                       (nth 20 (get-remaining-rsvdbyts str))))))
                  (nth 13 (get-initial-bytes str)))
           268435445))
      (equal
       (update-fat-aux
        (resize-list
         (nth *fati* fat32-in-memory)
         (floor (* (combine16u (nth 12 (get-initial-bytes str))
                               (nth 11 (get-initial-bytes str)))
                   (combine32u (nth 23 (get-remaining-rsvdbyts str))
                               (nth 22 (get-remaining-rsvdbyts str))
                               (nth 21 (get-remaining-rsvdbyts str))
                               (nth 20 (get-remaining-rsvdbyts str))))
                4)
         0)
        (implode (take (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                         (nth 11 (get-initial-bytes str)))
                             (combine16u (nth 15 (get-initial-bytes str))
                                         (nth 14 (get-initial-bytes str))))
                          (- (* (combine16u (nth 12 (get-initial-bytes str))
                                            (nth 11 (get-initial-bytes str)))
                                (combine16u (nth 15 (get-initial-bytes str))
                                            (nth 14 (get-initial-bytes str)))))
                          (* (combine16u (nth 12 (get-initial-bytes str))
                                         (nth 11 (get-initial-bytes str)))
                             (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                         (nth 22 (get-remaining-rsvdbyts str))
                                         (nth 21 (get-remaining-rsvdbyts str))
                                         (nth 20 (get-remaining-rsvdbyts str)))))
                       (nthcdr (* (combine16u (nth 12 (get-initial-bytes str))
                                              (nth 11 (get-initial-bytes str)))
                                  (combine16u (nth 15 (get-initial-bytes str))
                                              (nth 14 (get-initial-bytes str))))
                               (explode str))))
        (floor (* (combine16u (nth 12 (get-initial-bytes str))
                              (nth 11 (get-initial-bytes str)))
                  (combine32u (nth 23 (get-remaining-rsvdbyts str))
                              (nth 22 (get-remaining-rsvdbyts str))
                              (nth 21 (get-remaining-rsvdbyts str))
                              (nth 20 (get-remaining-rsvdbyts str))))
               4))
       (update-fat-aux
        (resize-list
         (nth *fati* (create-fat32-in-memory))
         (floor (* (combine16u (nth 12 (get-initial-bytes str))
                               (nth 11 (get-initial-bytes str)))
                   (combine32u (nth 23 (get-remaining-rsvdbyts str))
                               (nth 22 (get-remaining-rsvdbyts str))
                               (nth 21 (get-remaining-rsvdbyts str))
                               (nth 20 (get-remaining-rsvdbyts str))))
                4)
         0)
        (implode (take (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                         (nth 11 (get-initial-bytes str)))
                             (combine16u (nth 15 (get-initial-bytes str))
                                         (nth 14 (get-initial-bytes str))))
                          (- (* (combine16u (nth 12 (get-initial-bytes str))
                                            (nth 11 (get-initial-bytes str)))
                                (combine16u (nth 15 (get-initial-bytes str))
                                            (nth 14 (get-initial-bytes str)))))
                          (* (combine16u (nth 12 (get-initial-bytes str))
                                         (nth 11 (get-initial-bytes str)))
                             (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                         (nth 22 (get-remaining-rsvdbyts str))
                                         (nth 21 (get-remaining-rsvdbyts str))
                                         (nth 20 (get-remaining-rsvdbyts str)))))
                       (nthcdr (* (combine16u (nth 12 (get-initial-bytes str))
                                              (nth 11 (get-initial-bytes str)))
                                  (combine16u (nth 15 (get-initial-bytes str))
                                              (nth 14 (get-initial-bytes str))))
                               (explode str))))
        (floor (* (combine16u (nth 12 (get-initial-bytes str))
                              (nth 11 (get-initial-bytes str)))
                  (combine32u (nth 23 (get-remaining-rsvdbyts str))
                              (nth 22 (get-remaining-rsvdbyts str))
                              (nth 21 (get-remaining-rsvdbyts str))
                              (nth 20 (get-remaining-rsvdbyts str))))
               4))))
     :hints
     (("goal"
       :use
       (:instance
        (:rewrite take-of-update-fat-aux)
        (str
         (implode
          (take (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                  (nth 11 (get-initial-bytes str)))
                      (combine16u (nth 15 (get-initial-bytes str))
                                  (nth 14 (get-initial-bytes str))))
                   (- (* (combine16u (nth 12 (get-initial-bytes str))
                                     (nth 11 (get-initial-bytes str)))
                         (combine16u (nth 15 (get-initial-bytes str))
                                     (nth 14 (get-initial-bytes str)))))
                   (* (combine16u (nth 12 (get-initial-bytes str))
                                  (nth 11 (get-initial-bytes str)))
                      (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                  (nth 22 (get-remaining-rsvdbyts str))
                                  (nth 21 (get-remaining-rsvdbyts str))
                                  (nth 20 (get-remaining-rsvdbyts str)))))
                (nthcdr (* (combine16u (nth 12 (get-initial-bytes str))
                                       (nth 11 (get-initial-bytes str)))
                           (combine16u (nth 15 (get-initial-bytes str))
                                       (nth 14 (get-initial-bytes str))))
                        (explode str)))))
        (fa-table1
         (resize-list
          (nth *fati* fat32-in-memory)
          (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                (nth 11 (get-initial-bytes str)))
                    (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                (nth 22 (get-remaining-rsvdbyts str))
                                (nth 21 (get-remaining-rsvdbyts str))
                                (nth 20 (get-remaining-rsvdbyts str))))
                 4)
          0))
        (fa-table2
         (resize-list
          (nth *fati* (create-fat32-in-memory))
          (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                (nth 11 (get-initial-bytes str)))
                    (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                (nth 22 (get-remaining-rsvdbyts str))
                                (nth 21 (get-remaining-rsvdbyts str))
                                (nth 20 (get-remaining-rsvdbyts str))))
                 4)
          0))
        (pos (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                   (nth 11 (get-initial-bytes str)))
                       (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                   (nth 22 (get-remaining-rsvdbyts str))
                                   (nth 21 (get-remaining-rsvdbyts str))
                                   (nth 20 (get-remaining-rsvdbyts str))))
                    4)))))))

  (local (include-book "std/lists/nth" :dir :system))

  (local (in-theory (e/d
                     (count-of-clusters cluster-size fat-entry-count)
                     (nth-when-zp
                      ;; These are from accumulated-persistence.
                      (:definition update-nth-array)
                      (:definition len)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-15
     (implies
      (and
       (<= 512
           (combine16u (nth 12 (get-initial-bytes str))
                       (nth 11 (get-initial-bytes str))))
       (<= 1 (nth 13 (get-initial-bytes str)))
       (<= 2
           (fat32-entry-mask (combine32u (nth 31 (get-remaining-rsvdbyts str))
                                         (nth 30 (get-remaining-rsvdbyts str))
                                         (nth 29 (get-remaining-rsvdbyts str))
                                         (nth 28 (get-remaining-rsvdbyts str)))))
       (<
        (fat32-entry-mask (combine32u (nth 31 (get-remaining-rsvdbyts str))
                                      (nth 30 (get-remaining-rsvdbyts str))
                                      (nth 29 (get-remaining-rsvdbyts str))
                                      (nth 28 (get-remaining-rsvdbyts str))))
        (+ 2
           (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                    (nth 14 (get-initial-bytes str))))
                     (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                 (nth 18 (get-remaining-rsvdbyts str))
                                 (nth 17 (get-remaining-rsvdbyts str))
                                 (nth 16 (get-remaining-rsvdbyts str)))
                     (- (* (nth 0 (get-remaining-rsvdbyts str))
                           (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                       (nth 22 (get-remaining-rsvdbyts str))
                                       (nth 21 (get-remaining-rsvdbyts str))
                                       (nth 20 (get-remaining-rsvdbyts str))))))
                  (nth 13 (get-initial-bytes str)))))
       (equal
        (mv-nth
         1
         (update-data-region
          (resize-data-region
           (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                    (nth 14 (get-initial-bytes str))))
                     (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                 (nth 18 (get-remaining-rsvdbyts str))
                                 (nth 17 (get-remaining-rsvdbyts str))
                                 (nth 16 (get-remaining-rsvdbyts str)))
                     (- (* (nth 0 (get-remaining-rsvdbyts str))
                           (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                       (nth 22 (get-remaining-rsvdbyts str))
                                       (nth 21 (get-remaining-rsvdbyts str))
                                       (nth 20 (get-remaining-rsvdbyts str))))))
                  (nth 13 (get-initial-bytes str)))
           (update-fat
            (update-bs_filsystype
             (take 8
                   (nthcdr 66 (get-remaining-rsvdbyts str)))
             (update-bs_vollab
              (take 11
                    (nthcdr 55 (get-remaining-rsvdbyts str)))
              (update-bs_volid
               (combine32u (nth 54 (get-remaining-rsvdbyts str))
                           (nth 53 (get-remaining-rsvdbyts str))
                           (nth 52 (get-remaining-rsvdbyts str))
                           (nth 51 (get-remaining-rsvdbyts str)))
               (update-bs_bootsig
                (nth 50 (get-remaining-rsvdbyts str))
                (update-bs_reserved1
                 (nth 49 (get-remaining-rsvdbyts str))
                 (update-bs_drvnum
                  (nth 48 (get-remaining-rsvdbyts str))
                  (update-bpb_reserved
                   (take 12
                         (nthcdr 36 (get-remaining-rsvdbyts str)))
                   (update-bpb_bkbootsec
                    (combine16u (nth 35 (get-remaining-rsvdbyts str))
                                (nth 34 (get-remaining-rsvdbyts str)))
                    (update-bpb_fsinfo
                     (combine16u (nth 33 (get-remaining-rsvdbyts str))
                                 (nth 32 (get-remaining-rsvdbyts str)))
                     (update-bpb_rootclus
                      (combine32u (nth 31 (get-remaining-rsvdbyts str))
                                  (nth 30 (get-remaining-rsvdbyts str))
                                  (nth 29 (get-remaining-rsvdbyts str))
                                  (nth 28 (get-remaining-rsvdbyts str)))
                      (update-bpb_fsver_major
                       (nth 27 (get-remaining-rsvdbyts str))
                       (update-bpb_fsver_minor
                        (nth 26 (get-remaining-rsvdbyts str))
                        (update-bpb_extflags
                         (combine16u (nth 25 (get-remaining-rsvdbyts str))
                                     (nth 24 (get-remaining-rsvdbyts str)))
                         (update-bpb_totsec32
                          (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                      (nth 18 (get-remaining-rsvdbyts str))
                                      (nth 17 (get-remaining-rsvdbyts str))
                                      (nth 16 (get-remaining-rsvdbyts str)))
                          (update-bpb_hiddsec
                           (combine32u (nth 15 (get-remaining-rsvdbyts str))
                                       (nth 14 (get-remaining-rsvdbyts str))
                                       (nth 13 (get-remaining-rsvdbyts str))
                                       (nth 12 (get-remaining-rsvdbyts str)))
                           (update-bpb_numheads
                            (combine16u (nth 11 (get-remaining-rsvdbyts str))
                                        (nth 10 (get-remaining-rsvdbyts str)))
                            (update-bpb_secpertrk
                             (combine16u (nth 9 (get-remaining-rsvdbyts str))
                                         (nth 8 (get-remaining-rsvdbyts str)))
                             (update-bpb_fatsz16
                              (combine16u (nth 7 (get-remaining-rsvdbyts str))
                                          (nth 6 (get-remaining-rsvdbyts str)))
                              (update-bpb_media
                               (nth 5 (get-remaining-rsvdbyts str))
                               (update-bpb_totsec16
                                (combine16u (nth 4 (get-remaining-rsvdbyts str))
                                            (nth 3 (get-remaining-rsvdbyts str)))
                                (update-bpb_rootentcnt
                                 (combine16u
                                  (nth 2 (get-remaining-rsvdbyts str))
                                  (nth 1 (get-remaining-rsvdbyts str)))
                                 (update-bs_oemname
                                  (take 8 (nthcdr 3 (get-initial-bytes str)))
                                  (update-bs_jmpboot
                                   (take 3 (get-initial-bytes str))
                                   (update-bpb_bytspersec
                                    (combine16u (nth 12 (get-initial-bytes str))
                                                (nth 11 (get-initial-bytes str)))
                                    (update-bpb_fatsz32
                                     (combine32u
                                      (nth 23 (get-remaining-rsvdbyts str))
                                      (nth 22 (get-remaining-rsvdbyts str))
                                      (nth 21 (get-remaining-rsvdbyts str))
                                      (nth 20 (get-remaining-rsvdbyts str)))
                                     (update-bpb_numfats
                                      (nth 0 (get-remaining-rsvdbyts str))
                                      (update-bpb_rsvdseccnt
                                       (combine16u
                                        (nth 15 (get-initial-bytes str))
                                        (nth 14 (get-initial-bytes str)))
                                       (update-bpb_secperclus
                                        (nth 13 (get-initial-bytes str))
                                        (resize-fat
                                         (floor
                                          (*
                                           (combine16u
                                            (nth 12 (get-initial-bytes str))
                                            (nth 11 (get-initial-bytes str)))
                                           (combine32u
                                            (nth 23 (get-remaining-rsvdbyts str))
                                            (nth 22 (get-remaining-rsvdbyts str))
                                            (nth 21 (get-remaining-rsvdbyts str))
                                            (nth
                                             20 (get-remaining-rsvdbyts str))))
                                          4)
                                         (create-fat32-in-memory))))))))))))))))))))))))))))))
            (implode
             (take (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                     (nth 11 (get-initial-bytes str)))
                         (combine16u (nth 15 (get-initial-bytes str))
                                     (nth 14 (get-initial-bytes str))))
                      (- (* (combine16u (nth 12 (get-initial-bytes str))
                                        (nth 11 (get-initial-bytes str)))
                            (combine16u (nth 15 (get-initial-bytes str))
                                        (nth 14 (get-initial-bytes str)))))
                      (* (combine16u (nth 12 (get-initial-bytes str))
                                     (nth 11 (get-initial-bytes str)))
                         (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                     (nth 22 (get-remaining-rsvdbyts str))
                                     (nth 21 (get-remaining-rsvdbyts str))
                                     (nth 20 (get-remaining-rsvdbyts str)))))
                   (nthcdr (* (combine16u (nth 12 (get-initial-bytes str))
                                          (nth 11 (get-initial-bytes str)))
                              (combine16u (nth 15 (get-initial-bytes str))
                                          (nth 14 (get-initial-bytes str))))
                           (explode str))))
            (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                  (nth 11 (get-initial-bytes str)))
                      (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                  (nth 22 (get-remaining-rsvdbyts str))
                                  (nth 21 (get-remaining-rsvdbyts str))
                                  (nth 20 (get-remaining-rsvdbyts str))))
                   4)))
          (implode
           (take
            (+ (len (explode str))
               (- (* (combine16u (nth 12 (get-initial-bytes str))
                                 (nth 11 (get-initial-bytes str)))
                     (combine16u (nth 15 (get-initial-bytes str))
                                 (nth 14 (get-initial-bytes str)))))
               (- (* (combine16u (nth 12 (get-initial-bytes str))
                                 (nth 11 (get-initial-bytes str)))
                     (nth 0 (get-remaining-rsvdbyts str))
                     (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                 (nth 22 (get-remaining-rsvdbyts str))
                                 (nth 21 (get-remaining-rsvdbyts str))
                                 (nth 20 (get-remaining-rsvdbyts str))))))
            (nthcdr (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                      (nth 11 (get-initial-bytes str)))
                          (combine16u (nth 15 (get-initial-bytes str))
                                      (nth 14 (get-initial-bytes str))))
                       (* (combine16u (nth 12 (get-initial-bytes str))
                                      (nth 11 (get-initial-bytes str)))
                          (nth 0 (get-remaining-rsvdbyts str))
                          (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                      (nth 22 (get-remaining-rsvdbyts str))
                                      (nth 21 (get-remaining-rsvdbyts str))
                                      (nth 20 (get-remaining-rsvdbyts str)))))
                    (explode str))))
          (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                   (nth 14 (get-initial-bytes str))))
                    (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                (nth 18 (get-remaining-rsvdbyts str))
                                (nth 17 (get-remaining-rsvdbyts str))
                                (nth 16 (get-remaining-rsvdbyts str)))
                    (- (* (nth 0 (get-remaining-rsvdbyts str))
                          (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                      (nth 22 (get-remaining-rsvdbyts str))
                                      (nth 21 (get-remaining-rsvdbyts str))
                                      (nth 20 (get-remaining-rsvdbyts str))))))
                 (nth 13 (get-initial-bytes str)))))
        0))
      (integerp
       (binary-+
        (len (explode$inline str))
        (binary-+
         (unary--
          (binary-* (combine16u$inline (nth '12 (get-initial-bytes str))
                                       (nth '11 (get-initial-bytes str)))
                    (combine16u$inline (nth '15 (get-initial-bytes str))
                                       (nth '14 (get-initial-bytes str)))))
         (unary--
          (binary-*
           (combine16u$inline (nth '12 (get-initial-bytes str))
                              (nth '11 (get-initial-bytes str)))
           (binary-*
            (nth '0 (get-remaining-rsvdbyts str))
            (combine32u$inline (nth '23 (get-remaining-rsvdbyts str))
                               (nth '22 (get-remaining-rsvdbyts str))
                               (nth '21 (get-remaining-rsvdbyts str))
                               (nth '20
                                    (get-remaining-rsvdbyts str))))))))))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-18
     (implies
      (and (not (equal fat32-in-memory
                       (create-fat32-in-memory)))
           (fat32-in-memoryp fat32-in-memory)
           (equal (mv-nth 1
                          (string-to-lofat fat32-in-memory str))
                  0)
           (equal (mv-nth 1
                          (string-to-lofat (create-fat32-in-memory)
                                           str))
                  0)
           (integerp n)
           (<= 0 n)
           (< n 30))
      (equal (nth n
                  (mv-nth 0
                          (string-to-lofat fat32-in-memory str)))
             (nth n
                  (mv-nth 0
                          (string-to-lofat (create-fat32-in-memory)
                                           str)))))
     :hints
     (("goal" :cases ((equal n *bs_jmpbooti*)
                      (equal n *bs_oemnamei*)
                      (equal n *bpb_bytspersec*)
                      (equal n *bpb_secperclus*)
                      (equal n *bpb_rsvdseccnt*)
                      (equal n *bpb_numfats*)
                      (equal n *bpb_rootentcnt*)
                      (equal n *bpb_totsec16*)
                      (equal n *bpb_media*)
                      (equal n *bpb_fatsz16*)
                      (equal n *bpb_secpertrk*)
                      (equal n *bpb_numheads*)
                      (equal n *bpb_hiddsec*)
                      (equal n *bpb_totsec32*)
                      (equal n *bpb_fatsz32*)
                      (equal n *bpb_extflags*)
                      (equal n *bpb_fsver_minor*)
                      (equal n *bpb_fsver_major*)
                      (equal n *bpb_rootclus*)
                      (equal n *bpb_fsinfo*)
                      (equal n *bpb_bkbootsec*)
                      (equal n *bpb_reservedi*)
                      (equal n *bs_drvnum*)
                      (equal n *bs_reserved1*)
                      (equal n *bs_bootsig*)
                      (equal n *bs_volid*)
                      (equal n *bs_vollabi*)
                      (equal n *bs_filsystypei*)
                      (equal n *fati*)
                      (equal n *data-regioni*))
       :in-theory (e/d (string-to-lofat read-reserved-area)
                       (;; accumulated-persistence suggests disabling a bunch of
                        ;; rules.
                        (:REWRITE NTH-WHEN-ATOM)
                        (:DEFINITION UPDATE-DATA-REGION)
                        (:REWRITE CONSP-OF-TAKE)
                        (:REWRITE
                         RESIZE-FAT-OF-FAT-LENGTH-WHEN-FAT32-IN-MEMORYP
                         . 2)
                        (:REWRITE CAR-OF-NTHCDR)
                        (:REWRITE NTH-OF-MAKE-CHARACTER-LIST)
                        (:DEFINITION UPDATE-FAT)))))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-19
     (implies (and (equal (mv-nth 1 (string-to-lofat fat32-in-memory str))
                          0)
                   (stringp str)
                   (fat32-in-memoryp fat32-in-memory)
                   (equal (mv-nth 1
                                  (string-to-lofat (create-fat32-in-memory)
                                                   str))
                          0)
                   (not (equal fat32-in-memory
                               (create-fat32-in-memory)))
                   (not (equal (mv-nth 0 (string-to-lofat fat32-in-memory str))
                               (mv-nth 0
                                       (string-to-lofat (create-fat32-in-memory)
                                                        str)))))
              (equal (string-to-lofat fat32-in-memory str)
                     (string-to-lofat (create-fat32-in-memory)
                                      str)))
     :hints
     (("goal"
       :use
       ((:functional-instance
         equal-by-nths
         (equal-by-nths-hyp
          (lambda nil
            (and (stringp str)
                 (not (equal fat32-in-memory
                             (create-fat32-in-memory)))
                 (fat32-in-memoryp fat32-in-memory)
                 (equal (mv-nth 1 (string-to-lofat fat32-in-memory str))
                        0)
                 (equal (mv-nth 1
                                (string-to-lofat (create-fat32-in-memory)
                                                 str))
                        0))))
         (equal-by-nths-lhs
          (lambda nil
            (mv-nth 0
                    (string-to-lofat fat32-in-memory str))))
         (equal-by-nths-rhs
          (lambda nil
            (mv-nth 0
                    (string-to-lofat (create-fat32-in-memory)
                                     str))))))))))

  (local
   (defthmd
     string-to-lofat-ignore-lemma-20
     (implies
      (and
       (stringp str)
       (case-split
        (not (equal fat32-in-memory
                    (create-fat32-in-memory))))
       (fat32-in-memoryp fat32-in-memory)
       (equal
        (mv-nth 1
                (string-to-lofat (create-fat32-in-memory)
                                 str))
        0))
      (equal (string-to-lofat fat32-in-memory str)
             (string-to-lofat (create-fat32-in-memory)
                              str)))
     :hints
     (("goal"
       :in-theory (enable
                   string-to-lofat-ignore-lemma-14)
       :use
       (string-to-lofat-correctness-1
        (:instance string-to-lofat-correctness-1
                   (fat32-in-memory (create-fat32-in-memory))))
       :cases
       ((equal
         (mv-nth 0
                 (string-to-lofat fat32-in-memory str))
         (mv-nth
          0
          (string-to-lofat (create-fat32-in-memory)
                           str))))))))

  (defthm
    string-to-lofat-ignore
    (implies
     (and
      (stringp str)
      (fat32-in-memoryp fat32-in-memory)
      (equal (mv-nth 1 (string-to-lofat-nx str)) 0))
     (equal (string-to-lofat fat32-in-memory str)
            (string-to-lofat-nx str)))
    :hints
    (("goal"
      :in-theory (enable string-to-lofat-nx)
      :use string-to-lofat-ignore-lemma-20
      :cases
      ((equal fat32-in-memory (create-fat32-in-memory)))))))

(defthm
  string-to-lofat-inversion-lemma-1
  (implies (equal (mv-nth 1 (string-to-lofat-nx str))
                  0)
           (lofat-fs-p (mv-nth 0 (string-to-lofat-nx str))))
  :hints (("goal" :in-theory (enable string-to-lofat-nx))))

(defthm
  string-to-lofat-inversion
  (implies
   (and (stringp str)
        (fat32-in-memoryp fat32-in-memory)
        (equal (mv-nth 1 (string-to-lofat fat32-in-memory str))
               0))
   (eqfat (lofat-to-string
           (mv-nth 0
                   (string-to-lofat fat32-in-memory str)))
          str))
  :hints
  (("goal"
    :in-theory (e/d (eqfat)
                    (create-fat32-in-memory
                     (:rewrite lofat-to-string-inversion)))
    :use
    ((:instance
      (:rewrite lofat-to-string-inversion)
      (fat32-in-memory
       (mv-nth 0
               (string-to-lofat (create-fat32-in-memory)
                                str))))
     (:instance
      (:rewrite string-to-lofat-ignore-lemma-14)
      (str
       (lofat-to-string
        (mv-nth 0
                (string-to-lofat (create-fat32-in-memory)
                                 str))))
      (fat32-in-memory
       (mv-nth 0
               (string-to-lofat (create-fat32-in-memory)
                                str))))
     string-to-lofat-ignore-lemma-14))))

(defthm
  hifat-to-string-inversion
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (hifat-bounded-file-alist-p fs)
        (hifat-no-dups-p fs)
        (<= (hifat-entry-count fs)
            (max-entry-count fat32-in-memory)))
   (b*
       (((mv fat32-in-memory error-code)
         (hifat-to-lofat fat32-in-memory fs)))
     (implies
      (zp error-code)
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat
         (mv-nth
          0
          (string-to-lofat
           fat32-in-memory
           (lofat-to-string fat32-in-memory)))))
       fs)))))

(defthm
  string-to-hifat-inversion
  (implies
   (and (stringp str)
        (fat32-in-memoryp fat32-in-memory))
   (b*
       (((mv fat32-in-memory error-code1)
         (string-to-lofat fat32-in-memory str))
        ((mv fs error-code2)
         (lofat-to-hifat fat32-in-memory)))
     (implies
      (and (equal error-code1 0)
           (equal error-code2 0)
           (hifat-bounded-file-alist-p fs)
           (hifat-no-dups-p fs)
           (equal (mv-nth 1 (hifat-to-lofat fat32-in-memory fs))
                  0))
      (eqfat (lofat-to-string
              (mv-nth 0 (hifat-to-lofat fat32-in-memory fs)))
             str))))
  :hints
  (("goal"
    :in-theory (e/d (eqfat)
                    ((:rewrite lofat-to-string-inversion)
                     (:rewrite string-to-lofat-ignore)))
    :use
    ((:instance
      (:rewrite lofat-to-string-inversion)
      (fat32-in-memory
       (mv-nth
        0
        (hifat-to-lofat
         (mv-nth 0 (string-to-lofat-nx str))
         (mv-nth 0
                 (lofat-to-hifat
                  (mv-nth 0 (string-to-lofat-nx str))))))))
     (:instance
      (:rewrite string-to-lofat-ignore)
      (str
       (lofat-to-string
        (mv-nth
         0
         (hifat-to-lofat
          (mv-nth 0 (string-to-lofat-nx str))
          (mv-nth 0
                  (lofat-to-hifat
                   (mv-nth 0 (string-to-lofat-nx str))))))))
      (fat32-in-memory
       (mv-nth
        0
        (hifat-to-lofat
         (mv-nth 0 (string-to-lofat-nx str))
         (mv-nth 0
                 (lofat-to-hifat
                  (mv-nth 0 (string-to-lofat-nx str))))))))
     (:rewrite string-to-lofat-ignore)
     string-to-lofat-ignore-lemma-14
     (:instance
      (:rewrite string-to-lofat-ignore-lemma-14)
      (str
       (lofat-to-string
        (mv-nth
         0
         (hifat-to-lofat
          (mv-nth 0 (string-to-lofat fat32-in-memory str))
          (mv-nth
           0
           (lofat-to-hifat
            (mv-nth 0
                    (string-to-lofat fat32-in-memory str))))))))
      (fat32-in-memory
       (mv-nth
        0
        (hifat-to-lofat
         (mv-nth 0 (string-to-lofat fat32-in-memory str))
         (mv-nth
          0
          (lofat-to-hifat
           (mv-nth 0
                   (string-to-lofat fat32-in-memory str))))))))
     (:instance
      (:rewrite lofat-to-string-inversion)
      (fat32-in-memory
       (mv-nth
        0
        (hifat-to-lofat
         (mv-nth 0 (string-to-lofat fat32-in-memory str))
         (mv-nth
          0
          (lofat-to-hifat
           (mv-nth
            0
            (string-to-lofat fat32-in-memory str))))))))))))

#|
Some (rather awful) testing forms are
(b* (((mv contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*)))
  (get-dir-filenames fat32-in-memory contents *ms-max-dir-size*))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*)))
  (lofat-to-hifat fat32-in-memory))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (lofat-to-hifat fat32-in-memory)))
  (hifat-open (list "INITRD  IMG")
           fs nil nil))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (lofat-to-hifat fat32-in-memory))
     ((mv fd-table file-table & &)
      (hifat-open (list "INITRD  IMG")
               fs nil nil)))
  (hifat-pread 0 6 49 fs fd-table file-table))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (lofat-to-hifat fat32-in-memory))
     ((mv fd-table file-table & &)
      (hifat-open (list "INITRD  IMG")
               fs nil nil)))
  (hifat-pwrite 0 "ornery" 49 fs fd-table file-table))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (lofat-to-hifat fat32-in-memory))
     ((mv fd-table file-table & &)
      (hifat-open (list "INITRD  IMG")
               fs nil nil))
     ((mv fs & &)
      (hifat-pwrite 0 "ornery" 49 fs fd-table file-table))
     ((mv fat32-in-memory dir-ent-list)
      (hifat-to-lofat-helper fat32-in-memory fs)))
  (mv fat32-in-memory dir-ent-list))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (lofat-to-hifat fat32-in-memory))
     ((mv fd-table file-table & &)
      (hifat-open (list "INITRD  IMG")
               fs nil nil))
     ((mv fs & &)
      (hifat-pwrite 0 "ornery" 49 fs fd-table file-table)))
  (hifat-to-lofat fat32-in-memory fs))
(time$
 (b*
     ((str (lofat-to-string
            fat32-in-memory))
      ((unless (and (stringp str)
                    (>= (length str) *initialbytcnt*)))
       (mv fat32-in-memory -1))
      ((mv fat32-in-memory error-code)
       (read-reserved-area fat32-in-memory str))
      ((unless (equal error-code 0))
       (mv fat32-in-memory "it was read-reserved-area"))
      (fat-read-size (/ (* (bpb_fatsz32 fat32-in-memory)
                           (bpb_bytspersec fat32-in-memory))
                        4))
      ((unless (integerp fat-read-size))
       (mv fat32-in-memory "it was fat-read-size"))
      (data-byte-count (* (count-of-clusters fat32-in-memory)
                          (cluster-size fat32-in-memory)))
      ((unless (> data-byte-count 0))
       (mv fat32-in-memory "it was data-byte-count"))
      (tmp_bytspersec (bpb_bytspersec fat32-in-memory))
      (tmp_init (* tmp_bytspersec
                   (+ (bpb_rsvdseccnt fat32-in-memory)
                      (* (bpb_numfats fat32-in-memory)
                         (bpb_fatsz32 fat32-in-memory)))))
      ((unless (>= (length str)
                   (+ tmp_init
                      (data-region-length fat32-in-memory))))
       (mv fat32-in-memory "it was (length str)"))
      (fat32-in-memory (resize-fat fat-read-size fat32-in-memory))
      (fat32-in-memory
       (update-fat fat32-in-memory
                   (subseq str
                           (* (bpb_rsvdseccnt fat32-in-memory)
                              (bpb_bytspersec fat32-in-memory))
                           (+ (* (bpb_rsvdseccnt fat32-in-memory)
                                 (bpb_bytspersec fat32-in-memory))
                              (* fat-read-size 4)))
                   fat-read-size))
      (fat32-in-memory
       (resize-data-region data-byte-count fat32-in-memory))
      (data-region-string
       (subseq str tmp_init
               (+ tmp_init
                  (data-region-length fat32-in-memory))))
      (fat32-in-memory
       (update-data-region fat32-in-memory data-region-string
                           (data-region-length fat32-in-memory)
                           0)))
   (mv fat32-in-memory error-code)))
(time$
 (b*
     (((mv channel state)
       (open-output-channel "test/disk2.raw" :character state))
      (state
         (princ$
          (lofat-to-string fat32-in-memory)
          channel state))
      (state
       (close-output-channel channel state)))
   (mv fat32-in-memory state)))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (lofat-to-hifat fat32-in-memory))
     ((mv fs & &)
      (hifat-mkdir fs (list "" "TMP        "))))
  (hifat-to-lofat fat32-in-memory fs))
|#

(defund lofat-file-contents-p (contents)
  (declare (xargs :guard t))
  (or (and (stringp contents)
           (unsigned-byte-p 32 (length contents)))
      (dir-ent-list-p contents)))

(defund lofat-file-contents-fix (contents)
  (declare (xargs :guard t))
  (if (lofat-file-contents-p contents)
      contents
    ""))

(defthm
  lofat-file-contents-fix-of-lofat-file-contents-fix
  (equal (lofat-file-contents-fix (lofat-file-contents-fix x))
         (lofat-file-contents-fix x))
  :hints (("goal" :in-theory (enable lofat-file-contents-fix))))

(fty::deffixtype lofat-file-contents
                 :pred lofat-file-contents-p
                 :fix lofat-file-contents-fix
                 :equiv lofat-file-contents-equiv
                 :define t)

(defthm
  lofat-file-contents-p-of-lofat-file-contents-fix
  (lofat-file-contents-p (lofat-file-contents-fix x))
  :hints (("goal" :in-theory (enable lofat-file-contents-fix
                                     lofat-file-contents-p))))

(defthm
  lofat-file-contents-fix-when-lofat-file-contents-p
  (implies (lofat-file-contents-p x)
           (equal (lofat-file-contents-fix x) x))
  :hints (("goal" :in-theory (enable lofat-file-contents-fix
                                     lofat-file-contents-p))))

(defthm
  lofat-file-contents-p-when-stringp
  (implies (stringp contents)
           (equal (lofat-file-contents-p contents)
                  (unsigned-byte-p 32 (length contents))))
  :hints (("goal" :in-theory (enable lofat-file-contents-p))))

(defthm lofat-file-contents-p-when-dir-ent-listp
  (implies (dir-ent-list-p contents)
           (lofat-file-contents-p contents))
  :hints (("goal" :in-theory (enable lofat-file-contents-p))))

(fty::defprod
 lofat-file
 ((dir-ent dir-ent-p :default (dir-ent-fix nil))
  (contents lofat-file-contents-p :default (lofat-file-contents-fix nil))))

(defund lofat-regular-file-p (file)
  (declare (xargs :guard t))
  (and (lofat-file-p file)
       (stringp (lofat-file->contents file))
       (unsigned-byte-p 32 (length (lofat-file->contents file)))))

(defund lofat-directory-file-p (file)
  (declare (xargs :guard t))
  (and (lofat-file-p file)
       (dir-ent-list-p (lofat-file->contents file))))

(defthm
  lofat-regular-file-p-correctness-1
  (implies
   (dir-ent-list-p contents)
   (not (lofat-regular-file-p (lofat-file dir-ent contents))))
  :hints (("goal" :in-theory (enable lofat-regular-file-p))))

(defthm
  lofat-regular-file-p-correctness-2
  (implies
   (lofat-regular-file-p file)
   (stringp (lofat-file->contents file)))
  :hints (("goal" :in-theory (enable lofat-regular-file-p))))

(defthm
  lofat-directory-file-p-correctness-1
  (implies
   (stringp contents)
   (not (lofat-directory-file-p (lofat-file dir-ent contents))))
  :hints (("goal" :in-theory (enable lofat-directory-file-p))))

(defthm
  lofat-directory-file-p-correctness-2
  (implies (lofat-regular-file-p file)
           (not (lofat-directory-file-p file)))
  :hints (("goal" :in-theory (enable lofat-directory-file-p
                                     lofat-regular-file-p))))

(defthm
  lofat-directory-file-p-when-lofat-file-p
  (implies (and (lofat-file-p file)
                (not (lofat-regular-file-p file)))
           (lofat-directory-file-p file))
  :hints (("goal" :in-theory (enable lofat-directory-file-p
                                     lofat-regular-file-p lofat-file-p
                                     lofat-file-contents-p
                                     lofat-file->contents))))

(defun lofat-statfs (fat32-in-memory)
  (declare (xargs :stobjs (fat32-in-memory)
                  :guard (lofat-fs-p fat32-in-memory)))
  (b*
      ((total_blocks (count-of-clusters fat32-in-memory))
       (available_blocks
        (len (stobj-find-n-free-clusters
              fat32-in-memory
              (count-of-clusters fat32-in-memory)))))
    (make-struct-statfs
     :f_type *S_MAGIC_FUSEBLK*
     :f_bsize (cluster-size fat32-in-memory)
     :f_blocks total_blocks
     :f_bfree available_blocks
     :f_bavail available_blocks
     :f_files 0
     :f_ffree 0
     :f_fsid 0
     :f_namelen 72)))

(defun
  find-dir-ent (dir-ent-list filename)
  (declare (xargs :guard (and (fat32-filename-p filename)
                              (dir-ent-list-p dir-ent-list))))
  (b* (((when (atom dir-ent-list))
        (mv (dir-ent-fix nil) *enoent*))
       (dir-ent (mbe :exec (car dir-ent-list)
                     :logic (dir-ent-fix (car dir-ent-list))))
       ((when (equal (dir-ent-filename dir-ent)
                     filename))
        (mv dir-ent 0)))
    (find-dir-ent (cdr dir-ent-list)
                  filename)))

(defthm
  find-dir-ent-correctness-1
  (and
   (dir-ent-p (mv-nth 0 (find-dir-ent dir-ent-list filename)))
   (natp (mv-nth 1
                 (find-dir-ent dir-ent-list filename))))
  :hints (("goal" :induct (find-dir-ent dir-ent-list filename)))
  :rule-classes
  ((:rewrite
    :corollary
    (dir-ent-p (mv-nth 0
                       (find-dir-ent dir-ent-list filename))))
   (:type-prescription
    :corollary
    (natp (mv-nth 1
                  (find-dir-ent dir-ent-list filename))))))

(defthm
  find-dir-ent-correctness-2
  (implies
   (not (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
               0))
   (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
          *enoent*)))

(defun lofat-find-file-by-pathname (fat32-in-memory dir-ent-list pathname)
  (declare (xargs :guard (and (lofat-fs-p fat32-in-memory)
                              (fat32-filename-list-p pathname)
                              (useful-dir-ent-list-p dir-ent-list))
                  :measure (acl2-count pathname)
                  :stobjs fat32-in-memory))
  (b* (((unless (consp pathname))
        (mv (make-lofat-file) *enoent*))
       (name (fat32-filename-fix (car pathname)))
       ((mv dir-ent error-code) (find-dir-ent dir-ent-list name))
       ((unless (equal error-code 0))
        (mv (make-lofat-file) error-code))
       (first-cluster (dir-ent-first-cluster dir-ent))
       (directory-p
        (dir-ent-directory-p dir-ent))
       (length (if directory-p
                   *ms-max-dir-size*
                 (dir-ent-file-size dir-ent)))
       ((mv contents &)
        (if
            (or (< first-cluster
                   *ms-first-data-cluster*)
                (>=
                 first-cluster
                 (+ (count-of-clusters fat32-in-memory)
                    *ms-first-data-cluster*)))
            (mv "" 0)
          (get-clusterchain-contents fat32-in-memory
                                     first-cluster
                                     length)))
       ((unless directory-p)
        (if (consp (cdr pathname))
            (mv (make-lofat-file) *enotdir*)
          (mv (make-lofat-file :dir-ent dir-ent :contents contents) 0)))
       ((when (atom (cdr pathname)))
        (mv
         (make-lofat-file :dir-ent dir-ent
                          :contents (make-dir-ent-list
                                     (string=>nats contents)))
         0)))
    (lofat-find-file-by-pathname
     fat32-in-memory
     (make-dir-ent-list (string=>nats contents))
     (cdr pathname))))

;; The dir-ent-list-p hypothesis is only there because
;; lofat-to-hifat-helper-exec doesn't fix its arguments. Should it?
(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-1
  (implies
   (and (dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper-exec
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0))
   (iff
    (consp
     (assoc-equal name
                  (mv-nth 0
                          (lofat-to-hifat-helper-exec
                           fat32-in-memory
                           dir-ent-list entry-limit))))
    (equal (mv-nth 1 (find-dir-ent dir-ent-list name))
           0)))
  :hints
  (("goal"
    :in-theory (enable lofat-to-hifat-helper-exec))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-2
  (implies
   (and
    (useful-dir-ent-list-p dir-ent-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper-exec fat32-in-memory
                                                    dir-ent-list entry-limit))
           0))
   (equal
    (m1-file->dir-ent
     (cdr
      (assoc-equal
       name
       (mv-nth 0
               (lofat-to-hifat-helper-exec fat32-in-memory
                                                dir-ent-list entry-limit)))))
    (mv-nth 0 (find-dir-ent dir-ent-list name))))
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper-exec))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-3
  (implies
   (and
    (equal (mv-nth 1 (find-dir-ent dir-ent-list name))
           0)
    (useful-dir-ent-list-p dir-ent-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper-exec
                    fat32-in-memory
                    dir-ent-list entry-limit))
           0)
    (not (dir-ent-directory-p
          (mv-nth 0 (find-dir-ent dir-ent-list name))))
    (or (< (dir-ent-first-cluster
            (mv-nth 0 (find-dir-ent dir-ent-list name)))
           2)
        (<= (+ 2 (count-of-clusters fat32-in-memory))
            (dir-ent-first-cluster
             (mv-nth 0 (find-dir-ent dir-ent-list name))))))
   (equal
    (cdr (assoc-equal name
                      (mv-nth 0
                              (lofat-to-hifat-helper-exec
                               fat32-in-memory
                               dir-ent-list entry-limit))))
    (make-m1-file
     :contents ""
     :dir-ent (mv-nth 0 (find-dir-ent dir-ent-list name)))))
  :hints
  (("goal"
    :in-theory (enable lofat-to-hifat-helper-exec))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-4
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper-exec
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0)
        (not (dir-ent-directory-p
              (mv-nth 0 (find-dir-ent dir-ent-list name))))
        (<= 2
            (dir-ent-first-cluster
             (mv-nth 0 (find-dir-ent dir-ent-list name))))
        (< (dir-ent-first-cluster
            (mv-nth 0 (find-dir-ent dir-ent-list name)))
           (+ 2 (count-of-clusters fat32-in-memory))))
   (equal
    (cdr (assoc-equal name
                      (mv-nth 0
                              (lofat-to-hifat-helper-exec
                               fat32-in-memory
                               dir-ent-list entry-limit))))
    (make-m1-file
     :contents
     (mv-nth
      0
      (get-clusterchain-contents
       fat32-in-memory
       (dir-ent-first-cluster
        (mv-nth 0 (find-dir-ent dir-ent-list name)))
       (dir-ent-file-size
        (mv-nth 0 (find-dir-ent dir-ent-list name)))))
     :dir-ent (mv-nth 0 (find-dir-ent dir-ent-list name)))))
  :hints
  (("goal"
    :in-theory (enable lofat-to-hifat-helper-exec))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-5
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper-exec
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0))
   (equal
    (m1-directory-file-p
     (cdr
      (assoc-equal name
                   (mv-nth 0
                           (lofat-to-hifat-helper-exec
                            fat32-in-memory
                            dir-ent-list entry-limit)))))
    (dir-ent-directory-p
     (mv-nth 0
             (find-dir-ent dir-ent-list name)))))
  :hints
  (("goal" :in-theory (enable lofat-to-hifat-helper-exec
                              m1-directory-file-p))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-6
  (implies
   (and (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list name)))
        (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper-exec fat32-in-memory
                                                   dir-ent-list entry-limit))
               0))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper-exec
      fat32-in-memory
      (make-dir-ent-list
       (string=>nats
        (mv-nth
         0
         (get-clusterchain-contents
          fat32-in-memory
          (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list name)))
          2097152))))
      entry-limit))
    0))
  :hints
  (("goal" :in-theory
    (e/d (lofat-to-hifat-helper-exec-correctness-4
          lofat-to-hifat-helper-exec
          make-dir-ent-list-of-remove1-dir-ent)
         ((:rewrite not-intersectp-list-of-lofat-to-hifat-helper-exec)
          (:definition free-index-listp)
          (:definition not-intersectp-list)
          (:rewrite nth-of-effective-fat)
          (:definition no-duplicatesp-equal)
          (:definition member-equal))))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-7
  (implies
   (and (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list name)))
        (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper-exec fat32-in-memory
                                                   dir-ent-list entry-limit))
               0))
   (equal
    (cdr (assoc-equal
          name
          (mv-nth 0
                  (lofat-to-hifat-helper-exec fat32-in-memory
                                              dir-ent-list entry-limit))))
    (make-m1-file
     :dir-ent (mv-nth 0 (find-dir-ent dir-ent-list name))
     :contents
     (mv-nth
      0
      (lofat-to-hifat-helper-exec
       fat32-in-memory
       (make-dir-ent-list
        (string=>nats
         (mv-nth
          0
          (get-clusterchain-contents
           fat32-in-memory
           (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list name)))
           2097152))))
       entry-limit)))))
  :hints
  (("goal" :in-theory (enable lofat-to-hifat-helper-exec-correctness-4
                              make-dir-ent-list-of-remove1-dir-ent)
    :induct (find-dir-ent dir-ent-list name)
    :expand (lofat-to-hifat-helper-exec fat32-in-memory
                                        dir-ent-list entry-limit))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-8
  (implies
   (and
    (dir-ent-directory-p
     (mv-nth 0 (find-dir-ent dir-ent-list name)))
    (not
     (and (<= 2
              (dir-ent-first-cluster
               (mv-nth 0 (find-dir-ent dir-ent-list name))))
          (< (dir-ent-first-cluster
              (mv-nth 0 (find-dir-ent dir-ent-list name)))
             (+ 2
                (count-of-clusters fat32-in-memory)))))
    (useful-dir-ent-list-p dir-ent-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper-exec
                    fat32-in-memory
                    dir-ent-list entry-limit))
           0))
   (equal
    (cdr (assoc-equal name
                      (mv-nth 0
                              (lofat-to-hifat-helper-exec
                               fat32-in-memory
                               dir-ent-list entry-limit))))
    (make-m1-file
     :dir-ent (mv-nth 0 (find-dir-ent dir-ent-list name))
     :contents nil)))
  :hints
  (("goal"
    :in-theory
    (enable lofat-to-hifat-helper-exec-correctness-4)
    :induct (find-dir-ent dir-ent-list name)
    :expand
    ((lofat-to-hifat-helper-exec fat32-in-memory
                                      dir-ent-list entry-limit)
     (lofat-to-hifat-helper-exec
      fat32-in-memory
      nil (+ -1 entry-limit))))))

(encapsulate
  () ;; start lemmas for lofat-find-file-by-pathname-correctness-1-lemma-9

  (local
   (defthm lemma-1
     (implies (and (stringp contents) (unsigned-byte-p 32 (length contents)))
              (equal (m1-file-contents-fix contents) contents))
     :hints (("Goal" :in-theory (enable m1-file-contents-fix m1-file-contents-p)) )))

  (defthm
    lofat-find-file-by-pathname-correctness-1-lemma-9
    (implies
     (useful-dir-ent-list-p dir-ent-list)
     (iff
      (m1-file-p
       (cdr
        (assoc-equal name
                     (mv-nth 0
                             (lofat-to-hifat-helper-exec
                              fat32-in-memory
                              dir-ent-list entry-limit)))))
      (consp
       (assoc-equal name
                    (mv-nth 0
                            (lofat-to-hifat-helper-exec
                             fat32-in-memory
                             dir-ent-list entry-limit))))))
    :hints
    (("goal" :in-theory (enable lofat-to-hifat-helper-exec
                                m1-regular-file-p)))))

(defthm
  lofat-find-file-by-pathname-correctness-1
  (b*
      (((mv file error-code)
        (hifat-find-file-by-pathname
         (mv-nth 0
                 (lofat-to-hifat-helper-exec
                  fat32-in-memory
                  dir-ent-list entry-limit))
         pathname)))
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (useful-dir-ent-list-p dir-ent-list)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper-exec
                      fat32-in-memory
                      dir-ent-list entry-limit))
             0)
      (lofat-regular-file-p
       (mv-nth
        0
        (lofat-find-file-by-pathname fat32-in-memory
                                     dir-ent-list pathname))))
     (equal (lofat-find-file-by-pathname
             fat32-in-memory dir-ent-list pathname)
            (mv (make-lofat-file :contents (m1-file->contents file)
                                 :dir-ent (m1-file->dir-ent file))
                error-code))))
  :hints (("Goal" :in-theory (enable hifat-find-file-by-pathname)) ))

(defthm
  lofat-find-file-by-pathname-correctness-2
  (b*
      (((mv file error-code)
        (hifat-find-file-by-pathname
         (mv-nth 0
                 (lofat-to-hifat-helper-exec
                  fat32-in-memory
                  dir-ent-list entry-limit))
         pathname)))
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (useful-dir-ent-list-p dir-ent-list)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper-exec
                      fat32-in-memory
                      dir-ent-list entry-limit))
             0)
      (lofat-directory-file-p
       (mv-nth
        0
        (lofat-find-file-by-pathname fat32-in-memory
                                     dir-ent-list pathname))))
     (and
      (equal
       (lofat-file->dir-ent
        (mv-nth 0
                (lofat-find-file-by-pathname
                 fat32-in-memory dir-ent-list pathname)))
       (m1-file->dir-ent file))
      (equal
       (mv-nth
        0
        (lofat-to-hifat-helper-exec
         fat32-in-memory
         (lofat-file->contents
          (mv-nth 0
                  (lofat-find-file-by-pathname
                   fat32-in-memory dir-ent-list pathname)))
         entry-limit))
       (m1-file->contents file))
      (equal
       (mv-nth 1
               (lofat-find-file-by-pathname
                fat32-in-memory dir-ent-list pathname))
       error-code))))
  :hints
  (("goal" :in-theory (enable hifat-find-file-by-pathname)
    :induct
    (mv (mv-nth 0
                (hifat-find-file-by-pathname
                 (mv-nth 0
                         (lofat-to-hifat-helper-exec
                          fat32-in-memory
                          dir-ent-list entry-limit))
                 pathname))
        (mv-nth 0
                (lofat-find-file-by-pathname
                 fat32-in-memory dir-ent-list pathname)))
    :expand (lofat-to-hifat-helper-exec
             fat32-in-memory nil entry-limit))))

(defthm
  lofat-find-file-by-pathname-correctness-3
  (and
   (lofat-file-p
    (mv-nth
     0
     (lofat-find-file-by-pathname fat32-in-memory dir-ent-list pathname)))
   (integerp (mv-nth 1
                     (lofat-find-file-by-pathname fat32-in-memory
                                                  dir-ent-list pathname))))
  :hints (("goal" :induct t))
  :rule-classes
  ((:type-prescription
    :corollary
    (integerp (mv-nth 1
                      (lofat-find-file-by-pathname fat32-in-memory
                                                   dir-ent-list pathname))))
   (:rewrite
    :corollary
    (lofat-file-p
     (mv-nth 0
             (lofat-find-file-by-pathname fat32-in-memory
                                          dir-ent-list pathname))))))

(defun
  place-dir-ent (dir-ent-list dir-ent)
  (declare (xargs :guard (and (dir-ent-p dir-ent)
                              (dir-ent-list-p dir-ent-list))))
  (b*
      ((dir-ent (mbe :exec dir-ent
                     :logic (dir-ent-fix dir-ent)))
       ((when (atom dir-ent-list))
        (list dir-ent))
       ((when (equal (dir-ent-filename dir-ent)
                     (dir-ent-filename (car dir-ent-list))))
        (list*
         dir-ent
         (mbe :exec (cdr dir-ent-list)
              :logic (dir-ent-list-fix (cdr dir-ent-list))))))
    (list* (mbe :logic (dir-ent-fix (car dir-ent-list))
                :exec (car dir-ent-list))
           (place-dir-ent (cdr dir-ent-list)
                          dir-ent))))

(defthm dir-ent-list-p-of-place-dir-ent
  (dir-ent-list-p (place-dir-ent dir-ent-list dir-ent)))

(defthm
  find-dir-ent-of-place-dir-ent
  (implies
   (and (dir-ent-list-p dir-ent-list)
        (dir-ent-p dir-ent))
   (equal (find-dir-ent (place-dir-ent dir-ent-list dir-ent)
                        (dir-ent-filename dir-ent))
          (mv dir-ent 0))))

(defund
  update-dir-contents
  (fat32-in-memory first-cluster dir-contents dir-ent)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (fat32-masked-entry-p first-cluster)
                (<= *ms-first-data-cluster* first-cluster)
                (dir-ent-p dir-ent)
                (> (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory))
                   first-cluster)
                (stringp dir-contents))
    :guard-hints
    (("goal" :expand (fat32-build-index-list
                      (effective-fat fat32-in-memory)
                      first-cluster 2097152
                      (cluster-size fat32-in-memory))))))
  (b* (((mv dir-clusterchain error-code)
        (get-clusterchain fat32-in-memory
                          first-cluster *ms-max-dir-size*))
       ((unless (equal error-code 0))
        (mv fat32-in-memory *eio*))
       (fat32-in-memory
        (stobj-set-indices-in-fa-table
         fat32-in-memory dir-clusterchain
         (make-list (len dir-clusterchain)
                    :initial-element 0)))
       (fat32-in-memory (update-fati first-cluster *ms-end-of-clusterchain*
                                     fat32-in-memory))
       ((unless (> (length dir-contents) 0))
        (mv fat32-in-memory 0))
       ((mv fat32-in-memory & error-code &)
        (place-contents fat32-in-memory
                        dir-ent dir-contents 0 first-cluster)))
    (mv fat32-in-memory error-code)))

(defthm
  count-of-clusters-of-update-dir-contents
  (equal
   (count-of-clusters
    (mv-nth
     0
     (update-dir-contents fat32-in-memory
                          first-cluster dir-contents dir-ent)))
   (count-of-clusters fat32-in-memory))
  :hints (("goal" :in-theory (enable update-dir-contents))))

(defthm
  lofat-fs-p-of-update-dir-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (fat32-masked-entry-p first-cluster)
        (<= *ms-first-data-cluster* first-cluster)
        (> (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory))
           first-cluster)
        (stringp dir-contents))
   (lofat-fs-p
    (mv-nth 0
            (update-dir-contents fat32-in-memory
                                 first-cluster dir-contents dir-ent))))
  :hints (("goal" :in-theory (enable update-dir-contents))))

(defun
  lofat-place-file-by-pathname
  (fat32-in-memory rootclus pathname file)
  (declare
   (xargs
    :guard (and (lofat-fs-p fat32-in-memory)
                (fat32-masked-entry-p rootclus)
                (>= rootclus *ms-first-data-cluster*)
                (< rootclus
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory)))
                (fat32-filename-list-p pathname)
                (lofat-file-p file))
    :measure (acl2-count pathname)
    :stobjs fat32-in-memory
    :verify-guards nil))
  (b*
      (;; Pathnames aren't going to be empty lists. Even the emptiest of
       ;; empty pathnames has to have at least a slash in it, because we are
       ;; absolutely dealing in absolute pathnames.
       ((unless (consp pathname))
        (mv fat32-in-memory *enoent*))
       (name (mbe :logic (fat32-filename-fix (car pathname))
                  :exec (car pathname)))
       ((mv dir-contents &)
        (get-clusterchain-contents fat32-in-memory
                                   rootclus *ms-max-dir-size*))
       (dir-ent-list
        (make-dir-ent-list (string=>nats dir-contents)))
       ((mv dir-ent error-code)
        (find-dir-ent dir-ent-list name))
       ((unless (equal error-code 0))
        (if
         (atom (cdr pathname))
         (b*
             ((file-length
               (if (lofat-directory-file-p file)
                   0 (length (lofat-file->contents file))))
              (indices (stobj-find-n-free-clusters fat32-in-memory 1))
              ((when (< (len indices) 1))
               (mv fat32-in-memory *enospc*))
              (first-cluster (nth 0 indices))
              (contents
               (if
                (lofat-directory-file-p file)
                (nats=>string (flatten (lofat-file->contents file)))
                (lofat-file->contents file)))
              ((mv fat32-in-memory dir-ent & &)
               (if
                   (equal (length contents) 0)
                   (mv fat32-in-memory dir-ent nil nil)
                 (place-contents fat32-in-memory
                                 (lofat-file->dir-ent file)
                                 contents file-length first-cluster)))
              (dir-ent-list (place-dir-ent dir-ent-list dir-ent)))
           (update-dir-contents
            fat32-in-memory rootclus
            (nats=>string (flatten dir-ent-list))
            dir-ent))
         (mv fat32-in-memory *enotdir*)))
       ((unless (dir-ent-directory-p dir-ent))
        (if
         (or (consp (cdr pathname))
             ;; This is the case where a regular file could get replaced by a
             ;; directory, which is a bad idea.
             (lofat-directory-file-p file))
         (mv fat32-in-memory *enotdir*)
         (b*
             ((file-length (length (lofat-file->contents file)))
              (indices (stobj-find-n-free-clusters fat32-in-memory 1))
              ((when (< (len indices) 1))
               (mv fat32-in-memory *enospc*))
              (first-cluster (nth 0 indices))
              ((mv fat32-in-memory dir-ent & &)
               (if
                   (equal (length (lofat-file->contents file)) 0)
                   (mv fat32-in-memory dir-ent nil nil)
                 (place-contents fat32-in-memory
                                 (lofat-file->dir-ent file)
                                 (lofat-file->contents file)
                                 file-length first-cluster)))
              (dir-ent-list
               (place-dir-ent dir-ent-list
                              (lofat-file->dir-ent file))))
           (update-dir-contents
            fat32-in-memory rootclus
            (nats=>string (flatten dir-ent-list))
            dir-ent))))
       ;; This case should never arise - we should never legitimately find a
       ;; directory entry with a cluster index outside the allowable range.
       ((unless
         (and
          (< (dir-ent-first-cluster (lofat-file->dir-ent file))
             (+ *ms-first-data-cluster*
                (count-of-clusters fat32-in-memory)))
          (>= (dir-ent-first-cluster (lofat-file->dir-ent file))
              *ms-first-data-cluster*)))
        (mv fat32-in-memory *eio*)))
    (lofat-place-file-by-pathname
     fat32-in-memory
     (dir-ent-first-cluster (lofat-file->dir-ent file))
     (cdr pathname)
     file)))

(defthm
  count-of-clusters-of-lofat-place-file-by-pathname
  (equal
   (count-of-clusters
    (mv-nth
     0
     (lofat-place-file-by-pathname fat32-in-memory
                                   rootclus pathname file)))
   (count-of-clusters fat32-in-memory)))

(defthm
  lofat-fs-p-of-lofat-place-file-by-pathname-lemma-1
  (implies (lofat-file-p file)
           (iff (stringp (lofat-file->contents file))
                (not (lofat-directory-file-p file))))
  :hints
  (("goal" :in-theory (enable lofat-directory-file-p
                              lofat-file-p lofat-file-contents-p
                              lofat-file->contents))))

(defthm
  lofat-fs-p-of-lofat-place-file-by-pathname
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (fat32-masked-entry-p rootclus)
        (>= rootclus *ms-first-data-cluster*)
        (< rootclus
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (lofat-file-p file))
   (lofat-fs-p
    (mv-nth
     0
     (lofat-place-file-by-pathname fat32-in-memory
                                   rootclus pathname file))))
  :hints
  (("goal" :induct (lofat-place-file-by-pathname
                    fat32-in-memory rootclus pathname file))
   ("subgoal *1/7"
    :in-theory
    (disable (:linear find-n-free-clusters-correctness-7))
    :use (:instance (:linear find-n-free-clusters-correctness-7)
                    (n 1)
                    (fa-table (effective-fat fat32-in-memory))
                    (m 0)))
   ("subgoal *1/5"
    :in-theory
    (disable (:linear find-n-free-clusters-correctness-7))
    :use (:instance (:linear find-n-free-clusters-correctness-7)
                    (n 1)
                    (fa-table (effective-fat fat32-in-memory))
                    (m 0)))))

(defthm
  lofat-place-file-by-pathname-guard-lemma-1
  (implies (lofat-regular-file-p file)
           (unsigned-byte-p
            32
            (len (explode (lofat-file->contents file)))))
  :hints (("goal" :in-theory (enable lofat-regular-file-p))))

(defthm
  lofat-place-file-by-pathname-guard-lemma-2
  (implies (and (lofat-file-p file)
                (not (lofat-directory-file-p file)))
           (lofat-regular-file-p file))
  :hints
  (("goal" :in-theory (enable lofat-file-p lofat-regular-file-p
                              lofat-directory-file-p
                              lofat-file-contents-p
                              lofat-file->contents))))

(defthm
  lofat-place-file-by-pathname-guard-lemma-3
  (implies (lofat-directory-file-p file)
           (dir-ent-list-p (lofat-file->contents file)))
  :hints (("goal" :in-theory (enable lofat-directory-file-p))))

(verify-guards
  lofat-place-file-by-pathname
  :guard-debug t
  :hints
  (("goal"
    :in-theory
    (disable (:linear find-n-free-clusters-correctness-7)
             unsigned-byte-p)
    :use (:instance (:linear find-n-free-clusters-correctness-7)
                    (n 1)
                    (fa-table (effective-fat fat32-in-memory))
                    (m 0)))))

(defun
  delete-dir-ent (dir-ent-list filename)
  (declare (xargs :guard (and (fat32-filename-p filename)
                              (dir-ent-list-p dir-ent-list))
                  :guard-debug t))
  (b*
      (((when (atom dir-ent-list)) nil)
       (dir-ent (car dir-ent-list))
       ((when (equal (dir-ent-filename dir-ent)
                     filename))
        (delete-dir-ent (cdr dir-ent-list) filename)))
    (list* (dir-ent-fix dir-ent)
           (delete-dir-ent (cdr dir-ent-list)
                          filename))))

(defthm dir-ent-list-p-of-delete-dir-ent
  (dir-ent-list-p (delete-dir-ent dir-ent-list filename)))

(defthm len-of-delete-dir-ent
  (<= (len (delete-dir-ent dir-ent-list filename))
      (len dir-ent-list))
  :rule-classes :linear)

(defthm
  find-dir-ent-of-delete-dir-ent
  (implies
   (useful-dir-ent-list-p dir-ent-list)
   (equal (find-dir-ent (delete-dir-ent dir-ent-list filename1)
                        filename2)
          (if (equal filename1 filename2)
              (mv (dir-ent-fix nil) *enoent*)
              (find-dir-ent dir-ent-list filename2))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (useful-dir-ent-list-p dir-ent-filename len-when-dir-ent-p)
     ((:rewrite dir-ent-filename-of-dir-ent-set-filename)
      (:rewrite string=>nats-of-nats=>string)
      (:rewrite nth-update-nth)))
    :induct (delete-dir-ent dir-ent-list filename1))
   ("subgoal *1/2"
    :use
    ((:instance
      (:rewrite dir-ent-filename-of-dir-ent-set-filename)
      (filename
       (nats=>string
        (update-nth
         0 0
         (string=>nats (dir-ent-filename (car dir-ent-list))))))
      (dir-ent (car dir-ent-list)))
     (:instance
      (:rewrite string=>nats-of-nats=>string)
      (nats
       (update-nth
        0 0
        (string=>nats
         (nats=>string (take 11 (car dir-ent-list)))))))
     (:instance (:rewrite string=>nats-of-nats=>string)
                (nats (take 11 (car dir-ent-list))))
     (:instance (:rewrite nth-update-nth)
                (l (take 11 (car dir-ent-list)))
                (val 0)
                (n 0)
                (m 0))))))

(defthm
  delete-dir-ent-correctness-1
  (implies
   (not (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
                0))
   (equal (delete-dir-ent dir-ent-list filename)
          (dir-ent-list-fix dir-ent-list))))

;; Care should be taken before choosing to change this function's
;; definition. It has the very useful property that the length of the directory
;; contents remain the same, which means no reallocation is required.
(defun
  clear-dir-ent (dir-contents filename)
  (declare
   (xargs :measure (len dir-contents)
          :guard (and (fat32-filename-p filename)
                      (unsigned-byte-listp 8 dir-contents))
          :guard-hints (("goal" :in-theory (enable dir-ent-p)))
          :guard-debug t))
  (b*
      (((when (< (len dir-contents)
                 *ms-dir-ent-length*))
        dir-contents)
       (dir-ent (take *ms-dir-ent-length* dir-contents))
       ((when (equal (char (dir-ent-filename dir-ent) 0)
                     (code-char 0)))
        dir-contents)
       ((when (equal (dir-ent-filename dir-ent)
                     filename))
        (append
         (dir-ent-set-filename
          dir-ent
          (nats=>string
           (update-nth 0 229
                       (string=>nats (dir-ent-filename dir-ent)))))
         (clear-dir-ent (nthcdr *ms-dir-ent-length* dir-contents)
                        filename))))
    (append
     dir-ent
     (clear-dir-ent (nthcdr *ms-dir-ent-length* dir-contents)
                    filename))))

(defthm
  len-of-clear-dir-ent
  (equal (len (clear-dir-ent dir-contents filename))
         (len dir-contents))
  :hints (("goal" :in-theory (enable len-when-dir-ent-p))))

(defthm
  unsigned-byte-listp-of-clear-dir-ent
  (implies
   (unsigned-byte-listp 8 dir-contents)
   (unsigned-byte-listp 8
                        (clear-dir-ent dir-contents filename))))

(defthm
  make-dir-ent-list-of-clear-dir-ent-lemma-1
  (implies
   (equal (char filename 0)
          (code-char #xe5))
   (useless-dir-ent-p (dir-ent-set-filename dir-ent filename)))
  :hints (("goal" :in-theory (enable useless-dir-ent-p))))

(defthm make-dir-ent-list-of-clear-dir-ent
  (equal (make-dir-ent-list (clear-dir-ent dir-contents filename))
         (delete-dir-ent (make-dir-ent-list dir-contents)
                         filename))
  :hints (("goal" :in-theory (enable make-dir-ent-list dir-ent-fix))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    make-dir-ent-list-of-append-3
    (implies
     (equal (mod (len dir-contents)
                 *ms-dir-ent-length*)
            0)
     (equal (make-dir-ent-list (append (clear-dir-ent dir-contents filename)
                                       (make-list-ac n 0 nil)))
            (delete-dir-ent (make-dir-ent-list dir-contents)
                            filename)))
    :hints (("goal" :induct (clear-dir-ent dir-contents filename)
             :in-theory (enable make-dir-ent-list dir-ent-fix)
             :expand (len dir-contents)))))

;; We're going to have to add a weird stipulation here about the length of a
;; directory file's contents being more than 0 (which is true, because dot and
;; dotdot entries have to be everywhere other than the root.)
(defun
    lofat-remove-file-by-pathname
    (fat32-in-memory rootclus pathname)
  (declare
   (xargs
    :guard (and (lofat-fs-p fat32-in-memory)
                (fat32-masked-entry-p rootclus)
                (>= rootclus *ms-first-data-cluster*)
                (< rootclus
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory)))
                (fat32-filename-list-p pathname))
    :guard-debug t
    :measure (acl2-count pathname)
    :stobjs fat32-in-memory))
  (b*
      (((unless (consp pathname))
        (mv fat32-in-memory *enoent*))
       ;; Design choice - calls which ask for the entire root directory to be
       ;; affected will fail.
       (name (mbe :logic (fat32-filename-fix (car pathname))
                  :exec (car pathname)))
       ((mv dir-contents &)
        (get-clusterchain-contents fat32-in-memory
                                   rootclus *ms-max-dir-size*))
       (dir-ent-list
        (make-dir-ent-list (string=>nats dir-contents)))
       ((mv dir-ent error-code)
        (find-dir-ent dir-ent-list name))
       ;; If it's not there, it can't be removed
       ((unless (equal error-code 0))
        (mv fat32-in-memory *enoent*))
       ;; ENOTDIR - can't delete anything that supposedly exists inside a
       ;; regular file.
       ((when (and (consp (cdr pathname)) (not (dir-ent-directory-p dir-ent))))
        (mv fat32-in-memory *enotdir*))
       (first-cluster (dir-ent-first-cluster dir-ent))
       ((when
            (or (< first-cluster *ms-first-data-cluster*)
                (<= (+ *ms-first-data-cluster*
                       (count-of-clusters fat32-in-memory))
                    first-cluster)))
        (if
            (consp (cdr pathname))
            (mv fat32-in-memory *eio*)
          (update-dir-contents fat32-in-memory rootclus
                               (nats=>string (clear-dir-ent (string=>nats dir-contents) name))
                               dir-ent)))
       ((when (consp (cdr pathname)))
        ;; Recursion
        (lofat-remove-file-by-pathname
         fat32-in-memory
         (dir-ent-first-cluster dir-ent)
         (cdr pathname)))
       ;; After these conditionals, the only remaining possibility is that
       ;; (cdr pathname) is an atom, which means we need to delete a file or
       ;; a(n empty) directory.
       (length (dir-ent-file-size dir-ent))
       ((mv clusterchain &)
        (if
            (or (< first-cluster *ms-first-data-cluster*)
                (<= (+ *ms-first-data-cluster*
                       (count-of-clusters fat32-in-memory))
                    first-cluster))
            (mv nil 0)
          (get-clusterchain
           fat32-in-memory
           first-cluster
           length)))
       (fat32-in-memory
        (stobj-set-indices-in-fa-table
         fat32-in-memory
         clusterchain
         (make-list (len clusterchain) :initial-element 0))))
    (update-dir-contents fat32-in-memory rootclus
                         (nats=>string (clear-dir-ent (string=>nats dir-contents) name))
                         dir-ent)))

(defthm
  lofat-remove-file-by-pathname-correctness-1-lemma-1
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p first-cluster)
    (<= *ms-first-data-cluster* first-cluster)
    (> (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory))
       first-cluster)
    (equal
     (mv-nth
      1
      (update-dir-contents fat32-in-memory
                           first-cluster dir-contents dir-ent))
     0)
    (stringp dir-contents)
    (< 0 (length dir-contents))
    (<= (length dir-contents)
        *ms-max-dir-size*))
   (equal
    (get-clusterchain-contents
     (mv-nth
      0
      (update-dir-contents fat32-in-memory
                           first-cluster dir-contents dir-ent))
     first-cluster *ms-max-dir-size*)
    (mv
     (implode
      (append
       (explode dir-contents)
       (make-list-ac
        (+
         (- (len (explode dir-contents)))
         (*
          (cluster-size fat32-in-memory)
          (len (make-clusters dir-contents
                              (cluster-size fat32-in-memory)))))
        (code-char 0)
        nil)))
     0)))
  :hints (("goal" :in-theory (enable update-dir-contents))))

(defthm
  lofat-remove-file-by-pathname-correctness-1-lemma-3
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (<=
     (len
      (remove1-dir-ent
       (string=>nats
        (mv-nth
         0
         (get-clusterchain-contents fat32-in-memory
                                    (dir-ent-first-cluster (car dir-ent-list))
                                    2097152)))
       ".          "))
     (+
      -32
      (len
       (explode
        (mv-nth
         0
         (get-clusterchain-contents fat32-in-memory
                                    (dir-ent-first-cluster (car dir-ent-list))
                                    2097152))))))
    (<=
     (len
      (remove1-dir-ent
       (remove1-dir-ent
        (string=>nats (mv-nth 0
                              (get-clusterchain-contents
                               fat32-in-memory
                               (dir-ent-first-cluster (car dir-ent-list))
                               2097152)))
        ".          ")
       "..         "))
     (+
      -32
      (len
       (remove1-dir-ent
        (string=>nats (mv-nth 0
                              (get-clusterchain-contents
                               fat32-in-memory
                               (dir-ent-first-cluster (car dir-ent-list))
                               2097152)))
        ".          ")))))
   (<=
    (len
     (make-dir-ent-list
      (string=>nats
       (mv-nth
        0
        (get-clusterchain-contents fat32-in-memory
                                   (dir-ent-first-cluster (car dir-ent-list))
                                   2097152)))))
    65534))
  :rule-classes :linear
  :hints
  (("goal"
    :in-theory (e/d (make-dir-ent-list-of-remove1-dir-ent)
                    (length-of-get-clusterchain-contents))
    :use
    ((:instance
      (:linear len-of-make-dir-ent-list)
      (dir-contents
       (remove1-dir-ent
        (remove1-dir-ent
         (string=>nats (mv-nth 0
                               (get-clusterchain-contents
                                fat32-in-memory
                                (dir-ent-first-cluster (car dir-ent-list))
                                2097152)))
         ".          ")
        "..         ")))
     (:instance
      (:linear painful-debugging-lemma-16)
      (j 32)
      (i1
       (len
        (remove1-dir-ent
         (remove1-dir-ent
          (string=>nats
           (mv-nth 0
                   (get-clusterchain-contents
                    fat32-in-memory
                    (dir-ent-first-cluster (car dir-ent-list))
                    2097152)))
          ".          ")
         "..         ")))
      (i2
       (+
        -32
        (len (remove1-dir-ent
              (string=>nats
               (mv-nth 0
                       (get-clusterchain-contents
                        fat32-in-memory
                        (dir-ent-first-cluster (car dir-ent-list))
                        2097152)))
              ".          ")))))
     (:instance
      (:linear painful-debugging-lemma-16)
      (j 32)
      (i1
       (+
        -32
        (len (remove1-dir-ent
              (string=>nats
               (mv-nth 0
                       (get-clusterchain-contents
                        fat32-in-memory
                        (dir-ent-first-cluster (car dir-ent-list))
                        2097152)))
              ".          "))))
      (i2
       (+
        -64
        (len
         (string=>nats (mv-nth 0
                               (get-clusterchain-contents
                                fat32-in-memory
                                (dir-ent-first-cluster (car dir-ent-list))
                                2097152)))))))
     (:instance
      (:linear painful-debugging-lemma-16)
      (j 32)
      (i1
       (+
        -64
        (len (explode (mv-nth 0
                              (get-clusterchain-contents
                               fat32-in-memory
                               (dir-ent-first-cluster (car dir-ent-list))
                               2097152))))))
      (i2 (+ -64 *ms-max-dir-size*)))
     (:instance
      (:linear length-of-get-clusterchain-contents)
      (length *ms-max-dir-size*)
      (masked-current-cluster (dir-ent-first-cluster (car dir-ent-list)))
      (fat32-in-memory fat32-in-memory))))))

(defthm
  lofat-remove-file-by-pathname-correctness-1-lemma-2
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper-exec fat32-in-memory
                                                   dir-ent-list entry-limit))
               0)
        (dir-ent-directory-p (mv-nth 0
                                     (find-dir-ent dir-ent-list filename))))
   (>=
    *ms-max-dir-ent-count*
    (len
     (make-dir-ent-list
      (string=>nats
       (mv-nth 0
               (get-clusterchain-contents
                fat32-in-memory
                (dir-ent-first-cluster
                 (mv-nth 0 (find-dir-ent dir-ent-list filename)))
                *ms-max-dir-size*)))))))
  :rule-classes :linear
  :hints
  (("goal" :in-theory
    (e/d (lofat-to-hifat-helper-exec)
         ((:definition assoc-equal)
          (:rewrite lofat-to-hifat-helper-exec-correctness-5-lemma-5
                    . 2)
          (:rewrite not-intersectp-list-of-lofat-to-hifat-helper-exec)
          (:definition free-index-listp)
          (:rewrite lofat-find-file-by-pathname-correctness-1-lemma-1)
          (:definition not-intersectp-list)
          (:rewrite nth-of-effective-fat)
          (:definition no-duplicatesp-equal)
          (:definition member-equal)))
    :induct (lofat-to-hifat-helper-exec fat32-in-memory
                                        dir-ent-list entry-limit))))

(defthm
  lofat-remove-file-by-pathname-correctness-1-lemma-4
  (implies (and (alistp alist)
                (atom (assoc-equal x alist)))
           (equal (remove-assoc-equal x alist)
                  alist))
  :hints
  (("goal"
    :in-theory (enable dir-ent-set-filename dir-ent-fix))))

(defthm
  lofat-remove-file-by-pathname-correctness-1-lemma-5
  (implies
   (and
    (dir-ent-list-p dir-ent-list)
    (not
     (equal (mv-nth 1 (find-dir-ent dir-ent-list filename1))
            0)))
   (equal
    (find-dir-ent
     (make-dir-ent-list
      (flatten (delete-dir-ent dir-ent-list filename2)))
     filename1)
    (mv (dir-ent-fix nil) *enoent*))))

(defthm
  lofat-remove-file-by-pathname-correctness-1-lemma-11
  (implies
   (and (not (zp entry-limit))
        (equal (mv-nth 3
                       (lofat-to-hifat-helper-exec
                        fat32-in-memory
                        (make-dir-ent-list (flatten (cdr dir-ent-list)))
                        (+ -1 entry-limit)))
               0))
   (equal (mv-nth 3
                  (lofat-to-hifat-helper-exec
                   fat32-in-memory
                   (make-dir-ent-list (flatten (cdr dir-ent-list)))
                   entry-limit))
          0))
  :hints
  (("goal"
    :in-theory (disable lofat-to-hifat-helper-exec-correctness-4)
    :use
    (:instance lofat-to-hifat-helper-exec-correctness-4
               (entry-limit2 entry-limit)
               (dir-ent-list (make-dir-ent-list (flatten (cdr dir-ent-list))))
               (entry-limit1 (+ -1 entry-limit))))))

(defthm
  lofat-remove-file-by-pathname-correctness-1-lemma-12
  (implies
   (and
    (not (zp entry-limit))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper-exec
       fat32-in-memory
       (make-dir-ent-list (flatten (delete-dir-ent (cdr dir-ent-list)
                                                   filename)))
       (+ -1 entry-limit)))
     0))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper-exec
      fat32-in-memory
      (make-dir-ent-list (flatten (delete-dir-ent (cdr dir-ent-list)
                                                  filename)))
      entry-limit))
    0))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-exec-correctness-4)
     (entry-limit1 (- entry-limit 1))
     (entry-limit2 entry-limit)
     (dir-ent-list
      (make-dir-ent-list (flatten (delete-dir-ent (cdr dir-ent-list)
                                                  filename))))
     (fat32-in-memory fat32-in-memory)))))

(defthm
  lofat-remove-file-by-pathname-correctness-1-lemma-13
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper-exec
       fat32-in-memory
       (make-dir-ent-list (flatten (cdr dir-ent-list)))
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper-exec
            fat32-in-memory
            (make-dir-ent-list
             (string=>nats
              (mv-nth 0
                      (get-clusterchain-contents
                       fat32-in-memory
                       (dir-ent-first-cluster (car dir-ent-list))
                       2097152))))
            (+ -1 entry-limit))))))))
     0)
    (<=
     0
     (+
      -1 entry-limit
      (-
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper-exec
          fat32-in-memory
          (make-dir-ent-list
           (string=>nats
            (mv-nth 0
                    (get-clusterchain-contents
                     fat32-in-memory
                     (dir-ent-first-cluster (car dir-ent-list))
                     2097152))))
          (+ -1 entry-limit))))))))
   (equal (mv-nth 3
                  (lofat-to-hifat-helper-exec
                   fat32-in-memory
                   (make-dir-ent-list (flatten (cdr dir-ent-list)))
                   entry-limit))
          0))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-exec-correctness-4)
     (entry-limit1
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper-exec
           fat32-in-memory
           (make-dir-ent-list
            (string=>nats
             (mv-nth 0
                     (get-clusterchain-contents
                      fat32-in-memory
                      (dir-ent-first-cluster (car dir-ent-list))
                      2097152))))
           (+ -1 entry-limit)))))))
     (entry-limit2 entry-limit)
     (dir-ent-list (make-dir-ent-list (flatten (cdr dir-ent-list))))
     (fat32-in-memory fat32-in-memory)))))

;; (defthm
;;   lofat-remove-file-by-pathname-correctness-1-lemma-6
;;   (implies
;;    (and (dir-ent-list-p dir-ent-list)
;;         (equal (mv-nth 3
;;                        (lofat-to-hifat-helper-exec fat32-in-memory
;;                                                    dir-ent-list entry-limit))
;;                0))
;;    (equal
;;     (mv-nth
;;      3
;;      (lofat-to-hifat-helper-exec
;;       fat32-in-memory
;;       (make-dir-ent-list (flatten (delete-dir-ent dir-ent-list filename)))
;;       entry-limit))
;;     0))
;;   :hints
;;   (("goal"
;;     :induct (lofat-to-hifat-helper-exec fat32-in-memory
;;                                         dir-ent-list entry-limit)
;;     :in-theory (e/d (lofat-to-hifat-helper-exec
;;                      dir-ent-list-p
;;                      make-dir-ent-list-of-remove1-dir-ent
;;                      nthcdr-when->=-n-len-l len-when-dir-ent-p)
;;                     ((:linear lofat-to-hifat-helper-exec-correctness-3)))
;;     :expand
;;     ((:free (fat32-in-memory dir-ent dir-ent-list entry-limit)
;;             (lofat-to-hifat-helper-exec fat32-in-memory
;;                                         (cons dir-ent dir-ent-list)
;;                                         entry-limit))
;;      (make-dir-ent-list (car dir-ent-list))))))

(encapsulate
  ()

  (local
   (defthm
     lofat-remove-file-by-pathname-correctness-1-lemma-7
     (implies
      (and
       (integerp entry-limit)
       (equal
        (mv-nth
         3
         (lofat-to-hifat-helper-exec
          fat32-in-memory
          (make-dir-ent-list
           (flatten (delete-dir-ent (cdr dir-ent-list)
                                   filename)))
          (+ -1 entry-limit)))
        0))
      (equal
       (lofat-to-hifat-helper-exec
        fat32-in-memory
        (make-dir-ent-list
         (flatten (delete-dir-ent (cdr dir-ent-list)
                                 filename)))
        (+ -1 entry-limit))
       (lofat-to-hifat-helper-exec
        fat32-in-memory
        (make-dir-ent-list
         (flatten (delete-dir-ent (cdr dir-ent-list)
                                 filename)))
        entry-limit)))
     :hints
     (("goal"
       :in-theory
       (disable
        (:linear lofat-to-hifat-helper-exec-correctness-3))
       :use
       ((:instance
         (:rewrite lofat-to-hifat-helper-exec-correctness-4)
         (entry-limit1 (+ -1 entry-limit))
         (entry-limit2 entry-limit)
         (dir-ent-list
          (make-dir-ent-list
           (flatten (delete-dir-ent (cdr dir-ent-list)
                                   filename))))
         (fat32-in-memory fat32-in-memory))
        (:instance
         (:linear lofat-to-hifat-helper-exec-correctness-3)
         (entry-limit (+ -1 entry-limit))
         (dir-ent-list
          (make-dir-ent-list
           (flatten (delete-dir-ent (cdr dir-ent-list)
                                   filename))))
         (fat32-in-memory fat32-in-memory)))))))

  ;; (defthm
  ;;   lofat-remove-file-by-pathname-correctness-1-lemma-8
  ;;   (implies
  ;;    (and (equal (mv-nth 3
  ;;                        (lofat-to-hifat-helper-exec fat32-in-memory
  ;;                                                    dir-ent-list entry-limit))
  ;;                0)
  ;;         (useful-dir-ent-list-p dir-ent-list))
  ;;    (equal
  ;;     (mv-nth
  ;;      0
  ;;      (lofat-to-hifat-helper-exec
  ;;       fat32-in-memory
  ;;       (delete-dir-ent dir-ent-list filename)
  ;;       entry-limit))
  ;;     (remove-assoc-equal
  ;;      filename
  ;;      (mv-nth 0
  ;;              (lofat-to-hifat-helper-exec fat32-in-memory
  ;;                                          dir-ent-list entry-limit)))))
  ;;   :hints
  ;;   (("goal"
  ;;     :in-theory (e/d (lofat-to-hifat-helper-exec useful-dir-ent-list-p))
  ;;     :induct (lofat-to-hifat-helper-exec fat32-in-memory
  ;;                                         dir-ent-list entry-limit)
  ;;     :expand (:free (fat32-in-memory dir-ent dir-ent-list entry-limit)
  ;;                    (lofat-to-hifat-helper-exec fat32-in-memory
  ;;                                                (cons dir-ent dir-ent-list)
  ;;                                                entry-limit)))
  ;;    ("subgoal *1/4"
  ;;     :use
  ;;     ((:instance
  ;;       (:rewrite lofat-to-hifat-helper-exec-correctness-4)
  ;;       (entry-limit1
  ;;        (+
  ;;         -1 entry-limit))
  ;;       (entry-limit2 entry-limit)
  ;;       (dir-ent-list (cdr dir-ent-list))
  ;;       (fat32-in-memory fat32-in-memory))
  ;;      (:instance
  ;;       (:rewrite lofat-to-hifat-helper-exec-correctness-4)
  ;;       (entry-limit1
  ;;        (+
  ;;         -1 entry-limit
  ;;         (-
  ;;          (hifat-entry-count
  ;;           (mv-nth
  ;;            0
  ;;            (lofat-to-hifat-helper-exec
  ;;             fat32-in-memory
  ;;             (make-dir-ent-list
  ;;              (string=>nats
  ;;               (mv-nth 0
  ;;                       (get-clusterchain-contents
  ;;                        fat32-in-memory
  ;;                        (dir-ent-first-cluster (car dir-ent-list))
  ;;                        2097152))))
  ;;             (+ -1 entry-limit)))))))
  ;;       (entry-limit2 entry-limit)
  ;;       (dir-ent-list (cdr dir-ent-list))
  ;;       (fat32-in-memory fat32-in-memory))))))
  )

(local
 (defthm
   lofat-remove-file-by-pathname-correctness-1-lemma-9
   (iff
    (equal
     (len
      (explode (mv-nth 0
                       (get-clusterchain-contents
                        fat32-in-memory rootclus 2097152))))
     0)
    (equal (mv-nth 0
                   (get-clusterchain-contents
                    fat32-in-memory rootclus 2097152))
           ""))
   :hints
   (("goal"
     :expand
     (len
      (explode
       (mv-nth 0
               (get-clusterchain-contents
                fat32-in-memory rootclus 2097152))))))))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defthm
    lofat-remove-file-by-pathname-correctness-1-lemma-10
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (not (zp y))
          (equal (mod length y) 0)
          (equal (mod (cluster-size fat32-in-memory) y)
                 0))
     (equal
      (mod
       (len
        (explode
         (mv-nth 0
                 (get-clusterchain-contents fat32-in-memory
                                            masked-current-cluster length))))
       y)
      0))
    :hints
    (("goal" :induct (get-clusterchain-contents fat32-in-memory
                                                masked-current-cluster length)
      :in-theory (enable get-clusterchain-contents)))))

;; (thm-cp
;;  (b*
;;      (((mv fs error-code)
;;        (hifat-remove-file-by-pathname
;;         (mv-nth 0
;;                 (lofat-to-hifat-helper-exec
;;                  fat32-in-memory
;;                  (make-dir-ent-list
;;                   (string=>nats
;;                    (mv-nth 0
;;                            (get-clusterchain-contents fat32-in-memory
;;                                                       rootclus *ms-max-dir-size*))))
;;                  entry-limit))
;;         pathname)))
;;    (implies
;;     (and
;;      (lofat-fs-p fat32-in-memory)
;;      (equal (mv-nth 3
;;                     (lofat-to-hifat-helper-exec
;;                      fat32-in-memory
;;                      (make-dir-ent-list
;;                       (string=>nats
;;                        (mv-nth 0
;;                                (get-clusterchain-contents fat32-in-memory
;;                                                           rootclus *ms-max-dir-size*))))
;;                      entry-limit))
;;             0)
;;      (fat32-masked-entry-p rootclus)
;;      (<= *ms-first-data-cluster* rootclus)
;;      (< rootclus (+ *ms-first-data-cluster* (count-of-clusters
;;                                              fat32-in-memory)))
;;      (<
;;       '0
;;       (len
;;        (make-dir-ent-list
;;         (string=>nats
;;          (mv-nth
;;           '0
;;           (get-clusterchain-contents fat32-in-memory rootclus '2097152))))))
;;      (>= *ms-max-dir-ent-count*
;;          (len
;;           (make-dir-ent-list
;;            (string=>nats
;;             (mv-nth
;;              '0
;;              (get-clusterchain-contents fat32-in-memory rootclus *ms-max-dir-size*))))))
;;      ;; This hypothesis should eventually be proved to be true and thus removed.
;;      (equal
;;       (mv-nth
;;        1
;;        (lofat-remove-file-by-pathname fat32-in-memory rootclus pathname))
;;       error-code))
;;     (hifat-equiv
;;      (mv-nth 0
;;              (lofat-to-hifat-helper-exec
;;               (mv-nth
;;                0
;;                (lofat-remove-file-by-pathname fat32-in-memory rootclus
;;                                               pathname))
;;               (make-dir-ent-list
;;                (string=>nats
;;                 (mv-nth 0
;;                         (get-clusterchain-contents
;;                          (mv-nth
;;                           0
;;                           (lofat-remove-file-by-pathname fat32-in-memory rootclus pathname))
;;                          rootclus *ms-max-dir-size*))))
;;               entry-limit))
;;      fs)))
;;  :hints
;;  (("goal"
;;    :induct
;;    (mv
;;     (mv-nth
;;      0
;;      (hifat-remove-file-by-pathname
;;       (mv-nth 0
;;               (lofat-to-hifat-helper-exec
;;                fat32-in-memory
;;                (make-dir-ent-list
;;                 (string=>nats
;;                  (mv-nth 0
;;                          (get-clusterchain-contents fat32-in-memory
;;                                                     rootclus *ms-max-dir-size*))))
;;                entry-limit))
;;       pathname))
;;     (mv-nth
;;      0
;;      (lofat-remove-file-by-pathname fat32-in-memory rootclus pathname)))
;;    :expand
;;    (lofat-remove-file-by-pathname fat32-in-memory rootclus pathname))
;;   ("subgoal *1/3"
;;    :in-theory
;;    (disable (:REWRITE LOFAT-REMOVE-FILE-BY-PATHNAME-CORRECTNESS-1-LEMMA-1))
;;    :use
;;    (:instance
;;     (:REWRITE LOFAT-REMOVE-FILE-BY-PATHNAME-CORRECTNESS-1-LEMMA-1)
;;     (DIR-ENT
;;                   (MV-NTH
;;                    0
;;                    (FIND-DIR-ENT
;;                     (MAKE-DIR-ENT-LIST
;;                        (STRING=>NATS
;;                             (MV-NTH 0
;;                                     (GET-CLUSTERCHAIN-CONTENTS
;;                                          FAT32-IN-MEMORY ROOTCLUS 2097152))))
;;                     (FAT32-FILENAME-FIX (CAR PATHNAME)))))
;;                  (DIR-CONTENTS
;;                   (NATS=>STRING
;;                    (CLEAR-DIR-ENT
;;                         (STRING=>NATS
;;                              (MV-NTH 0
;;                                      (GET-CLUSTERCHAIN-CONTENTS
;;                                           FAT32-IN-MEMORY ROOTCLUS 2097152)))
;;                         (FAT32-FILENAME-FIX (CAR PATHNAME)))))
;;                  (FIRST-CLUSTER ROOTCLUS)
;;                  (FAT32-IN-MEMORY FAT32-IN-MEMORY)))))

