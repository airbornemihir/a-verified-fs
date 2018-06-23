(in-package "ACL2")

;  file-system-m2.lisp                                  Mihir Mehta

; This is a stobj model of the FAT32 filesystem.

(include-book "file-system-m1")
(include-book "std/lists/resize-list" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(include-book "kestrel/utilities/strings" :dir :system)

(defthm len-of-chars=>nats
  (equal (len (chars=>nats chars))
         (len chars))
  :hints (("goal" :in-theory (enable chars=>nats))))

(defthm len-of-string=>nats
  (implies (stringp string)
           (equal (len (string=>nats string))
                  (length string)))
  :hints (("goal" :in-theory (enable string=>nats))))

(make-event
 `(defstobj fat32-in-memory

    ;; The following fields are noted to be common to both FAT16 and FAT32, per
    ;; the Microsoft specification.
    (bs_jmpboot :type (array (unsigned-byte 8) (3))
                ;; boilerplate
                :initially 0)
    (bs_oemname :type (array (unsigned-byte 8) (8))
                ;; boilerplate
                :initially 0)
    (bpb_bytspersec :type (unsigned-byte 16)
                    ;; per spec
                    :initially ,*ms-min-bytes-per-sector*)
    (bpb_secperclus :type (unsigned-byte 8)
                    ;; boilerplate
                    :initially 0)
    (bpb_rsvdseccnt :type (unsigned-byte 16)
                    ;; per spec
                    :initially 32)
    (bpb_numfats :type (unsigned-byte 8)
                 ;; per spec
                 :initially 2)
    (bpb_rootentcnt :type (unsigned-byte 16)
                    ;; per spec
                    :initially 0)
    (bpb_totsec16 :type (unsigned-byte 16)
                  ;; per spec
                  :initially 0)
    (bpb_media :type (unsigned-byte 8)
               ;; boilerplate
               :initially 0)
    (bpb_fatsz16 :type (unsigned-byte 16)
                 ;; per spec
                 :initially 0)
    (bpb_secpertrk :type (unsigned-byte 16)
                   ;; boilerplate
                   :initially 0)
    (bpb_numheads :type (unsigned-byte 16)
                  ;; boilerplate
                  :initially 0)
    (bpb_hiddsec :type (unsigned-byte 32)
                 ;; boilerplate
                 :initially 0)
    (bpb_totsec32 :type (unsigned-byte 32)
                  ;; boilerplate
                  :initially 0)

    ;; The following fields are noted to be specific to FAT32, per the Microsoft
    ;; specification.
    (bpb_fatsz32 :type (unsigned-byte 32)
                 ;; per spec
                 :initially ,*ms-fat32-min-count-of-clusters*)
    (bpb_extflags :type (unsigned-byte 16)
                  ;; boilerplate
                  :initially 0)
    (bpb_fsver_minor :type (unsigned-byte 8)
               ;; boilerplate
               :initially 0)
    (bpb_fsver_major :type (unsigned-byte 8)
               ;; boilerplate
               :initially 0)
    (bpb_rootclus :type (unsigned-byte 32)
                  ;; per spec
                  :initially ,*ms-first-data-cluster*)
    (bpb_fsinfo :type (unsigned-byte 16)
                ;; per spec
                :initially 1)
    (bpb_bkbootsec :type (unsigned-byte 16)
                   ;; per spec
                   :initially 6)
    (bpb_reserved :type (array (unsigned-byte 8) (12))
                  ;; boilerplate
                  :initially 0)
    (bs_drvnum :type (unsigned-byte 8)
                ;; boilerplate
                :initially 0)
    (bs_reserved1 :type (unsigned-byte 8)
                  ;; boilerplate
                  :initially 0)
    (bs_bootsig :type (unsigned-byte 8)
                ;; boilerplate
                :initially 0)
    (bs_volid :type (unsigned-byte 32)
              ;; boilerplate
              :initially 0)
    (bs_vollab :type (array (unsigned-byte 8) (11))
               ;; boilerplate
               :initially 0)
    (bs_filsystype :type (array (unsigned-byte 8) (8))
                   ;; boilerplate
                   :initially 0)

    ;; The first FAT is placed here. Other copies are not guaranteed to be
    ;; consistent.
    (fat :type (array (unsigned-byte 32) (*ms-fat32-min-count-of-clusters*))
         :resizable t
         ;; per spec
         :initially 0)

    (data-region :type (array (unsigned-byte 8) (*ms-min-data-region-size*))
         :resizable t
         ;; per spec
         :initially 0)))

(defthm bs_oemnamep-alt
  (equal (bs_oemnamep x)
         (unsigned-byte-listp 8 x))
  :rule-classes :definition)

(defthm bs_jmpbootp-alt
  (equal (bs_jmpbootp x)
         (unsigned-byte-listp 8 x))
  :rule-classes :definition)

(defthm bs_vollabp-alt
  (equal (bs_vollabp x)
         (unsigned-byte-listp 8 x))
  :rule-classes :definition)

(defthm bs_filsystypep-alt
  (equal (bs_filsystypep x)
         (unsigned-byte-listp 8 x))
  :rule-classes :definition)

(defthm fatp-alt
  (equal (fatp x) (fat32-entry-list-p x))
  :rule-classes :definition
  :hints (("goal" :in-theory (enable fat32-entry-p))))

(defthm data-regionp-alt
  (equal (data-regionp x)
         (unsigned-byte-listp 8 x))
  :rule-classes :definition)

(local
 (in-theory (disable take-of-too-many take-of-len-free)))

(local
 (in-theory (disable bs_oemnamep bs_jmpbootp bs_filsystypep fatp data-regionp)))

(local
 (in-theory (disable bpb_secperclus bpb_fatsz32 bpb_rsvdseccnt
                     bpb_numfats bpb_bytspersec bpb_rootclus bpb_fsinfo
                     bpb_bkbootsec bs_drvnum bs_reserved1 bs_bootsig
                     bpb_media bpb_fsver_major bpb_fsver_major bpb_fatsz16
                     bpb_secpertrk bpb_numheads bpb_rootentcnt
                     bpb_extflags bpb_hiddsec bpb_totsec32 bpb_fatsz32
                     bpb_rootentcnt bpb_totsec16 bs_volid
                     update-bpb_secperclus update-bpb_rsvdseccnt
                     update-bpb_bytspersec update-bpb_numfats
                     update-bpb_rootclus update-bpb_fsinfo update-bpb_bkbootsec
                     update-bs_drvnum update-bs_reserved1 update-bs_bootsig
                     update-bpb_media update-bpb_fsver_minor
                     update-bpb_fsver_major update-bpb_fatsz16
                     update-bpb_secpertrk update-bpb_numheads
                     update-bpb_extflags update-bpb_hiddsec update-bpb_totsec32
                     update-bpb_fatsz32 update-bpb_rootentcnt
                     update-bpb_totsec16 update-bs_volid)))

(local
 (in-theory (disable fati fat-length update-fati
                     data-regioni data-region-length update-data-regioni)))

(defmacro
  update-stobj-scalar-correctness
  (bit-width updater accessor
             stobj stobj-recogniser lemma-name1 lemma-name2 lemma-name3)
  `(encapsulate
     nil
     (defthm
       ,lemma-name1
       (implies (and (unsigned-byte-p ,bit-width v)
                     (,stobj-recogniser ,stobj))
                (,stobj-recogniser (,updater v ,stobj)))
       :hints (("goal" :in-theory (enable ,updater))))
     (defthm
       ,lemma-name2
       (implies (,stobj-recogniser ,stobj)
                (unsigned-byte-p ,bit-width (,accessor ,stobj)))
       :hints (("goal" :in-theory (enable ,accessor)))
       :rule-classes
       (:rewrite
        (:rewrite
         :corollary (implies (,stobj-recogniser ,stobj)
                             (integerp (,accessor ,stobj)))
         :hints
         (("goal" :use (:instance unsigned-byte-p-forward-to-nonnegative-integerp
                                  (n ,bit-width)
                                  (x (,accessor ,stobj))))))
        (:rewrite
         :corollary (implies (,stobj-recogniser ,stobj)
                             (rationalp (,accessor ,stobj)))
         :hints
         (("goal" :use (:instance unsigned-byte-p-forward-to-nonnegative-integerp
                                  (n ,bit-width)
                                  (x (,accessor ,stobj))))))))
     (defthm
       ,lemma-name3
       (equal (,accessor (,updater v ,stobj))
              v)
       :hints (("Goal" :in-theory (enable ,accessor ,updater))))))

(update-stobj-scalar-correctness 16 update-bpb_rsvdseccnt bpb_rsvdseccnt
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_rsvdseccnt-correctness-1
                                 update-bpb_rsvdseccnt-correctness-2
                                 update-bpb_rsvdseccnt-correctness-3)

(update-stobj-scalar-correctness 8 update-bpb_secperclus bpb_secperclus
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_secperclus-correctness-1
                                 update-bpb_secperclus-correctness-2
                                 update-bpb_secperclus-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_bytspersec bpb_bytspersec
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_bytspersec-correctness-1
                                 update-bpb_bytspersec-correctness-2
                                 update-bpb_bytspersec-correctness-3)

(update-stobj-scalar-correctness 8 update-bpb_numfats bpb_numfats
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_numfats-correctness-1
                                 update-bpb_numfats-correctness-2
                                 update-bpb_numfats-correctness-3)

(update-stobj-scalar-correctness 32 update-bpb_rootclus bpb_rootclus
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_rootclus-correctness-1
                                 update-bpb_rootclus-correctness-2
                                 update-bpb_rootclus-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_fsinfo bpb_fsinfo
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fsinfo-correctness-1
                                 update-bpb_fsinfo-correctness-2
                                 update-bpb_fsinfo-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_bkbootsec bpb_bkbootsec
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_bkbootsec-correctness-1
                                 update-bpb_bkbootsec-correctness-2
                                 update-bpb_bkbootsec-correctness-3)

(update-stobj-scalar-correctness 8 update-bs_drvnum bs_drvnum
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_drvnum-correctness-1
                                 update-bs_drvnum-correctness-2
                                 update-bs_drvnum-correctness-3)

(update-stobj-scalar-correctness 8 update-bs_reserved1 bs_reserved1
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_reserved1-correctness-1
                                 update-bs_reserved1-correctness-2
                                 update-bs_reserved1-correctness-3)

(update-stobj-scalar-correctness 8 update-bs_bootsig bs_bootsig
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_bootsig-correctness-1
                                 update-bs_bootsig-correctness-2
                                 update-bs_bootsig-correctness-3)

(update-stobj-scalar-correctness 8 update-bpb_media bpb_media
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_media-correctness-1
                                 update-bpb_media-correctness-2
                                 update-bpb_media-correctness-3)

(update-stobj-scalar-correctness 8 update-bpb_fsver_minor bpb_fsver_minor
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fsver_minor-correctness-1
                                 update-bpb_fsver_minor-correctness-2
                                 update-bpb_fsver_minor-correctness-3)

(update-stobj-scalar-correctness 8 update-bpb_fsver_major bpb_fsver_major
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fsver_major-correctness-1
                                 update-bpb_fsver_major-correctness-2
                                 update-bpb_fsver_major-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_fatsz16 bpb_fatsz16
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fatsz16-correctness-1
                                 update-bpb_fatsz16-correctness-2
                                 update-bpb_fatsz16-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_secpertrk bpb_secpertrk
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_secpertrk-correctness-1
                                 update-bpb_secpertrk-correctness-2
                                 update-bpb_secpertrk-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_numheads bpb_numheads
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_numheads-correctness-1
                                 update-bpb_numheads-correctness-2
                                 update-bpb_numheads-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_extflags bpb_extflags
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_extflags-correctness-1
                                 update-bpb_extflags-correctness-2
                                 update-bpb_extflags-correctness-3)

(update-stobj-scalar-correctness 32 update-bpb_hiddsec bpb_hiddsec
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_hiddsec-correctness-1
                                 update-bpb_hiddsec-correctness-2
                                 update-bpb_hiddsec-correctness-3)

(update-stobj-scalar-correctness 32 update-bpb_totsec32 bpb_totsec32
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_totsec32-correctness-1
                                 update-bpb_totsec32-correctness-2
                                 update-bpb_totsec32-correctness-3)

(update-stobj-scalar-correctness 32 update-bpb_fatsz32 bpb_fatsz32
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fatsz32-correctness-1
                                 update-bpb_fatsz32-correctness-2
                                 update-bpb_fatsz32-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_rootentcnt bpb_rootentcnt
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_rootentcnt-correctness-1
                                 update-bpb_rootentcnt-correctness-2
                                 update-bpb_rootentcnt-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_totsec16 bpb_totsec16
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_totsec16-correctness-1
                                 update-bpb_totsec16-correctness-2
                                 update-bpb_totsec16-correctness-3)

(update-stobj-scalar-correctness 32 update-bs_volid bs_volid
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_volid-correctness-1
                                 update-bs_volid-correctness-2
                                 update-bs_volid-correctness-3)

(defund cluster-size (fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory :guard (fat32-in-memoryp fat32-in-memory)))
  (* (bpb_secperclus fat32-in-memory)
     (bpb_bytspersec fat32-in-memory)))

(defund compliant-fat32-in-memoryp (fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory :guard t))
  (and (fat32-in-memoryp fat32-in-memory)
       (>= (bpb_bytspersec fat32-in-memory) *ms-min-bytes-per-sector*)
       (>= (bpb_secperclus fat32-in-memory) 1)))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top"
                       :dir :system))

  (defthm
    compliant-fat32-in-memoryp-correctness-1
    (implies (compliant-fat32-in-memoryp fat32-in-memory)
             (and (integerp (cluster-size fat32-in-memory))
                  (>= (cluster-size fat32-in-memory)
                      *ms-min-bytes-per-sector*)))
    :hints
    (("goal"
      :in-theory (e/d (compliant-fat32-in-memoryp cluster-size)
                      (fat32-in-memoryp))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (integerp (cluster-size fat32-in-memory))))
     (:forward-chaining
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (integerp (cluster-size fat32-in-memory))))
     (:linear
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (>= (cluster-size fat32-in-memory)
                   *ms-min-bytes-per-sector*))))))

(defthm
  fati-when-compliant-fat32-in-memoryp
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp i)
                (< i (fat-length fat32-in-memory)))
           (fat32-entry-p (fati i fat32-in-memory)))
  :hints (("goal" :in-theory (enable compliant-fat32-in-memoryp
                                     fati fat-length))))

(defthm
  compliant-fat32-in-memoryp-of-update-fati
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp i)
                (< i (fat-length fat32-in-memory))
                (fat32-entry-p v))
           (compliant-fat32-in-memoryp
            (update-fati i v fat32-in-memory)))
  :hints
  (("goal" :in-theory (enable compliant-fat32-in-memoryp
                              update-fati fat-length
                              bpb_bytspersec bpb_secperclus))))

(defthm
  data-regioni-when-compliant-fat32-in-memoryp
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp i)
                (< i (data-region-length fat32-in-memory)))
           (unsigned-byte-p 8 (data-regioni i fat32-in-memory)))
  :hints (("goal" :in-theory (enable compliant-fat32-in-memoryp
                                     data-regioni data-region-length))))

(defthm
  compliant-fat32-in-memoryp-of-update-data-regioni
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp i)
                (< i (data-region-length fat32-in-memory))
                (unsigned-byte-p 8 v))
           (compliant-fat32-in-memoryp
            (update-data-regioni i v fat32-in-memory)))
  :hints
  (("goal" :in-theory (enable compliant-fat32-in-memoryp
                              update-data-regioni data-region-length
                              bpb_bytspersec bpb_secperclus))))

(defconst *initialbytcnt* 16)

(defmacro
  update-stobj-array
  (name array-length bit-width array-updater array-accessor constant
        stobj stobj-recogniser lemma-name1 lemma-name2 lemma-name3 lemma-name4)
  `(encapsulate
     nil

     (defun
       ,name (v ,stobj)
       (declare
        (xargs
         :guard (and (unsigned-byte-listp ,bit-width v)
                     (<= (len v)
                         (,array-length ,stobj))
                     (,stobj-recogniser ,stobj))
         :guard-hints
         (("goal" :in-theory (disable ,stobj-recogniser unsigned-byte-p nth)))
         :stobjs (,stobj)))
       (if
           (atom v)
           ,stobj
        (let* ((,stobj
                (,array-updater (- (,array-length ,stobj)
                                       (len v))
                                (car v)
                                ,stobj))
               (,stobj (,name (cdr v)
                              ,stobj)))
          ,stobj)))

     (defthm
       ,lemma-name1
       t
       :rule-classes
       ((:rewrite :corollary
                   (equal (bpb_secperclus (,name v ,stobj))
                          (bpb_secperclus fat32-in-memory))
                   :hints (("Goal" :in-theory (enable bpb_secperclus)) ))
        (:rewrite :corollary
                   (equal (bpb_rsvdseccnt (,name v ,stobj))
                          (bpb_rsvdseccnt fat32-in-memory))
                  :hints (("Goal" :in-theory (enable bpb_rsvdseccnt)) ))
        (:rewrite :corollary
                   (equal (bpb_numfats (,name v ,stobj))
                          (bpb_numfats fat32-in-memory))
                  :hints (("Goal" :in-theory (enable bpb_numfats)) ))
        (:rewrite :corollary
                   (equal (bpb_fatsz32 (,name v ,stobj))
                          (bpb_fatsz32 fat32-in-memory))
                  :hints (("Goal" :in-theory (enable bpb_fatsz32)) ))
        (:rewrite :corollary
                   (equal (bpb_bytspersec (,name v ,stobj))
                          (bpb_bytspersec fat32-in-memory))
                   :hints (("Goal" :in-theory (enable bpb_bytspersec)) ))))

     (defthm
       ,lemma-name2 t
       :rule-classes
       ((:rewrite
         :corollary
         (implies
          (and (,stobj-recogniser ,stobj)
               (integerp i)
               (<= 0 i)
               (< i (,array-length ,stobj))
               (unsigned-byte-p ,bit-width v))
          (,stobj-recogniser (,array-updater i v ,stobj))))
        (:rewrite
         :corollary
         (implies
          (and (,stobj-recogniser ,stobj)
               (integerp i)
               (<= 0 i)
               (< i (,array-length ,stobj))
               (unsigned-byte-p ,bit-width v))
          (equal (len (nth ,constant
                           (,array-updater i v ,stobj)))
                 (len (nth ,constant ,stobj)))))))

     (defthm ,lemma-name3
       (implies (and (unsigned-byte-listp ,bit-width v)
                     (<= (len v)
                         (,array-length ,stobj))
                     (,stobj-recogniser ,stobj))
                (,stobj-recogniser (,name v ,stobj)))
       :hints (("goal" :in-theory (e/d (unsigned-byte-listp)
                                       (,stobj-recogniser ,array-updater))
                :induct
                (,stobj-recogniser (,name v ,stobj)))))

     (defthm ,lemma-name4
       (implies (and (,stobj-recogniser ,stobj)
                     (integerp i)
                     (<= 0 i)
                     (< i (,array-length ,stobj)))
                (unsigned-byte-p ,bit-width (,array-accessor i ,stobj)))
       :hints (("Goal" :in-theory (disable nth unsigned-byte-p))))))

(update-stobj-array
 update-bs_jmpboot bs_jmpboot-length 8
 update-bs_jmpbooti bs_jmpbooti *bs_jmpbooti*
 fat32-in-memory fat32-in-memoryp
 update-bs_jmpboot-correctness-1
 update-bs_jmpboot-correctness-2
 update-bs_jmpboot-correctness-3
 update-bs_jmpboot-correctness-4)

(update-stobj-array
 update-bs_oemname bs_oemname-length 8
 update-bs_oemnamei bs_oemnamei *bs_oemnamei*
 fat32-in-memory fat32-in-memoryp
 update-bs_oemname-correctness-1
 update-bs_oemname-correctness-2
 update-bs_oemname-correctness-3
 update-bs_oemname-correctness-4)

(update-stobj-array
 update-bs_vollab bs_vollab-length 8
 update-bs_vollabi bs_vollabi *bs_vollabi*
 fat32-in-memory fat32-in-memoryp
 update-bs_vollab-correctness-1
 update-bs_vollab-correctness-2
 update-bs_vollab-correctness-3
 update-bs_vollab-correctness-4)

(update-stobj-array
 update-bs_filsystype bs_filsystype-length 8
 update-bs_filsystypei bs_filsystypei *bs_filsystypei*
 fat32-in-memory fat32-in-memoryp
 update-bs_filsystype-correctness-1
 update-bs_filsystype-correctness-2
 update-bs_filsystype-correctness-3
 update-bs_filsystype-correctness-4)

(defthm
  read-reserved-area-guard-lemma-1
  (implies (and (member-equal x
                              (mv-nth 0 (read-byte$-n n channel state)))
                (state-p1 state)
                (symbolp channel)
                (open-input-channel-p1 channel
                                       :byte state)
                (not (equal (mv-nth 0 (read-byte$-n n channel state))
                            'fail)))
           (unsigned-byte-p 8 x))
  :rule-classes :forward-chaining)

(defthm
  read-reserved-area-guard-lemma-2
  (implies
   (and (natp n)
        (< (nfix m) n)
        (state-p1 state)
        (symbolp channel)
        (open-input-channel-p1 channel
                               :byte state)
        (not (equal (mv-nth 0 (read-byte$-n n channel state))
                    'fail)))
   (unsigned-byte-p
    8
    (nth m
         (mv-nth 0 (read-byte$-n n channel state)))))
  :hints
  (("goal"
    :in-theory (disable unsigned-byte-p nth)
    :use
    (:instance
     read-reserved-area-guard-lemma-1
     (x (nth m
             (mv-nth 0 (read-byte$-n n channel state))))))))

(defthm
  read-reserved-area-guard-lemma-3
  (implies
   (and (state-p1 state)
        (symbolp channel)
        (open-input-channel-p1 channel
                               :byte state)
        (not (equal (mv-nth 0 (read-byte$-n n channel state))
                    'fail)))
   (unsigned-byte-listp
    8
    (mv-nth 0 (read-byte$-n n channel state))))
  :hints (("goal" :in-theory (disable unsigned-byte-p))))

(defthm
  read-reserved-area-guard-lemma-4
  (equal (stringp (mv-nth 0 (read-byte$-n n channel state)))
         nil)
  :hints (("goal" :in-theory (disable read-byte$-n-data)
           :use read-byte$-n-data)))

(defund get-initial-bytes (str)
  (declare (xargs :guard (and (stringp str)
                              (>= (length str) *initialbytcnt*))))
  (string=>nats (subseq str 0 *initialbytcnt*)))

(defthm
  get-initial-bytes-correctness-1
  (implies (stringp str)
           (equal (len (get-initial-bytes str))
                  *initialbytcnt*))
  :hints (("goal" :in-theory (enable get-initial-bytes))))

(defthm
  get-initial-bytes-correctness-2
           (unsigned-byte-listp 8 (get-initial-bytes str))
  :hints (("goal" :in-theory (enable get-initial-bytes))))

(defund
  get-remaining-rsvdbyts (str)
  (declare (xargs :guard (and (stringp str)
                              (>= (length str) *initialbytcnt*)
                              (<= (* (combine16u (nth 12 (get-initial-bytes str))
                                                 (nth 11 (get-initial-bytes str)))
                                     (combine16u (nth 15 (get-initial-bytes str))
                                                 (nth 14 (get-initial-bytes str))))
                                  (len (explode str)))
                              (<= 16
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
  get-remaining-rsvdbyts-correctness-1
  (implies
   (stringp str)
   (equal
    (len (get-remaining-rsvdbyts str))
    (nfix
     (+ -16
        (* (combine16u (nth 12 (get-initial-bytes str))
                       (nth 11 (get-initial-bytes str)))
           (combine16u (nth 15 (get-initial-bytes str))
                       (nth 14 (get-initial-bytes str))))))))
  :hints (("goal" :in-theory (enable get-remaining-rsvdbyts))))

(defthm
  get-remaining-rsvdbyts-correctness-2
           (unsigned-byte-listp 8 (get-remaining-rsvdbyts str))
  :hints (("goal" :in-theory (enable get-remaining-rsvdbyts))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top"
                       :dir :system))

  ;; This must be called after the file is opened.
  (defun
      read-reserved-area (fat32-in-memory str)
    (declare
     (xargs
      :guard (and (stringp str)
                  (>= (length str) *initialbytcnt*)
                  (fat32-in-memoryp fat32-in-memory))
      :guard-debug t
      :guard-hints
      (("goal"
        :do-not-induct t
        :in-theory (disable fat32-in-memoryp unsigned-byte-p nth))
       ("Subgoal 7" :in-theory (disable nth-of-unsigned-byte-list)
        :use (:instance
              nth-of-unsigned-byte-list
              (n 13)
              (l (get-initial-bytes str))
              (bits 8)))
       ("Subgoal 6" :in-theory (disable nth-of-unsigned-byte-list)
        :use (:instance
              nth-of-unsigned-byte-list
              (n 0)
              (l (get-remaining-rsvdbyts str))
              (bits 8)))
       ;; ("Subgoal 8" :in-theory (disable nth-of-unsigned-byte-list)
       ;;  :use (:instance
       ;;        nth-of-unsigned-byte-list
       ;;        (n 13)
       ;;        (l (get-initial-bytes str))
       ;;        (bits 8)))
       ;; ("Subgoal 7" :in-theory (disable nth-of-unsigned-byte-list)
       ;;  :use (:instance
       ;;        nth-of-unsigned-byte-list
       ;;        (n 0)
       ;;        (l
       ;;         (STRING=>NATS
       ;;          (IMPLODE
       ;;           (TAKE
       ;;            (+
       ;;             -16
       ;;             (*
       ;;              (COMBINE16U (NTH 12
       ;;                               (GET-INITIAL-BYTES STR))
       ;;                          (NTH 11
       ;;                               (GET-INITIAL-BYTES STR)))
       ;;              (COMBINE16U (NTH 15
       ;;                               (GET-INITIAL-BYTES STR))
       ;;                          (NTH 14
       ;;                               (GET-INITIAL-BYTES STR)))))
       ;;            (NTHCDR 16 (EXPLODE STR))))))
       ;;        (bits 8)))
       ;; ("subgoal 5"
       ;;  :in-theory (disable nth-of-unsigned-byte-list)
       ;;  :use
       ;;  (:instance
       ;;   nth-of-unsigned-byte-list (bits 8)
       ;;   (n 13)
       ;;   (l (get-initial-bytes str))))
       ;; ("subgoal 4"
       ;;  :in-theory (disable nth-of-unsigned-byte-list)
       ;;  :use
       ;;  (:instance
       ;;   nth-of-unsigned-byte-list (bits 8)
       ;;   (n 0)
       ;;   (l
       ;;    (string=>nats
       ;;     (implode
       ;;      (take
       ;;       (+
       ;;        -16
       ;;        (*
       ;;         (combine16u
       ;;          (nth
       ;;           12
       ;;           (get-initial-bytes str))
       ;;          (nth 11
       ;;               (string=>nats
       ;;                (implode (take 16 (explode str))))))
       ;;         (combine16u
       ;;          (nth
       ;;           15
       ;;           (get-initial-bytes str))
       ;;          (nth 14
       ;;               (string=>nats
       ;;                (implode (take 16 (explode str))))))))
       ;;       (nthcdr 16 (explode str))))))))
       )
      :stobjs (fat32-in-memory)))
    (b*
        (;; we want to do this unconditionally, in order to prove a strong linear
         ;; rule
         (fat32-in-memory
          (update-bpb_secperclus 1
                                 fat32-in-memory))
         ;; also needs to be unconditional
         (fat32-in-memory
          (update-bpb_rsvdseccnt 1
                                 fat32-in-memory))
         ;; also needs to be unconditional
         (fat32-in-memory
          (update-bpb_numfats 1
                              fat32-in-memory))
         ;; I feel weird about stipulating this, but the FAT size has to be at
         ;; least 1 if we're going to have at least 65536 clusters of data.
         (fat32-in-memory
          (update-bpb_fatsz32 1
                              fat32-in-memory))
         ;; This needs to be at least 512, per the spec.
         (fat32-in-memory
          (update-bpb_bytspersec 512
                                 fat32-in-memory))
         ;; common stuff for fat filesystems
         (initial-bytes
          (get-initial-bytes str))
         (fat32-in-memory
          (update-bs_jmpboot (subseq initial-bytes 0 3) fat32-in-memory))
         (fat32-in-memory
          (update-bs_oemname (subseq initial-bytes 3 8) fat32-in-memory))
         (tmp_bytspersec (combine16u (nth (+ 11 1) initial-bytes)
                                     (nth (+ 11 0) initial-bytes)))
         ((unless (>= tmp_bytspersec 512))
          (mv fat32-in-memory -1))
         (fat32-in-memory
          (update-bpb_bytspersec tmp_bytspersec fat32-in-memory))
         (tmp_secperclus (nth 13 initial-bytes))
         ;; this is actually a proxy for testing membership in the set {1, 2, 4,
         ;; 8, 16, 32, 64, 128}
         ((unless (>= tmp_secperclus 1))
          (mv fat32-in-memory -1))
         (fat32-in-memory
          (update-bpb_secperclus tmp_secperclus
                                 fat32-in-memory))
         (tmp_rsvdseccnt (combine16u (nth (+ 14 1) initial-bytes)
                                     (nth (+ 14 0) initial-bytes)))
         ((unless (>= tmp_rsvdseccnt 1))
          (mv fat32-in-memory -1))
         (fat32-in-memory
          (update-bpb_rsvdseccnt tmp_rsvdseccnt fat32-in-memory))
         (tmp_rsvdbytcnt (* tmp_rsvdseccnt tmp_bytspersec))
         ((unless (and (>= tmp_rsvdbytcnt *initialbytcnt*)
                       (>= (length str) tmp_rsvdbytcnt)))
          (mv fat32-in-memory -1))
         (remaining-rsvdbyts
          (get-remaining-rsvdbyts str))
         (tmp_numfats (nth (- 16 *initialbytcnt*) remaining-rsvdbyts))
         ((unless (>= tmp_numfats 1))
          (mv fat32-in-memory -1))
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
          (mv fat32-in-memory -1))
         (fat32-in-memory
          (update-bpb_fatsz32
           tmp_fatsz32
           fat32-in-memory))
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
         ;; skipping bpb_reserved for now
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
                                    (+ 71 (- *initialbytcnt*) 11)) fat32-in-memory))
         (fat32-in-memory
          (update-bs_filsystype (subseq remaining-rsvdbyts
                                        (+ 82 (- *initialbytcnt*) 0)
                                        (+ 82 (- *initialbytcnt*) 8)) fat32-in-memory)))
      (mv fat32-in-memory 0))))

(defthm
  read-fat-guard-lemma-1
  (implies
   (and (state-p1 state)
        (symbolp channel)
        (open-input-channel-p1 channel
                               :byte state)
        (not (equal (mv-nth 0 (read-32ule-n n channel state))
                    'fail)))
   (unsigned-byte-listp
    32
    (mv-nth 0 (read-32ule-n n channel state))))
  :hints (("goal" :in-theory (disable unsigned-byte-p))))

(defun
  update-data-region
  (fat32-in-memory str len pos)
  (declare
   (xargs :guard (and (stringp str)
                      (natp len)
                      (natp pos)
                      (<= pos len)
                      (= len (length str))
                      (<= len
                          (data-region-length fat32-in-memory))
                      (<= (data-region-length fat32-in-memory)
                          *ms-max-data-region-size*))
          :guard-hints
          (("goal"
            :in-theory (e/d (data-region-length update-data-regioni)
                            (fat32-in-memoryp))))
          :guard-debug t
          :measure (nfix (- len pos))
          :stobjs fat32-in-memory))
  (b*
      ((len (the (unsigned-byte 47) len))
       (pos (the (unsigned-byte 47) pos)))
    (if
     (mbe :logic (zp (- len pos))
          :exec (>= pos len))
     fat32-in-memory
     (b*
         ((ch (char str pos))
          (ch-byte (the (unsigned-byte 8) (char-code ch)))
          (pos+1 (the (unsigned-byte 47) (1+ pos)))
          (fat32-in-memory
           (update-data-regioni pos ch-byte fat32-in-memory)))
       (update-data-region fat32-in-memory str len pos+1)))))

(defun
  update-fat (fat32-in-memory str pos)
  (declare
   (xargs :guard (and (stringp str)
                      (natp pos)
                      (<= (* pos 4) (length str))
                      (equal (length str)
                             (* (fat-length fat32-in-memory) 4))
                      (<= pos *ms-bad-cluster*))
          :guard-hints
          (("goal" :in-theory (e/d (fat-length update-fati)
                                   (fat32-in-memoryp))))
          :guard-debug t
          :stobjs fat32-in-memory))
  (b*
      ((pos (the (unsigned-byte 28) pos)))
    (if
     (zp pos)
     fat32-in-memory
     (b*
         ((ch-word
           (the
            (unsigned-byte 32)
            (combine32u (char-code (char str
                                         (the (unsigned-byte 30)
                                              (- (* pos 4) 1))))
                        (char-code (char str
                                         (the (unsigned-byte 30)
                                              (- (* pos 4) 2))))
                        (char-code (char str
                                         (the (unsigned-byte 30)
                                              (- (* pos 4) 3))))
                        (char-code (char str
                                         (the (unsigned-byte 30)
                                              (- (* pos 4) 4)))))))
          (fat32-in-memory (update-fati (- pos 1)
                                        ch-word fat32-in-memory)))
       (update-fat fat32-in-memory str
                   (the (unsigned-byte 28) (- pos 1)))))))

(defthm
  read-fat-guard-lemma-2
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (<= 0 (bpb_fatsz32 fat32-in-memory)))
  :hints (("Goal" :use update-bpb_fatsz32-correctness-2) )
  :rule-classes :linear)

(defthm
  read-fat-guard-lemma-3
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (<= 0 (bpb_bytspersec fat32-in-memory)))
  :hints (("Goal" :use update-bpb_bytspersec-correctness-2) )
  :rule-classes :linear)

(defthm
  slurp-disk-image-guard-lemma-2
  (implies (member n
                   (list *bpb_secperclus*
                         *bpb_fatsz32* *bpb_numfats*
                         *bpb_rsvdseccnt* *data-regioni*))
           (equal (nth n (update-fat fat32-in-memory str pos))
                  (nth n fat32-in-memory)))
  :hints (("goal" :in-theory (enable update-fat update-fati))))

(defthm slurp-disk-image-guard-lemma-3
  (equal (bpb_secperclus
              (update-fat fat32-in-memory str pos))
         (bpb_secperclus fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_secperclus)) ))

(defthm slurp-disk-image-guard-lemma-4
  (equal (bpb_fatsz32
              (update-fat fat32-in-memory str pos))
         (bpb_fatsz32 fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_fatsz32)) ))

(defthm slurp-disk-image-guard-lemma-5
  (equal (bpb_numfats
              (update-fat fat32-in-memory str pos))
         (bpb_numfats fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_numfats)) ))

(defthm slurp-disk-image-guard-lemma-6
  (equal (bpb_rsvdseccnt
              (update-fat fat32-in-memory str pos))
         (bpb_rsvdseccnt fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_rsvdseccnt)) ))

;; Per accumulated-persistence, the rule (:rewrite
;; update-bpb_secperclus-correctness-2 . 3) is pretty darned useless. We need
;; to find a way to do without it and its kind.
(encapsulate
  ()

  (local
   (defun
       make-corollary
       (accessor1 updater2 constant2 stobj)
     (list ':rewrite
           ':corollary
           (list 'implies
                 (list 'equal 'key constant2)
                 (list 'equal
                       (list accessor1 (list updater2 'val stobj))
                       (list accessor1 stobj)))
           ':hints
           (list (list '"goal"
                       ':in-theory
                       (list 'enable updater2))))))

  (local
   (defun
       make-corollaries
       (accessor1 updaters-constants stobj)
     (if (atom updaters-constants)
         (list ':rewrite)
       (list*
        (make-corollary
         accessor1
         (caar updaters-constants)
         (cdar updaters-constants)
         stobj)
        (make-corollaries
         accessor1 (cdr updaters-constants) stobj)))))

  (local
   (defconst *the-list*
     (list
      (cons 'update-bpb_fatsz32 *bpb_fatsz32*)
      (cons 'update-bpb_bytspersec *bpb_bytspersec*)
      (cons 'update-bpb_rsvdseccnt *bpb_rsvdseccnt*)
      (cons 'update-bpb_rootclus *bpb_rootclus*)
      (cons 'update-bs_bootsig *bs_bootsig*)
      (cons 'update-bs_reserved1 *bs_reserved1*)
      (cons 'update-bs_drvnum *bs_drvnum*)
      (cons 'update-bpb_bkbootsec *bpb_bkbootsec*)
      (cons 'update-bpb_fsinfo *bpb_fsinfo*)
      (cons 'update-bpb_fsver_major *bpb_fsver_major*)
      (cons 'update-bpb_fsver_minor *bpb_fsver_minor*)
      (cons 'update-bpb_extflags *bpb_extflags*)
      (cons 'update-bpb_secperclus *bpb_secperclus*)
      (cons 'update-bpb_totsec32 *bpb_totsec32*)
      (cons 'update-bpb_hiddsec *bpb_hiddsec*)
      (cons 'update-bpb_numheads *bpb_numheads*)
      (cons 'update-bpb_secpertrk *bpb_secpertrk*)
      (cons 'update-bpb_fatsz16 *bpb_fatsz16*)
      (cons 'update-bpb_media *bpb_media*)
      (cons 'update-bpb_totsec16 *bpb_totsec16*)
      (cons 'update-bpb_rootentcnt *bpb_rootentcnt*)
      (cons 'update-bpb_numfats *bpb_numfats*)
      (cons 'update-bs_volid *bs_volid*))))

  (make-event
   `(defthm
      slurp-disk-image-guard-lemma-7
      (implies
       (not (equal key *bpb_fatsz32*))
       (equal
        (bpb_fatsz32 (update-nth key val fat32-in-memory))
        (bpb_fatsz32 fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_fatsz32)))
      :rule-classes
      ,(make-corollaries
        'bpb_fatsz32
        (delete-assoc 'update-bpb_fatsz32 *the-list*)
        'fat32-in-memory)))

  (make-event
   `(defthm
      slurp-disk-image-guard-lemma-8
      (implies
       (not (equal key *bpb_secperclus*))
       (equal (bpb_secperclus (update-nth key val fat32-in-memory))
              (bpb_secperclus fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_secperclus)))
      :rule-classes
      ,(make-corollaries
        'bpb_secperclus
        (delete-assoc 'update-bpb_secperclus *the-list*)
        'fat32-in-memory)))

  (make-event
   `(defthm
      slurp-disk-image-guard-lemma-9
      (implies
       (not (equal key *bpb_rsvdseccnt*))
       (equal
        (bpb_rsvdseccnt (update-nth key val fat32-in-memory))
        (bpb_rsvdseccnt fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_rsvdseccnt)))
      :rule-classes
      ,(make-corollaries
        'bpb_rsvdseccnt
        (delete-assoc 'update-bpb_rsvdseccnt *the-list*)
        'fat32-in-memory)))

  (make-event
   `(defthm
      slurp-disk-image-guard-lemma-10
      (implies
       (not (equal key *bpb_numfats*))
       (equal
        (bpb_numfats (update-nth key val fat32-in-memory))
        (bpb_numfats fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_numfats)))
      :rule-classes
      ,(make-corollaries
        'bpb_numfats
        (delete-assoc 'update-bpb_numfats *the-list*)
        'fat32-in-memory)))

  (make-event
   `(defthm
      slurp-disk-image-guard-lemma-31
      (implies
       (not (equal key *bpb_bytspersec*))
       (equal
        (bpb_bytspersec (update-nth key val fat32-in-memory))
        (bpb_bytspersec fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_bytspersec)))
      :rule-classes
      ,(make-corollaries
        'bpb_bytspersec
        (delete-assoc 'update-bpb_bytspersec *the-list*)
        'fat32-in-memory))))

;; BOZO: Remove these.

(defthm
  slurp-disk-image-guard-lemma-11
  (implies (and (integerp x) (integerp y))
           (integerp (+ x y))))

(defthm
  slurp-disk-image-guard-lemma-12
  (implies (and (integerp x) (integerp y))
           (integerp (* x y))))

;; (defun m2-stricter-fs-p (fat32-in-memory)
;;   (declare (xargs :guard t))
;;   (and (fat32-in-memoryp fat32-in-memory)
;;        (<= 1
;;            (bpb_secperclus fat32-in-memory))
;;        (<= 1
;;            (bpb_rsvdseccnt fat32-in-memory))))

(defthm
  slurp-disk-image-guard-lemma-13
  (<= 1
      (bpb_secperclus
       (mv-nth 0
               (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable fat32-in-memoryp nth subseq))))

(defthm
  slurp-disk-image-guard-lemma-14
  (<= 1
      (bpb_rsvdseccnt
       (mv-nth
        0
        (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable fat32-in-memoryp nth subseq))))

(defthm
  slurp-disk-image-guard-lemma-15
  (<= 1
      (bpb_numfats
       (mv-nth
        0
        (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable fat32-in-memoryp nth subseq))))

(defthm
  slurp-disk-image-guard-lemma-16
  (<= 1
      (bpb_fatsz32
       (mv-nth
        0
        (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable fat32-in-memoryp nth subseq))))

(defthm
  slurp-disk-image-guard-lemma-17
  (<= *ms-min-bytes-per-sector*
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable fat32-in-memoryp nth subseq))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top"
                       :dir :system))

  (defthm
    read-reserved-area-correctness-1
    (implies (and (fat32-in-memoryp fat32-in-memory)
                  (stringp str))
             (fat32-in-memoryp
              (mv-nth 0
                      (read-reserved-area fat32-in-memory str))))
    :hints
    (("Goal" :in-theory (disable fat32-in-memoryp)))))

(defun
    slurp-disk-image
    (fat32-in-memory image-path state)
  (declare
   (xargs
    :guard (and (stringp image-path)
                (fat32-in-memoryp fat32-in-memory))
    :guard-debug t
    :guard-hints
    (("goal" :do-not-induct t
      :in-theory (disable fat32-in-memoryp
                          read-reserved-area)))
    :stobjs (fat32-in-memory state)))
  (b* ((str
        (read-file-into-string image-path))
       ((unless (and (stringp str)
                     (>= (length str) *initialbytcnt*)))
        (mv fat32-in-memory -1))
       ((mv fat32-in-memory error-code)
        (read-reserved-area fat32-in-memory str))
       ((unless (equal error-code 0))
        (mv fat32-in-memory error-code))
       (fat-read-size (/ (* (bpb_fatsz32 fat32-in-memory) (bpb_bytspersec
                                                           fat32-in-memory)) 4))
       ((unless (integerp fat-read-size)) (mv fat32-in-memory -1))
       (data-byte-count
        (* (- (bpb_totsec32 fat32-in-memory)
              (+ (bpb_rsvdseccnt fat32-in-memory)
                 (* (bpb_numfats fat32-in-memory)
                    (bpb_fatsz32 fat32-in-memory))))
           (bpb_bytspersec fat32-in-memory)))
       ((unless (> data-byte-count 0))
        (mv fat32-in-memory -1))
       (tmp_bytspersec (bpb_bytspersec fat32-in-memory))
       (tmp_init (* tmp_bytspersec
                    (+ (bpb_rsvdseccnt fat32-in-memory)
                       (* (bpb_numfats fat32-in-memory) (bpb_fatsz32
                                                         fat32-in-memory)))))
       ((unless (>= (length str)
                    (+ tmp_init
                       (data-region-length fat32-in-memory))))
        (mv fat32-in-memory -1))
       (fat32-in-memory (resize-fat fat-read-size
                                    fat32-in-memory))
       (fat32-in-memory (update-fat fat32-in-memory
                                    (subseq str
                                            (cluster-size fat32-in-memory)
                                            (+
                                             (cluster-size fat32-in-memory)
                                             (* fat-read-size 4)))
                                    fat-read-size))
       (fat32-in-memory (resize-data-region data-byte-count
                                            fat32-in-memory))
       (data-region-string
        (subseq str tmp_init (+ tmp_init
                                (data-region-length fat32-in-memory))))
       (fat32-in-memory
        (update-data-region
         fat32-in-memory
         data-region-string
         (data-region-length fat32-in-memory)
         0)))
    (mv fat32-in-memory error-code)))

(defun get-dir-ent-helper (fat32-in-memory data-region-index len)
  (declare
   (xargs
    :guard (and (fat32-in-memoryp fat32-in-memory)
                (natp data-region-index)
                (natp len)
                (<= (+ data-region-index len)
                    (data-region-length fat32-in-memory)))
    :stobjs (fat32-in-memory)))
  (if (zp len)
      nil
    (cons
     (data-regioni (+ data-region-index len -1) fat32-in-memory)
     (get-dir-ent-helper fat32-in-memory data-region-index (- len 1)))))

(defthm
  get-dir-ent-helper-correctness-1-lemma-1
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (integerp i)
                (<= 0 i)
                (< i (data-region-length fat32-in-memory)))
           (unsigned-byte-p 8 (data-regioni i fat32-in-memory)))
  :hints (("goal" :in-theory (disable unsigned-byte-p))))

(defthm
  get-dir-ent-helper-correctness-1
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (natp data-region-index)
        (<= (+ data-region-index len)
            (data-region-length fat32-in-memory)))
   (and
    (unsigned-byte-listp
     8
     (get-dir-ent-helper fat32-in-memory data-region-index len))
    (equal (len (get-dir-ent-helper
                 fat32-in-memory data-region-index len))
           (nfix len))))
  :hints
  (("goal"
    :in-theory
    (e/d (unsigned-byte-listp)
         (fat32-in-memoryp unsigned-byte-p data-regioni)))))

(defund get-dir-ent (fat32-in-memory data-region-index)
  (declare
   (xargs
    :guard (and (fat32-in-memoryp fat32-in-memory)
                (natp data-region-index)
                (<= (+ data-region-index *ms-dir-ent-length*)
                    (data-region-length fat32-in-memory)))
    :stobjs (fat32-in-memory)))
  (rev (get-dir-ent-helper fat32-in-memory data-region-index
                           *ms-dir-ent-length*)))

(defthm
  get-dir-ent-correctness-1
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp data-region-index)
                (<= (+ data-region-index *ms-dir-ent-length*)
                    (data-region-length fat32-in-memory)))
           (and (unsigned-byte-listp 8 (get-dir-ent fat32-in-memory
                                                    data-region-index))
                (equal (len (get-dir-ent fat32-in-memory
                                         data-region-index))
                       *ms-dir-ent-length*)))
  :hints (("Goal" :in-theory (e/d (get-dir-ent unsigned-byte-listp)
                                  (fat32-in-memoryp)))))

;; (defun
;;   get-dir-filenames
;;   (fat32-in-memory data-region-index entry-limit)
;;   (declare (xargs :measure (acl2-count entry-limit)
;;                   :verify-guards nil
;;                   :stobjs (fat32-in-memory)))
;;   (if
;;    (or (zp entry-limit)
;;        (equal (data-regioni data-region-index fat32-in-memory)
;;               0))
;;    nil
;;    (let*
;;     ((dir-ent (get-dir-ent fat32-in-memory data-region-index))
;;      (first-cluster (combine32u (nth 21 dir-ent)
;;                                 (nth 20 dir-ent)
;;                                 (nth 27 dir-ent)
;;                                 (nth 26 dir-ent)))
;;      (filename (nats=>string (subseq dir-ent 0 11))))
;;     (list*
;;      (if (or (zp (logand (data-regioni (+ data-region-index 11)
;;                                        fat32-in-memory)
;;                          (ash 1 4)))
;;              (equal filename ".          ")
;;              (equal filename "..         "))
;;          (list* filename first-cluster)
;;          (list filename first-cluster
;;                (get-dir-filenames
;;                 fat32-in-memory
;;                 (* (nfix (- first-cluster 2))
;;                    (bpb_secperclus fat32-in-memory)
;;                    (bpb_bytspersec fat32-in-memory))
;;                 (- entry-limit 1))))
;;      (get-dir-filenames
;;       fat32-in-memory (+ data-region-index 32)
;;       (- entry-limit 1))))))

(defund
  get-clusterchain
  (fat32-in-memory masked-current-cluster length)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :measure (nfix length)
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                (fat32-masked-entry-p masked-current-cluster)
                (natp length)
                (>= masked-current-cluster 2)
                (< masked-current-cluster
                   (fat-length fat32-in-memory)))))
  (let
   ((cluster-size (cluster-size fat32-in-memory)))
   (if
    (or (zp length) (zp cluster-size))
    (mv nil (- *eio*))
    (let
     ((masked-next-cluster
       (fat32-entry-mask (fati masked-current-cluster
                               fat32-in-memory))))
     (if
      (< masked-next-cluster *ms-first-data-cluster*)
      (mv (list masked-current-cluster)
          (- *eio*))
      (if
       (or (fat32-is-eof masked-next-cluster)
           (>= masked-next-cluster
               (fat-length fat32-in-memory)))
       (mv (list masked-current-cluster) 0)
       (b*
           (((mv tail-index-list tail-error)
             (get-clusterchain fat32-in-memory masked-next-cluster
                               (nfix (- length cluster-size)))))
         (mv (list* masked-current-cluster tail-index-list)
             tail-error))))))))

(defthm
  get-clusterchain-alt
  (equal (get-clusterchain fat32-in-memory
                           masked-current-cluster length)
         (fat32-build-index-list
          (nth *fati* fat32-in-memory)
          masked-current-cluster
          length (cluster-size fat32-in-memory)))
  :rule-classes :definition
  :hints
  (("goal"
    :in-theory (enable get-clusterchain fati fat-length))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top"
                       :dir :system))

  (defun
      get-contents-from-clusterchain
      (fat32-in-memory clusterchain file-size)
    (declare
     (xargs
      :stobjs (fat32-in-memory)
      :guard
      (and (compliant-fat32-in-memoryp fat32-in-memory)
           (fat32-masked-entry-list-p clusterchain)
           (natp file-size)
           (bounded-nat-listp
            clusterchain
            (floor (data-region-length fat32-in-memory)
                   (cluster-size fat32-in-memory)))
           (lower-bounded-integer-listp
            clusterchain *ms-first-data-cluster*))
      :guard-hints
      (("goal" :in-theory (e/d (lower-bounded-integer-listp)
                               (fat32-in-memoryp))))))
    (if
        (atom clusterchain)
        nil
      (let*
          ((cluster-size (cluster-size fat32-in-memory))
           (masked-current-cluster (car clusterchain))
           (data-region-index (* (nfix (- masked-current-cluster 2))
                                 cluster-size)))
        (append
         (rev (get-dir-ent-helper fat32-in-memory data-region-index
                                  (min file-size cluster-size)))
         (get-contents-from-clusterchain
          fat32-in-memory (cdr clusterchain)
          (nfix (- file-size cluster-size)))))))

  (defun
      get-clusterchain-contents
      (fat32-in-memory masked-current-cluster length)
    (declare
     (xargs
      :stobjs fat32-in-memory
      :measure (nfix length)
      :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                  (fat32-masked-entry-p masked-current-cluster)
                  (natp length)
                  (>= masked-current-cluster *ms-first-data-cluster*)
                  (< masked-current-cluster
                     (floor (data-region-length fat32-in-memory)
                            (cluster-size fat32-in-memory)))
                  (<=
                   (floor (data-region-length fat32-in-memory)
                          (cluster-size fat32-in-memory))
                   (fat-length fat32-in-memory)))
      :guard-debug t
      :guard-hints (("Goal" :do-not-induct t :in-theory (e/d (cluster-size) (fat32-in-memoryp)))
                    ("Subgoal 1.10'" :in-theory (e/d (fat32-in-memoryp)
                                                 (SET-INDICES-IN-FA-TABLE-GUARD-LEMMA-3))
                     :use (:instance SET-INDICES-IN-FA-TABLE-GUARD-LEMMA-3
                                     (n MASKED-CURRENT-CLUSTER)
                                     (l
                                      (NTH *FATI* FAT32-IN-MEMORY)))))))
    (b*
        ((cluster-size (cluster-size fat32-in-memory))
         ((unless
              (and (not (zp length)) (not (zp cluster-size))))
          (mv nil (- *eio*)))
         (data-region-index (* (nfix (- masked-current-cluster 2))
                               cluster-size))
         (current-cluster-contents
          (rev (get-dir-ent-helper fat32-in-memory data-region-index
                                   (min length cluster-size))))
         (masked-next-cluster
          (fat32-entry-mask (fati masked-current-cluster
                                  fat32-in-memory)))
         ((unless
              (>= masked-next-cluster *ms-first-data-cluster*))
          (mv
           current-cluster-contents
           (- *eio*)))
         ((unless
              (and (not (fat32-is-eof masked-next-cluster))
                   (< masked-next-cluster
                      (floor (data-region-length fat32-in-memory)
                             (cluster-size fat32-in-memory)))))
          (mv current-cluster-contents 0))
         ((mv tail-character-list tail-error)
          (get-clusterchain-contents fat32-in-memory masked-next-cluster
                                     (nfix (- length cluster-size))))
         ((unless (equal tail-error 0)) (mv nil (- *eio*))))
      (mv
       (append
        current-cluster-contents
        tail-character-list)
       0))))

(defthm
  get-clusterchain-contents-correctness-2-lemma-1
  (implies
   (not
    (equal
     (mv-nth
      1
      (fat32-build-index-list fa-table masked-current-cluster
                              length cluster-size))
     0))
   (equal
    (mv-nth
     1
     (fat32-build-index-list fa-table masked-current-cluster
                             length cluster-size))
    (- *eio*)))
  :hints (("goal" :in-theory (disable fat32-in-memoryp))))

(defthm
  get-clusterchain-contents-correctness-2
  (implies
   (and (fat32-masked-entry-p masked-current-cluster)
        (>= masked-current-cluster
            *ms-first-data-cluster*)
        (fat32-in-memoryp fat32-in-memory)
        (equal (floor (data-region-length fat32-in-memory)
                      (cluster-size fat32-in-memory))
               (fat-length fat32-in-memory)))
   (equal (mv-nth 1
                  (fat32-build-index-list
                   (nth *fati* fat32-in-memory)
                   masked-current-cluster
                   length (cluster-size fat32-in-memory)))
          (mv-nth 1
                  (get-clusterchain-contents
                   fat32-in-memory
                   masked-current-cluster length))))
  :hints (("goal" :in-theory (e/d (cluster-size fat-length fati)
                                  (fat32-in-memoryp)))))

(defthm
  get-clusterchain-contents-correctness-1
  (implies
   (and
    (fat32-masked-entry-p masked-current-cluster)
    (>= masked-current-cluster
        *ms-first-data-cluster*)
    (fat32-in-memoryp fat32-in-memory)
    (equal (floor (data-region-length fat32-in-memory)
                  (cluster-size fat32-in-memory))
           (fat-length fat32-in-memory))
    (equal
     (mv-nth
      1
      (get-clusterchain-contents fat32-in-memory
                                 masked-current-cluster length))
     0))
   (equal
    (get-contents-from-clusterchain
     fat32-in-memory
     (mv-nth 0
             (get-clusterchain fat32-in-memory
                               masked-current-cluster length))
     length)
    (mv-nth 0
            (get-clusterchain-contents
             fat32-in-memory
             masked-current-cluster length))))
  :hints
  (("goal" :in-theory (e/d (fat-length fati) (min nth fat32-in-memoryp)))))

;; This whole thing is subject to two criticisms.
;; - The choice not to treat the root directory like other directories is
;; justified on the grounds that it doesn't have a name or a directory
;; entry. However, presumably we'll want to have a function for updating the
;; contents of a directory when a new file is added, and we might have to take
;; the root as a special case.
;; - The name should be stored separately from the rest of the directory entry
;; (or perhaps even redundantly) because not being able to use assoc is a
;; serious issue.

(defun
  fat32-in-memory-to-m1-fs
  (fat32-in-memory dir-contents entry-limit)
  (declare (xargs :measure (acl2-count entry-limit)
                  :verify-guards nil
                  :stobjs (fat32-in-memory)))
  (b*
      (((when (or (zp entry-limit)
                  (equal (nth 0 dir-contents) 0)))
        nil)
       (tail (fat32-in-memory-to-m1-fs
              fat32-in-memory (nthcdr 32 dir-contents)
              (- entry-limit 1)))
       ((when (equal (nth 0 dir-contents) #xe5))
        tail)
       (dir-ent (take 32 dir-contents))
       (first-cluster (combine32u (nth 21 dir-ent)
                                  (nth 20 dir-ent)
                                  (nth 27 dir-ent)
                                  (nth 26 dir-ent)))
       (filename (nats=>string (subseq dir-ent 0 11)))
       (not-right-kind-of-directory-p
        (or (zp (logand (nth 11 dir-ent) (ash 1 4)))
            (equal filename ".          ")
            (equal filename "..         ")))
       (length (if not-right-kind-of-directory-p
                   (dir-ent-file-size dir-ent)
                   (ash 1 21)))
       ((mv contents &)
        (get-clusterchain-contents fat32-in-memory
                                   (fat32-entry-mask first-cluster)
                                   length)))
    (list*
     (cons
      filename
      (if
       not-right-kind-of-directory-p
       (make-m1-file :dir-ent dir-ent
                     :contents (nats=>string contents))
       (make-m1-file
        :dir-ent dir-ent
        :contents
        (fat32-in-memory-to-m1-fs fat32-in-memory
                                  contents (- entry-limit 1)))))
     tail)))

(defthm
  fat32-in-memory-to-m1-fs-correctness-1
  (m1-file-alist-p
   (fat32-in-memory-to-m1-fs fat32-in-memory
                             dir-contents entry-limit))
  :hints (("Goal" :in-theory (disable m1-file-p)) ))

(defund
  stobj-find-n-free-clusters-helper
  (fat32-in-memory n start)
  (declare
   (xargs :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                      (natp n)
                      (natp start))
          :stobjs fat32-in-memory
          :measure (nfix (- (fat-length fat32-in-memory)
                            start))))
  (if
   (or (zp n)
       (mbe :logic (zp (- (fat-length fat32-in-memory) start))
            :exec (>= start (fat-length fat32-in-memory))))
   nil
   (if
    (not (equal (fat32-entry-mask (fati start fat32-in-memory))
                0))
    (stobj-find-n-free-clusters-helper
     fat32-in-memory n (+ start 1))
    (cons
     start
     (stobj-find-n-free-clusters-helper fat32-in-memory (- n 1)
                                        (+ start 1))))))

(defthm
  stobj-find-n-free-clusters-helper-correctness-1
  (implies
   (natp start)
   (equal
    (stobj-find-n-free-clusters-helper fat32-in-memory n start)
    (find-n-free-clusters-helper
     (nthcdr start (nth *fati* fat32-in-memory))
     n start)))
  :hints
  (("goal"
    :in-theory (enable stobj-find-n-free-clusters-helper
                       find-n-free-clusters-helper fat-length fati)
    :induct
    (stobj-find-n-free-clusters-helper fat32-in-memory n start))
   ("subgoal *1/3''"
    :in-theory (disable len-of-nthcdr nth-of-nthcdr)
    :use ((:instance len-of-nthcdr (n start)
                     (l (nth *fati* fat32-in-memory)))
          (:instance nth-of-nthcdr (n 0)
                     (m start)
                     (x (nth *fati* fat32-in-memory)))
          (:instance nthcdr-of-cdr (i start)
                     (x (nth *fati* fat32-in-memory))))
    :expand (find-n-free-clusters-helper
             (nthcdr start (nth *fati* fat32-in-memory))
             n start))
   ("subgoal *1/2'''"
    :in-theory (disable len-of-nthcdr nth-of-nthcdr)
    :use ((:instance len-of-nthcdr (n start)
                     (l (nth *fati* fat32-in-memory)))
          (:instance nth-of-nthcdr (n 0)
                     (m start)
                     (x (nth *fati* fat32-in-memory)))
          (:instance nthcdr-of-cdr (i start)
                     (x (nth *fati* fat32-in-memory))))
    :expand (find-n-free-clusters-helper
             (nthcdr start (nth *fati* fat32-in-memory))
             n start))
   ("subgoal *1/1''"
    :in-theory (disable len-of-nthcdr nth-of-nthcdr)
    :use ((:instance len-of-nthcdr (n start)
                     (l (nth *fati* fat32-in-memory)))
          (:instance nth-of-nthcdr (n 0)
                     (m start)
                     (x (nth *fati* fat32-in-memory)))
          (:instance nthcdr-of-cdr (i start)
                     (x (nth *fati* fat32-in-memory))))
    :expand (find-n-free-clusters-helper
             (nthcdr start (nth *fati* fat32-in-memory))
             n start))))

(defund
  stobj-find-n-free-clusters
  (fat32-in-memory n)
  (declare
   (xargs :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                      (natp n))
          :stobjs fat32-in-memory))
  (stobj-find-n-free-clusters-helper
   fat32-in-memory n 2))

(defthm
  stobj-find-n-free-clusters-correctness-1
  (equal (stobj-find-n-free-clusters fat32-in-memory n)
         (find-n-free-clusters (nth *fati* fat32-in-memory)
                               n))
  :hints (("goal" :in-theory (enable stobj-find-n-free-clusters
                                     find-n-free-clusters)))
  :rule-classes :definition)

(defthm
  stobj-set-indices-in-fa-table-guard-lemma-1
  (implies (fat32-in-memoryp fat32-in-memory)
           (fat32-entry-list-p (nth *fati* fat32-in-memory))))

(defthm
  stobj-set-indices-in-fa-table-guard-lemma-2
  (implies
   (and (fat32-entry-p entry)
        (fat32-masked-entry-p masked-entry))
   (unsigned-byte-p 32
                    (fat32-update-lower-28 entry masked-entry)))
  :hints
  (("goal"
    :in-theory
    (e/d (fat32-entry-p)
         (fat32-update-lower-28-correctness-1 unsigned-byte-p))
    :use fat32-update-lower-28-correctness-1)))

(defund
  stobj-set-indices-in-fa-table
  (fat32-in-memory index-list value-list)
  (declare
   (xargs :measure (acl2-count index-list)
          :stobjs fat32-in-memory
          :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                      (nat-listp index-list)
                      (fat32-masked-entry-list-p value-list)
                      (equal (len index-list)
                             (len value-list)))
          :guard-debug t
          :guard-hints (("Goal" :in-theory (disable unsigned-byte-p)))))
  (b*
      (((when (atom index-list)) fat32-in-memory)
       (current-index (car index-list))
       ((when
            (or (not (natp current-index))
                (>= current-index (fat-length fat32-in-memory))))
        fat32-in-memory)
       (fat32-in-memory
        (update-fati current-index
                     (fat32-update-lower-28 (fati current-index fat32-in-memory)
                                            (car value-list))
                     fat32-in-memory)))
    (stobj-set-indices-in-fa-table
     fat32-in-memory
     (cdr index-list)
     (cdr value-list))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1-lemma-1
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal (update-nth *fati* (nth *fati* fat32-in-memory)
                      fat32-in-memory)
          fat32-in-memory)))

(defthm
  stobj-set-indices-in-fa-table-correctness-1-lemma-2
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal
    (fat32-in-memoryp (update-nth *fati* val fat32-in-memory))
    (fat32-entry-list-p val))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1
  (implies
   (and (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list))
        (fat32-in-memoryp fat32-in-memory))
   (equal (nth *fati*
               (stobj-set-indices-in-fa-table
                fat32-in-memory index-list value-list))
          (set-indices-in-fa-table (nth *fati* fat32-in-memory)
                                   index-list value-list)))
  :hints
  (("goal"
    :in-theory
    (e/d (set-indices-in-fa-table stobj-set-indices-in-fa-table
                                  fati fat-length update-fati)
         (fat32-in-memoryp))
    :induct t)))

(defun
  dir-ent-set-first-cluster-file-size
    (dir-ent first-cluster file-size)
  (declare (xargs :guard (and (dir-ent-p dir-ent)
                              (fat32-masked-entry-p first-cluster)
                              (unsigned-byte-p 32 file-size))))
  (let
      ((dir-ent (dir-ent-fix dir-ent))
       (first-cluster (fat32-masked-entry-fix first-cluster))
       (file-size (if (not (unsigned-byte-p 32 file-size)) 0 file-size)))
   (append
    (subseq dir-ent 0 20)
    (list* (logtail 16 (loghead 24 first-cluster))
           (logtail 24 first-cluster)
           (append (subseq dir-ent 22 26)
                   (list (loghead 8 first-cluster)
                         (logtail 8 (loghead 16 first-cluster))
                         (loghead 8 file-size)
                         (logtail 8 (loghead 16 file-size))
                         (logtail 16 (loghead 24 file-size))
                         (logtail 24 file-size)))))))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (defthm dir-ent-set-first-cluster-file-size-correctness-1
    (dir-ent-p (dir-ent-set-first-cluster-file-size dir-ent first-cluster file-size))
    :hints (("goal" :in-theory (e/d (fat32-masked-entry-fix fat32-masked-entry-p)
                                    (loghead logtail))))))

(defund make-clusters (text cluster-size)
  (declare (xargs :guard (and (character-listp text) (natp cluster-size))
                  :measure (len text)
                  :guard-debug t))
  (if (or (atom text) (zp cluster-size))
      nil
    (list*
     (make-character-list (take cluster-size text))
     (make-clusters (nthcdr cluster-size text) cluster-size))))

(defthm
  data-region-length-of-update-data-regioni
  (implies
   (and (natp i)
        (< i (data-region-length fat32-in-memory)))
   (equal (data-region-length
           (update-data-regioni i v fat32-in-memory))
          (data-region-length fat32-in-memory)))
  :hints (("goal" :in-theory (enable data-region-length
                                     update-data-regioni))))

(defun stobj-set-cluster (cluster fat32-in-memory end-index)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                              (integerp end-index)
                              (>= end-index (len cluster))
                              (<= end-index (data-region-length
                                             fat32-in-memory))
                              (unsigned-byte-listp 8 cluster))
                  :guard-hints (("Goal" :in-theory (disable fat32-in-memoryp)) )))
  (b*
      (((unless (consp cluster))
        fat32-in-memory)
       (fat32-in-memory
        (update-data-regioni (- end-index (len cluster)) (car cluster)
                             fat32-in-memory)))
    (stobj-set-cluster (cdr cluster) fat32-in-memory end-index)))

(defun cluster-listp (l fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory))
  (if
      (atom l)
      (equal l nil)
    (and (unsigned-byte-listp 8 (car l))
         (equal (len (car l))
                (cluster-size fat32-in-memory))
         (cluster-listp (cdr l) fat32-in-memory))))

(defthm
  bpb_bytspersec-of-update-data-regioni
  (equal
   (bpb_bytspersec (update-data-regioni i v fat32-in-memory))
   (bpb_bytspersec fat32-in-memory))
  :hints (("goal" :in-theory (enable update-data-regioni))))

(defthm
  bpb_secperclus-of-update-data-regioni
  (equal
   (bpb_secperclus (update-data-regioni i v fat32-in-memory))
   (bpb_secperclus fat32-in-memory))
  :hints (("goal" :in-theory (enable update-data-regioni))))

(defthm
  cluster-size-of-stobj-set-cluster
  (equal
   (cluster-size
    (stobj-set-cluster cluster fat32-in-memory end-index))
   (cluster-size fat32-in-memory))
  :hints (("goal" :in-theory (enable cluster-size))))

(defthm
  cluster-listp-of-stobj-set-cluster
  (equal
   (cluster-listp
    l
    (stobj-set-cluster cluster fat32-in-memory end-index))
   (cluster-listp l fat32-in-memory))
  :hints (("goal" :induct (cluster-listp l fat32-in-memory))))

(defthm
  compliant-fat32-in-memoryp-of-stobj-set-cluster
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (unsigned-byte-listp 8 cluster)
        (integerp end-index)
        (>= end-index (len cluster))
        (<= end-index
            (data-region-length fat32-in-memory)))
   (compliant-fat32-in-memoryp
    (stobj-set-cluster cluster fat32-in-memory end-index))))

(defthm
  data-region-length-of-stobj-set-cluster
  (implies
   (and (integerp end-index)
        (>= end-index (len cluster))
        (<= end-index
            (data-region-length fat32-in-memory)))
   (equal
    (data-region-length
     (stobj-set-cluster cluster fat32-in-memory end-index))
    (data-region-length fat32-in-memory))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top"
                       :dir :system))

  (defun
    stobj-set-clusters
    (cluster-list index-list fat32-in-memory)
    (declare
     (xargs
      :stobjs fat32-in-memory
      :guard
      (and (compliant-fat32-in-memoryp fat32-in-memory)
           (bounded-nat-listp
            index-list
            (floor (data-region-length fat32-in-memory)
                   (cluster-size fat32-in-memory)))
           (lower-bounded-integer-listp
            index-list *ms-first-data-cluster*)
           (cluster-listp cluster-list fat32-in-memory)
           (equal (len cluster-list)
                  (len index-list)))
      :guard-hints
      (("goal" :in-theory (e/d (lower-bounded-integer-listp)
                               (fat32-in-memoryp)))
       ("subgoal 7"
        :expand ((cluster-listp cluster-list fat32-in-memory)
                 (lower-bounded-integer-listp
                  index-list *ms-first-data-cluster*)))
       ("subgoal 6"
        :expand ((cluster-listp cluster-list fat32-in-memory)
                 (lower-bounded-integer-listp
                  index-list *ms-first-data-cluster*)))
       ("subgoal 5"
        :expand ((cluster-listp cluster-list fat32-in-memory))))
      :guard-debug t))
    (b*
        (((unless (consp cluster-list))
          fat32-in-memory)
         (fat32-in-memory
          (stobj-set-cluster (car cluster-list)
                             fat32-in-memory
                             (* (- (car index-list) 1)
                                (cluster-size fat32-in-memory)))))
      (stobj-set-clusters (cdr cluster-list)
                          (cdr index-list)
                          fat32-in-memory))))

;; Gotta return a list of directory entries to join up later when constructing
;; the containing directory.
(defun m1-fs-to-fat32-in-memory (fat32-in-memory fs)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (fat32-in-memoryp fat32-in-memory)
                              (m1-file-alistp fat32-in-memory))))
  (if (atom fs)
    (mv fat32-in-memory nil)
    (b*
        (((mv fat32-in-memory tail-list)
          (m1-fs-to-fat32-in-memory fat32-in-memory (cdr fs)))
         (head (car fs))
         (dir-ent (m1-file->dir-ent (cdr head)))
         ((mv fat32-in-memory dir-ent)
          (if (m1-regular-file-p (cdr head))
              (b*
                  ((contents (m1-file->contents (cdr head)))
                   (file-length (length contents))
                   (indices
                    (stobj-find-n-free-clusters
                     fat32-in-memory (ceiling
                                      (/ file-length
                                         (cluster-size fat32-in-memory)))))
                   ((mv fat32-in-memory dir-ent)
                    (if
                        (consp indices)
                        (mv (stobj-set-indices-in-fa-table fa-table-after-free
                                                           indices
                                                           (binary-append
                                                            (cdr indices)
                                                            (list
                                                             *MS-END-OF-CLUSTERCHAIN*)))
                            (dir-ent-set-first-cluster-file-size
                             dir-ent
                             (car indices)
                             file-length))
                      ;; All these expressions have 0 instead of the bit-masked
                      ;; value... meh.
                      (mv fat32-in-memory
                          (dir-ent-set-first-cluster-file-size
                           dir-ent
                           0
                           file-length))))
                   (blocks contents) ;; obviously not, but we haven't yet written
                   ;; code to split it apart
                   (fat32-in-memory
                    (stobj-set-indices fat32-in-memory indices blocks) ;; nor
                    ;; have we written code for this
                   ))
                (mv fat32-in-memory dir-ent))
            (b*
                ((contents (m1-file->contents (cdr head)))
                 (file-length 0) ;; per the specification
                 ((mv fat32-in-memory unflattened-contents)
                  (m1-fs-to-fat32-in-memory fat32-in-memory contents))
                 (contents (flatten unflattened-contents))
                 (indices
                  (stobj-find-n-free-clusters
                   fat32-in-memory (ceiling
                                    (/ file-length
                                       (cluster-size fat32-in-memory)))))
                 ((mv fat32-in-memory dir-ent)
                  (if
                      (consp indices)
                      (mv (stobj-set-indices-in-fa-table fa-table-after-free
                                                         indices
                                                         (binary-append
                                                          (cdr indices)
                                                          (list
                                                           *MS-END-OF-CLUSTERCHAIN*)))
                          (dir-ent-set-first-cluster-file-size
                           dir-ent
                           (car indices)
                           file-length))
                    ;; All these expressions have 0 instead of the bit-masked
                    ;; value... meh.
                    (mv fat32-in-memory
                        (dir-ent-set-first-cluster-file-size
                         dir-ent
                         0
                         file-length))))
                 (blocks contents) ;; obviously not, but we haven't yet written
                 ;; code to split it apart
                 (fat32-in-memory
                  (stobj-set-indices fat32-in-memory indices blocks) ;; nor
                  ;; have we written code for this
                  ))
              (mv fat32-in-memory dir-ent)))))
      (mv fat32-in-memory (list* dir-ent tail-list)))))

#|
Currently the function call to test out this function is
(b* (((mv contents &)
      (get-clusterchain-contents
       fat32-in-memory 2 (ash 1 21))))
  (get-dir-filenames
   fat32-in-memory contents (ash 1 21)))
More (rather awful) testing forms are
(b* (((mv dir-contents &)
      (get-clusterchain-contents
       fat32-in-memory 2 (ash 1 21))))
  (fat32-in-memory-to-m1-fs
  fat32-in-memory dir-contents 40))
(b* (((mv dir-contents &)
      (get-clusterchain-contents
       fat32-in-memory 2 (ash 1 21))) (fs (fat32-in-memory-to-m1-fs
  fat32-in-memory dir-contents 40) ))
  (m1-open (list "INITRD  IMG") fs nil nil))
(b* (((mv dir-contents &)
      (get-clusterchain-contents
       fat32-in-memory 2 (ash 1 21))) (fs (fat32-in-memory-to-m1-fs
  fat32-in-memory dir-contents 40) ) ((mv fd-table file-table & &)
  (m1-open (list "INITRD  IMG") fs nil nil))) (M1-PREAD
                0 6 49 FS FD-TABLE FILE-TABLE))
|#
(defun
  get-dir-filenames
  (fat32-in-memory dir-contents entry-limit)
  (declare (xargs :measure (acl2-count entry-limit)
                  :verify-guards nil
                  :stobjs (fat32-in-memory)))
  (if
   (or (zp entry-limit)
       (equal (nth 0 dir-contents)
              0))
   nil
   (let*
    ((dir-ent (take 32 dir-contents))
     (first-cluster (combine32u (nth 21 dir-ent)
                                (nth 20 dir-ent)
                                (nth 27 dir-ent)
                                (nth 26 dir-ent)))
     (filename (nats=>string (subseq dir-ent 0 11))))
    (list*
     (if (or (zp (logand (nth 11 dir-ent)
                         (ash 1 4)))
             (equal filename ".          ")
             (equal filename "..         "))
         (list filename first-cluster)
       (b*
           (((mv contents &) 
             (get-clusterchain
              fat32-in-memory
              (fat32-entry-mask first-cluster)
              (ash 1 21))) )
         (list filename first-cluster
               contents)))
     (get-dir-filenames
      fat32-in-memory (nthcdr 32 dir-contents)
      (- entry-limit 1))))))
