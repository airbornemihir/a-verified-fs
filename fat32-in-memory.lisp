(in-package "ACL2")

;  fat32-in-memory.lisp                                 Mihir Mehta

; These are the basic definitions and lemmas for a stobj model of the FAT32
; filesystem.

(include-book "fat32")
(include-book "std/lists/resize-list" :dir :system)
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)

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

    (data-region :type (array string (*ms-fat32-min-count-of-clusters*))
         :resizable t
         ;; per spec
         :initially "")))

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

(defthm bpb_reservedp-alt
  (equal (bpb_reservedp x)
         (unsigned-byte-listp 8 x))
  :rule-classes :definition)

(defthm fatp-alt
  (equal (fatp x) (fat32-entry-list-p x))
  :rule-classes :definition
  :hints (("goal" :in-theory (enable fat32-entry-p))))

(defthm data-regionp-alt
  (equal (data-regionp x)
         (string-listp x))
  :rule-classes :definition)

(in-theory (disable bs_oemnamep bs_jmpbootp bs_filsystypep fatp data-regionp))

(in-theory (disable bpb_secperclus bpb_fatsz32 bpb_rsvdseccnt
                    bpb_numfats bpb_bytspersec bpb_rootclus bpb_fsinfo
                    bpb_bkbootsec bs_drvnum bs_reserved1 bs_bootsig
                    bpb_media bpb_fsver_minor bpb_fsver_major bpb_fatsz16
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
                    update-bpb_totsec16 update-bs_volid))

(in-theory (disable fati fat-length update-fati resize-fat
                    data-regioni data-region-length update-data-regioni
                    resize-data-region))

(defmacro
  update-stobj-scalar-correctness
  (bit-width updater accessor
             stobj stobj-recogniser lemma-name1 lemma-name2 lemma-name3
             lemma-name4 lemma-name5 updater-of-updater updater-of-accessor
             accessor-of-resize-fat)
  (let
      ((upper-bound (ash 1 bit-width)))
  `(encapsulate
     nil
     (defthm
       ,lemma-name1
       (implies (,stobj-recogniser ,stobj)
                (equal (,stobj-recogniser (,updater v ,stobj))
                       (unsigned-byte-p ,bit-width v)))
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
                                  (x (,accessor ,stobj))))))
        (:linear
         :corollary (implies (,stobj-recogniser ,stobj)
                             (and (<= 0 (,accessor ,stobj))
                                  (< (,accessor ,stobj) ,upper-bound))))))
     (defthm
       ,lemma-name3
       (equal (,accessor (,updater v ,stobj))
              v)
       :hints (("Goal" :in-theory (enable ,accessor ,updater))))
     (defthm
       ,lemma-name4
       (equal (resize-fat i (,updater v ,stobj))
              (,updater v (resize-fat i ,stobj)))
       :hints
       (("goal" :in-theory (enable resize-fat ,updater))))
     (defthm
       ,lemma-name5
       (equal (resize-data-region i (,updater v ,stobj))
              (,updater v (resize-data-region i ,stobj)))
       :hints
       (("goal" :in-theory (enable resize-data-region ,updater))))
     (defthm
       ,updater-of-updater
       (equal (,updater
               v1
               (,updater v2 fat32-in-memory))
              (,updater v1 fat32-in-memory))
       :hints (("goal" :in-theory (enable ,updater))))
     (defthm
       ,updater-of-accessor
       (implies (,stobj-recogniser ,stobj)
                (equal (,updater
                        (,accessor ,stobj)
                        ,stobj)
                       ,stobj))
       :hints (("goal" :in-theory (enable ,updater ,accessor))))
     (defthm ,accessor-of-resize-fat
       (equal (,accessor (resize-fat i fat32-in-memory))
              (,accessor ,stobj))
       :hints (("goal" :in-theory (enable resize-fat ,accessor)))))))

(update-stobj-scalar-correctness 16 update-bpb_rsvdseccnt bpb_rsvdseccnt
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_rsvdseccnt-correctness-1
                                 update-bpb_rsvdseccnt-correctness-2
                                 update-bpb_rsvdseccnt-correctness-3
                                 update-bpb_rsvdseccnt-correctness-4
                                 update-bpb_rsvdseccnt-correctness-5
                                 update-bpb_rsvdseccnt-of-update-bpb_rsvdseccnt
                                 update-bpb_rsvdseccnt-of-bpb_rsvdseccnt
                                 bpb_rsvdseccnt-of-resize-fat)

(update-stobj-scalar-correctness 8 update-bpb_secperclus bpb_secperclus
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_secperclus-correctness-1
                                 update-bpb_secperclus-correctness-2
                                 update-bpb_secperclus-correctness-3
                                 update-bpb_secperclus-correctness-4
                                 update-bpb_secperclus-correctness-5
                                 update-bpb_secperclus-of-update-bpb_secperclus
                                 update-bpb_secperclus-of-bpb_secperclus
                                 bpb_secperclus-of-resize-fat)

(update-stobj-scalar-correctness 16 update-bpb_bytspersec bpb_bytspersec
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_bytspersec-correctness-1
                                 update-bpb_bytspersec-correctness-2
                                 update-bpb_bytspersec-correctness-3
                                 update-bpb_bytspersec-correctness-4
                                 update-bpb_bytspersec-correctness-5
                                 update-bpb_bytspersec-of-update-bpb_bytspersec
                                 update-bpb_bytspersec-of-bpb_bytspersec
                                 bpb_bytspersec-of-resize-fat)

(update-stobj-scalar-correctness 8 update-bpb_numfats bpb_numfats
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_numfats-correctness-1
                                 update-bpb_numfats-correctness-2
                                 update-bpb_numfats-correctness-3
                                 update-bpb_numfats-correctness-4
                                 update-bpb_numfats-correctness-5
                                 update-bpb_numfats-of-update-bpb_numfats
                                 update-bpb_numfats-of-bpb_numfats
                                 bpb_numfats-of-resize-fat)

(update-stobj-scalar-correctness 32 update-bpb_rootclus bpb_rootclus
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_rootclus-correctness-1
                                 update-bpb_rootclus-correctness-2
                                 update-bpb_rootclus-correctness-3
                                 update-bpb_rootclus-correctness-4
                                 update-bpb_rootclus-correctness-5
                                 update-bpb_rootclus-of-update-bpb_rootclus
                                 update-bpb_rootclus-of-bpb_rootclus
                                 bpb_rootclus-of-resize-fat)

(update-stobj-scalar-correctness 16 update-bpb_fsinfo bpb_fsinfo
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fsinfo-correctness-1
                                 update-bpb_fsinfo-correctness-2
                                 update-bpb_fsinfo-correctness-3
                                 update-bpb_fsinfo-correctness-4
                                 update-bpb_fsinfo-correctness-5
                                 update-bpb_fsinfo-of-update-bpb_fsinfo
                                 update-bpb_fsinfo-of-bpb_fsinfo
                                 bpb_fsinfo-of-resize-fat)

(update-stobj-scalar-correctness 16 update-bpb_bkbootsec bpb_bkbootsec
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_bkbootsec-correctness-1
                                 update-bpb_bkbootsec-correctness-2
                                 update-bpb_bkbootsec-correctness-3
                                 update-bpb_bkbootsec-correctness-4
                                 update-bpb_bkbootsec-correctness-5
                                 update-bpb_bkbootsec-of-update-bpb_bkbootsec
                                 update-bpb_bkbootsec-of-bpb_bkbootsec
                                 bpb_bkbootsec-of-resize-fat)

(update-stobj-scalar-correctness 8 update-bs_drvnum bs_drvnum
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_drvnum-correctness-1
                                 update-bs_drvnum-correctness-2
                                 update-bs_drvnum-correctness-3
                                 update-bs_drvnum-correctness-4
                                 update-bs_drvnum-correctness-5
                                 update-bs_drvnum-of-update-bs_drvnum
                                 update-bs_drvnum-of-bs_drvnum
                                 bs_drvnum-of-resize-fat)

(update-stobj-scalar-correctness 8 update-bs_reserved1 bs_reserved1
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_reserved1-correctness-1
                                 update-bs_reserved1-correctness-2
                                 update-bs_reserved1-correctness-3
                                 update-bs_reserved1-correctness-4
                                 update-bs_reserved1-correctness-5
                                 update-bs_reserved1-of-update-bs_reserved1
                                 update-bs_reserved1-of-bs_reserved1
                                 bs_reserved1-of-resize-fat)

(update-stobj-scalar-correctness 8 update-bs_bootsig bs_bootsig
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_bootsig-correctness-1
                                 update-bs_bootsig-correctness-2
                                 update-bs_bootsig-correctness-3
                                 update-bs_bootsig-correctness-4
                                 update-bs_bootsig-correctness-5
                                 update-bs_bootsig-of-update-bs_bootsig
                                 update-bs_bootsig-of-bs_bootsig
                                 bs_bootsig-of-resize-fat)

(update-stobj-scalar-correctness 8 update-bpb_media bpb_media
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_media-correctness-1
                                 update-bpb_media-correctness-2
                                 update-bpb_media-correctness-3
                                 update-bpb_media-correctness-4
                                 update-bpb_media-correctness-5
                                 update-bpb_media-of-update-bpb_media
                                 update-bpb_media-of-bpb_media
                                 bpb_media-of-resize-fat)

(update-stobj-scalar-correctness 8 update-bpb_fsver_minor bpb_fsver_minor
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fsver_minor-correctness-1
                                 update-bpb_fsver_minor-correctness-2
                                 update-bpb_fsver_minor-correctness-3
                                 update-bpb_fsver_minor-correctness-4
                                 update-bpb_fsver_minor-correctness-5
                                 update-bpb_fsver_minor-of-update-bpb_fsver_minor
                                 update-bpb_fsver_minor-of-bpb_fsver_minor
                                 bpb_fsver_minor-of-resize-fat)

(update-stobj-scalar-correctness 8 update-bpb_fsver_major bpb_fsver_major
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fsver_major-correctness-1
                                 update-bpb_fsver_major-correctness-2
                                 update-bpb_fsver_major-correctness-3
                                 update-bpb_fsver_major-correctness-4
                                 update-bpb_fsver_major-correctness-5
                                 update-bpb_fsver_major-of-update-bpb_fsver_major
                                 update-bpb_fsver_major-of-bpb_fsver_major
                                 bpb_fsver_major-of-resize-fat)

(update-stobj-scalar-correctness 16 update-bpb_fatsz16 bpb_fatsz16
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fatsz16-correctness-1
                                 update-bpb_fatsz16-correctness-2
                                 update-bpb_fatsz16-correctness-3
                                 update-bpb_fatsz16-correctness-4
                                 update-bpb_fatsz16-correctness-5
                                 update-bpb_fatsz16-of-update-bpb_fatsz16
                                 update-bpb_fatsz16-of-bpb_fatsz16
                                 bpb_fatsz16-of-resize-fat)

(update-stobj-scalar-correctness 16 update-bpb_secpertrk bpb_secpertrk
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_secpertrk-correctness-1
                                 update-bpb_secpertrk-correctness-2
                                 update-bpb_secpertrk-correctness-3
                                 update-bpb_secpertrk-correctness-4
                                 update-bpb_secpertrk-correctness-5
                                 update-bpb_secpertrk-of-update-bpb_secpertrk
                                 update-bpb_secpertrk-of-bpb_secpertrk
                                 bpb_secpertrk-of-resize-fat)

(update-stobj-scalar-correctness 16 update-bpb_numheads bpb_numheads
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_numheads-correctness-1
                                 update-bpb_numheads-correctness-2
                                 update-bpb_numheads-correctness-3
                                 update-bpb_numheads-correctness-4
                                 update-bpb_numheads-correctness-5
                                 update-bpb_numheads-of-update-bpb_numheads
                                 update-bpb_numheads-of-bpb_numheads
                                 bpb_numheads-of-resize-fat)

(update-stobj-scalar-correctness 16 update-bpb_extflags bpb_extflags
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_extflags-correctness-1
                                 update-bpb_extflags-correctness-2
                                 update-bpb_extflags-correctness-3
                                 update-bpb_extflags-correctness-4
                                 update-bpb_extflags-correctness-5
                                 update-bpb_extflags-of-update-bpb_extflags
                                 update-bpb_extflags-of-bpb_extflags
                                 bpb_extflags-of-resize-fat)

(update-stobj-scalar-correctness 32 update-bpb_hiddsec bpb_hiddsec
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_hiddsec-correctness-1
                                 update-bpb_hiddsec-correctness-2
                                 update-bpb_hiddsec-correctness-3
                                 update-bpb_hiddsec-correctness-4
                                 update-bpb_hiddsec-correctness-5
                                 update-bpb_hiddsec-of-update-bpb_hiddsec
                                 update-bpb_hiddsec-of-bpb_hiddsec
                                 bpb_hiddsec-of-resize-fat)

(update-stobj-scalar-correctness 32 update-bpb_totsec32 bpb_totsec32
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_totsec32-correctness-1
                                 update-bpb_totsec32-correctness-2
                                 update-bpb_totsec32-correctness-3
                                 update-bpb_totsec32-correctness-4
                                 update-bpb_totsec32-correctness-5
                                 update-bpb_totsec32-of-update-bpb_totsec32
                                 update-bpb_totsec32-of-bpb_totsec32
                                 bpb_totsec32-of-resize-fat)

(update-stobj-scalar-correctness 32 update-bpb_fatsz32 bpb_fatsz32
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fatsz32-correctness-1
                                 update-bpb_fatsz32-correctness-2
                                 update-bpb_fatsz32-correctness-3
                                 update-bpb_fatsz32-correctness-4
                                 update-bpb_fatsz32-correctness-5
                                 update-bpb_fatsz32-of-update-bpb_fatsz32
                                 update-bpb_fatsz32-of-bpb_fatsz32
                                 bpb_fatsz32-of-resize-fat)

(update-stobj-scalar-correctness 16 update-bpb_rootentcnt bpb_rootentcnt
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_rootentcnt-correctness-1
                                 update-bpb_rootentcnt-correctness-2
                                 update-bpb_rootentcnt-correctness-3
                                 update-bpb_rootentcnt-correctness-4
                                 update-bpb_rootentcnt-correctness-5
                                 update-bpb_rootentcnt-of-update-bpb_rootentcnt
                                 update-bpb_rootentcnt-of-bpb_rootentcnt
                                 bpb_rootentcnt-of-resize-fat)

(update-stobj-scalar-correctness 16 update-bpb_totsec16 bpb_totsec16
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_totsec16-correctness-1
                                 update-bpb_totsec16-correctness-2
                                 update-bpb_totsec16-correctness-3
                                 update-bpb_totsec16-correctness-4
                                 update-bpb_totsec16-correctness-5
                                 update-bpb_totsec16-of-update-bpb_totsec16
                                 update-bpb_totsec16-of-bpb_totsec16
                                 bpb_totsec16-of-resize-fat)

(update-stobj-scalar-correctness 32 update-bs_volid bs_volid
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_volid-correctness-1
                                 update-bs_volid-correctness-2
                                 update-bs_volid-correctness-3
                                 update-bs_volid-correctness-4
                                 update-bs_volid-correctness-5
                                 update-bs_volid-of-update-bs_volid
                                 update-bs_volid-of-bs_volid
                                 bs_volid-of-resize-fat)
