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

(defthm fati-of-update-fati
  (equal (fati i1 (update-fati i2 v fat32-in-memory))
         (if (equal (nfix i1) (nfix i2))
             v (fati i1 fat32-in-memory)))
  :hints (("goal" :in-theory (enable fati update-fati))))

(defthm
  data-regioni-of-update-data-regioni
  (equal
   (data-regioni i1
                 (update-data-regioni i2 v fat32-in-memory))
   (if (equal (nfix i1) (nfix i2))
       v (data-regioni i1 fat32-in-memory)))
  :hints
  (("goal"
    :in-theory (enable data-regioni update-data-regioni))))

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
      bpb_fatsz32-of-update-nth
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
      bpb_secperclus-of-update-nth
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
      bpb_rsvdseccnt-of-update-nth
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
      bpb_numfats-of-update-nth
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
      bpb_bytspersec-of-update-nth
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
        'fat32-in-memory)))

  (make-event
   `(defthm
      bpb_totsec32-of-update-nth
      (implies
       (not (equal key *bpb_totsec32*))
       (equal
        (bpb_totsec32 (update-nth key val fat32-in-memory))
        (bpb_totsec32 fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_totsec32)))
      :rule-classes
      ,(make-corollaries
        'bpb_totsec32
        (delete-assoc 'update-bpb_totsec32 *the-list*)
        'fat32-in-memory)))

  (make-event
   `(defthm
      bpb_rootclus-of-update-nth
      (implies
       (not (equal key *bpb_rootclus*))
       (equal
        (bpb_rootclus (update-nth key val fat32-in-memory))
        (bpb_rootclus fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_rootclus)))
      :rule-classes
      ,(make-corollaries
        'bpb_rootclus
        (delete-assoc 'update-bpb_rootclus *the-list*)
        'fat32-in-memory))))

(defthm bpb_rootclus-of-update-fati
  (equal (bpb_rootclus (update-fati i v fat32-in-memory))
         (bpb_rootclus fat32-in-memory))
  :hints (("Goal" :in-theory (enable update-fati))))

(defthm bpb_rootclus-of-update-data-regioni
  (equal (bpb_rootclus (update-data-regioni i v fat32-in-memory))
         (bpb_rootclus fat32-in-memory))
  :hints (("Goal" :in-theory (enable update-data-regioni))))

(defthm
  fat-length-of-update-fati
  (equal (fat-length (update-fati i v fat32-in-memory))
         (max (fat-length fat32-in-memory)
              (1+ (nfix i))))
  :hints (("goal" :in-theory (enable fat-length update-fati))))

(defthm
  fat-length-of-resize-fat
  (equal (fat-length (resize-fat i fat32-in-memory))
         (nfix i))
  :hints (("goal" :in-theory (enable fat-length resize-fat))))

(defthm
  data-regioni-of-update-fati
  (equal (data-regioni i1 (update-fati i2 v fat32-in-memory))
         (data-regioni i1 fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable data-regioni update-fati))))

(defthm
  data-region-length-of-update-data-regioni
  (equal (data-region-length (update-data-regioni i v fat32-in-memory))
         (max (data-region-length fat32-in-memory)
              (1+ (nfix i))))
  :hints (("goal" :in-theory (enable data-region-length update-data-regioni))))

(defthm
  fati-of-update-data-regioni
  (equal (fati i1
               (update-data-regioni i2 v fat32-in-memory))
         (fati i1 fat32-in-memory))
  :hints
  (("goal" :in-theory (enable fati update-data-regioni))))

(defthm
  data-region-length-of-resize-data-region
  (equal (data-region-length
          (resize-data-region i data-region32-in-memory))
         (nfix i))
  :hints (("goal" :in-theory (enable data-region-length
                                     resize-data-region))))

(defmacro
  update-stobj-array
  (name array-length bit-width array-updater array-accessor constant
        stobj stobj-recogniser lemma-name1 lemma-name2 lemma-name3
        unsigned-byte-p-of-array-accessor lemma-name5 lemma-name6 lemma-name7
        lemma-name8 lemma-name9)
  (let
      ((upper-bound (ash 1 bit-width)))
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
         (("goal" :in-theory (disable ,stobj-recogniser unsigned-byte-p)))
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
                   :hints (("Goal" :in-theory (enable bpb_bytspersec)) ))
        (:rewrite :corollary
                   (equal (bpb_totsec32 (,name v ,stobj))
                          (bpb_totsec32 fat32-in-memory))
                   :hints (("Goal" :in-theory (enable bpb_totsec32)) ))))

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

     (defthm ,unsigned-byte-p-of-array-accessor
       (implies (,stobj-recogniser ,stobj)
                (equal
                 (unsigned-byte-p ,bit-width (,array-accessor i ,stobj))
                 (< (nfix i) (,array-length ,stobj))))
       :hints (("Goal" :in-theory (disable unsigned-byte-p)))
       :rule-classes
       (:rewrite
        (:rewrite
         :corollary
         (implies (and
                   (,stobj-recogniser ,stobj)
                   (< (nfix i) (,array-length ,stobj)))
                  (integerp (,array-accessor i ,stobj)))
         :hints (("Goal" :in-theory (disable fat32-in-memoryp))))
        (:linear
         :corollary
         (implies (and
                   (,stobj-recogniser ,stobj)
                   (< (nfix i) (,array-length ,stobj)))
                  (and
                   (<= 0 (,array-accessor i ,stobj))
                   (< (,array-accessor i ,stobj) ,upper-bound)))
         :hints (("Goal" :in-theory (disable fat32-in-memoryp))))))

     (defthm ,lemma-name5
       (equal
        (resize-fat i
                    (,name v ,stobj))
        (,name v (resize-fat i ,stobj)))
       :hints (("goal" :in-theory (enable resize-fat))))

     (defthm ,lemma-name6
       (equal
        (resize-data-region i
                    (,name v ,stobj))
        (,name v (resize-data-region i ,stobj)))
       :hints (("goal" :in-theory (enable resize-data-region))))

     (defthm ,lemma-name7
       (equal (fat-length (,name v ,stobj))
              (fat-length ,stobj))
       :hints (("goal" :in-theory (enable fat-length))))

     (defthm ,lemma-name8
       (equal (data-region-length (,name v ,stobj))
              (data-region-length ,stobj))
       :hints (("goal" :in-theory (enable data-region-length))))

     ;; Why didn't this work with nfix?
     (defthm ,lemma-name9
       (implies
        (and (,stobj-recogniser ,stobj)
             (natp i)
             (< i (,array-length ,stobj)))
        (equal (,array-updater i (,array-accessor i ,stobj) ,stobj)
               ,stobj))))))

(update-stobj-array
 update-bs_jmpboot bs_jmpboot-length 8
 update-bs_jmpbooti bs_jmpbooti *bs_jmpbooti*
 fat32-in-memory fat32-in-memoryp
 update-bs_jmpboot-correctness-1
 update-bs_jmpboot-correctness-2
 update-bs_jmpboot-correctness-3
 unsigned-byte-p-of-update-bs_jmpbooti
 update-bs_jmpboot-correctness-5
 update-bs_jmpboot-correctness-6
 update-bs_jmpboot-correctness-7
 update-bs_jmpboot-correctness-8
 update-bs_jmpboot-correctness-9)

(update-stobj-array
 update-bs_oemname bs_oemname-length 8
 update-bs_oemnamei bs_oemnamei *bs_oemnamei*
 fat32-in-memory fat32-in-memoryp
 update-bs_oemname-correctness-1
 update-bs_oemname-correctness-2
 update-bs_oemname-correctness-3
 unsigned-byte-p-of-update-bs_oemnamei
 update-bs_oemname-correctness-5
 update-bs_oemname-correctness-6
 update-bs_oemname-correctness-7
 update-bs_oemname-correctness-8
 update-bs_oemname-correctness-9)

(update-stobj-array
 update-bs_vollab bs_vollab-length 8
 update-bs_vollabi bs_vollabi *bs_vollabi*
 fat32-in-memory fat32-in-memoryp
 update-bs_vollab-correctness-1
 update-bs_vollab-correctness-2
 update-bs_vollab-correctness-3
 unsigned-byte-p-of-update-bs_vollabi
 update-bs_vollab-correctness-5
 update-bs_vollab-correctness-6
 update-bs_vollab-correctness-7
 update-bs_vollab-correctness-8
 update-bs_vollab-correctness-9)

(update-stobj-array
 update-bs_filsystype bs_filsystype-length 8
 update-bs_filsystypei bs_filsystypei *bs_filsystypei*
 fat32-in-memory fat32-in-memoryp
 update-bs_filsystype-correctness-1
 update-bs_filsystype-correctness-2
 update-bs_filsystype-correctness-3
 unsigned-byte-p-of-update-bs_filsystypei
 update-bs_filsystype-correctness-5
 update-bs_filsystype-correctness-6
 update-bs_filsystype-correctness-7
 update-bs_filsystype-correctness-8
 update-bs_filsystype-correctness-9)

(update-stobj-array
 update-bpb_reserved bpb_reserved-length 8
 update-bpb_reservedi bpb_reservedi *bpb_reservedi*
 fat32-in-memory fat32-in-memoryp
 update-bpb_reserved-correctness-1
 update-bpb_reserved-correctness-2
 update-bpb_reserved-correctness-3
 unsigned-byte-p-of-update-bpb_reservedi
 update-bpb_reserved-correctness-5
 update-bpb_reserved-correctness-6
 update-bpb_reserved-correctness-7
 update-bpb_reserved-correctness-8
 update-bpb_reserved-correctness-9)

;; The strategy of just using compliant-fat32-in-memoryp everywhere is not
;; going to work. It's going to be desirable to prove lemmas with the weaker
;; hypothesis (fat32-in-memoryp fat32-in-memory) where possible, and we do want
;; to be able to use those lemmas in a context where
;; (compliant-fat32-in-memoryp fat32-in-memory) is known to be true without
;; allowing for the definition of fat32-in-memoryp to be expanded.
(in-theory (disable fat32-in-memoryp))
