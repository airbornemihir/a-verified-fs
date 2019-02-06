(in-package "ACL2")

;  file-system-m2.lisp                                  Mihir Mehta

; This is a stobj model of the FAT32 filesystem.

(include-book "generate-index-list")
(include-book "m1-dir-equiv")
(include-book "flatten-lemmas")

(include-book "std/lists/resize-list" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)

(defthm take-of-update-nth
  (equal (take n (update-nth key val l))
         (if (< (nfix key) (nfix n))
             (update-nth key val (take n l))
           (take n l))))

(defthm
  unsigned-byte-listp-of-make-list-ac
  (equal (unsigned-byte-listp n1 (make-list-ac n2 val ac))
         (and (unsigned-byte-listp n1 ac)
              (or (zp n2) (unsigned-byte-p n1 val)))))

(encapsulate
  ()

  (local (include-book "std/basic/inductions" :dir :system))

  (defthm take-of-make-list-ac
    (implies (<= (nfix n1) (nfix n2))
             (equal (take n1 (make-list-ac n2 val ac))
                    (make-list-ac n1 val nil)))
    :hints (("goal'" :induct (dec-dec-induct n1 n2)))))

;; This is to get the theorem about the nth element of a list of unsigned
;; bytes.
(local (include-book "std/typed-lists/integer-listp" :dir :system))

(defthm unsigned-byte-listp-of-revappend
  (equal (unsigned-byte-listp width (revappend x y))
         (and (unsigned-byte-listp width (list-fix x))
              (unsigned-byte-listp width y)))
  :hints (("goal" :induct (revappend x y))))

(encapsulate
  ()

  (local (include-book "std/basic/inductions" :dir :system))
  (defcong
    str::charlisteqv equal (chars=>nats x)
    1
    :hints
    (("goal" :in-theory (enable chars=>nats)
      :induct (cdr-cdr-induct x str::x-equiv)))))

(defthm consp-of-chars=>nats
  (iff (consp (chars=>nats chars))
       (consp chars))
  :hints (("goal" :in-theory (enable chars=>nats))))

(defthm consp-of-string=>nats
  (iff (consp (string=>nats string))
       (consp (explode string)))
  :hints (("goal" :in-theory (enable string=>nats))))

(defthm chars=>nats-of-make-list-ac
  (equal (chars=>nats (make-list-ac n val ac))
         (make-list-ac n (char-code val)
                       (chars=>nats ac)))
  :hints (("goal" :in-theory (enable chars=>nats))))

(defthm string=>nats-of-implode
  (implies (character-listp chars)
           (equal (string=>nats (implode chars))
                  (chars=>nats chars)))
  :hints (("goal" :in-theory (enable string=>nats))))

(defthmd chars=>nats-of-take
  (implies (<= (nfix n) (len chars))
           (equal (chars=>nats (take n chars))
                  (take n (chars=>nats chars))))
  :hints (("goal" :in-theory (enable chars=>nats))))

(defthmd chars=>nats-of-nthcdr
  (equal (chars=>nats (nthcdr n chars))
         (nthcdr n (chars=>nats chars)))
  :hints (("goal" :in-theory (enable chars=>nats nthcdr-of-nil))))

(defthmd chars=>nats-of-revappend
  (equal (chars=>nats (revappend x y))
         (revappend (chars=>nats x) (chars=>nats y)))
  :hints (("goal" :in-theory (enable chars=>nats))))

(defthm explode-of-nats=>string
  (equal (explode (nats=>string nats))
         (nats=>chars nats))
  :hints (("goal" :in-theory (enable nats=>string))))

(defthmd nats=>chars-of-revappend
  (equal (nats=>chars (revappend x y))
         (revappend (nats=>chars x) (nats=>chars y)))
  :hints (("goal" :in-theory (enable nats=>chars))))

(defthm explode-of-dir-ent-filename
  (equal (explode (dir-ent-filename dir-ent))
         (nats=>chars (subseq dir-ent 0 11)))
  :hints (("goal" :in-theory (enable dir-ent-filename))))

;; This relies on take-of-update-nth - it can't be moved to file-system-m1.lisp
;; until that theorem is moved to file-system-lemmas.lisp.
(defthm
  dir-ent-filename-of-dir-ent-install-directory-bit
  (implies
   (dir-ent-p dir-ent)
   (equal (dir-ent-filename
           (dir-ent-install-directory-bit dir-ent val))
          (dir-ent-filename dir-ent)))
  :hints
  (("goal" :in-theory (enable dir-ent-filename
                              dir-ent-install-directory-bit))))

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

(local
 (in-theory (disable take-of-too-many take-of-len-free make-list-ac-removal
                     revappend-removal)))

(local
 (in-theory (disable bs_oemnamep bs_jmpbootp bs_filsystypep fatp data-regionp)))

(local
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
                     update-bpb_totsec16 update-bs_volid)))

(local
 (in-theory (disable fati fat-length update-fati resize-fat
                     data-regioni data-region-length update-data-regioni
                     resize-data-region)))

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

(defund
  cluster-size (fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (fat32-in-memoryp fat32-in-memory)))
  (* (bpb_secperclus fat32-in-memory)
     (bpb_bytspersec fat32-in-memory)))

(defthm natp-of-cluster-size
  (implies (fat32-in-memoryp fat32-in-memory)
           (natp (cluster-size fat32-in-memory)))
  :hints (("goal" :in-theory (e/d (cluster-size bpb_bytspersec bpb_secperclus) ())))
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

(defund cluster-p (cluster cluster-size)
  (declare (xargs :guard t))
  (and (stringp cluster)
       (equal (length cluster) cluster-size)))

(defthm cluster-p-of-implode
  (iff (cluster-p (implode x) cluster-size)
       (equal (len x) cluster-size))
  :hints (("goal" :in-theory (enable cluster-p))))

(defthm
  cluster-p-correctness-1
  (implies (not (stringp v))
           (not (cluster-p v (cluster-size fat32-in-memory))))
  :hints (("goal" :in-theory (enable cluster-p))))

(defun cluster-listp (l cluster-size)
  (declare (xargs :guard t))
  (if
      (atom l)
      (equal l nil)
    (and (cluster-p (car l) cluster-size)
         (cluster-listp (cdr l) cluster-size))))

(defthm
  cluster-listp-of-update-nth
  (implies (cluster-listp l cluster-size)
           (equal (cluster-listp (update-nth key val l)
                                 cluster-size)
                  (and (<= (nfix key) (len l))
                       (cluster-p val cluster-size))))
  :hints (("goal" :induct (mv (update-nth key val l)
                              (cluster-listp l cluster-size))
           :in-theory (enable cluster-p))))

(defthm cluster-p-of-nth
  (implies (cluster-listp l cluster-size)
           (iff (cluster-p (nth n l) cluster-size)
                (< (nfix n) (len l))))
  :hints (("goal" :induct (nth n l)
           :in-theory (enable cluster-p))))

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
    :in-theory (enable data-regioni data-region-length)
    :induct (stobj-cluster-listp-helper fat32-in-memory n))
   ("subgoal *1/3''"
    :expand
    (cluster-listp
     (nthcdr
      (+ (- n)
         (len (nth *data-regioni* fat32-in-memory)))
      (true-list-fix (nth *data-regioni* fat32-in-memory)))
     (cluster-size fat32-in-memory)))
   ("subgoal *1/2.1"
    :in-theory (disable car-of-list-fix cdr-of-list-fix)
    :expand
    (true-list-fix (nth *data-regioni* fat32-in-memory)))
   ("subgoal *1/1.1" :in-theory (enable nthcdr-when->=-n-len-l))))

(defthm
  compliant-fat32-in-memoryp-guard-lemma-1
  (implies (fat32-in-memoryp fat32-in-memory)
           (fat32-entry-p (bpb_rootclus fat32-in-memory)))
  :hints (("goal" :in-theory (enable fat32-entry-p))))

(defund compliant-fat32-in-memoryp (fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory :guard t))
  (and (fat32-in-memoryp fat32-in-memory)
       (>= (bpb_bytspersec fat32-in-memory) *ms-min-bytes-per-sector*)
       (>= (bpb_secperclus fat32-in-memory) 1)
       (>= (count-of-clusters fat32-in-memory)
           *ms-fat32-min-count-of-clusters*)
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
          (count-of-clusters fat32-in-memory))
       ;; This is a stop-gap until we figure out the proper constraints to
       ;; impose on the cluster size. The spec (page 9) imposes both hard and
       ;; soft limits on the legal values of the cluster size, but this is less
       ;; stringent than either of those.
       (equal (mod (cluster-size fat32-in-memory) *ms-dir-ent-length*) 0)
       ;; Some array properties in addition to the scalar properties
       (stobj-cluster-listp-helper
        fat32-in-memory
        (data-region-length fat32-in-memory))
       (equal (data-region-length fat32-in-memory)
              (count-of-clusters fat32-in-memory))
       (<= (+ (count-of-clusters fat32-in-memory)
              *ms-first-data-cluster*)
           (fat-length fat32-in-memory))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    compliant-fat32-in-memoryp-correctness-1
    (implies (compliant-fat32-in-memoryp fat32-in-memory)
             (and (fat32-in-memoryp fat32-in-memory)
                  (integerp (cluster-size fat32-in-memory))
                  (>= (cluster-size fat32-in-memory)
                      *ms-min-bytes-per-sector*)
                  (>= (count-of-clusters fat32-in-memory)
                      *ms-fat32-min-count-of-clusters*)
                  (equal (mod (cluster-size fat32-in-memory) *ms-dir-ent-length*) 0)
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
                     (count-of-clusters fat32-in-memory))
                  (>= (bpb_bytspersec fat32-in-memory)
                      *ms-min-bytes-per-sector*)
                  (equal (data-region-length fat32-in-memory)
                         (count-of-clusters fat32-in-memory))
                  (<= (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*)
                      (fat-length fat32-in-memory))))
    :hints
    (("goal"
      :in-theory (e/d (compliant-fat32-in-memoryp cluster-size)
                      (fat32-in-memoryp))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (and (fat32-in-memoryp fat32-in-memory)
                    (integerp (cluster-size fat32-in-memory))
                    (equal (mod (cluster-size fat32-in-memory) *ms-dir-ent-length*) 0)
                    (equal (data-region-length fat32-in-memory)
                           (count-of-clusters fat32-in-memory)))))
     (:forward-chaining
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (integerp (cluster-size fat32-in-memory))))
     (:linear
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (and (>= (cluster-size fat32-in-memory)
                        *ms-min-bytes-per-sector*)
                    (>= (count-of-clusters fat32-in-memory)
                        *ms-fat32-min-count-of-clusters*)
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
                       (count-of-clusters fat32-in-memory))
                    (>= (bpb_bytspersec fat32-in-memory)
                        *ms-min-bytes-per-sector*)
                    (>= (* (cluster-size fat32-in-memory)
                           (count-of-clusters fat32-in-memory))
                        (* *ms-min-bytes-per-sector*
                           *ms-fat32-min-count-of-clusters*))
                    (<= (+ (count-of-clusters fat32-in-memory)
                           *ms-first-data-cluster*)
                        (fat-length fat32-in-memory))))))))

(defthm
  fati-when-compliant-fat32-in-memoryp
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (< (nfix i) (fat-length fat32-in-memory)))
           (fat32-entry-p (fati i fat32-in-memory)))
  :hints (("goal" :in-theory (enable compliant-fat32-in-memoryp
                                     fati fat-length))))

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
  cluster-size-of-update-fati
  (equal (cluster-size (update-fati i v fat32-in-memory))
         (cluster-size fat32-in-memory))
  :hints
  (("goal" :in-theory (enable cluster-size update-fati))))

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
  count-of-clusters-of-update-fati
  (equal (count-of-clusters (update-fati i v fat32-in-memory))
         (count-of-clusters fat32-in-memory))
  :hints
  (("goal"
    :in-theory (e/d (count-of-clusters update-fati bpb_totsec32)
                    (floor)))))

(defthm
  compliant-fat32-in-memoryp-of-update-fati
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (< i (fat-length fat32-in-memory)))
           (equal
            (compliant-fat32-in-memoryp
             (update-fati i v fat32-in-memory))
            (fat32-entry-p v)))
  :hints
  (("goal"
    :in-theory (e/d (compliant-fat32-in-memoryp
                     update-fati fat-length count-of-clusters
                     data-region-length)
                    (floor
                     cluster-size-of-update-fati))
    :use cluster-size-of-update-fati)))

(defthm
  data-regioni-of-update-fati
  (equal (data-regioni i1 (update-fati i2 v fat32-in-memory))
         (data-regioni i1 fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable data-regioni update-fati))))

(defthm
  data-regioni-when-compliant-fat32-in-memoryp
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (< (nfix i)
                   (data-region-length fat32-in-memory)))
           (cluster-p (data-regioni i fat32-in-memory)
                      (cluster-size fat32-in-memory)))
  :hints
  (("goal" :in-theory (e/d (compliant-fat32-in-memoryp
                            data-regioni data-region-length)
                           (unsigned-byte-p))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
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
  compliant-fat32-in-memoryp-of-update-data-regioni
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (< i (data-region-length fat32-in-memory)))
           (equal
            (compliant-fat32-in-memoryp
             (update-data-regioni i v fat32-in-memory))
            (cluster-p v (cluster-size fat32-in-memory))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (compliant-fat32-in-memoryp
                     update-data-regioni
                     data-region-length count-of-clusters
                     fat-length)
                    (floor
                     cluster-size-of-update-data-regioni))
    :use
    cluster-size-of-update-data-regioni)))

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

(defconst *initialbytcnt* 16)

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
       :hints (("Goal" :in-theory (disable nth unsigned-byte-p)))
       :rule-classes
       (:rewrite
        (:rewrite
         :corollary
         (implies (and
                   (,stobj-recogniser ,stobj)
                   (< (nfix i) (,array-length ,stobj)))
                  (integerp (,array-accessor i ,stobj)))
         :hints (("Goal" :in-theory (disable nth fat32-in-memoryp))))
        (:linear
         :corollary
         (implies (and
                   (,stobj-recogniser ,stobj)
                   (< (nfix i) (,array-length ,stobj)))
                  (and
                   (<= 0 (,array-accessor i ,stobj))
                   (< (,array-accessor i ,stobj) ,upper-bound)))
         :hints (("Goal" :in-theory (disable nth fat32-in-memoryp))))))

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

;; (encapsulate
;;   ()

;;   (local
;;    (defthm update-multiple-elements-fn-correctness-1-lemma-1
;;      (implies (natp key)
;;               (equal (update-nth key (char-code x) l)
;;                      (append (take key l)
;;                              (list (char-code x))
;;                              (nthcdr (+ 1 key) l))))))

;;   (local
;;    (defthm update-multiple-elements-fn-correctness-1-lemma-3
;;      (equal (take n (cdr l))
;;             (cdr (take (+ 1 n) l)))))

;;   (local
;;    (defthmd update-multiple-elements-fn-correctness-1-lemma-4
;;      (implies (not (zp n))
;;               (equal (cons (car l)
;;                            (append (cdr (take n l)) y))
;;                      (append (take n l) y)))))

;;   (local
;;    (defthm update-multiple-elements-fn-correctness-1-lemma-6
;;      (implies (not (zp n))
;;               (equal (cons (car l) (cdr (take n l)))
;;                      (take n l)))))

;;   (encapsulate
;;     (((update-single-element-fn * * fat32-in-memory)
;;       => fat32-in-memory)
;;      ((stobj-array-index) => *)
;;      ((stobj-array-length fat32-in-memory)
;;       => *)
;;      ((max-stobj-array-length) => *))

;;     (local
;;      (defund
;;        stobj-array-length (fat32-in-memory)
;;        (declare (xargs :guard (fat32-in-memoryp fat32-in-memory)
;;                        :stobjs fat32-in-memory))
;;        (data-region-length fat32-in-memory)))

;;     (local
;;      (defund
;;        update-single-element-fn
;;        (i v fat32-in-memory)
;;        (declare
;;         (xargs
;;          :stobjs fat32-in-memory
;;          :guard (and (fat32-in-memoryp fat32-in-memory)
;;                      (integerp i)
;;                      (<= 0 i)
;;                      (< i (stobj-array-length fat32-in-memory))
;;                      (unsigned-byte-p 8 v))
;;          :guard-hints (("Goal" :in-theory (enable
;;                                            stobj-array-length)))))
;;        (update-data-regioni i v fat32-in-memory)))

;;     (local (defund stobj-array-index () *data-regioni*))

;;     (local (defund max-stobj-array-length () *ms-max-data-region-size*))

;;     (local
;;      (defthm
;;        update-multiple-elements-fn-correctness-1-lemma-5
;;        (implies
;;         (and (natp pos)
;;              (integerp len)
;;              (< pos len))
;;         (equal
;;          (nthcdr
;;           len
;;           (nth (stobj-array-index)
;;                (update-single-element-fn pos v fat32-in-memory)))
;;          (nthcdr len
;;                  (nth (stobj-array-index)
;;                       fat32-in-memory))))
;;        :hints
;;        (("goal" :in-theory (enable update-single-element-fn))
;;         ("subgoal *1/3"
;;          :expand (update-data-regioni (+ -1 len)
;;                                       v fat32-in-memory)
;;          :in-theory (disable nthcdr-of-cdr)
;;          :use (:instance nthcdr-of-cdr
;;                          (x (nth *data-regioni* fat32-in-memory))
;;                          (i (+ -1 len)))))))

;;     (local
;;      (defthm
;;        update-multiple-elements-fn-correctness-1-lemma-7
;;        (implies
;;         (and (natp pos) (stringp str))
;;         (equal
;;          (take (+ 1 pos)
;;                (nth (stobj-array-index)
;;                     (update-single-element-fn
;;                      pos (char-code (nth pos (explode str)))
;;                      fat32-in-memory)))
;;          (append (take pos
;;                        (nth (stobj-array-index)
;;                             fat32-in-memory))
;;                  (list (char-code (nth pos (explode str)))))))
;;        :hints
;;        (("goal" :in-theory (enable update-data-regioni
;;                                    update-single-element-fn)))))

;;     (defthm
;;       update-multiple-elements-fn-correctness-1-lemma-8
;;       (implies
;;        (< (nfix i)
;;           (stobj-array-length fat32-in-memory))
;;        (equal (stobj-array-length
;;                (update-single-element-fn i v fat32-in-memory))
;;               (stobj-array-length fat32-in-memory)))
;;       :hints (("goal" :in-theory (enable update-single-element-fn
;;                                          stobj-array-length))))

;;     (defthm
;;       update-multiple-elements-fn-correctness-1-lemma-9
;;       (integerp (stobj-array-length fat32-in-memory))
;;       :hints (("goal" :in-theory (enable stobj-array-length))))

;;     (defthm
;;       update-multiple-elements-fn-correctness-1-lemma-10
;;       (implies
;;        (and (compliant-fat32-in-memoryp fat32-in-memory)
;;             (< i (stobj-array-length fat32-in-memory)))
;;        (equal (compliant-fat32-in-memoryp
;;                (update-single-element-fn i v fat32-in-memory))
;;               (unsigned-byte-p 8 v)))
;;       :hints (("goal" :in-theory (enable update-single-element-fn
;;                                          stobj-array-length))))

;;     (defthmd
;;       update-multiple-elements-fn-correctness-1-lemma-11
;;       (equal (update-single-element-fn i v fat32-in-memory)
;;              (update-nth-array (stobj-array-index)
;;                                i v fat32-in-memory))
;;       :hints (("goal" :in-theory (enable update-single-element-fn
;;                                          update-data-regioni))))

;;     (defthm
;;       update-multiple-elements-fn-correctness-1-lemma-12
;;       (integerp (max-stobj-array-length))
;;       :hints (("goal" :in-theory (enable stobj-array-length))))

;;     (defthm
;;       update-multiple-elements-fn-correctness-1-lemma-14
;;       (and
;;        (not (equal (stobj-array-index) *bpb_secperclus*))
;;        (not (equal (stobj-array-index) *bpb_rsvdseccnt*))
;;        (not (equal (stobj-array-index) *bpb_numfats*))
;;        (not (equal (stobj-array-index) *bpb_fatsz32*))
;;        (not (equal (stobj-array-index) *bpb_bytspersec*))
;;        (not (equal (stobj-array-index) *bpb_totsec32*)))
;;       :hints (("goal" :in-theory (enable stobj-array-length))))

;;     (defthm
;;       update-multiple-elements-fn-correctness-1-lemma-15
;;       (implies (and (fat32-in-memoryp fat32-in-memory)
;;                     (< i (stobj-array-length fat32-in-memory)))
;;                (equal
;;                 (fat32-in-memoryp
;;                  (update-single-element-fn i v fat32-in-memory))
;;                 (unsigned-byte-p 8 v)))
;;       :hints
;;       (("goal" :do-not-induct t
;;         :in-theory (e/d (stobj-array-length
;;                          update-multiple-elements-fn-correctness-1-lemma-11
;;                          data-region-length) (unsigned-byte-p)))))

;;     (defthm
;;       update-multiple-elements-fn-correctness-1-lemma-16
;;       (<= 0 (stobj-array-length fat32-in-memory))
;;       :rule-classes :linear
;;       :hints (("goal" :in-theory (enable stobj-array-length)))))

;;   (defun
;;     update-multiple-elements-fn
;;     (fat32-in-memory str len pos)
;;     (declare
;;      (xargs
;;       :guard (and (stringp str)
;;                   (natp len)
;;                   (natp pos)
;;                   (<= pos len)
;;                   (= len (length str))
;;                   (<= len
;;                       (stobj-array-length fat32-in-memory))
;;                   (<= (stobj-array-length fat32-in-memory)
;;                       (max-stobj-array-length)))
;;       :guard-hints
;;       (("goal"
;;         :in-theory (e/d (data-region-length update-data-regioni)
;;                         (fat32-in-memoryp))))
;;       :stobjs fat32-in-memory
;;       :measure (nfix (- len pos))))
;;     (if
;;      (zp (- len pos))
;;      fat32-in-memory
;;      (b*
;;          ((ch (char str pos))
;;           (ch-byte (char-code ch))
;;           (pos+1 (1+ pos))
;;           (fat32-in-memory
;;            (update-single-element-fn pos ch-byte fat32-in-memory)))
;;        (update-multiple-elements-fn
;;         fat32-in-memory str len pos+1))))

;;   (local
;;    (defthm
;;      update-multiple-elements-fn-correctness-1-lemma-13
;;      t
;;      :rule-classes
;;      ((:rewrite
;;        :corollary
;;        (equal (bpb_secperclus
;;                (update-single-element-fn i v fat32-in-memory))
;;               (bpb_secperclus fat32-in-memory))
;;        :hints
;;        (("goal"
;;          :in-theory
;;          (enable
;;           update-multiple-elements-fn-correctness-1-lemma-11
;;           bpb_secperclus))))
;;       (:rewrite
;;        :corollary
;;        (equal (bpb_rsvdseccnt
;;                (update-single-element-fn i v fat32-in-memory))
;;               (bpb_rsvdseccnt fat32-in-memory))
;;        :hints
;;        (("goal"
;;          :in-theory
;;          (enable
;;           update-multiple-elements-fn-correctness-1-lemma-11
;;           bpb_rsvdseccnt))))
;;       (:rewrite
;;        :corollary
;;        (equal (bpb_numfats
;;                (update-single-element-fn i v fat32-in-memory))
;;               (bpb_numfats fat32-in-memory))
;;        :hints
;;        (("goal"
;;          :in-theory
;;          (enable
;;           update-multiple-elements-fn-correctness-1-lemma-11
;;           bpb_numfats))))
;;       (:rewrite
;;        :corollary
;;        (equal (bpb_fatsz32
;;                (update-single-element-fn i v fat32-in-memory))
;;               (bpb_fatsz32 fat32-in-memory))
;;        :hints
;;        (("goal"
;;          :in-theory
;;          (enable
;;           update-multiple-elements-fn-correctness-1-lemma-11
;;           bpb_fatsz32))))
;;       (:rewrite
;;        :corollary
;;        (equal (bpb_bytspersec
;;                (update-single-element-fn i v fat32-in-memory))
;;               (bpb_bytspersec fat32-in-memory))
;;        :hints
;;        (("goal"
;;          :in-theory
;;          (enable
;;           update-multiple-elements-fn-correctness-1-lemma-11
;;           bpb_bytspersec))))
;;       (:rewrite
;;        :corollary
;;        (equal (bpb_totsec32
;;                (update-single-element-fn i v fat32-in-memory))
;;               (bpb_totsec32 fat32-in-memory))
;;        :hints
;;        (("goal"
;;          :in-theory
;;          (enable
;;           update-multiple-elements-fn-correctness-1-lemma-11
;;           bpb_totsec32)))))))

;;   (local (include-book "std/lists/nthcdr" :dir :system))

;;   (defthmd
;;     update-multiple-elements-fn-correctness-1
;;     (implies
;;      (and (natp pos)
;;           (natp len)
;;           (< pos len)
;;           (<= len
;;               (stobj-array-length fat32-in-memory))
;;           (compliant-fat32-in-memoryp fat32-in-memory)
;;           (stringp str)
;;           (<= len (length str)))
;;      (equal
;;       (update-multiple-elements-fn fat32-in-memory str len pos)
;;       (update-nth (stobj-array-index)
;;                   (append (take pos
;;                                 (nth (stobj-array-index)
;;                                      fat32-in-memory))
;;                           (string=>nats (subseq str pos len))
;;                           (nthcdr len
;;                                   (nth (stobj-array-index)
;;                                        fat32-in-memory)))
;;                   fat32-in-memory)))
;;     :hints
;;     (("goal"
;;       :in-theory (disable fat32-in-memoryp)
;;       :induct
;;       (update-multiple-elements-fn fat32-in-memory str len pos))
;;      ("subgoal *1/7''"
;;       :in-theory (e/d (update-multiple-elements-fn-correctness-1-lemma-4
;;                        string=>nats chars=>nats)
;;                       (append-of-cons))
;;       :expand
;;       ((:free (v fat32-in-memory)
;;               (update-data-regioni 0 v fat32-in-memory))))
;;      ("subgoal *1/7.2"
;;       :expand (update-data-regioni
;;                pos (char-code (nth pos (explode str)))
;;                fat32-in-memory))
;;      ("subgoal *1/4'''"
;;       :expand
;;       ((string=>nats
;;         (implode (list (nth (+ -1 len) (explode str)))))
;;        (update-data-regioni
;;         (+ -1 len)
;;         (char-code (nth (+ -1 len) (explode str)))
;;         fat32-in-memory)))
;;      ("subgoal *1/2" :in-theory (enable string=>nats))
;;      ("subgoal *1/2.3'''"
;;       :in-theory
;;       (e/d (update-multiple-elements-fn-correctness-1-lemma-11)
;;            (update-multiple-elements-fn-correctness-1-lemma-1))
;;       :use (:instance
;;             update-multiple-elements-fn-correctness-1-lemma-1
;;             (key (+ -1 len))
;;             (x (nth (+ -1 len) (explode str)))
;;             (l (nth (stobj-array-index)
;;                     fat32-in-memory))))
;;      ("subgoal *1/2.2"
;;       :in-theory (e/d (update-multiple-elements-fn-correctness-1-lemma-11
;;                        chars=>nats)
;;                       (nthcdr-of-cdr))
;;       :use (:instance nthcdr-of-cdr (i (+ -1 len))
;;                       (x (nth (stobj-array-index)
;;                               fat32-in-memory)))
;;       :expand
;;       ((append (chars=>nats (take (+ len (- pos))
;;                                   (nthcdr pos (explode str))))
;;                (nthcdr len
;;                        (nth (stobj-array-index)
;;                             fat32-in-memory)))
;;        (nthcdr len
;;                (nth (stobj-array-index)
;;                     fat32-in-memory))))
;;      ("subgoal *1/1'''"
;;       :in-theory (enable data-region-length fat32-in-memoryp))))

;;   (defthm
;;     update-multiple-elements-fn-correctness-2
;;     (and
;;      (equal (bpb_secperclus
;;              (update-multiple-elements-fn
;;               fat32-in-memory str len pos))
;;             (bpb_secperclus fat32-in-memory))
;;      (equal (bpb_rsvdseccnt
;;              (update-multiple-elements-fn
;;               fat32-in-memory str len pos))
;;             (bpb_rsvdseccnt fat32-in-memory))
;;      (equal (bpb_numfats
;;              (update-multiple-elements-fn
;;               fat32-in-memory str len pos))
;;             (bpb_numfats fat32-in-memory))
;;      (equal (bpb_fatsz32
;;              (update-multiple-elements-fn
;;               fat32-in-memory str len pos))
;;             (bpb_fatsz32 fat32-in-memory))
;;      (equal (bpb_bytspersec
;;              (update-multiple-elements-fn
;;               fat32-in-memory str len pos))
;;             (bpb_bytspersec fat32-in-memory))
;;      (equal (bpb_totsec32
;;              (update-multiple-elements-fn
;;               fat32-in-memory str len pos))
;;             (bpb_totsec32 fat32-in-memory))))

;;   (defthm
;;     update-multiple-elements-fn-correctness-3
;;     (implies
;;      (and (fat32-in-memoryp fat32-in-memory)
;;           (natp pos)
;;           (integerp len)
;;           (<= pos len)
;;           (<= len
;;               (stobj-array-length fat32-in-memory)))
;;      (fat32-in-memoryp
;;       (update-multiple-elements-fn fat32-in-memory str len pos)))
;;     :hints (("goal" :in-theory (disable fat32-in-memoryp)))))

(defthm
  compliant-fat32-in-memoryp-of-update-bs_oemnamei
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (< i (bs_oemname-length fat32-in-memory)))
           (equal (compliant-fat32-in-memoryp
                   (update-bs_oemnamei i v fat32-in-memory))
                  (unsigned-byte-p 8 v)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (compliant-fat32-in-memoryp
                     update-bs_oemnamei bs_oemname-length
                     fat-length data-region-length
                     count-of-clusters cluster-size)
                    (floor)))))

;; Look, the strategy of just using compliant-fat32-in-memoryp everywhere does
;; not seem to be working.
(local
 (in-theory (disable fat32-in-memoryp)))

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

(defthm
  nth-of-get-initial-bytes
  (equal (integerp (nth n (get-initial-bytes str)))
         (< (nfix n)
            (len (get-initial-bytes str))))
  :hints (("goal" :in-theory (enable get-initial-bytes))))

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
  unsigned-byte-p-of-get-remaining-rsvdbyts
  (unsigned-byte-listp 8 (get-remaining-rsvdbyts str))
  :hints (("goal" :in-theory (enable get-remaining-rsvdbyts))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm fat32-in-memory-to-string-inversion-lemma-29
    (implies (and (not (zp j)) (integerp i) (> i j))
             (> (floor i j) 0))
    :rule-classes :linear)

  (local
   (defthm read-reserved-area-guard-lemma-5
     (implies (and (unsigned-byte-listp 8 l)
                   (natp n)
                   (< n (len l)))
              (rationalp (nth n l)))))

  ;; This must be called after the file is opened.
  (defun
      read-reserved-area (fat32-in-memory str)
    (declare
     (xargs
      :guard (and (stringp str)
                  (>= (length str) *initialbytcnt*)
                  (fat32-in-memoryp fat32-in-memory))
      :guard-hints
      (("goal"
        :do-not-induct t
        :in-theory (disable unsigned-byte-p nth))
       ("subgoal 7" :in-theory (disable unsigned-byte-p-of-nth-when-unsigned-byte-listp)
        :use ((:instance
               unsigned-byte-p-of-nth-when-unsigned-byte-listp
               (n 13)
               (l (get-initial-bytes str))
               (bits 8))
              (:instance unsigned-byte-p-forward-to-nonnegative-integerp
                         (n bits)
                         (x (nth 13 (get-initial-bytes str))))))
       ("subgoal 6" :in-theory (disable unsigned-byte-p-of-nth-when-unsigned-byte-listp)
        :use (:instance
              unsigned-byte-p-of-nth-when-unsigned-byte-listp
              (n 0)
              (l (get-remaining-rsvdbyts str))
              (bits 8))))
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
         ;; least 1 sector if we're going to have at least 65536 clusters of
         ;; data, as required by the FAT specification at the place where it
         ;; specifies how to distinguish between volumes formatted with FAT12,
         ;; FAT16 and FAT32.
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
          (update-bs_oemname (subseq initial-bytes 3 11) fat32-in-memory))
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

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defun
    update-data-region
    (fat32-in-memory str len)
    (declare
     (xargs
      :guard (and (stringp str)
                  (natp len)
                  (<= len
                      (data-region-length fat32-in-memory))
                  (equal (length str)
                         (* (data-region-length fat32-in-memory)
                            (cluster-size fat32-in-memory)))
                  (<= len
                      (- *ms-bad-cluster*
                         *ms-first-data-cluster*)))
      :guard-hints
      (("goal" :in-theory (e/d nil (fat32-in-memoryp))))
      :stobjs fat32-in-memory))
    (b*
        ((len (the (unsigned-byte 28) len)))
      (if
       (zp len)
       fat32-in-memory
       (b*
           ((cluster-size (cluster-size fat32-in-memory))
            (index (- (data-region-length fat32-in-memory)
                      len))
            (current-cluster (subseq str (* index cluster-size)
                                     (* (+ index 1) cluster-size)))
            (fat32-in-memory
             (update-data-regioni
              index current-cluster fat32-in-memory)))
         (update-data-region
          fat32-in-memory str
          (the (unsigned-byte 28) (- len 1))))))))

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
  bpb_totsec32-of-update-data-regioni
  (equal
   (bpb_totsec32 (update-data-regioni i v fat32-in-memory))
   (bpb_totsec32 fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni bpb_totsec32))))

(defthm
  bpb_rsvdseccnt-of-update-data-regioni
  (equal
   (bpb_rsvdseccnt (update-data-regioni i v fat32-in-memory))
   (bpb_rsvdseccnt fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni bpb_rsvdseccnt))))

(defthm
  bpb_numfats-of-update-data-regioni
  (equal
   (bpb_numfats (update-data-regioni i v fat32-in-memory))
   (bpb_numfats fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni bpb_numfats))))

(defthm
  bpb_fatsz32-of-update-data-regioni
  (equal
   (bpb_fatsz32 (update-data-regioni i v fat32-in-memory))
   (bpb_fatsz32 fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni bpb_fatsz32))))

(defthm
  update-data-regioni-of-data-regioni
  (implies
   (and (fat32-in-memoryp fat32-in-memory)
        (< (nfix i)
           (data-region-length fat32-in-memory)))
   (equal
    (update-data-regioni i (data-regioni i fat32-in-memory)
                         fat32-in-memory)
    fat32-in-memory))
  :hints
  (("goal" :in-theory (enable fat32-in-memoryp
                              data-regioni update-data-regioni
                              data-region-length))))

;; (encapsulate
;;   ()

;;   (local
;;    (defthm fat32-in-memory-of-update-data-regioni
;;      (implies (and (fat32-in-memoryp fat32-in-memory)
;;                    (< i (data-region-length fat32-in-memory)))
;;               (equal (fat32-in-memoryp (update-data-regioni i v
;;                                                             fat32-in-memory))
;;                      (stringp v)))
;;      :hints (("Goal" :in-theory (enable update-data-regioni data-region-length)))))

;;   (defthmd
;;     update-data-region-correctness-1
;;     (implies
;;      (and (natp pos)
;;           (natp len)
;;           (< pos len)
;;           (<= len
;;               (data-region-length fat32-in-memory))
;;           (compliant-fat32-in-memoryp fat32-in-memory)
;;           (stringp str)
;;           (<= len (length str)))
;;      (equal
;;       (update-data-region fat32-in-memory str len pos)
;;       (update-nth
;;        *data-regioni*
;;        (append (take pos
;;                      (nth *data-regioni* fat32-in-memory))
;;                (string=>nats (subseq str pos len))
;;                (nthcdr len
;;                        (nth *data-regioni* fat32-in-memory)))
;;        fat32-in-memory)))
;;     :hints
;;     (("Goal"
;;       :use
;;       ((:functional-instance
;;         update-multiple-elements-fn-correctness-1
;;         ;; Instantiate the generic functions:
;;         (update-single-element-fn update-data-regioni)
;;         (stobj-array-index (lambda () *data-regioni*))
;;         (stobj-array-length data-region-length)
;;         (max-stobj-array-length (lambda () *ms-max-data-region-size*))
;;         ;; Instantiate the other relevant functions:
;;         (update-multiple-elements-fn update-data-region)))
;;       :in-theory (disable fat32-in-memoryp))
;;      ("Subgoal 4"
;;       :in-theory (enable update-data-regioni)))))

(defthm
  count-of-clusters-of-update-data-regioni
  (equal
   (count-of-clusters (update-data-regioni i v fat32-in-memory))
   (count-of-clusters fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable count-of-clusters))))

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

(defthm
  bpb_secperclus-of-read-reserved-area
  (implies
   (stringp str)
   (natp
    (-
     (bpb_secperclus
      (mv-nth 0
              (read-reserved-area fat32-in-memory str)))
     1)))
  :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable nth subseq)))
  :rule-classes
  ((:linear
    :corollary
    (<= 1
        (bpb_secperclus
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str))))
    :hints
    (("goal" :do-not-induct t
      :in-theory (disable nth subseq))))
   (:rewrite
    :corollary
    (implies
     (stringp str)
     (integerp
      (bpb_secperclus
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable nth subseq))))))

(defthm
  bpb_rsvdseccnt-of-read-reserved-area
  (<= 1
      (bpb_rsvdseccnt
       (mv-nth
        0
        (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable nth subseq))))

(defthm
  bpb_numfats-of-read-reserved-area
  (<= 1
      (bpb_numfats
       (mv-nth
        0
        (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable nth subseq))))

(defthm
  bpb_fatsz32-of-read-reserved-area
  (<= 1
      (bpb_fatsz32
       (mv-nth
        0
        (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable nth subseq))))

(defthm
  bpb_bytspersec-of-read-reserved-area
  (<= *ms-min-bytes-per-sector*
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable nth subseq))))

(defthm
  bpb_secperclus-of-resize-data-region
  (equal (bpb_secperclus (resize-data-region i fat32-in-memory))
         (bpb_secperclus fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable bpb_secperclus resize-data-region))))

(defthm
  bpb_bytspersec-of-resize-data-region
  (equal (bpb_bytspersec (resize-data-region i fat32-in-memory))
         (bpb_bytspersec fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable bpb_bytspersec resize-data-region))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    read-reserved-area-correctness-1
    (implies (and (fat32-in-memoryp fat32-in-memory)
                  (stringp str))
             (fat32-in-memoryp
              (mv-nth 0
                      (read-reserved-area fat32-in-memory str)))))

  (defund
    string-to-fat32-in-memory
    (fat32-in-memory str)
    (declare
     (xargs
      :guard (and (stringp str)
                  (>= (length str) *initialbytcnt*)
                  (fat32-in-memoryp fat32-in-memory))
      :guard-debug t
      :guard-hints
      (("goal"
        :do-not-induct t
        :in-theory (e/d (cluster-size count-of-clusters)
                        (read-reserved-area))))
      :stobjs fat32-in-memory))
    (b*
        (((mv fat32-in-memory error-code)
          (read-reserved-area fat32-in-memory str))
         ((unless (equal error-code 0))
          (mv fat32-in-memory error-code))
         (fat-read-size (/ (* (bpb_fatsz32 fat32-in-memory)
                              (bpb_bytspersec fat32-in-memory))
                           4))
         ((unless (integerp fat-read-size))
          (mv fat32-in-memory -1))
         (data-byte-count (* (count-of-clusters fat32-in-memory)
                             (cluster-size fat32-in-memory)))
         ((unless (> data-byte-count 0))
          (mv fat32-in-memory -1))
         (tmp_bytspersec (bpb_bytspersec fat32-in-memory))
         (tmp_init (* tmp_bytspersec
                      (+ (bpb_rsvdseccnt fat32-in-memory)
                         (* (bpb_numfats fat32-in-memory)
                            (bpb_fatsz32 fat32-in-memory)))))
         (fat32-in-memory
          (resize-fat fat-read-size fat32-in-memory))
         ((unless (and (<= fat-read-size *ms-bad-cluster*)
                       (<= (+ (* (bpb_rsvdseccnt fat32-in-memory)
                                 (bpb_bytspersec fat32-in-memory))
                              (* fat-read-size 4))
                           (length str))))
          (mv fat32-in-memory -1))
         (fat32-in-memory
          (update-fat
           fat32-in-memory
           (subseq str
                   (* (bpb_rsvdseccnt fat32-in-memory)
                      (bpb_bytspersec fat32-in-memory))
                   (+ (* (bpb_rsvdseccnt fat32-in-memory)
                         (bpb_bytspersec fat32-in-memory))
                      (* fat-read-size 4)))
           fat-read-size))
         (fat32-in-memory
          (resize-data-region (count-of-clusters fat32-in-memory) fat32-in-memory))
         ((unless
              (and (<= (data-region-length fat32-in-memory)
                       (- *ms-bad-cluster* *ms-first-data-cluster*))
                (>= (length str)
                    (+ tmp_init data-byte-count))))
          (mv fat32-in-memory -1))
         (data-region-string
          (subseq str tmp_init
                  (+ tmp_init data-byte-count)))
         (fat32-in-memory
          (update-data-region fat32-in-memory data-region-string
                              (data-region-length fat32-in-memory))))
      (mv fat32-in-memory error-code))))

(defun
  disk-image-to-fat32-in-memory
  (fat32-in-memory image-path state)
  (declare
   (xargs
    :guard (and (stringp image-path)
                (fat32-in-memoryp fat32-in-memory))
    :guard-hints
    (("goal"
      :do-not-induct t
      :in-theory (disable read-reserved-area)))
    :stobjs (fat32-in-memory state)))
  (b* ((str (read-file-into-string image-path))
       ((unless (and (stringp str)
                     (>= (length str) *initialbytcnt*)))
        (mv fat32-in-memory -1)))
    (string-to-fat32-in-memory fat32-in-memory str)))

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
                (>= masked-current-cluster
                    *ms-first-data-cluster*)
                (< masked-current-cluster
                   (+ (count-of-clusters fat32-in-memory)
                      *ms-first-data-cluster*)))))
  (let
   ((cluster-size (cluster-size fat32-in-memory)))
   (if
    (or (zp length) (zp cluster-size))
    (mv nil (- *eio*))
    (let
     ((masked-next-cluster
       (fat32-entry-mask
        (if (mbt (< (nfix masked-current-cluster)
                    (nfix (+ (count-of-clusters fat32-in-memory)
                             *ms-first-data-cluster*))))
            (fati masked-current-cluster fat32-in-memory)
            nil))))
     (if
      (< masked-next-cluster
         *ms-first-data-cluster*)
      (mv (list masked-current-cluster)
          (- *eio*))
      (if
       (or
        (fat32-is-eof masked-next-cluster)
        (>=
         masked-next-cluster
         (mbe
          :exec (+ (count-of-clusters fat32-in-memory)
                   *ms-first-data-cluster*)
          :logic (nfix (+ (count-of-clusters fat32-in-memory)
                          *ms-first-data-cluster*)))))
       (mv (list masked-current-cluster) 0)
       (b*
           (((mv tail-index-list tail-error)
             (get-clusterchain fat32-in-memory masked-next-cluster
                               (nfix (- length cluster-size)))))
         (mv (list* masked-current-cluster tail-index-list)
             tail-error))))))))

(defund-nx
  effective-fat (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (compliant-fat32-in-memoryp fat32-in-memory)
          :guard-hints
          (("goal" :in-theory (enable fat32-in-memoryp)))))
  (take (+ (count-of-clusters fat32-in-memory)
           *ms-first-data-cluster*)
        (nth *fati* fat32-in-memory)))

(defthm len-of-effective-fat
  (equal (len (effective-fat fat32-in-memory))
         (nfix (+ (count-of-clusters fat32-in-memory)
                  *ms-first-data-cluster*)))
  :hints (("goal" :in-theory (enable effective-fat))))

(defthm
  fat32-entry-list-p-of-effective-fat
  (implies (and (fat32-in-memoryp fat32-in-memory)
                (<= (+ (count-of-clusters fat32-in-memory)
                       *ms-first-data-cluster*)
                    (fat-length fat32-in-memory)))
           (fat32-entry-list-p (effective-fat fat32-in-memory)))
  :hints
  (("goal" :in-theory (enable effective-fat
                              fat-length fat32-in-memoryp))))

(defthm
  nth-of-effective-fat
  (equal (nth n (effective-fat fat32-in-memory))
         (if (< (nfix n)
                (nfix (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*)))
             (fati n fat32-in-memory)
             nil))
  :hints (("goal" :in-theory (enable fati effective-fat))))

(defthm
  get-clusterchain-alt
  (equal (get-clusterchain fat32-in-memory
                           masked-current-cluster length)
         (fat32-build-index-list
          (effective-fat fat32-in-memory)
          masked-current-cluster
          length (cluster-size fat32-in-memory)))
  :rule-classes :definition
  :hints
  (("goal" :in-theory (enable get-clusterchain
                              fati fat-length effective-fat))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defun
      get-contents-from-clusterchain
      (fat32-in-memory clusterchain file-size)
    (declare
     (xargs
      :stobjs (fat32-in-memory)
      :guard
      (and
       (compliant-fat32-in-memoryp fat32-in-memory)
       (equal (data-region-length fat32-in-memory)
              (count-of-clusters fat32-in-memory))
       (fat32-masked-entry-list-p clusterchain)
       (natp file-size)
       (bounded-nat-listp clusterchain
                          (count-of-clusters fat32-in-memory))
       (lower-bounded-integer-listp
        clusterchain *ms-first-data-cluster*))
      :verify-guards nil))
    (if
        (atom clusterchain)
        ""
      (let*
          ((cluster-size (cluster-size fat32-in-memory))
           (masked-current-cluster (car clusterchain)))
        (concatenate
         'string
         (subseq
          (data-regioni
           (nfix (- masked-current-cluster *ms-first-data-cluster*))
           fat32-in-memory)
          0
          (min file-size cluster-size))
         (get-contents-from-clusterchain
          fat32-in-memory (cdr clusterchain)
          (nfix (- file-size cluster-size)))))))

  (defthm
    stringp-of-get-contents-from-clusterchain
      (stringp
       (get-contents-from-clusterchain
        fat32-in-memory clusterchain file-size)))

  (verify-guards get-contents-from-clusterchain
      :hints
      (("goal" :in-theory (e/d (lower-bounded-integer-listp)))))

  (defun
    get-clusterchain-contents
    (fat32-in-memory masked-current-cluster length)
    (declare
     (xargs
      :stobjs fat32-in-memory
      :measure (nfix length)
      :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                  (equal (data-region-length fat32-in-memory)
                         (count-of-clusters fat32-in-memory))
                  (fat32-masked-entry-p masked-current-cluster)
                  (natp length)
                  (>= masked-current-cluster
                      *ms-first-data-cluster*)
                  (< masked-current-cluster
                     (+ (count-of-clusters fat32-in-memory)
                        *ms-first-data-cluster*)))
      :verify-guards nil))
    (b*
        ((cluster-size (cluster-size fat32-in-memory))
         ((unless (and (not (zp length))
                       (not (zp cluster-size))
                       (>= masked-current-cluster
                           *ms-first-data-cluster*)))
          (mv "" (- *eio*)))
         (current-cluster-contents
          (str-fix
           (data-regioni (- masked-current-cluster 2) fat32-in-memory)))
         (masked-next-cluster
          (fat32-entry-mask
           ;; This mbt (must be true) form was inserted in order to comport
           ;; with our current definition of effective-fat, which is implicitly
           ;; used in the rule get-clusterchain-contents-correctness-1.
           (if (mbt (< (nfix masked-current-cluster)
                       (nfix (+ (count-of-clusters fat32-in-memory)
                                *ms-first-data-cluster*))))
               (fati masked-current-cluster fat32-in-memory)
             nil)))
         ((unless (>= masked-next-cluster
                      *ms-first-data-cluster*))
          (mv (subseq current-cluster-contents 0 (min length cluster-size))
              (- *eio*)))
         ((unless (and (not (fat32-is-eof masked-next-cluster))
                       (< masked-next-cluster
                          (+ (count-of-clusters fat32-in-memory)
                             *ms-first-data-cluster*))))
          (mv (subseq current-cluster-contents 0 (min length cluster-size)) 0))
         ((mv tail-string tail-error)
          (get-clusterchain-contents
           fat32-in-memory masked-next-cluster
           (nfix (- length cluster-size))))
         ((unless (equal tail-error 0))
          (mv "" (- *eio*))))
      (mv (concatenate 'string
                       current-cluster-contents
                       tail-string)
          0)))

  (defthm stringp-of-get-clusterchain-contents
    (stringp
     (mv-nth 0
             (get-clusterchain-contents
              fat32-in-memory masked-current-cluster length)))
    :rule-classes (:rewrite :type-prescription))

  (verify-guards
    get-clusterchain-contents
    :hints
      (("goal"
        :do-not-induct t
        :in-theory (e/d (fati-when-compliant-fat32-in-memoryp))))))

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
    (- *eio*))))

(defthm
  get-clusterchain-contents-correctness-2
  (implies
   (>= masked-current-cluster
       *ms-first-data-cluster*)
   (equal
    (mv-nth 1
            (fat32-build-index-list (effective-fat fat32-in-memory)
                                    masked-current-cluster
                                    length (cluster-size fat32-in-memory)))
    (mv-nth 1
            (get-clusterchain-contents fat32-in-memory
                                       masked-current-cluster length))))
  :hints (("goal" :in-theory (e/d (fat-length fati effective-fat)))))

(defthm
  get-contents-from-clusterchain-of-update-data-regioni
  (implies
   (and (integerp file-size)
        (compliant-fat32-in-memoryp fat32-in-memory)
        (equal (data-region-length fat32-in-memory)
               (count-of-clusters fat32-in-memory))
        (natp i)
        (not (member-equal (+ i *ms-first-data-cluster*)
                           clusterchain))
        (lower-bounded-integer-listp
         clusterchain *ms-first-data-cluster*))
   (equal
    (get-contents-from-clusterchain
     (update-data-regioni i v fat32-in-memory)
     clusterchain file-size)
    (get-contents-from-clusterchain fat32-in-memory
                                    clusterchain file-size)))
  :hints
  (("goal" :in-theory (enable lower-bounded-integer-listp))))

(defthm
  get-clusterchain-contents-correctness-1
  (implies
   (and
    (fat32-masked-entry-p masked-current-cluster)
    (compliant-fat32-in-memoryp fat32-in-memory)
    (equal (mv-nth 1
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
            (get-clusterchain-contents fat32-in-memory
                                       masked-current-cluster length))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (fat32-masked-entry-p masked-current-cluster)
      (>= masked-current-cluster
          *ms-first-data-cluster*)
      (compliant-fat32-in-memoryp fat32-in-memory)
      (equal
       (mv-nth 1
               (fat32-build-index-list (effective-fat fat32-in-memory)
                                       masked-current-cluster
                                       length (cluster-size fat32-in-memory)))
       0))
     (equal
      (get-contents-from-clusterchain
       fat32-in-memory
       (mv-nth 0
               (fat32-build-index-list (effective-fat fat32-in-memory)
                                       masked-current-cluster
                                       length (cluster-size fat32-in-memory)))
       length)
      (mv-nth 0
              (get-clusterchain-contents fat32-in-memory
                                         masked-current-cluster length)))))))

(defthm
  get-clusterchain-contents-correctness-3
  (equal
   (mv
    (mv-nth
     0
     (get-clusterchain-contents fat32-in-memory
                                masked-current-cluster length))
    (mv-nth
     1
     (get-clusterchain-contents fat32-in-memory
                                masked-current-cluster length)))
   (get-clusterchain-contents fat32-in-memory
                              masked-current-cluster length)))

;; The following is not a theorem, because we took our error codes, more or
;; less, from fs/fat/cache.c, and there the length is not taken into account
;; while returning error codes (or not). Thus, it's possible to return an error
;; code of 0 without conforming to the length.
;; (defthm len-of-get-clusterchain-contents
;;   (b*
;;       (((mv contents error-code)
;;         (get-clusterchain-contents fat32-in-memory masked-current-cluster length)))
;;     (implies
;;      (equal error-code 0)
;;      (equal (length contents) length))))

;; Here's the idea: while transforming from M2 to M1,
;; - we are not going to to take directory entries which are deleted
;; - we are not going to take dot or dotdot entries
(defund
  useless-dir-ent-p (dir-ent)
  (declare
   (xargs
    :guard (dir-ent-p dir-ent)
    :guard-hints
    (("goal" :in-theory (e/d (dir-ent-p dir-ent-first-cluster)
                             (unsigned-byte-p))))))
  (or
   ;; the byte #xe5 marks deleted files, according to the spec
   (equal (nth 0 dir-ent) #xe5)
   (equal (dir-ent-filename dir-ent)
          *current-dir-fat32-name*)
   (equal (dir-ent-filename dir-ent)
          *parent-dir-fat32-name*)))

(defthm
  useless-dir-ent-p-of-dir-ent-install-directory-bit
  (implies
   (dir-ent-p dir-ent)
   (equal (useless-dir-ent-p
           (dir-ent-install-directory-bit dir-ent val))
          (useless-dir-ent-p dir-ent)))
  :hints
  (("goal"
    :in-theory (enable dir-ent-install-directory-bit
                       useless-dir-ent-p dir-ent-filename))))

(defthm
  useless-dir-ent-p-of-dir-ent-set-filename
  (implies (and (fat32-filename-p filename)
                (dir-ent-p dir-ent))
           (not (useless-dir-ent-p
                 (dir-ent-set-filename dir-ent filename))))
  :hints (("goal" :in-theory (e/d (useless-dir-ent-p) (nth)))))

(defund
  make-dir-ent-list (dir-contents)
  (declare
   (xargs
    :guard (unsigned-byte-listp 8 dir-contents)
    :measure (len dir-contents)
    :guard-hints (("goal" :in-theory (e/d (dir-ent-p) (nth))))))
  (b* (((when (< (len dir-contents)
                 *ms-dir-ent-length*))
        nil)
       (dir-ent
        (mbe
         :exec (take *ms-dir-ent-length* dir-contents)
         :logic (dir-ent-fix (take *ms-dir-ent-length* dir-contents))))
       ;; From page 24 of the specification: "If DIR_Name[0] == 0x00, then the
       ;; directory entry is free (same as for 0xE5), and there are no
       ;; allocated directory entries after this one (all of the DIR_Name[0]
       ;; bytes in all of the entries after this one are also set to 0). The
       ;; special 0 value, rather than the 0xE5 value, indicates to FAT file
       ;; system driver code that the rest of the entries in this directory do
       ;; not need to be examined because they are all free."
       ((when (equal (nth 0 dir-ent) 0)) nil)
       ((when (useless-dir-ent-p dir-ent))
        (make-dir-ent-list
         (nthcdr *ms-dir-ent-length* dir-contents))))
    (list* dir-ent
           (make-dir-ent-list
            (nthcdr *ms-dir-ent-length* dir-contents)))))

(defthm
  dir-ent-list-p-of-make-dir-ent-list
  (dir-ent-list-p (make-dir-ent-list dir-contents))
  :hints (("goal" :in-theory (e/d (make-dir-ent-list) (nth)))))

;; Here's the idea behind this recursion: A loop could occur on a badly formed
;; FAT32 volume which has a cycle in its directory structure (for instance, if
;; / and /tmp/ were to point to the same cluster as their initial cluster.)
;; This loop could be stopped most cleanly by maintaining a list of all
;; clusters which could be visited, and checking them off as we visit more
;; entries. Then, we would detect a second visit to the same cluster, and
;; terminate with an error condition . Only otherwise would we make a recursive
;; call, and our measure - the length of the list of unvisited clusters - would
;; decrease.

;; This would probably impose performance penalties, and so there's a better
;; way which does not (good!), and also does not cleanly detect cycles in the
;; directory structure (bad.) Still, it returns exactly the same result for
;; good FAT32 volumes, so it's acceptable. In this helper function, we set our
;; measure to be entry-limit, an upper bound on the number of entries we can
;; visit, and decrement every time we visit a new entry. In the main function,
;; we count the total number of visitable directory entries, by dividing the
;; entire length of the data region by *ms-dir-ent-length*, and set that as the
;; upper limit. This makes sure that we aren't disallowing any legitimate FAT32
;; volumes which just happen to be full of directories.

;; We're adding a return value for collecting all these clusterchains... again,
;; for proof purposes. We're also adding a return value, to signal an error
;; when we run out of entries.

(defund
  fat32-in-memory-to-m1-fs-helper
  (fat32-in-memory dir-ent-list entry-limit)
  (declare (xargs :measure (nfix entry-limit)
                  :guard (and (natp entry-limit)
                              (dir-ent-list-p dir-ent-list)
                              (compliant-fat32-in-memoryp fat32-in-memory))
                  :verify-guards nil
                  :stobjs (fat32-in-memory)))
  (b*
      (;; entry-limit is the loop stopper, kind of - we know that in a
       ;; filesystem instance without any looping clusterchains (where, for
       ;; instance, 2 points to 3 and 3 points to 2), we can't have more
       ;; entries than the total number of entries possible if the data region
       ;; was fully packed with directory entries. So, we begin with that
       ;; number as the entry count, and keep decreasing in recursive
       ;; calls. This means we also decrease when we find an entry for a
       ;; deleted file, or a "." or ".."  entry, even though we won't include
       ;; these in the filesystem instance. The measure must strictly decrease.
       ;; If there isn't a full directory entry in dir-contents, we're done.
       ((when
            (atom dir-ent-list))
        (mv nil 0 nil 0))
       ((when (zp entry-limit))
        (mv nil 0 nil *EIO*))
       (dir-ent
        (car dir-ent-list))
       ;; Learn about the file we're looking at.
       (first-cluster (dir-ent-first-cluster dir-ent))
       (filename (dir-ent-filename dir-ent))
       (directory-p
        (dir-ent-directory-p dir-ent))
       ;; From page 36 of the specification: "Similarly, a FAT file system
       ;; driver must not allow a directory (a file that is actually a
       ;; container for other files) to be larger than 65,536 * 32 (2,097,152)
       ;; bytes." Note, this is the length value we'll use to traverse the
       ;; clusterchain, not the value we'll store in the directory entry -
       ;; that's 0, per the spec.
       (length (if directory-p
                   *ms-max-dir-size*
                 (dir-ent-file-size dir-ent)))
       ((mv contents error-code)
        (if
            ;; This clause is intended to make sure we don't try to explore the
            ;; contents of an empty file; that would cause a guard
            ;; violation. Unlike deleted file entries and dot or dotdot
            ;; entries, though, these will be present in the m1 instance.
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
       ((mv clusterchain &)
        (if
            ;; This clause is intended to make sure we don't try to explore the
            ;; contents of an empty file; that would cause a guard
            ;; violation. Unlike deleted file entries and dot or dotdot
            ;; entries, though, these will be present in the m1 instance.
            (or (< first-cluster
                   *ms-first-data-cluster*)
                (>=
                 first-cluster
                 (+ (count-of-clusters fat32-in-memory)
                    *ms-first-data-cluster*)))
            (mv nil 0)
            (get-clusterchain fat32-in-memory
                              first-cluster
                              length)))
       ;; head-entry-count and head-clusterchain-list, here, do not include the
       ;; entry or clusterchain respectively for the head itself. Those will be
       ;; added at the end.
       ((mv head head-entry-count head-clusterchain-list head-error-code)
        (if directory-p
            (fat32-in-memory-to-m1-fs-helper
             fat32-in-memory
             (make-dir-ent-list (string=>nats contents))
             (- entry-limit 1))
          (mv contents 0 nil 0)))
       ;; get-clusterchain-contents returns either 0 or a negative error code,
       ;; which is not what we want...
       (error-code
        (if (equal error-code 0)
            head-error-code
          *EIO*))
       ;; we want entry-limit to serve both as a measure and an upper
       ;; bound on how many entries are found.
       (tail-entry-limit (nfix (- entry-limit
                                  (+ 1 (nfix head-entry-count)))))
       ((mv tail tail-entry-count tail-clusterchain-list tail-error-code)
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory
         (cdr dir-ent-list)
         tail-entry-limit))
       ;; This clause states that we simply can't store any files with length
       ;; (ash 1 32) or more - of course, this arises from the bit-width (32)
       ;; of the segment of the directory entry which is going to store the
       ;; length of the file.
       ((when (and (not directory-p) (not (unsigned-byte-p 32 (length contents)))))
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory
         (cdr dir-ent-list)
         (- entry-limit 1)))
       (error-code (if (zp error-code) tail-error-code error-code)))
    ;; We add the file to this m1 instance.
    (mv (list* (cons filename
                     (make-m1-file :dir-ent dir-ent
                                   :contents head))
               tail)
        (+ 1 head-entry-count tail-entry-count)
        (append (list clusterchain) head-clusterchain-list
                tail-clusterchain-list)
        error-code)))

(defthm fat32-in-memory-to-m1-fs-helper-correctness-1-lemma-1
  (equal (rationalp (nth n (dir-ent-fix x)))
         (< (nfix n) *ms-dir-ent-length*)))

(defthm
  fat32-in-memory-to-m1-fs-helper-correctness-1
  (b* (((mv m1-file-alist entry-count
            clusterchain-list error-code)
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory
         dir-ent-list entry-limit)))
    (and (natp entry-count)
         (<= entry-count (nfix entry-limit))
         ;; The following is no longer unconditionally true.
         ;; (m1-file-alist-p m1-file-alist)
         (alistp m1-file-alist)
         (true-list-listp clusterchain-list)
         (natp error-code)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (fat32-filename-p fat32-in-memory-to-m1-fs-helper)
     (nth-of-string=>nats natp-of-cluster-size
                          get-clusterchain-contents
                          take-redefinition
                          by-slice-you-mean-the-whole-cake-2
                          nth floor))
    :induct
    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                     dir-ent-list entry-limit)))
  :rule-classes
  ((:type-prescription
    :corollary (b* (((mv & entry-count & &)
                     (fat32-in-memory-to-m1-fs-helper
                      fat32-in-memory
                      dir-ent-list entry-limit)))
                 (natp entry-count)))
   (:type-prescription
    :corollary (b* (((mv & & & error-code)
                     (fat32-in-memory-to-m1-fs-helper
                      fat32-in-memory
                      dir-ent-list entry-limit)))
                 (natp error-code)))
   (:linear
    :corollary (b* (((mv & entry-count & error-code)
                     (fat32-in-memory-to-m1-fs-helper
                      fat32-in-memory
                      dir-ent-list entry-limit)))
                 (and (<= 0 entry-count)
                      (<= entry-count (nfix entry-limit))
                      (<= 0 error-code))))
   (:rewrite :corollary (b* (((mv & entry-count clusterchain-list error-code)
                              (fat32-in-memory-to-m1-fs-helper
                               fat32-in-memory
                               dir-ent-list entry-limit)))
                          (and (integerp entry-count)
                               (integerp error-code)
                               (true-list-listp clusterchain-list))))
   (:type-prescription
    :corollary (b* (((mv m1-file-alist &)
                     (fat32-in-memory-to-m1-fs-helper
                      fat32-in-memory
                      dir-ent-list entry-limit)))
                 (true-listp m1-file-alist)))))

(defthm
  fat32-in-memory-to-m1-fs-helper-correctness-2
  (b* (((mv m1-file-alist &)
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory
         dir-ent-list entry-limit)))
    (<= (len m1-file-alist)
        (len dir-ent-list)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (fat32-in-memory-to-m1-fs-helper)
     (nth-of-string=>nats natp-of-cluster-size
                          get-clusterchain-contents
                          take-redefinition
                          by-slice-you-mean-the-whole-cake-2))
    :induct
    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                     dir-ent-list entry-limit)))
  :rule-classes :linear)

(defthm
  fat32-in-memory-to-m1-fs-helper-guard-lemma-1
  (implies (and (unsigned-byte-listp 8 dir-contents)
                (>= (len dir-contents) *ms-dir-ent-length*))
           (dir-ent-p (take *ms-dir-ent-length* dir-contents)))
  :hints (("Goal" :in-theory (enable dir-ent-p))))

(defthm fat32-in-memory-to-m1-fs-helper-guard-lemma-2
  (implies (unsigned-byte-listp 8 dir-contents)
           (iff (unsigned-byte-p 8 (nth n dir-contents))
                (< (nfix n) (len dir-contents))))
  :rule-classes ((:rewrite :corollary
                           (implies (and (unsigned-byte-listp 8 dir-contents)
                                         (< (nfix n) (len dir-contents)))
                                    (integerp (nth n dir-contents))))
                 (:rewrite :corollary
                           (implies (and (unsigned-byte-listp 8 dir-contents)
                                         (< (nfix n) (len dir-contents))
                                         (unsigned-byte-p 8 i))
                                    (unsigned-byte-p 8 (logand i (nth
                                                                  n
                                                                  dir-contents))))
                           :hints (("Goal" :in-theory (disable unsigned-byte-p)
                                    :do-not-induct t)))))

;; (defthm
;;   fat32-in-memory-to-m1-fs-helper-guard-lemma-3
;;   (implies (not (useless-dir-ent-p dir-ent count-of-clusters))
;;            (and
;;            (>= (fat32-entry-mask (combine32u (nth 21 dir-ent)
;;                                              (nth 20 dir-ent)
;;                                              (nth 27 dir-ent)
;;                                              (nth 26 dir-ent)))
;;                *ms-first-data-cluster*)
;;            (< (fat32-entry-mask (combine32u (nth 21 dir-ent)
;;                                              (nth 20 dir-ent)
;;                                              (nth 27 dir-ent)
;;                                              (nth 26 dir-ent)))
;;               (+
;;                *ms-first-data-cluster*
;;                count-of-clusters))))
;;   :hints (("goal" :in-theory (enable useless-dir-ent-p)))
;;   :rule-classes :linear)

(defthm true-listp-of-fat32-in-memory-to-m1-fs-helper
  (true-listp (mv-nth 2
                      (fat32-in-memory-to-m1-fs-helper
                       fat32-in-memory
                       dir-contents entry-limit))))

(verify-guards
  fat32-in-memory-to-m1-fs-helper
  :guard-debug t
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite fat32-in-memory-to-m1-fs-helper-guard-lemma-2
               . 2)
     (:e dir-ent-directory-p)
     (:t dir-ent-directory-p))
    :use
    ((:instance
      (:rewrite fat32-in-memory-to-m1-fs-helper-guard-lemma-2
                . 2)
      (i 16)
      (n 11))))))

;; for later
;; (defthm
;;   fat32-in-memory-to-m1-fs-helper-correctness-3
;;   (b* (((mv & entry-count-a)
;;         (fat32-in-memory-to-m1-fs-helper
;;          fat32-in-memory
;;          dir-contents entry-limit-a)))
;;     (implies
;;      (and
;;       (< entry-count-a (nfix entry-limit-a))
;;       (< (nfix entry-limit-a) (nfix entry-limit-b)))
;;      (equal
;;       (fat32-in-memory-to-m1-fs-helper
;;        fat32-in-memory
;;        dir-contents entry-limit-b)
;;       (fat32-in-memory-to-m1-fs-helper
;;        fat32-in-memory
;;        dir-contents entry-limit-a))))
;;   :rule-classes nil)

(defund
  fat32-in-memory-to-m1-fs
  (fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (compliant-fat32-in-memoryp fat32-in-memory)
                  :guard-hints
                  (("goal"
                    :in-theory
                    (disable floor)))))
  (b*
      (((mv root-dir-contents &)
        (get-clusterchain-contents
         fat32-in-memory
         (fat32-entry-mask (bpb_rootclus fat32-in-memory))
         *ms-max-dir-size*))
       (entry-limit (floor (* (data-region-length fat32-in-memory)
                              (cluster-size fat32-in-memory))
                           *ms-dir-ent-length*))
       ((mv m1-file-alist & & &)
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory
         (string=>nats root-dir-contents)
         entry-limit)))
    m1-file-alist))

(defthm
  fat32-in-memory-to-m1-fs-correctness-1
  (m1-file-alist-p (fat32-in-memory-to-m1-fs fat32-in-memory))
  :hints (("goal" :in-theory (e/d (fat32-in-memory-to-m1-fs)
                                  (m1-file-p))))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary
    (true-listp (fat32-in-memory-to-m1-fs fat32-in-memory)))))

(defthm
  fat32-in-memory-to-m1-fs-correctness-2
  (implies
   (equal
    (mv-nth
     0
     (get-clusterchain-contents
      fat32-in-memory
      (fat32-entry-mask (bpb_rootclus fat32-in-memory))
      *ms-max-dir-size*))
    "")
   (equal (fat32-in-memory-to-m1-fs fat32-in-memory)
          nil))
  :hints
  (("goal"
    :in-theory
    (e/d (fat32-in-memory-to-m1-fs)
         (fat32-in-memory-to-m1-fs-helper-correctness-2))
    :use
    (:instance
     fat32-in-memory-to-m1-fs-helper-correctness-2
     (dir-contents
      (mv-nth
       0
       (get-clusterchain-contents
        fat32-in-memory
        (fat32-entry-mask (bpb_rootclus fat32-in-memory))
        *ms-max-dir-size*)))
     (entry-limit (floor (* (data-region-length fat32-in-memory)
                            (cluster-size fat32-in-memory))
                         *ms-dir-ent-length*))))))

(defund
  stobj-find-n-free-clusters-helper
  (fat32-in-memory n start)
  (declare
   (xargs
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp n)
                (natp start))
    :stobjs fat32-in-memory
    :measure (nfix (- (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*)
                      start))))
  (if
   (or (zp n)
       (mbe :logic (zp (- (+ (count-of-clusters fat32-in-memory)
                             *ms-first-data-cluster*)
                          start))
            :exec (>= start
                      (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*))))
   nil
   (if
    (not (equal (fat32-entry-mask (fati start fat32-in-memory))
                0))
    (stobj-find-n-free-clusters-helper
     fat32-in-memory n (+ start 1))
    (cons
     (mbe :exec start :logic (nfix start))
     (stobj-find-n-free-clusters-helper fat32-in-memory (- n 1)
                                        (+ start 1))))))

(defthm
  nat-listp-of-stobj-find-n-free-clusters-helper
  (nat-listp
   (stobj-find-n-free-clusters-helper fat32-in-memory n start))
  :hints
  (("goal"
    :in-theory (enable stobj-find-n-free-clusters-helper)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (integer-listp (stobj-find-n-free-clusters-helper
                               fat32-in-memory n start)))))

(defthm
  nth-of-update-data-regioni
  (implies
   (not (equal (nfix n) *data-regioni*))
   (equal (nth n
               (update-data-regioni i v fat32-in-memory))
          (nth n fat32-in-memory)))
  :hints (("goal" :in-theory (enable update-data-regioni))))

(defthm
  effective-fat-of-update-data-regioni
  (equal
   (effective-fat (update-data-regioni i v fat32-in-memory))
   (effective-fat fat32-in-memory))
  :hints (("goal" :in-theory (enable effective-fat))))

(defthm
  fat-length-of-update-data-regioni
  (equal
   (fat-length (update-data-regioni i v fat32-in-memory))
   (fat-length fat32-in-memory))
  :hints (("goal" :in-theory (enable update-data-regioni fat-length))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1-lemma-3
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
  effective-fat-of-update-fati
  (equal (effective-fat (update-fati i v fat32-in-memory))
         (if (< (nfix i)
                (+ (count-of-clusters fat32-in-memory)
                   *ms-first-data-cluster*))
             (update-nth i v (effective-fat fat32-in-memory))
             (effective-fat fat32-in-memory)))
  :hints (("goal" :in-theory (enable effective-fat update-fati)
           :do-not-induct t)))

(defthm
  stobj-find-n-free-clusters-helper-correctness-1
  (implies
   (and (natp start)
        (compliant-fat32-in-memoryp fat32-in-memory))
   (equal
    (stobj-find-n-free-clusters-helper fat32-in-memory n start)
    (find-n-free-clusters-helper
     (nthcdr start (effective-fat fat32-in-memory))
     n start)))
  :hints
  (("goal"
    :in-theory (enable stobj-find-n-free-clusters-helper
                       find-n-free-clusters-helper)
    :induct
    (stobj-find-n-free-clusters-helper fat32-in-memory n start))
   ("subgoal *1/2"
    :expand (find-n-free-clusters-helper
             (nthcdr start (effective-fat fat32-in-memory))
             n start))))

(defund
  stobj-find-n-free-clusters
  (fat32-in-memory n)
  (declare
   (xargs :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                      (natp n))
          :stobjs fat32-in-memory))
  (stobj-find-n-free-clusters-helper
   fat32-in-memory n *ms-first-data-cluster*))

(defthm
  nat-listp-of-stobj-find-n-free-clusters
  (nat-listp (stobj-find-n-free-clusters fat32-in-memory n))
  :hints
  (("goal" :in-theory (enable stobj-find-n-free-clusters)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (integer-listp (stobj-find-n-free-clusters-helper
                               fat32-in-memory n start)))))

(defthm
  stobj-find-n-free-clusters-correctness-1
  (implies
   (compliant-fat32-in-memoryp fat32-in-memory)
   (equal (stobj-find-n-free-clusters fat32-in-memory n)
          (find-n-free-clusters (effective-fat fat32-in-memory)
                                n)))
  :hints (("goal" :in-theory (enable stobj-find-n-free-clusters
                                     find-n-free-clusters)))
  :rule-classes :definition)

(defthm
  stobj-set-indices-in-fa-table-guard-lemma-1
  (implies (fat32-in-memoryp fat32-in-memory)
           (fat32-entry-list-p (nth *fati* fat32-in-memory)))
  :hints (("Goal" :in-theory (enable fat32-in-memoryp))))

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
   (xargs
    :measure (acl2-count index-list)
    :stobjs fat32-in-memory
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                (nat-listp index-list)
                (fat32-masked-entry-list-p value-list)
                (equal (len index-list)
                       (len value-list)))
    :guard-hints
    (("goal" :in-theory (disable unsigned-byte-p)))))
  (b*
      (((when (atom index-list))
        fat32-in-memory)
       (current-index (car index-list))
       ((when (or (not (natp current-index))
                  (>= current-index
                      (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*))
                  (mbe :logic (>= current-index
                                  (fat-length fat32-in-memory))
                       :exec nil)))
        fat32-in-memory)
       (fat32-in-memory
        (update-fati current-index
                     (fat32-update-lower-28
                      (fati current-index fat32-in-memory)
                      (car value-list))
                     fat32-in-memory)))
    (stobj-set-indices-in-fa-table
     fat32-in-memory (cdr index-list)
     (cdr value-list))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1-lemma-1
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal (update-nth *fati* (nth *fati* fat32-in-memory)
                      fat32-in-memory)
          fat32-in-memory))
  :hints (("Goal" :in-theory (enable fat32-in-memoryp))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1-lemma-2
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal
    (fat32-in-memoryp (update-nth *fati* val fat32-in-memory))
    (fat32-entry-list-p val)))
  :hints (("Goal" :in-theory (enable fat32-in-memoryp))))

(defthm
  count-of-clusters-of-stobj-set-indices-in-fa-table
  (equal
   (count-of-clusters (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (count-of-clusters fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1
  (implies
   (and (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list))
        (compliant-fat32-in-memoryp fat32-in-memory))
   (equal (effective-fat
               (stobj-set-indices-in-fa-table
                fat32-in-memory index-list value-list))
          (set-indices-in-fa-table (effective-fat fat32-in-memory)
                                   index-list value-list)))
  :hints
  (("goal"
    :in-theory
    (e/d (set-indices-in-fa-table stobj-set-indices-in-fa-table))
    :induct t)))

(defthm
  fati-of-stobj-set-indices-in-fa-table
  (implies
   (and (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list))
        (compliant-fat32-in-memoryp fat32-in-memory)
        (natp n)
        (nat-listp index-list)
        (not (member-equal n index-list)))
   (equal
    (nth n
         (effective-fat
          (stobj-set-indices-in-fa-table
           fat32-in-memory index-list value-list)))
    (nth n (effective-fat fat32-in-memory))))
  :hints (("goal" :in-theory (disable nth-of-effective-fat)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (fat32-masked-entry-list-p value-list)
          (equal (len index-list)
                 (len value-list))
          (compliant-fat32-in-memoryp fat32-in-memory)
          (natp n)
          (nat-listp index-list)
          (not (member-equal n index-list))
          (< n
             (+ (count-of-clusters fat32-in-memory)
                *ms-first-data-cluster*)))
     (equal (fati n
                  (stobj-set-indices-in-fa-table
                   fat32-in-memory index-list value-list))
            (fati n fat32-in-memory)))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (disable stobj-set-indices-in-fa-table-correctness-1))))))

(defthm
  compliant-fat32-in-memoryp-of-stobj-set-indices-in-fa-table
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (fat32-masked-entry-list-p value-list)
                (equal (len index-list)
                       (len value-list)))
           (compliant-fat32-in-memoryp
            (stobj-set-indices-in-fa-table
             fat32-in-memory index-list value-list)))
  :hints
  (("goal"
    :in-theory (enable stobj-set-indices-in-fa-table)
    :induct
    (stobj-set-indices-in-fa-table fat32-in-memory
                                   index-list value-list))))

(defthm
  cluster-size-of-stobj-set-indices-in-fa-table
  (equal
   (cluster-size (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (cluster-size fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  data-region-length-of-update-fati
  (equal (data-region-length (update-fati i v fat32-in-memory))
         (data-region-length fat32-in-memory))
  :hints
  (("goal" :in-theory (enable data-region-length update-fati))))

(defthm
  data-region-length-of-stobj-set-indices-in-fa-table
  (equal
   (data-region-length (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (data-region-length fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  fat-length-of-stobj-set-indices-in-fa-table
  (equal
   (fat-length (stobj-set-indices-in-fa-table
                fat32-in-memory index-list value-list))
   (fat-length fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  bpb_rootclus-of-stobj-set-indices-in-fa-table
  (equal
   (bpb_rootclus (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (bpb_rootclus fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  data-regioni-of-stobj-set-indices-in-fa-table
  (equal (data-regioni i (stobj-set-indices-in-fa-table
                          fat32-in-memory index-list value-list))
         (data-regioni i fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defund
  make-clusters (text cluster-size)
  (declare
   (xargs :guard (and (stringp text) (natp cluster-size))
          :measure (length text)))
  (if
      (or (zp (length text))
          (zp cluster-size))
      nil
    (list*
     (concatenate
      'string
      (subseq text 0 (min cluster-size (length text)))
      (coerce (make-list (nfix (- cluster-size (length text)))
                         :initial-element (code-char 0))
              'string))
     (make-clusters
      (subseq text (min cluster-size (length text))
              nil)
      cluster-size))))

(defthm
  make-clusters-correctness-1
  (iff (consp (make-clusters text cluster-size))
       (and (not (zp (length text)))
            (not (zp cluster-size))))
  :hints (("goal" :in-theory (enable make-clusters)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (iff (equal (len (make-clusters text cluster-size))
                0)
         (or (zp (length text)) (zp cluster-size)))
    :hints
    (("goal"
      :expand (len (make-clusters text cluster-size)))))))

(defthm
  cluster-listp-of-make-clusters
  (implies (stringp text)
           (cluster-listp (make-clusters text cluster-size)
                          cluster-size))
  :hints
  (("goal"
    :in-theory (enable cluster-listp
                       make-clusters make-list-ac-removal))
   ("subgoal *1/3"
    :in-theory (enable cluster-p cluster-listp
                       make-clusters make-list-ac-removal)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (stringp text)
     (let ((l (make-clusters text cluster-size)))
          (implies (consp l)
                   (and (cluster-p (car l) cluster-size)
                        (cluster-listp (cdr l)
                                       cluster-size))))))))

(defthm
  make-clusters-correctness-2
  (implies (not (zp cluster-size))
           (and (>= (* cluster-size
                       (len (make-clusters text cluster-size)))
                    (length text))
                (< (* cluster-size
                      (len (make-clusters text cluster-size)))
                   (+ cluster-size (length text)))))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable make-clusters))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthmd
    len-of-make-clusters
    (implies (not (zp cluster-size))
             (equal (len (make-clusters text cluster-size))
                    (floor (+ (length text) cluster-size -1)
                           cluster-size)))
    :hints (("goal" :in-theory (e/d (make-clusters) (floor))))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (set-default-hints '((nonlinearp-default-hint++
                        id
                        stable-under-simplificationp hist nil)))

  (defthm
    make-clusters-correctness-3
    (implies (and (stringp text)
                  (not (zp cluster-size))
                  (<= (length text) max-length)
                  (equal (mod max-length cluster-size) 0))
             (<= (* cluster-size
                    (len (make-clusters text cluster-size)))
                 max-length))
    :rule-classes :linear
    :hints (("goal" :in-theory (e/d nil
                                    (mod floor make-clusters-correctness-2))
             :use len-of-make-clusters))))

(defun
    stobj-set-clusters
    (cluster-list index-list fat32-in-memory)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard
    (and (compliant-fat32-in-memoryp fat32-in-memory)
         (lower-bounded-integer-listp
          index-list *ms-first-data-cluster*)
         (cluster-listp cluster-list (cluster-size fat32-in-memory))
         (equal (len index-list)
                (len cluster-list)))
    :verify-guards nil))
  (b*
      (((unless (consp cluster-list))
        fat32-in-memory)
       (fat32-in-memory
        (stobj-set-clusters (cdr cluster-list)
                            (cdr index-list)
                            fat32-in-memory))
       ((unless (and (integerp (car index-list))
                     (>= (car index-list)
                         *ms-first-data-cluster*)
                     (< (car index-list)
                        (+ *ms-first-data-cluster*
                           (data-region-length fat32-in-memory)))))
        fat32-in-memory))
    (update-data-regioni (- (car index-list) *ms-first-data-cluster*)
                         (car cluster-list)
                         fat32-in-memory)))

(defthm
  cluster-size-of-stobj-set-clusters
  (equal
   (cluster-size
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (cluster-size fat32-in-memory)))

(defthm
  count-of-clusters-of-stobj-set-clusters
  (equal
   (count-of-clusters
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (count-of-clusters fat32-in-memory)))

(defthm
  data-region-length-of-stobj-set-clusters
  (equal
   (data-region-length
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (data-region-length fat32-in-memory)))

(defthm
  compliant-fat32-in-memoryp-of-stobj-set-clusters
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (lower-bounded-integer-listp
         index-list *ms-first-data-cluster*)
        (cluster-listp cluster-list (cluster-size fat32-in-memory))
        (equal (len cluster-list)
               (len index-list))
        (equal (data-region-length fat32-in-memory)
               (count-of-clusters fat32-in-memory)))
   (compliant-fat32-in-memoryp
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory)))
  :hints
  (("goal"
    :induct
    (stobj-set-clusters cluster-list index-list fat32-in-memory)
    :in-theory (enable lower-bounded-integer-listp))
   ("subgoal *1/1"
    :expand (lower-bounded-integer-listp index-list 2))))

(defthm
  fati-of-stobj-set-clusters
  (equal (fati i
               (stobj-set-clusters cluster-list
                                   index-list fat32-in-memory))
         (fati i fat32-in-memory)))

(verify-guards
  stobj-set-clusters
  :hints
  (("goal"
    :in-theory (e/d (lower-bounded-integer-listp))
    :induct (stobj-set-clusters cluster-list
                                index-list fat32-in-memory))))

;; (defthm
;;   bounded-nat-listp-of-stobj-set-clusters
;;   (implies
;;    (and (lower-bounded-integer-listp
;;          index-list *ms-first-data-cluster*)
;;         (equal (len index-list)
;;                (len cluster-list)))
;;    (bounded-nat-listp
;;     (mv-nth 1
;;             (stobj-set-clusters cluster-list
;;                                 index-list fat32-in-memory))
;;     (+ *ms-first-data-cluster*
;;        (data-region-length fat32-in-memory))))
;;   :hints
;;   (("goal" :in-theory (enable lower-bounded-integer-listp))))

;; (defthm
;;   fat32-masked-entry-list-p-of-stobj-set-clusters
;;   (implies
;;    (and (lower-bounded-integer-listp
;;          index-list *ms-first-data-cluster*)
;;         (equal (len index-list)
;;                (len cluster-list))
;;         (<= (+ *ms-first-data-cluster*
;;                (data-region-length fat32-in-memory))
;;             *ms-bad-cluster*))
;;    (fat32-masked-entry-list-p
;;     (mv-nth 1
;;             (stobj-set-clusters cluster-list
;;                                 index-list fat32-in-memory))))
;;   :rule-classes
;;   (:rewrite
;;    (:rewrite
;;     :corollary
;;     (implies
;;      (and (lower-bounded-integer-listp
;;            index-list *ms-first-data-cluster*)
;;           (equal (len index-list)
;;                  (len cluster-list))
;;           (<= (+ *ms-first-data-cluster*
;;                  (data-region-length fat32-in-memory))
;;               *ms-bad-cluster*))
;;      (let
;;       ((l
;;         (mv-nth
;;          1
;;          (stobj-set-clusters cluster-list
;;                              index-list fat32-in-memory))))
;;       (implies (consp l)
;;                (and (fat32-masked-entry-list-p (cdr l))
;;                     (fat32-masked-entry-p (car l))))))))
;;   :hints
;;   (("goal"
;;     :use
;;     ((:instance
;;       fat32-masked-entry-list-p-alt
;;       (x (mv-nth
;;           1
;;           (stobj-set-clusters cluster-list
;;                               index-list fat32-in-memory))))
;;      (:instance
;;       bounded-nat-listp-correctness-5
;;       (l
;;        (mv-nth 1
;;                (stobj-set-clusters cluster-list
;;                                    index-list fat32-in-memory)))
;;       (x (+ (data-region-length fat32-in-memory)
;;             *ms-first-data-cluster*))
;;       (y *expt-2-28*))))))

(defthm
  fat-length-of-stobj-set-clusters
  (equal
   (fat-length
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (fat-length fat32-in-memory)))

(defthm
  bpb_rootclus-of-stobj-set-clusters
  (equal
   (bpb_rootclus
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (bpb_rootclus fat32-in-memory)))

;; This function needs to return an mv containing the fat32-in-memory stobj,
;; the new directory entry, and an errno value (either 0 or ENOSPC).

;; One idea we tried was setting first-cluster to *ms-end-of-clusterchain*
;; (basically, marking it used) inside the body of this function. This would
;; have made some proofs more modular... but it doesn't work, because when
;; we're placing the contents of a directory (inside
;; m1-fs-to-fat32-in-memory-helper), we need to make a recursive call to get
;; the contents of that directory in the first place... and first-cluster must
;; be marked used before that call is made to ensure that cluster doesn't get
;; used.
(defund
  place-contents
  (fat32-in-memory dir-ent
                   contents file-length first-cluster)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                (dir-ent-p dir-ent)
                (unsigned-byte-p 32 file-length)
                (stringp contents)
                (<= (fat-length fat32-in-memory)
                    *ms-bad-cluster*)
                (>= (fat-length fat32-in-memory)
                    *ms-first-data-cluster*)
                (fat32-masked-entry-p first-cluster)
                (>= first-cluster *ms-first-data-cluster*)
                (< first-cluster
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory))))
    :guard-hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (lower-bounded-integer-listp)
       ((:rewrite
         fat32-masked-entry-list-p-of-find-n-free-clusters
         . 1)
        unsigned-byte-p))
      :use
      (:instance
       (:rewrite
        fat32-masked-entry-list-p-of-find-n-free-clusters
        . 1)
       (n
        (binary-+
         '-1
         (len (make-clusters contents
                             (cluster-size fat32-in-memory)))))
       (fa-table (effective-fat fat32-in-memory)))))))
  (b*
      ((dir-ent (dir-ent-fix dir-ent))
       (cluster-size (cluster-size fat32-in-memory))
       (clusters (make-clusters contents cluster-size)))
    (if
        (and
         (< (len clusters) 1)
         (mbt
          (and
           (fat32-masked-entry-p first-cluster)
           (< first-cluster
              (fat-length fat32-in-memory)))))
        (b*
            (;; There shouldn't be a memory leak - mark this as free.
             (fat32-in-memory
              (update-fati first-cluster
                           (fat32-update-lower-28
                            (fati first-cluster fat32-in-memory)
                            0)
                           fat32-in-memory))
             ;; From page 17 of the FAT specification: "Note that a zero-length
             ;; file [...] has a first cluster number of 0 placed in its
             ;; directory entry."
             (dir-ent (dir-ent-set-first-cluster-file-size
                       dir-ent 0 file-length)))
          (mv fat32-in-memory dir-ent 0 nil))
      (b*
          ((indices
            (list* first-cluster
                   (stobj-find-n-free-clusters
                    fat32-in-memory (- (len clusters) 1))))
           ((unless (equal (len indices) (len clusters)))
            (mv fat32-in-memory dir-ent *enospc* nil))
           (fat32-in-memory
            (stobj-set-clusters clusters indices fat32-in-memory))
           (fat32-in-memory
            (stobj-set-indices-in-fa-table
             fat32-in-memory indices
             (binary-append (cdr indices)
                            (list *ms-end-of-clusterchain*)))))
        (mv
         fat32-in-memory
         (dir-ent-set-first-cluster-file-size dir-ent (car indices)
                                              file-length)
         0 indices)))))

(defthm
  compliant-fat32-in-memoryp-of-place-contents
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (stringp contents)
        (natp file-length)
        (integerp first-cluster)
        (>= first-cluster *ms-first-data-cluster*)
        (< first-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory))))
   (compliant-fat32-in-memoryp
    (mv-nth
     0
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster))))
  :hints
  (("goal"
    :in-theory
    (e/d (place-contents lower-bounded-integer-listp)
         ((:rewrite
           fat32-masked-entry-list-p-of-find-n-free-clusters
           . 1)))
    :use
    (:instance
     (:rewrite fat32-masked-entry-list-p-of-find-n-free-clusters
               . 1)
     (n
      (binary-+
       '-1
       (len (make-clusters contents
                           (cluster-size fat32-in-memory)))))
     (fa-table (effective-fat fat32-in-memory))))))

(defthm
  cluster-size-of-place-contents
  (equal
   (cluster-size
    (mv-nth 0
            (place-contents fat32-in-memory
                            dir-ent contents file-length first-cluster)))
   (cluster-size fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  count-of-clusters-of-place-contents
  (equal
   (count-of-clusters
    (mv-nth 0
            (place-contents fat32-in-memory
                            dir-ent contents file-length first-cluster)))
   (count-of-clusters fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  data-region-length-of-place-contents
  (equal
   (data-region-length
    (mv-nth
     0
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster)))
   (data-region-length fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  bpb_rootclus-of-place-contents
  (equal
   (bpb_rootclus
    (mv-nth
     0
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster)))
   (bpb_rootclus fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  dir-ent-p-of-place-contents
  (dir-ent-p
   (mv-nth 1
           (place-contents fat32-in-memory
                           dir-ent contents file-length first-cluster)))
  :hints (("goal" :in-theory (enable place-contents)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (unsigned-byte-listp
     8
     (mv-nth 1
             (place-contents fat32-in-memory
                             dir-ent contents file-length first-cluster)))
    :hints (("goal" :in-theory (enable dir-ent-p))))
   (:rewrite
    :corollary
    (equal
     (len
      (mv-nth 1
              (place-contents fat32-in-memory
                              dir-ent contents file-length first-cluster)))
     *ms-dir-ent-length*)
    :hints (("goal" :in-theory (enable dir-ent-p))))
   (:rewrite
    :corollary
    (true-listp
     (mv-nth 1
             (place-contents fat32-in-memory
                             dir-ent contents file-length first-cluster)))
    :hints (("goal" :in-theory (enable dir-ent-p))))))

(defthm
  useless-dir-ent-p-of-dir-ent-set-first-cluster-file-size
  (implies
   (dir-ent-p dir-ent)
   (equal
    (useless-dir-ent-p (dir-ent-set-first-cluster-file-size
                        dir-ent first-cluster file-size))
    (useless-dir-ent-p dir-ent)))
  :hints
  (("goal"
    :in-theory
    (e/d (useless-dir-ent-p dir-ent-p dir-ent-filename
                            dir-ent-set-first-cluster-file-size)
         (loghead logtail (:rewrite logtail-loghead))))))

(defthm
  useless-dir-ent-p-of-place-contents
  (implies
   (dir-ent-p dir-ent)
   (equal
    (useless-dir-ent-p
     (mv-nth 1
             (place-contents fat32-in-memory
                             dir-ent contents file-length first-cluster)))
    (useless-dir-ent-p
     dir-ent)))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  fat-length-of-place-contents
  (equal
   (fat-length
    (mv-nth 0
            (place-contents fat32-in-memory
                            dir-ent contents file-length first-cluster)))
   (fat-length fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  natp-of-place-contents
  (natp
   (mv-nth 2
           (place-contents fat32-in-memory dir-ent
                           contents file-length first-cluster)))
  :hints (("goal" :in-theory (enable place-contents)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (integerp
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))))
   (:linear
    :corollary
    (<=
     0
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))))))

(defthm
  true-listp-of-place-contents
  (true-listp
   (mv-nth 3
           (place-contents fat32-in-memory dir-ent
                           contents file-length first-cluster)))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  fat32-masked-entry-list-p-of-place-contents
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (fat32-masked-entry-p first-cluster))
   (fat32-masked-entry-list-p
    (mv-nth
     3
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster))))
  :hints
  (("goal"
    :in-theory
    (e/d (place-contents)
         ((:rewrite
           fat32-masked-entry-list-p-of-find-n-free-clusters
           . 1)))
    :use
    (:instance
     (:rewrite fat32-masked-entry-list-p-of-find-n-free-clusters
               . 1)
     (n
      (binary-+
       '-1
       (len (make-clusters contents
                           (cluster-size fat32-in-memory)))))
     (fa-table (effective-fat fat32-in-memory))))))

;; OK, this function needs to return a list of directory entries, so that when
;; it is called recursively to take care of all the entries in a subdirectory,
;; the caller gets the list of these entries and becomes able to concatenate
;; them all together, add entries in the front for "." and "..", and then treat
;; the result as the contents of a file. In this scenario, the
;; caller must allocate one cluster even before making the recursive call for
;; the subdirectory, because  the FAT spec says, on page 26, "One cluster is
;; allocated to the directory (unless it is the root directory on a FAT16/FAT12
;; volume), and you set DIR_FstClusLO and DIR_FstClusHI to that cluster number
;; and place an EOC mark in that cluster's entry in the FAT." Now, after the
;; recursive call returns a list of entries, the caller can create a "." entry
;; using the index of the cluster allocated for this subdirectory before this
;; call, and a ".." entry using its own first cluster. However, it cannot know
;; its own first cluster without having it passed from its parent, so this must
;; be an extra argument to the recursive call.
;; Purely for proof purposes, we're also going to have to return an extra
;; argument, namely, the list of indices we used. That will be (mv-nth 3 ...)
;; of the thing.
(defun
    m1-fs-to-fat32-in-memory-helper
    (fat32-in-memory fs current-dir-first-cluster)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                (m1-file-alist-p fs)
                (>= (fat-length fat32-in-memory)
                    *ms-first-data-cluster*)
                (<= (fat-length fat32-in-memory)
                    *ms-bad-cluster*)
                (fat32-masked-entry-p current-dir-first-cluster))
    :hints (("goal" :in-theory (enable m1-file->contents
                                       m1-file-contents-fix)))
    :verify-guards nil))
  (b*
      (;; This is the base case; no directory entries are left. Return an error
       ;; code of 0 (that is, the (mv-nth 2 ...) of the return value).
       ((unless (consp fs))
        (mv fat32-in-memory nil 0 nil))
       ;; The induction case begins here. First, recursively take care of all
       ;; the directory entries after this one in the same directory.
       ((mv fat32-in-memory tail-list errno tail-index-list)
        (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster))
       ;; If there was an error in the recursive call, terminate.
       ((unless (zp errno)) (mv fat32-in-memory tail-list errno tail-index-list))
       (head (car fs))
       ;; "." and ".." entries are not even allowed to be part of an
       ;; m1-file-alist, so perhaps we can use mbt to wipe out this clause...
       ((when (or (equal (car head) *current-dir-fat32-name*)
                  (equal (car head) *parent-dir-fat32-name*)))
        (mv fat32-in-memory tail-list errno tail-index-list))
       ;; Get the directory entry for the first file in this directory.
       (dir-ent (m1-file->dir-ent (cdr head)))
       ;; Search for one cluster - unless empty, the file will need at least
       ;; one.
       (indices
        (stobj-find-n-free-clusters
         fat32-in-memory 1))
       ;; This means we couldn't find even one free cluster, so we return a "no
       ;; space left" error.
       ((when (< (len indices) 1))
        (mv fat32-in-memory tail-list *enospc* tail-index-list))
       (first-cluster
        (nth 0 indices))
       ;; The mbt below says this branch will never be taken; but having this
       ;; allows us to prove a strong rule about fat-length.
       ((unless (mbt (< first-cluster (fat-length fat32-in-memory))))
        (mv fat32-in-memory tail-list *enospc* tail-index-list))
       ;; Mark this cluster as used, without possibly interfering with any
       ;; existing clusterchains.
       (fat32-in-memory
        (update-fati
         first-cluster
         (fat32-update-lower-28 (fati first-cluster fat32-in-memory)
                                *ms-end-of-clusterchain*)
         fat32-in-memory)))
    (if
        (m1-regular-file-p (cdr head))
        (b* ((contents (m1-file->contents (cdr head)))
             (file-length (length contents))
             ((mv fat32-in-memory dir-ent errno head-index-list)
              (place-contents fat32-in-memory
                              dir-ent contents file-length first-cluster))
             (dir-ent (dir-ent-set-filename dir-ent (car head)))
             (dir-ent
              (dir-ent-install-directory-bit
               dir-ent nil)))
        (mv fat32-in-memory
            (list* dir-ent tail-list)
            errno
            (append head-index-list tail-index-list)))
      (b* ((contents (m1-file->contents (cdr head)))
           (file-length 0)
           ((mv fat32-in-memory unflattened-contents errno head-index-list1)
            (m1-fs-to-fat32-in-memory-helper
             fat32-in-memory contents first-cluster))
           ((unless (zp errno)) (mv fat32-in-memory tail-list errno tail-index-list))
           (contents
            (nats=>string
             (append
              (dir-ent-install-directory-bit
               (dir-ent-set-filename
                (dir-ent-set-first-cluster-file-size
                 dir-ent
                 first-cluster
                 0)
                *current-dir-fat32-name*)
               t)
              (dir-ent-install-directory-bit
               (dir-ent-set-filename
                (dir-ent-set-first-cluster-file-size
                 dir-ent
                 current-dir-first-cluster
                 0)
                *parent-dir-fat32-name*)
               t)
              (flatten unflattened-contents))))
           ((mv fat32-in-memory dir-ent errno head-index-list2)
            (place-contents fat32-in-memory
                            dir-ent contents file-length
                            first-cluster))
           (dir-ent (dir-ent-set-filename dir-ent (car head)))
           (dir-ent
            (dir-ent-install-directory-bit
             dir-ent t)))
        (mv fat32-in-memory
            (list* dir-ent tail-list)
            errno
            (append head-index-list1 head-index-list2 tail-index-list))))))

(defthm
  cluster-size-of-m1-fs-to-fat32-in-memory-helper
  (equal
   (cluster-size (mv-nth 0
                         (m1-fs-to-fat32-in-memory-helper
                          fat32-in-memory
                          fs current-dir-first-cluster)))
   (cluster-size fat32-in-memory)))

(defthm
  count-of-clusters-of-m1-fs-to-fat32-in-memory-helper
  (equal
   (count-of-clusters
    (mv-nth 0
            (m1-fs-to-fat32-in-memory-helper
             fat32-in-memory fs current-dir-first-cluster)))
   (count-of-clusters fat32-in-memory)))

(defthm natp-of-m1-fs-to-fat32-in-memory-helper
  (natp (mv-nth 2
                (m1-fs-to-fat32-in-memory-helper
                 fat32-in-memory
                 fs current-dir-first-cluster)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (integerp (mv-nth 2
                      (m1-fs-to-fat32-in-memory-helper
                       fat32-in-memory
                       fs current-dir-first-cluster))))
   (:linear
    :corollary
    (<= 0
        (mv-nth 2
                (m1-fs-to-fat32-in-memory-helper
                 fat32-in-memory
                 fs current-dir-first-cluster))))))

(defthm
  data-region-length-of-m1-fs-to-fat32-in-memory-helper
  (equal
   (data-region-length
    (mv-nth 0
            (m1-fs-to-fat32-in-memory-helper
             fat32-in-memory fs current-dir-first-cluster)))
   (data-region-length fat32-in-memory)))

(defthm
  bpb_rootclus-of-m1-fs-to-fat32-in-memory-helper
  (equal
   (bpb_rootclus
    (mv-nth 0
            (m1-fs-to-fat32-in-memory-helper
             fat32-in-memory fs current-dir-first-cluster)))
   (bpb_rootclus fat32-in-memory)))

(defthm
  fat-length-of-m1-fs-to-fat32-in-memory-helper
  (equal
   (fat-length (mv-nth 0
                       (m1-fs-to-fat32-in-memory-helper
                        fat32-in-memory fs first-cluster)))
   (fat-length fat32-in-memory)))

(defthm
  compliant-fat32-in-memoryp-of-m1-fs-to-fat32-in-memory-helper-lemma-1
  (implies
   (compliant-fat32-in-memoryp fat32-in-memory)
   (and
    (not (< (binary-+ '2
                      (count-of-clusters fat32-in-memory))
            '0))
    (not (< (binary-+ '2
                      (count-of-clusters fat32-in-memory))
            '2))
    (not
     (< (nfix (binary-+ '2
                        (count-of-clusters fat32-in-memory)))
        '2)))))

;; These subgoal hints were needed because :brr was unhelpful in figuring out
;; why compliant-fat32-in-memoryp-of-place-contents - a reasonably general
;; rewrite rule - was failing. The hypothesis cited as the cause was an
;; inequality which a linear rule should have take care of, but... no clear
;; further explanation emerged.
(defthm
  compliant-fat32-in-memoryp-of-m1-fs-to-fat32-in-memory-helper
  (implies
   (compliant-fat32-in-memoryp fat32-in-memory)
   (compliant-fat32-in-memoryp
    (mv-nth 0
            (m1-fs-to-fat32-in-memory-helper
             fat32-in-memory fs first-cluster))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lower-bounded-integer-listp
      painful-debugging-lemma-9)
     (stobj-set-indices-in-fa-table nth)))))

(defthm
  m1-fs-to-fat32-in-memory-helper-correctness-1
  (unsigned-byte-listp
   8
   (flatten (mv-nth 1
                    (m1-fs-to-fat32-in-memory-helper
                     fat32-in-memory fs first-cluster))))
  :hints (("Goal" :in-theory (enable lower-bounded-integer-listp))))

(defthm
  m1-fs-to-fat32-in-memory-helper-correctness-2
  (equal
   (len
    (flatten
     (mv-nth
      1
      (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs first-cluster))))
   (* *ms-dir-ent-length*
      (len
       (mv-nth
        1
        (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs first-cluster))))))

(defthm
  m1-fs-to-fat32-in-memory-helper-correctness-3
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (equal (data-region-length fat32-in-memory)
               (count-of-clusters fat32-in-memory)))
   (b*
       (((mv & dir-ent-list errno)
         (m1-fs-to-fat32-in-memory-helper
          fat32-in-memory
          fs current-dir-first-cluster)))
     (implies
      (and (zp errno)
           (atom (assoc-equal *current-dir-fat32-name* fs))
           (atom (assoc-equal *parent-dir-fat32-name* fs)))
      (equal (len dir-ent-list) (len fs))))))

(defthm
  m1-fs-to-fat32-in-memory-helper-correctness-4
  (implies
   (and (m1-file-alist-p fs)
        (zp (mv-nth 2
                    (m1-fs-to-fat32-in-memory-helper
                     fat32-in-memory fs first-cluster))))
   (equal (len (mv-nth 1
                       (m1-fs-to-fat32-in-memory-helper
                        fat32-in-memory fs first-cluster)))
          (len fs))))

(defthm
  true-listp-of-m1-fs-to-fat32-in-memory-helper
  (true-listp (mv-nth 3
                      (m1-fs-to-fat32-in-memory-helper
                       fat32-in-memory
                       fs current-dir-first-cluster))))

(encapsulate
  ()

  (local
   (defthm
     m1-fs-to-fat32-in-memory-helper-guard-lemma-1
     (implies (not (m1-regular-file-p file))
              (equal (m1-directory-file-p file)
                     (m1-file-p file)))
     :hints
     (("goal"
       :in-theory (enable m1-directory-file-p m1-file-p
                          m1-regular-file-p m1-file-contents-p
                          m1-file->contents)))))

  (local
   (defthm
     m1-fs-to-fat32-in-memory-helper-guard-lemma-2
     (implies (unsigned-byte-listp 8 x)
              (true-listp x))))

  (defthm
    m1-fs-to-fat32-in-memory-helper-guard-lemma-3
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (not
      (<
       (nth
        '0
        (find-n-free-clusters
         (effective-fat (mv-nth '0
                                (m1-fs-to-fat32-in-memory-helper
                                 fat32-in-memory (cdr fs)
                                 current-dir-first-cluster)))
         '1))
       '0))))

  (verify-guards
    m1-fs-to-fat32-in-memory-helper
    :hints
    (("goal"
      :in-theory
      (e/d
       (painful-debugging-lemma-9)
       (nth stobj-set-indices-in-fa-table))))))

(defthm
  m1-fs-to-fat32-in-memory-guard-lemma-1
  (implies
   (and (< (fat32-entry-mask (bpb_rootclus fat32-in-memory))
           (count-of-clusters fat32-in-memory))
        (<= (+ (count-of-clusters fat32-in-memory)
               *ms-first-data-cluster*)
            (fat-length fat32-in-memory)))
   (<
    (binary-+ '1
              (fat32-entry-mask (bpb_rootclus fat32-in-memory)))
    (fat-length fat32-in-memory))))

(defun
  m1-fs-to-fat32-in-memory
  (fat32-in-memory fs)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                (m1-file-alist-p fs)
                (equal (data-region-length fat32-in-memory)
                       (count-of-clusters fat32-in-memory))
                (>= (fat-length fat32-in-memory)
                    *ms-first-data-cluster*)
                (<= (fat-length fat32-in-memory)
                    *ms-bad-cluster*))
    :guard-hints
    (("goal" :in-theory (e/d (lower-bounded-integer-listp))
      :do-not-induct t))))
  (b*
      ((rootclus (bpb_rootclus fat32-in-memory))
       (cluster-size (cluster-size fat32-in-memory))
       ;; we keep the root cluster uncleared because we don't want anything
       ;; other than the root directory going into it
       (index-list-to-clear
        (remove
         (fat32-entry-mask rootclus)
         (generate-index-list *ms-first-data-cluster*
                              (- (fat-length fat32-in-memory)
                                 *ms-first-data-cluster*))))
       (fat32-in-memory (stobj-set-indices-in-fa-table
                         fat32-in-memory index-list-to-clear
                         (make-list (len index-list-to-clear)
                                    :initial-element 0)))
       ((mv fat32-in-memory root-dir-ent-list errno &)
        (m1-fs-to-fat32-in-memory-helper
         fat32-in-memory
         fs (fat32-entry-mask rootclus)))
       ((unless (zp errno))
        (mv fat32-in-memory errno))
       (contents (nats=>string (flatten root-dir-ent-list)))
       (clusters (make-clusters contents cluster-size))
       ;; Quote: "Note that a zero-length file [...] has a first cluster
       ;; number of 0 placed in its directory entry." from page 17 of the FAT
       ;; specification. This applies here in the very specific case of an
       ;; empty root directory with no files in it, which came up in a
       ;; regression test.
       ((when (atom clusters))
        (b*
            ((fat32-in-memory (update-fati (fat32-entry-mask rootclus)
                                           0 fat32-in-memory))
             (fat32-in-memory
              (update-data-regioni
               (- (fat32-entry-mask rootclus)
                  *ms-first-data-cluster*)
               (coerce (make-list (cluster-size fat32-in-memory)
                                  :initial-element (code-char 0))
                       'string)
               fat32-in-memory)))
          (mv fat32-in-memory 0)))
       (fat32-in-memory (update-fati (fat32-entry-mask rootclus)
                                     *ms-end-of-clusterchain* fat32-in-memory))
       (indices (list* (fat32-entry-mask rootclus)
                       (stobj-find-n-free-clusters
                        fat32-in-memory (- (len clusters) 1))))
       ((unless (equal (len indices) (len clusters)))
        (mv fat32-in-memory *enospc*))
       (fat32-in-memory
        (stobj-set-clusters clusters indices fat32-in-memory))
       (fat32-in-memory
        (stobj-set-indices-in-fa-table
         fat32-in-memory indices
         (binary-append (cdr indices)
                        (list *ms-end-of-clusterchain*)))))
    (mv fat32-in-memory 0)))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (defun
    stobj-fa-table-to-string-helper
    (fat32-in-memory length ac)
    (declare
     (xargs
      :stobjs fat32-in-memory
      :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                  (natp length)
                  (<= length (fat-length fat32-in-memory)))
      :guard-hints
      (("goal"
        :in-theory
        (e/d
         (fat32-entry-p)
         (unsigned-byte-p loghead logtail
                          fati-when-compliant-fat32-in-memoryp))
        :use (:instance fati-when-compliant-fat32-in-memoryp
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
        ac))))))

(defthm
  character-listp-of-stobj-fa-table-to-string-helper
  (equal
   (character-listp
    (stobj-fa-table-to-string-helper fat32-in-memory length ac))
   (character-listp ac))
  :hints (("Goal" :in-theory (disable loghead logtail))))

(defthm
  len-of-stobj-fa-table-to-string-helper
  (equal
   (len
    (stobj-fa-table-to-string-helper
     fat32-in-memory length ac))
   (+ (len ac) (* 4 (nfix length))))
  :hints (("Goal" :in-theory (disable loghead logtail))))

(defund
    stobj-fa-table-to-string
    (fat32-in-memory)
    (declare
     (xargs
      :stobjs fat32-in-memory
      :guard (compliant-fat32-in-memoryp fat32-in-memory)))
    (coerce
     (stobj-fa-table-to-string-helper
      fat32-in-memory (fat-length fat32-in-memory) nil)
     'string))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    reserved-area-string-guard-lemma-1
    (implies (compliant-fat32-in-memoryp fat32-in-memory)
             (natp (- (* (bpb_bytspersec fat32-in-memory)
                         (bpb_rsvdseccnt fat32-in-memory))
                      90)))
    :rule-classes
    ((:linear
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (<= 90
                   (* (bpb_bytspersec fat32-in-memory)
                      (bpb_rsvdseccnt fat32-in-memory)))))
     (:rewrite
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (integerp (* (bpb_bytspersec fat32-in-memory)
                            (bpb_rsvdseccnt fat32-in-memory)))))
     (:rewrite
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (integerp (- (* (bpb_bytspersec fat32-in-memory)
                               (bpb_rsvdseccnt fat32-in-memory)))))))
    :hints (("goal" :in-theory (e/d (compliant-fat32-in-memoryp)
                                    (fat32-in-memoryp))))))

(defthm
  reserved-area-string-guard-lemma-2
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp i)
                (< i (fat-length fat32-in-memory)))
           (and (integerp (fati i fat32-in-memory))
                (<= 0 (fati i fat32-in-memory))
                (< (fati i fat32-in-memory) 4294967296)))
  :rule-classes
  ((:rewrite
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (fat-length fat32-in-memory)))
                        (integerp (fati i fat32-in-memory))))
   (:linear
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (fat-length fat32-in-memory)))
                        (and (<= 0 (fati i fat32-in-memory))
                             (< (fati i fat32-in-memory)
                                4294967296)))))
  :hints
  (("goal"
    :in-theory
    (e/d (compliant-fat32-in-memoryp fat32-entry-p)
         (fati fati-when-compliant-fat32-in-memoryp))
    :use fati-when-compliant-fat32-in-memoryp)))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

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
                    :guard (compliant-fat32-in-memoryp fat32-in-memory)
                    :guard-debug t
                    :guard-hints (("Goal"
                                   :do-not-induct t
                                   :in-theory (disable loghead logtail
                                                       bs_vollabi
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
   (compliant-fat32-in-memoryp fat32-in-memory)
   (equal (len (reserved-area-chars fat32-in-memory))
          (* (bpb_rsvdseccnt fat32-in-memory)
             (bpb_bytspersec fat32-in-memory))))
  :hints (("goal" :in-theory (e/d (reserved-area-chars) (loghead logtail)))))

(defund
  reserved-area-string (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (compliant-fat32-in-memoryp fat32-in-memory)))
  (implode (reserved-area-chars fat32-in-memory)))

(defthm
  length-of-reserved-area-string
  (implies
   (compliant-fat32-in-memoryp fat32-in-memory)
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
  :instructions ((:in-theory (disable loghead logtail))
                 (:dive 1 2 1)
                 :x
                 :up (:rewrite str::explode-of-implode)
                 :s (:rewrite already-a-character-list)
                 :x :top
                 :bash :bash))

;; A bit of explanation is in order here - this function recurs on n, which is
;; instantiated with (bpb_numfats fat32-in-memory) in
;; fat32-in-memory-to-string. stobj-fa-table-to-string, in contrast, generates
;; one copy of the FAT string from the fat32-in-memory instance, and does all
;; the part-select heavy lifting.
(defund
  make-fat-string-ac
  (n fat32-in-memory ac)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
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
  :hints (("goal" :in-theory (e/d (stobj-fa-table-to-string) (loghead logtail)))))

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
                (compliant-fat32-in-memoryp fat32-in-memory)
                (<= len
                    (data-region-length fat32-in-memory))
                (character-listp ac))
    :guard-hints
    (("goal" :in-theory (disable fat32-in-memoryp)))))
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

(defun
    princ$-data-region-string-helper
    (fat32-in-memory len channel state)
  (declare
   (xargs
    :stobjs (fat32-in-memory state)
    :guard (and (natp len)
                (compliant-fat32-in-memoryp fat32-in-memory)
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
        (<= len
            (data-region-length fat32-in-memory))
        (compliant-fat32-in-memoryp fat32-in-memory)
        (natp len)
        (state-p1 state))
   (and (open-output-channel-p1
         channel
         :character (princ$-data-region-string-helper
                     fat32-in-memory len channel state))
        (state-p1 (princ$-data-region-string-helper
                   fat32-in-memory len channel state))))
  :hints
  (("goal" :induct (princ$-data-region-string-helper
                    fat32-in-memory len channel state))))

(verify-guards
  princ$-data-region-string-helper)

(defthm
  data-region-string-helper-of-binary-append
  (implies
   (and (natp len)
        (compliant-fat32-in-memoryp fat32-in-memory)
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
        (compliant-fat32-in-memoryp fat32-in-memory)
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
  fat32-in-memory-to-string
  (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (compliant-fat32-in-memoryp fat32-in-memory)))
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
  length-of-fat32-in-memory-to-string-lemma-1
  (implies (compliant-fat32-in-memoryp fat32-in-memory)
           (and
           (equal (nfix (bpb_numfats fat32-in-memory))
                  (bpb_numfats fat32-in-memory))
           (equal (nfix (count-of-clusters fat32-in-memory))
                  (count-of-clusters fat32-in-memory))))
  :hints (("goal" :in-theory (enable compliant-fat32-in-memoryp
                                     fat32-in-memoryp
                                     bpb_numfats))))

(defthm
  length-of-fat32-in-memory-to-string
  (implies
   (compliant-fat32-in-memoryp fat32-in-memory)
   (equal
    (len
     (explode (fat32-in-memory-to-string fat32-in-memory)))
    (+ (* (bpb_rsvdseccnt fat32-in-memory)
          (bpb_bytspersec fat32-in-memory))
       (* (bpb_numfats fat32-in-memory)
          (fat-length fat32-in-memory)
          4)
       (* (cluster-size fat32-in-memory)
          (data-region-length fat32-in-memory)))))
  :hints
  (("goal" :in-theory (e/d (fat32-in-memory-to-string) (nfix)))))

(defun
  fat32-in-memory-to-disk-image
  (fat32-in-memory image-path state)
  (declare
   (xargs
    :stobjs (fat32-in-memory state)
    :guard (and (state-p state)
                (stringp image-path)
                (compliant-fat32-in-memoryp fat32-in-memory))
    :guard-hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d (fat32-in-memory-to-string)
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
       ((when (null channel)) state)
       (state
        (mbe
         :logic (princ$ (fat32-in-memory-to-string fat32-in-memory)
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
    state))

(defmacro
    update-bpb_secperclus-macro
    (name stobj update-bpb_secperclus-of-name)
  `(defthm
     ,update-bpb_secperclus-of-name
     (equal
      (update-bpb_secperclus
       v1
       (,name v2 ,stobj))
      (,name
       v2
       (update-bpb_secperclus v1 ,stobj)))
     :hints (("goal" :in-theory (enable update-bpb_secperclus ,name)))))

(update-bpb_secperclus-macro update-bs_oemname fat32-in-memory
                             update-bpb_secperclus-of-update-bs_oemname)

(update-bpb_secperclus-macro update-bs_jmpboot fat32-in-memory
                             update-bpb_secperclus-of-update-bs_jmpboot)

(update-bpb_secperclus-macro update-bpb_bytspersec fat32-in-memory
                             update-bpb_secperclus-of-update-bpb_bytspersec)

(update-bpb_secperclus-macro update-bpb_fatsz32 fat32-in-memory
                             update-bpb_secperclus-of-update-bpb_fatsz32)

(update-bpb_secperclus-macro update-bpb_numfats fat32-in-memory
                             update-bpb_secperclus-of-update-bpb_numfats)

(update-bpb_secperclus-macro update-bpb_rsvdseccnt fat32-in-memory
                             update-bpb_secperclus-of-update-bpb_rsvdseccnt)

(defmacro
    update-bpb_rsvdseccnt-macro
    (name stobj update-bpb_rsvdseccnt-of-name)
  `(defthm
     ,update-bpb_rsvdseccnt-of-name
     (equal
      (update-bpb_rsvdseccnt
       v1
       (,name v2 ,stobj))
      (,name
       v2
       (update-bpb_rsvdseccnt v1 ,stobj)))
     :hints (("goal" :in-theory (enable update-bpb_rsvdseccnt ,name)))))

(update-bpb_rsvdseccnt-macro update-bs_oemname fat32-in-memory
                             update-bpb_rsvdseccnt-of-update-bs_oemname)

(update-bpb_rsvdseccnt-macro update-bs_jmpboot fat32-in-memory
                             update-bpb_rsvdseccnt-of-update-bs_jmpboot)

(update-bpb_rsvdseccnt-macro update-bpb_bytspersec fat32-in-memory
                             update-bpb_rsvdseccnt-of-update-bpb_bytspersec)

(update-bpb_rsvdseccnt-macro update-bpb_fatsz32 fat32-in-memory
                             update-bpb_rsvdseccnt-of-update-bpb_fatsz32)

(update-bpb_rsvdseccnt-macro update-bpb_numfats fat32-in-memory
                             update-bpb_rsvdseccnt-of-update-bpb_numfats)

(defmacro
    update-bpb_numfats-macro
    (name stobj update-bpb_numfats-of-name)
  `(defthm
     ,update-bpb_numfats-of-name
     (equal
      (update-bpb_numfats
       v1
       (,name v2 ,stobj))
      (,name
       v2
       (update-bpb_numfats v1 ,stobj)))
     :hints (("goal" :in-theory (enable update-bpb_numfats ,name)))))

(update-bpb_numfats-macro update-bs_oemname fat32-in-memory
                          update-bpb_numfats-of-update-bs_oemname)

(update-bpb_numfats-macro update-bs_jmpboot fat32-in-memory
                          update-bpb_numfats-of-update-bs_jmpboot)

(update-bpb_numfats-macro update-bpb_bytspersec fat32-in-memory
                          update-bpb_numfats-of-update-bpb_bytspersec)

(update-bpb_numfats-macro update-bpb_fatsz32 fat32-in-memory
                          update-bpb_numfats-of-update-bpb_fatsz32)

(defmacro
    update-bpb_fatsz32-macro
    (name stobj update-bpb_fatsz32-of-name)
  `(defthm
     ,update-bpb_fatsz32-of-name
     (equal
      (update-bpb_fatsz32
       v1
       (,name v2 ,stobj))
      (,name
       v2
       (update-bpb_fatsz32 v1 ,stobj)))
     :hints (("goal" :in-theory (enable update-bpb_fatsz32 ,name)))))

(update-bpb_fatsz32-macro update-bs_oemname fat32-in-memory
                          update-bpb_fatsz32-of-update-bs_oemname)

(update-bpb_fatsz32-macro update-bs_jmpboot fat32-in-memory
                          update-bpb_fatsz32-of-update-bs_jmpboot)

(update-bpb_fatsz32-macro update-bpb_totsec32 fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_totsec32)

(update-bpb_fatsz32-macro update-bpb_hiddsec fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_hiddsec)

(update-bpb_fatsz32-macro update-bpb_numheads fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_numheads)

(update-bpb_fatsz32-macro update-bpb_secpertrk fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_secpertrk)

(update-bpb_fatsz32-macro update-bpb_fatsz16 fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_fatsz16)

(update-bpb_fatsz32-macro update-bpb_media fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_media)

(update-bpb_fatsz32-macro update-bpb_totsec16 fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_totsec16)

(update-bpb_fatsz32-macro update-bpb_rootentcnt fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_rootentcnt)

(update-bpb_fatsz32-macro update-bpb_bytspersec fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_bytspersec)

(defmacro
    update-bpb_bytspersec-macro
    (name stobj update-bpb_bytspersec-of-name)
  `(defthm
     ,update-bpb_bytspersec-of-name
     (equal
      (update-bpb_bytspersec
       v1
       (,name v2 ,stobj))
      (,name
       v2
       (update-bpb_bytspersec v1 ,stobj)))
     :hints (("goal" :in-theory (enable update-bpb_bytspersec ,name)))))

(update-bpb_bytspersec-macro update-bs_oemname fat32-in-memory
                             update-bpb_bytspersec-of-update-bs_oemname)

(update-bpb_bytspersec-macro update-bs_jmpboot fat32-in-memory
                             update-bpb_bytspersec-of-update-bs_jmpboot)

;; We're not counting this very directory, because the root does not have a
;; directory entry for itself.
(defun m1-entry-count (fs)
  (declare (xargs :guard (m1-file-alist-p fs)))
  (if
      (atom fs)
      0
    (if (m1-directory-file-p (cdar fs))
        (+ 3
           (m1-entry-count (m1-file->contents (cdar fs)))
           (m1-entry-count (cdr fs)))
      (+ 1
         (m1-entry-count (cdr fs))))))

;; (defthm
;;   fat32-in-memory-to-m1-fs-helper-correctness-3
;;   (implies (unsigned-byte-listp 8 dir-contents)
;;            (b* (((mv m1-file-alist entry-count)
;;                  (fat32-in-memory-to-m1-fs-helper
;;                   fat32-in-memory
;;                   dir-contents entry-limit)))
;;              (equal
;;               entry-count
;;               (m1-entry-count m1-file-alist))))
;;   :hints (("goal" :induct (fat32-in-memory-to-m1-fs-helper
;;                            fat32-in-memory
;;                            dir-contents entry-limit))))

(defthm
  data-regioni-of-stobj-set-clusters
  (implies
   (and (natp i)
        (not (member-equal (+ i *ms-first-data-cluster*)
                           index-list)))
   (equal (data-regioni i
                        (stobj-set-clusters cluster-list
                                            index-list fat32-in-memory))
          (data-regioni i fat32-in-memory)))
  :hints (("goal" :in-theory (enable lower-bounded-integer-listp))))

(defthm
  get-clusterchain-contents-of-place-contents-disjoint
  (implies
   (and
    (compliant-fat32-in-memoryp fat32-in-memory)
    (stringp contents)
    (integerp first-cluster)
    (<= 2 first-cluster)
    (fat32-masked-entry-p masked-current-cluster)
    (equal (mv-nth 1
                   (get-clusterchain-contents fat32-in-memory
                                              masked-current-cluster length))
           0)
    (not
     (member-equal
      first-cluster
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster length
                                      (cluster-size fat32-in-memory))))))
   (equal (get-clusterchain-contents
           (mv-nth 0
                   (place-contents fat32-in-memory dir-ent
                                   contents file-length first-cluster))
           masked-current-cluster length)
          (get-clusterchain-contents fat32-in-memory
                                     masked-current-cluster length)))
  :hints (("goal" :in-theory (e/d (place-contents lower-bounded-integer-listp
                                                  intersectp-equal)
                                  (intersectp-is-commutative)))))

(defthm
  effective-fat-of-stobj-set-clusters
  (equal (effective-fat
          (stobj-set-clusters cluster-list
                              index-list fat32-in-memory))
         (effective-fat fat32-in-memory)))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-1
  (implies
   (and
    (compliant-fat32-in-memoryp fat32-in-memory)
    (natp masked-current-cluster)
    (integerp first-cluster)
    (>= first-cluster *ms-first-data-cluster*)
    (stringp contents)
    (not
     (member-equal
      first-cluster
      (mv-nth
       0
       (fat32-build-index-list (effective-fat fat32-in-memory)
                               masked-current-cluster
                               length cluster-size))))
    (equal
     (mv-nth
      1
      (fat32-build-index-list (effective-fat fat32-in-memory)
                              masked-current-cluster
                              length cluster-size))
     0))
   (equal
    (fat32-build-index-list
     (effective-fat
      (mv-nth
       0
       (place-contents fat32-in-memory dir-ent
                       contents file-length first-cluster)))
     masked-current-cluster
     length cluster-size)
    (fat32-build-index-list (effective-fat fat32-in-memory)
                            masked-current-cluster
                            length cluster-size)))
  :hints
  (("goal"
    :in-theory
    (e/d (place-contents lower-bounded-integer-listp)
         ((:rewrite
           fat32-masked-entry-list-p-of-find-n-free-clusters
           . 1)
          (:rewrite intersectp-is-commutative)))
    :do-not-induct t
    :use
    ((:instance
      (:rewrite
       fat32-masked-entry-list-p-of-find-n-free-clusters
       . 1)
      (n
       (+ -1
          (len (make-clusters contents
                              (cluster-size fat32-in-memory)))))
      (fa-table (effective-fat fat32-in-memory)))
     (:instance
      (:rewrite intersectp-is-commutative)
      (y
       (cons
        first-cluster
        (find-n-free-clusters
         (effective-fat fat32-in-memory)
         (+
          -1
          (len
           (make-clusters contents
                          (cluster-size fat32-in-memory)))))))
      (x
       (mv-nth
        0
        (fat32-build-index-list (effective-fat fat32-in-memory)
                                masked-current-cluster
                                length cluster-size)))))
    :expand
    (intersectp-equal
     (cons
      first-cluster
      (find-n-free-clusters
       (effective-fat fat32-in-memory)
       (+
        -1
        (len (make-clusters contents
                            (cluster-size fat32-in-memory))))))
     (mv-nth
      0
      (fat32-build-index-list (effective-fat fat32-in-memory)
                              masked-current-cluster
                              length cluster-size))))))

(defthm
  length-of-get-clusterchain-contents
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (natp length))
   (<=
    (len (explode (mv-nth 0
                          (get-clusterchain-contents
                           fat32-in-memory
                           masked-current-cluster length))))
    length))
  :rule-classes :linear)

(defthm
  fat32-in-memory-to-m1-fs-helper-of-place-contents
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (stringp contents)
        (integerp first-cluster)
        (>= first-cluster *ms-first-data-cluster*)
        (equal (mv-nth 3
                       (fat32-in-memory-to-m1-fs-helper
                        fat32-in-memory
                        dir-contents entry-limit))
               0)
        (not-intersectp-list
         (list first-cluster)
         (mv-nth 2
                 (fat32-in-memory-to-m1-fs-helper
                  fat32-in-memory
                  dir-contents entry-limit))))
   (equal
    (fat32-in-memory-to-m1-fs-helper
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     dir-contents entry-limit)
    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                     dir-contents entry-limit)))
  :hints
  (("goal"
    :in-theory
    (e/d nil
         (dir-ent-fix
          (:definition get-clusterchain-contents)
          (:rewrite by-slice-you-mean-the-whole-cake-2)))
    :induct
    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                     dir-contents entry-limit)
    :expand
    ((fat32-in-memory-to-m1-fs-helper
      (mv-nth
       0
       (place-contents fat32-in-memory dir-ent
                       contents file-length first-cluster))
      dir-contents entry-limit)
     (:free (y)
            (intersectp-equal (list first-cluster)
                              y))))))

(defthm
  get-clusterchain-contents-of-update-fati
  (implies
   (and
    (integerp masked-current-cluster)
    (not
     (member-equal
      i
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster length
                                      (cluster-size fat32-in-memory))))))
   (equal (get-clusterchain-contents (update-fati i v fat32-in-memory)
                                     masked-current-cluster length)
          (get-clusterchain-contents fat32-in-memory
                                     masked-current-cluster length)))
  :hints
  (("goal"
    :induct (get-clusterchain-contents fat32-in-memory
                                       masked-current-cluster length)
    :expand ((get-clusterchain-contents (update-fati i v fat32-in-memory)
                                        masked-current-cluster length)))))

(defthmd
  m1-fs-to-fat32-in-memory-inversion-lemma-2
  (implies
   (and (not (zp (cluster-size fat32-in-memory)))
        (dir-ent-p dir-ent))
   (equal
    (mv-nth 1
            (place-contents fat32-in-memory dir-ent
                            contents file-length first-cluster))
    (if
     (equal (length contents) 0)
     (dir-ent-set-first-cluster-file-size dir-ent 0 file-length)
     (if
      (equal
       (+
        1
        (len (stobj-find-n-free-clusters
              fat32-in-memory
              (+ -1
                 (len (make-clusters contents
                                     (cluster-size fat32-in-memory)))))))
       (len (make-clusters contents
                           (cluster-size fat32-in-memory))))
      (dir-ent-set-first-cluster-file-size dir-ent first-cluster file-length)
      dir-ent))))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  fat32-in-memory-to-m1-fs-helper-of-update-fati
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (< (nfix i)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (not-intersectp-list
         (list i)
         (mv-nth 2
                 (fat32-in-memory-to-m1-fs-helper
                  fat32-in-memory
                  dir-contents entry-limit)))
        (equal (mv-nth 3
                       (fat32-in-memory-to-m1-fs-helper
                        fat32-in-memory
                        dir-contents entry-limit))
               0))
   (equal
    (fat32-in-memory-to-m1-fs-helper
     (update-fati i v fat32-in-memory)
     dir-contents entry-limit)
    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                     dir-contents entry-limit)))
  :hints
  (("goal"
    :induct
    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                     dir-contents entry-limit)
    :expand ((fat32-in-memory-to-m1-fs-helper
              (update-fati i v fat32-in-memory)
              dir-contents entry-limit)
             (:free (x y)
                    (intersectp-equal (list x) y))
             (:free (y) (intersectp-equal nil y)))
    :in-theory
    (disable update-nth
             (:definition get-clusterchain-contents)
             (:rewrite natp-of-cluster-size . 1)
             (:rewrite by-slice-you-mean-the-whole-cake-2)
             (:definition fat32-build-index-list)))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-3
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (natp n)
        (equal (mv-nth 3
                       (fat32-in-memory-to-m1-fs-helper
                        fat32-in-memory
                        dir-contents entry-limit))
               0))
   (not-intersectp-list
    (find-n-free-clusters (effective-fat fat32-in-memory)
                          n)
    (mv-nth 2
            (fat32-in-memory-to-m1-fs-helper
             fat32-in-memory
             dir-contents entry-limit))))
  :hints
  (("goal"
    :in-theory
    (e/d (intersectp-equal)
         ((:definition get-clusterchain-contents)
          (:rewrite by-slice-you-mean-the-whole-cake-2)
          (:definition fat32-build-index-list)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (compliant-fat32-in-memoryp fat32-in-memory)
      (equal n 1)
      (equal
       (len
        (find-n-free-clusters (effective-fat fat32-in-memory)
                              n))
       1)
      (equal (mv-nth 3
                     (fat32-in-memory-to-m1-fs-helper
                      fat32-in-memory
                      dir-contents entry-limit))
             0))
     (not-intersectp-list
      (cons
       (nth
        0
        (find-n-free-clusters (effective-fat fat32-in-memory)
                              n))
       nil)
      (mv-nth 2
              (fat32-in-memory-to-m1-fs-helper
               fat32-in-memory
               dir-contents entry-limit))))
    :hints
    (("goal"
      :do-not-induct t
      :expand
      ((len
        (find-n-free-clusters (effective-fat fat32-in-memory)
                              1))
       (len
        (cdr
         (find-n-free-clusters (effective-fat fat32-in-memory)
                               1))))
      :cases
      ((equal
        (list
         (car
          (find-n-free-clusters (effective-fat fat32-in-memory)
                                1)))
        (find-n-free-clusters (effective-fat fat32-in-memory)
                              1))))))))

(defthmd m1-fs-to-fat32-in-memory-inversion-lemma-4
  (not (< (binary-+ '32 (binary-* '32 (len x)))
          '32)))

(defthm m1-fs-to-fat32-in-memory-inversion-lemma-5
  t
  :rule-classes
  ((:rewrite
    :corollary
    (implies (and (m1-file-alist-p m1-file-alist1)
                  (m1-file-no-dups-p m1-file-alist1)
                  (not (m1-file-no-dups-p m1-file-alist2)))
             (not (m1-dir-equiv m1-file-alist1 m1-file-alist2)))
    :hints (("goal" :in-theory (enable m1-dir-equiv))))
   (:rewrite
    :corollary
    (implies (and (m1-file-alist-p m1-file-alist2)
                  (m1-file-no-dups-p m1-file-alist2)
                  (not (m1-file-no-dups-p m1-file-alist1)))
             (not (m1-dir-equiv m1-file-alist1 m1-file-alist2)))
    :hints (("goal" :in-theory (enable m1-dir-equiv))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-6
  (implies (and (stringp (m1-file->contents file))
                (equal (len (explode (m1-file->contents file)))
                       0))
           (equal (m1-file->contents file) ""))
  :hints
  (("goal" :expand (len (explode (m1-file->contents file))))))

(defthmd
  m1-fs-to-fat32-in-memory-inversion-lemma-7
  (implies
   (and (not (zp (cluster-size fat32-in-memory)))
        (dir-ent-p dir-ent))
   (equal
    (mv-nth 2
            (place-contents fat32-in-memory dir-ent
                            contents file-length first-cluster))
    (if
     (equal (length contents) 0)
     0
     (if
      (equal
       (+
        1
        (len (stobj-find-n-free-clusters
              fat32-in-memory
              (+ -1
                 (len (make-clusters contents
                                     (cluster-size fat32-in-memory)))))))
       (len (make-clusters contents
                           (cluster-size fat32-in-memory))))
      0 *enospc*))))
  :hints (("goal" :in-theory (enable place-contents))))

(encapsulate
  ()

  (local
   (defun induction-scheme
     (index-list text cluster-size length)
     (if (or (zp (length text))
             (zp cluster-size))
         (mv index-list length)
         (induction-scheme
          (cdr index-list)
          (subseq text (min cluster-size (length text))
                  nil)
          cluster-size
          (+ length (- cluster-size))))))

  (local
   (defthm
     get-contents-from-clusterchain-of-stobj-set-clusters-coincident-lemma-1
     (iff (equal (+ 1 (len x)) 1)
          (atom x))))

  (defthm
    get-contents-from-clusterchain-of-stobj-set-clusters-coincident
    (implies
     (and (stringp text)
          (equal (len (make-clusters text (cluster-size fat32-in-memory)))
                 (len index-list))
          (integerp length)
          (>= length (length text))
          (lower-bounded-integer-listp index-list *ms-first-data-cluster*)
          (bounded-nat-listp index-list
                             (+ 2 (data-region-length fat32-in-memory)))
          (compliant-fat32-in-memoryp fat32-in-memory)
          (no-duplicatesp-equal index-list))
     (equal
      (get-contents-from-clusterchain
       (stobj-set-clusters (make-clusters text (cluster-size fat32-in-memory))
                           index-list fat32-in-memory)
       index-list length)
      (implode (append (explode text)
                       (make-list (- (min length
                                          (* (len index-list)
                                             (cluster-size fat32-in-memory)))
                                     (length text))
                                  :initial-element (code-char 0))))))
    :hints
    (("goal"
      :induct (induction-scheme index-list
                                text (cluster-size fat32-in-memory)
                                length)
      :in-theory (enable make-clusters
                         lower-bounded-integer-listp
                         nthcdr-when->=-n-len-l)
      :expand
      ((:free
        (fat32-in-memory length)
        (get-contents-from-clusterchain fat32-in-memory index-list length))
       (make-clusters text (cluster-size fat32-in-memory))))
     ("subgoal *1/2"
      :in-theory (e/d (make-clusters lower-bounded-integer-listp
                                     nthcdr-when->=-n-len-l)
                      ((:rewrite associativity-of-append)))
      :use ((:instance (:rewrite associativity-of-append)
                       (c (make-list-ac (+ (cluster-size fat32-in-memory)
                                           (- (len (explode text)))
                                           (* (cluster-size fat32-in-memory)
                                              (len (cdr index-list))))
                                        #\  nil))
                       (b (nthcdr (cluster-size fat32-in-memory)
                                  (explode text)))
                       (a (take (cluster-size fat32-in-memory)
                                (explode text))))
            (:instance (:rewrite associativity-of-append)
                       (c (make-list-ac (+ length (- (len (explode text))))
                                        #\  nil))
                       (b (nthcdr (cluster-size fat32-in-memory)
                                  (explode text)))
                       (a (take (cluster-size fat32-in-memory)
                                (explode text))))
            (:theorem (equal (+ (cluster-size fat32-in-memory)
                                (- (cluster-size fat32-in-memory))
                                (- (len (explode text))))
                             (- (len (explode text)))))))
     ("subgoal *1/1" :expand ((len (explode text))
                              (len index-list))))))

(defthm
  get-contents-from-clusterchain-of-stobj-set-indices-in-fa-table
  (equal
   (get-contents-from-clusterchain
    (stobj-set-indices-in-fa-table
     fat32-in-memory index-list value-list)
    clusterchain file-size)
   (get-contents-from-clusterchain fat32-in-memory
                                   clusterchain file-size)))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top"
                       :dir :system))

  (defthm
    get-clusterchain-contents-of-place-contents-coincident-lemma-1
    (implies (not (zp x))
             (<= (* x
                    (len (find-n-free-clusters fa-table n)))
                 (* x (nfix n))))
    :rule-classes :linear))

(defthm
  get-clusterchain-contents-of-place-contents-coincident
  (implies
   (and
    (equal
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     0)
    (not (zp (length contents)))
    (<= *ms-first-data-cluster* first-cluster)
    (stringp contents)
    (integerp length)
    (<= (length contents) length)
    (compliant-fat32-in-memoryp fat32-in-memory)
    (not
     (equal
      (fat32-entry-mask (fati first-cluster fat32-in-memory))
      0))
    (< first-cluster
       (+ 2 (count-of-clusters fat32-in-memory)))
    (fat32-masked-entry-p first-cluster))
   (equal
    (get-clusterchain-contents
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     first-cluster length)
    (mv
     (implode
      (append
       (explode contents)
       (make-list
        (+
         (min
          length
          (*
           (len (make-clusters contents
                               (cluster-size fat32-in-memory)))
           (cluster-size fat32-in-memory)))
         (- (length contents)))
        :initial-element (code-char 0))))
     0)))
  :hints
  (("goal" :in-theory (e/d (lower-bounded-integer-listp
                            place-contents)
                           ((:rewrite get-clusterchain-contents-correctness-1)
                            (:rewrite
                             fat32-build-index-list-of-set-indices-in-fa-table)
                            (:rewrite get-clusterchain-contents-correctness-3)
                            (:rewrite get-clusterchain-contents-correctness-2)))
    :do-not-induct t
    :use
    ((:instance
      (:rewrite get-clusterchain-contents-correctness-1)
      (length length)
      (masked-current-cluster first-cluster)
      (fat32-in-memory
       (stobj-set-indices-in-fa-table
        (stobj-set-clusters
         (make-clusters contents (cluster-size fat32-in-memory))
         (cons
          first-cluster
          (find-n-free-clusters
           (effective-fat fat32-in-memory)
           (+
            -1
            (len
             (make-clusters contents
                            (cluster-size fat32-in-memory))))))
         fat32-in-memory)
        (cons
         first-cluster
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory))))))
        (append
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory)))))
         '(268435455)))))
     (:instance
      (:rewrite fat32-build-index-list-of-set-indices-in-fa-table)
      (cluster-size (cluster-size fat32-in-memory))
      (file-length length)
      (file-index-list
       (cons
        first-cluster
        (find-n-free-clusters
         (effective-fat fat32-in-memory)
         (+
          -1
          (len (make-clusters contents
                              (cluster-size fat32-in-memory)))))))
      (fa-table (effective-fat fat32-in-memory)))
     (:instance
      (:rewrite get-clusterchain-contents-correctness-3)
      (length length)
      (masked-current-cluster first-cluster)
      (fat32-in-memory
       (stobj-set-indices-in-fa-table
        (stobj-set-clusters
         (make-clusters contents (cluster-size fat32-in-memory))
         (cons
          first-cluster
          (find-n-free-clusters
           (effective-fat fat32-in-memory)
           (+
            -1
            (len
             (make-clusters contents
                            (cluster-size fat32-in-memory))))))
         fat32-in-memory)
        (cons
         first-cluster
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory))))))
        (append
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory)))))
         '(268435455)))))
     (:instance
      (:rewrite get-clusterchain-contents-correctness-2)
      (length length)
      (masked-current-cluster first-cluster)
      (fat32-in-memory
       (stobj-set-indices-in-fa-table
        (stobj-set-clusters
         (make-clusters contents (cluster-size fat32-in-memory))
         (cons
          first-cluster
          (find-n-free-clusters
           (effective-fat fat32-in-memory)
           (+
            -1
            (len
             (make-clusters contents
                            (cluster-size fat32-in-memory))))))
         fat32-in-memory)
        (cons
         first-cluster
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory))))))
        (append
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory)))))
         '(268435455)))))))))

(defthmd
  lemma-1-3
  (implies
   (and
    (consp fs)
    (zp (mv-nth 2
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
    (not (or (equal (car (car fs)) ".          ")
             (equal (car (car fs)) "..         ")))
    (<=
     1
     (len
      (stobj-find-n-free-clusters
       (mv-nth 0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster))
       1)))
    (<
     (nth
      0
      (stobj-find-n-free-clusters
       (mv-nth 0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster))
       1))
     (fat-length fat32-in-memory))
    (m1-regular-file-p (cdr (car fs)))
    (implies
     (and (compliant-fat32-in-memoryp fat32-in-memory)
          (equal (mod 2097152 (cluster-size fat32-in-memory))
                 0)
          (m1-file-alist-p (cdr fs))
          (m1-bounded-file-alist-p (cdr fs))
          (m1-file-no-dups-p (cdr fs))
          (fat32-masked-entry-p current-dir-first-cluster)
          (<= 2 current-dir-first-cluster)
          (< current-dir-first-cluster
             (+ 2 (count-of-clusters fat32-in-memory)))
          (<= (+ 2 (count-of-clusters fat32-in-memory))
              (fat-length fat32-in-memory)))
     (let
         ((mv (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster))
          (fs (cdr fs)))
       (let
           ((fat32-in-memory (mv-nth 0 mv))
            (dir-ent-list (mv-nth 1 mv))
            (error-code (mv-nth 2 mv)))
         (implies
          (zp error-code)
          (and (equal (mv-nth 3
                              (fat32-in-memory-to-m1-fs-helper
                               fat32-in-memory (flatten dir-ent-list)
                               (m1-entry-count fs)))
                      0)
               (m1-dir-equiv (mv-nth 0
                                     (fat32-in-memory-to-m1-fs-helper
                                      fat32-in-memory (flatten dir-ent-list)
                                      (m1-entry-count fs)))
                             fs))))))
    (compliant-fat32-in-memoryp fat32-in-memory)
    (equal (mod 2097152 (cluster-size fat32-in-memory))
           0)
    (m1-file-alist-p fs)
    (m1-bounded-file-alist-p fs)
    (m1-file-no-dups-p fs)
    (fat32-masked-entry-p current-dir-first-cluster)
    (<= 2 current-dir-first-cluster)
    (< current-dir-first-cluster
       (+ 2 (count-of-clusters fat32-in-memory)))
    (<= (+ 2 (count-of-clusters fat32-in-memory))
        (fat-length fat32-in-memory)))
   (mv-let
     (fat32-in-memory dir-ent-list error-code)
     (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                      fs current-dir-first-cluster)
     (or
      (not (zp error-code))
      (and
       (equal
        (mv-nth
         3
         (fat32-in-memory-to-m1-fs-helper fat32-in-memory (flatten dir-ent-list)
                                          (m1-entry-count fs)))
        0)
       (m1-dir-equiv
        (mv-nth
         0
         (fat32-in-memory-to-m1-fs-helper fat32-in-memory (flatten dir-ent-list)
                                          (m1-entry-count fs)))
        fs)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d
                       (m1-fs-to-fat32-in-memory-inversion-lemma-2
                        m1-fs-to-fat32-in-memory-inversion-lemma-4
                        m1-fs-to-fat32-in-memory-inversion-lemma-7)
                       (mod floor nth
                            (:rewrite make-clusters-correctness-1 . 1)
                            (:rewrite by-slice-you-mean-the-whole-cake-2)))
           :expand
           ((:free (fat32-in-memory x y entry-limit)
                   (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                                    (append x y) entry-limit))
            (:free (x y)
                   (intersectp-equal (list x) y))))))

(defthm
  fati-of-place-contents-disjoint
  (implies
   (and (natp x)
        (not (equal x first-cluster))
        (< x
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (integerp first-cluster)
        (>= first-cluster *ms-first-data-cluster*)
        (compliant-fat32-in-memoryp fat32-in-memory)
        (stringp contents)
        (not (equal (fat32-entry-mask (fati x fat32-in-memory))
                    0)))
   (equal
    (fati
     x
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster)))
    (fati x fat32-in-memory)))
  :hints
  (("goal" :in-theory (enable place-contents
                              lower-bounded-integer-listp))))

(defthm
  fati-of-m1-fs-to-fat32-in-memory-helper-disjoint-lemma-1
  (implies
   (and
    (equal
     (len
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs
                                                 current-dir-first-cluster)))
       1))
     1)
    (equal
     (fati
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs
                                                  current-dir-first-cluster)))
        1))
      (mv-nth 0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs
                                               current-dir-first-cluster)))
     (fati
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs
                                                  current-dir-first-cluster)))
        1))
      fat32-in-memory))
    (compliant-fat32-in-memoryp fat32-in-memory))
   (equal
    (fat32-entry-mask
     (fati
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs
                                                  current-dir-first-cluster)))
        1))
      fat32-in-memory))
    0))
  :hints
  (("goal"
    :in-theory (disable nth
                        (:rewrite find-n-free-clusters-correctness-4))
    :use
    (:instance
     (:rewrite find-n-free-clusters-correctness-4)
     (n 1)
     (fa-table
      (effective-fat
       (mv-nth 0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs
                                                current-dir-first-cluster))))
     (x
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs
                                                  current-dir-first-cluster)))
        1)))))))

(defthm
  fati-of-m1-fs-to-fat32-in-memory-helper-disjoint-lemma-2
  (implies
   (and
    (equal
     (len
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs
                                                 current-dir-first-cluster)))
       1))
     1)
    (equal
     (fati
      x
      (mv-nth 0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs
                                               current-dir-first-cluster)))
     (fati x fat32-in-memory))
    (compliant-fat32-in-memoryp fat32-in-memory)
    (not (equal (fat32-entry-mask (fati x fat32-in-memory))
                0)))
   (not
    (equal
     x
     (nth
      '0
      (find-n-free-clusters
       (effective-fat
        (mv-nth '0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs
                                                 current-dir-first-cluster)))
       '1)))))
  :hints
  (("goal"
    :in-theory (e/d ()
                    (nth (:rewrite make-clusters-correctness-1 . 1))))))

(defthm
  fati-of-m1-fs-to-fat32-in-memory-helper-disjoint
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (integerp x)
        (>= x *ms-first-data-cluster*)
        (< x
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (not (equal (fat32-entry-mask (fati x fat32-in-memory))
                    0))
        (equal (mv-nth 2
                       (m1-fs-to-fat32-in-memory-helper
                        fat32-in-memory
                        fs current-dir-first-cluster))
               0))
   (equal (fati x
                (mv-nth 0
                        (m1-fs-to-fat32-in-memory-helper
                         fat32-in-memory
                         fs current-dir-first-cluster)))
          (fati x fat32-in-memory)))
  :hints
  (("goal"
    :in-theory
    (e/d ()
         (nth (:rewrite make-clusters-correctness-1 . 1))))))

(defthmd m1-fs-to-fat32-in-memory-inversion-lemma-8
  (implies
   (m1-file-alist-p fs)
   (iff
    (equal (m1-entry-count fs) 0)
    (equal fs nil))))

(defthm m1-fs-to-fat32-in-memory-inversion-lemma-9
  (implies (atom fs)
           (equal (m1-fs-to-fat32-in-memory-helper
                   fat32-in-memory
                   fs current-dir-first-cluster)
                  (mv fat32-in-memory nil 0 nil))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-10
  (implies
   (zp entry-limit)
   (equal
    (mv-nth
     0
     (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                      dir-contents entry-limit))
    nil)))

(defthm m1-fs-to-fat32-in-memory-inversion-lemma-11
  (implies (dir-ent-p nats)
           (equal (chars=>nats (nats=>chars nats))
                  nats))
  :hints (("goal" :in-theory (enable dir-ent-p))))

(defthmd m1-fs-to-fat32-in-memory-inversion-lemma-12
  (implies (m1-directory-file-p file)
           (m1-file-alist-p (m1-file->contents file))))

(defthmd m1-fs-to-fat32-in-memory-inversion-lemma-13
  (implies (and (m1-file-p fs)
                (not (m1-regular-file-p fs)))
           (m1-directory-file-p fs)))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-14
  (implies
   (and
    (equal
     (mv-nth
      2
      (place-contents
       (mv-nth
        0
        (m1-fs-to-fat32-in-memory-helper
         (update-fati
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth
              0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
            1))
          (fat32-update-lower-28
           (fati
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth
                0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
              1))
            (mv-nth
             0
             (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
           268435455)
          (mv-nth
           0
           (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
         (m1-file->contents (cdr (car fs)))
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth
             0
             (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
           1))))
       (m1-file->dir-ent (cdr (car fs)))
       (nats=>string
        (append
         (dir-ent-install-directory-bit
          (dir-ent-set-filename
           (dir-ent-set-first-cluster-file-size
            (m1-file->dir-ent (cdr (car fs)))
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth
                0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
              1))
            0)
           ".          ")
          t)
         (dir-ent-install-directory-bit
          (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                 (m1-file->dir-ent (cdr (car fs)))
                                 current-dir-first-cluster 0)
                                "..         ")
          t)
         (flatten
          (mv-nth
           1
           (m1-fs-to-fat32-in-memory-helper
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (effective-fat (mv-nth 0
                                        (m1-fs-to-fat32-in-memory-helper
                                         fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
                 1))
               (mv-nth
                0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
              268435455)
             (mv-nth
              0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
            (m1-file->contents (cdr (car fs)))
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth
                0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
              1)))))))
       0
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth
           0
           (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
         1))))
     0)
    (equal
     (mv-nth
      2
      (m1-fs-to-fat32-in-memory-helper
       (update-fati
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth
            0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
          1))
        (fat32-update-lower-28
         (fati
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth
              0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
            1))
          (mv-nth
           0
           (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
         268435455)
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
       (m1-file->contents (cdr (car fs)))
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth
           0
           (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
         1))))
     0)
    (<=
     2
     (nth
      0
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
       1)))
    (consp fs)
    (not (m1-regular-file-p (cdr (car fs))))
    (compliant-fat32-in-memoryp fat32-in-memory)
    (m1-file-alist-p fs)
    (m1-bounded-file-alist-p fs)
    (< current-dir-first-cluster
       (+ 2 (count-of-clusters fat32-in-memory))))
   (equal
    (mv-nth
     1
     (get-clusterchain-contents
      (mv-nth
       0
       (place-contents
        (mv-nth
         0
         (m1-fs-to-fat32-in-memory-helper
          (update-fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               1))
             (mv-nth
              0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
            268435455)
           (mv-nth
            0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
          (m1-file->contents (cdr (car fs)))
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth
              0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
            1))))
        (m1-file->dir-ent (cdr (car fs)))
        (nats=>string
         (append
          (dir-ent-install-directory-bit
           (dir-ent-set-filename
            (dir-ent-set-first-cluster-file-size
             (m1-file->dir-ent (cdr (car fs)))
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               1))
             0)
            ".          ")
           t)
          (dir-ent-install-directory-bit
           (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                  (m1-file->dir-ent (cdr (car fs)))
                                  current-dir-first-cluster 0)
                                 "..         ")
           t)
          (flatten
           (mv-nth
            1
            (m1-fs-to-fat32-in-memory-helper
             (update-fati
              (nth
               0
               (find-n-free-clusters
                (effective-fat (mv-nth 0
                                       (m1-fs-to-fat32-in-memory-helper
                                        fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
                1))
              (fat32-update-lower-28
               (fati
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat (mv-nth 0
                                         (m1-fs-to-fat32-in-memory-helper
                                          fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
                  1))
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               268435455)
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             (m1-file->contents (cdr (car fs)))
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               1)))))))
        0
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth
            0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
          1))))
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
        1))
      2097152))
    0)))

;; (defthm
;;   m1-fs-to-fat32-in-memory-inversion-lemma-15
;;   (implies
;;    (and
;;     (equal
;;      (mv-nth
;;       2
;;       (place-contents
;;        (mv-nth
;;         0
;;         (m1-fs-to-fat32-in-memory-helper
;;          (update-fati
;;           (nth
;;            0
;;            (find-n-free-clusters
;;             (effective-fat
;;              (mv-nth
;;               0
;;               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                current-dir-first-cluster)))
;;             1))
;;           (fat32-update-lower-28
;;            (fati
;;             (nth
;;              0
;;              (find-n-free-clusters
;;               (effective-fat
;;                (mv-nth
;;                 0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;               1))
;;             (mv-nth
;;              0
;;              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                               current-dir-first-cluster)))
;;            268435455)
;;           (mv-nth
;;            0
;;            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                             current-dir-first-cluster)))
;;          (m1-file->contents (cdr (car fs)))
;;          (nth
;;           0
;;           (find-n-free-clusters
;;            (effective-fat
;;             (mv-nth
;;              0
;;              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                               current-dir-first-cluster)))
;;            1))))
;;        (m1-file->dir-ent (cdr (car fs)))
;;        (nats=>string
;;         (append
;;          (dir-ent-install-directory-bit
;;           (dir-ent-set-filename
;;            (dir-ent-set-first-cluster-file-size
;;             (m1-file->dir-ent (cdr (car fs)))
;;             (nth
;;              0
;;              (find-n-free-clusters
;;               (effective-fat
;;                (mv-nth
;;                 0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;               1))
;;             0)
;;            ".          ")
;;           t)
;;          (dir-ent-install-directory-bit
;;           (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
;;                                  (m1-file->dir-ent (cdr (car fs)))
;;                                  current-dir-first-cluster 0)
;;                                 "..         ")
;;           t)
;;          (flatten
;;           (mv-nth
;;            1
;;            (m1-fs-to-fat32-in-memory-helper
;;             (update-fati
;;              (nth
;;               0
;;               (find-n-free-clusters
;;                (effective-fat
;;                 (mv-nth
;;                  0
;;                  (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                   current-dir-first-cluster)))
;;                1))
;;              (fat32-update-lower-28
;;               (fati
;;                (nth
;;                 0
;;                 (find-n-free-clusters
;;                  (effective-fat (mv-nth 0
;;                                         (m1-fs-to-fat32-in-memory-helper
;;                                          fat32-in-memory (cdr fs)
;;                                          current-dir-first-cluster)))
;;                  1))
;;                (mv-nth
;;                 0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;               268435455)
;;              (mv-nth
;;               0
;;               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                current-dir-first-cluster)))
;;             (m1-file->contents (cdr (car fs)))
;;             (nth
;;              0
;;              (find-n-free-clusters
;;               (effective-fat
;;                (mv-nth
;;                 0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;               1)))))))
;;        0
;;        (nth
;;         0
;;         (find-n-free-clusters
;;          (effective-fat
;;           (mv-nth
;;            0
;;            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                             current-dir-first-cluster)))
;;          1))))
;;      0)
;;     (equal
;;      (mv-nth
;;       2
;;       (m1-fs-to-fat32-in-memory-helper
;;        (update-fati
;;         (nth
;;          0
;;          (find-n-free-clusters
;;           (effective-fat
;;            (mv-nth
;;             0
;;             (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                              current-dir-first-cluster)))
;;           1))
;;         (fat32-update-lower-28
;;          (fati
;;           (nth
;;            0
;;            (find-n-free-clusters
;;             (effective-fat
;;              (mv-nth
;;               0
;;               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                current-dir-first-cluster)))
;;             1))
;;           (mv-nth
;;            0
;;            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                             current-dir-first-cluster)))
;;          268435455)
;;         (mv-nth 0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;        (m1-file->contents (cdr (car fs)))
;;        (nth
;;         0
;;         (find-n-free-clusters
;;          (effective-fat
;;           (mv-nth
;;            0
;;            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                             current-dir-first-cluster)))
;;          1))))
;;      0)
;;     (<=
;;      2
;;      (nth
;;       0
;;       (find-n-free-clusters
;;        (effective-fat
;;         (mv-nth 0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;        1)))
;;     (consp fs)
;;     (not (m1-regular-file-p (cdr (car fs))))
;;     (compliant-fat32-in-memoryp fat32-in-memory)
;;     (m1-file-alist-p fs)
;;     (m1-bounded-file-alist-p fs)
;;     (< current-dir-first-cluster
;;        (+ 2 (count-of-clusters fat32-in-memory))))
;;    (equal
;;     (get-clusterchain-contents
;;      (mv-nth
;;       0
;;       (place-contents
;;        (mv-nth
;;         0
;;         (m1-fs-to-fat32-in-memory-helper
;;          (update-fati
;;           (nth
;;            0
;;            (find-n-free-clusters
;;             (effective-fat
;;              (mv-nth
;;               0
;;               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                current-dir-first-cluster)))
;;             1))
;;           (fat32-update-lower-28
;;            (fati
;;             (nth
;;              0
;;              (find-n-free-clusters
;;               (effective-fat
;;                (mv-nth
;;                 0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;               1))
;;             (mv-nth
;;              0
;;              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                               current-dir-first-cluster)))
;;            268435455)
;;           (mv-nth
;;            0
;;            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                             current-dir-first-cluster)))
;;          (m1-file->contents (cdr (car fs)))
;;          (nth
;;           0
;;           (find-n-free-clusters
;;            (effective-fat
;;             (mv-nth
;;              0
;;              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                               current-dir-first-cluster)))
;;            1))))
;;        (m1-file->dir-ent (cdr (car fs)))
;;        (nats=>string
;;         (append
;;          (dir-ent-install-directory-bit
;;           (dir-ent-set-filename
;;            (dir-ent-set-first-cluster-file-size
;;             (m1-file->dir-ent (cdr (car fs)))
;;             (nth
;;              0
;;              (find-n-free-clusters
;;               (effective-fat
;;                (mv-nth
;;                 0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;               1))
;;             0)
;;            ".          ")
;;           t)
;;          (dir-ent-install-directory-bit
;;           (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
;;                                  (m1-file->dir-ent (cdr (car fs)))
;;                                  current-dir-first-cluster 0)
;;                                 "..         ")
;;           t)
;;          (flatten
;;           (mv-nth
;;            1
;;            (m1-fs-to-fat32-in-memory-helper
;;             (update-fati
;;              (nth
;;               0
;;               (find-n-free-clusters
;;                (effective-fat
;;                 (mv-nth
;;                  0
;;                  (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                   current-dir-first-cluster)))
;;                1))
;;              (fat32-update-lower-28
;;               (fati
;;                (nth
;;                 0
;;                 (find-n-free-clusters
;;                  (effective-fat (mv-nth 0
;;                                         (m1-fs-to-fat32-in-memory-helper
;;                                          fat32-in-memory (cdr fs)
;;                                          current-dir-first-cluster)))
;;                  1))
;;                (mv-nth
;;                 0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;               268435455)
;;              (mv-nth
;;               0
;;               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                current-dir-first-cluster)))
;;             (m1-file->contents (cdr (car fs)))
;;             (nth
;;              0
;;              (find-n-free-clusters
;;               (effective-fat
;;                (mv-nth
;;                 0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;               1)))))))
;;        0
;;        (nth
;;         0
;;         (find-n-free-clusters
;;          (effective-fat
;;           (mv-nth
;;            0
;;            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                             current-dir-first-cluster)))
;;          1))))
;;      (nth
;;       0
;;       (find-n-free-clusters
;;        (effective-fat
;;         (mv-nth 0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;        1))
;;      2097152)
;;     (cons
;;      (implode
;;       (append
;;        (explode
;;         (nats=>string
;;          (append
;;           (dir-ent-install-directory-bit
;;            (dir-ent-set-filename
;;             (dir-ent-set-first-cluster-file-size
;;              (m1-file->dir-ent (cdr (car fs)))
;;              (nth
;;               0
;;               (find-n-free-clusters
;;                (effective-fat
;;                 (mv-nth
;;                  0
;;                  (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                   current-dir-first-cluster)))
;;                1))
;;              0)
;;             ".          ")
;;            t)
;;           (dir-ent-install-directory-bit
;;            (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
;;                                   (m1-file->dir-ent (cdr (car fs)))
;;                                   current-dir-first-cluster 0)
;;                                  "..         ")
;;            t)
;;           (flatten
;;            (mv-nth
;;             1
;;             (m1-fs-to-fat32-in-memory-helper
;;              (update-fati
;;               (nth
;;                0
;;                (find-n-free-clusters
;;                 (effective-fat (mv-nth 0
;;                                        (m1-fs-to-fat32-in-memory-helper
;;                                         fat32-in-memory (cdr fs)
;;                                         current-dir-first-cluster)))
;;                 1))
;;               (fat32-update-lower-28
;;                (fati
;;                 (nth
;;                  0
;;                  (find-n-free-clusters
;;                   (effective-fat (mv-nth 0
;;                                          (m1-fs-to-fat32-in-memory-helper
;;                                           fat32-in-memory (cdr fs)
;;                                           current-dir-first-cluster)))
;;                   1))
;;                 (mv-nth
;;                  0
;;                  (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                   current-dir-first-cluster)))
;;                268435455)
;;               (mv-nth
;;                0
;;                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                 current-dir-first-cluster)))
;;              (m1-file->contents (cdr (car fs)))
;;              (nth
;;               0
;;               (find-n-free-clusters
;;                (effective-fat
;;                 (mv-nth
;;                  0
;;                  (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                   current-dir-first-cluster)))
;;                1))))))))
;;        (make-list-ac
;;         (+
;;          (min
;;           2097152
;;           (*
;;            (len
;;             (make-clusters
;;              (nats=>string
;;               (append
;;                (dir-ent-install-directory-bit
;;                 (dir-ent-set-filename
;;                  (dir-ent-set-first-cluster-file-size
;;                   (m1-file->dir-ent (cdr (car fs)))
;;                   (nth
;;                    0
;;                    (find-n-free-clusters
;;                     (effective-fat (mv-nth 0
;;                                            (m1-fs-to-fat32-in-memory-helper
;;                                             fat32-in-memory (cdr fs)
;;                                             current-dir-first-cluster)))
;;                     1))
;;                   0)
;;                  ".          ")
;;                 t)
;;                (dir-ent-install-directory-bit
;;                 (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
;;                                        (m1-file->dir-ent (cdr (car fs)))
;;                                        current-dir-first-cluster 0)
;;                                       "..         ")
;;                 t)
;;                (flatten
;;                 (mv-nth
;;                  1
;;                  (m1-fs-to-fat32-in-memory-helper
;;                   (update-fati
;;                    (nth
;;                     0
;;                     (find-n-free-clusters
;;                      (effective-fat (mv-nth 0
;;                                             (m1-fs-to-fat32-in-memory-helper
;;                                              fat32-in-memory (cdr fs)
;;                                              current-dir-first-cluster)))
;;                      1))
;;                    (fat32-update-lower-28
;;                     (fati
;;                      (nth 0
;;                           (find-n-free-clusters
;;                            (effective-fat
;;                             (mv-nth 0
;;                                     (m1-fs-to-fat32-in-memory-helper
;;                                      fat32-in-memory (cdr fs)
;;                                      current-dir-first-cluster)))
;;                            1))
;;                      (mv-nth 0
;;                              (m1-fs-to-fat32-in-memory-helper
;;                               fat32-in-memory (cdr fs)
;;                               current-dir-first-cluster)))
;;                     268435455)
;;                    (mv-nth 0
;;                            (m1-fs-to-fat32-in-memory-helper
;;                             fat32-in-memory (cdr fs)
;;                             current-dir-first-cluster)))
;;                   (m1-file->contents (cdr (car fs)))
;;                   (nth
;;                    0
;;                    (find-n-free-clusters
;;                     (effective-fat (mv-nth 0
;;                                            (m1-fs-to-fat32-in-memory-helper
;;                                             fat32-in-memory (cdr fs)
;;                                             current-dir-first-cluster)))
;;                     1)))))))
;;              (cluster-size
;;               (mv-nth
;;                0
;;                (m1-fs-to-fat32-in-memory-helper
;;                 (update-fati
;;                  (nth
;;                   0
;;                   (find-n-free-clusters
;;                    (effective-fat (mv-nth 0
;;                                           (m1-fs-to-fat32-in-memory-helper
;;                                            fat32-in-memory (cdr fs)
;;                                            current-dir-first-cluster)))
;;                    1))
;;                  (fat32-update-lower-28
;;                   (fati
;;                    (nth
;;                     0
;;                     (find-n-free-clusters
;;                      (effective-fat (mv-nth 0
;;                                             (m1-fs-to-fat32-in-memory-helper
;;                                              fat32-in-memory (cdr fs)
;;                                              current-dir-first-cluster)))
;;                      1))
;;                    (mv-nth 0
;;                            (m1-fs-to-fat32-in-memory-helper
;;                             fat32-in-memory (cdr fs)
;;                             current-dir-first-cluster)))
;;                   268435455)
;;                  (mv-nth 0
;;                          (m1-fs-to-fat32-in-memory-helper
;;                           fat32-in-memory (cdr fs)
;;                           current-dir-first-cluster)))
;;                 (m1-file->contents (cdr (car fs)))
;;                 (nth
;;                  0
;;                  (find-n-free-clusters
;;                   (effective-fat (mv-nth 0
;;                                          (m1-fs-to-fat32-in-memory-helper
;;                                           fat32-in-memory (cdr fs)
;;                                           current-dir-first-cluster)))
;;                   1)))))))
;;            (cluster-size
;;             (mv-nth
;;              0
;;              (m1-fs-to-fat32-in-memory-helper
;;               (update-fati
;;                (nth
;;                 0
;;                 (find-n-free-clusters
;;                  (effective-fat (mv-nth 0
;;                                         (m1-fs-to-fat32-in-memory-helper
;;                                          fat32-in-memory (cdr fs)
;;                                          current-dir-first-cluster)))
;;                  1))
;;                (fat32-update-lower-28
;;                 (fati
;;                  (nth
;;                   0
;;                   (find-n-free-clusters
;;                    (effective-fat (mv-nth 0
;;                                           (m1-fs-to-fat32-in-memory-helper
;;                                            fat32-in-memory (cdr fs)
;;                                            current-dir-first-cluster)))
;;                    1))
;;                  (mv-nth 0
;;                          (m1-fs-to-fat32-in-memory-helper
;;                           fat32-in-memory (cdr fs)
;;                           current-dir-first-cluster)))
;;                 268435455)
;;                (mv-nth
;;                 0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;               (m1-file->contents (cdr (car fs)))
;;               (nth
;;                0
;;                (find-n-free-clusters
;;                 (effective-fat (mv-nth 0
;;                                        (m1-fs-to-fat32-in-memory-helper
;;                                         fat32-in-memory (cdr fs)
;;                                         current-dir-first-cluster)))
;;                 1)))))))
;;          (-
;;           (length
;;            (nats=>string
;;             (append
;;              (dir-ent-install-directory-bit
;;               (dir-ent-set-filename
;;                (dir-ent-set-first-cluster-file-size
;;                 (m1-file->dir-ent (cdr (car fs)))
;;                 (nth
;;                  0
;;                  (find-n-free-clusters
;;                   (effective-fat (mv-nth 0
;;                                          (m1-fs-to-fat32-in-memory-helper
;;                                           fat32-in-memory (cdr fs)
;;                                           current-dir-first-cluster)))
;;                   1))
;;                 0)
;;                ".          ")
;;               t)
;;              (dir-ent-install-directory-bit
;;               (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
;;                                      (m1-file->dir-ent (cdr (car fs)))
;;                                      current-dir-first-cluster 0)
;;                                     "..         ")
;;               t)
;;              (flatten
;;               (mv-nth
;;                1
;;                (m1-fs-to-fat32-in-memory-helper
;;                 (update-fati
;;                  (nth
;;                   0
;;                   (find-n-free-clusters
;;                    (effective-fat (mv-nth 0
;;                                           (m1-fs-to-fat32-in-memory-helper
;;                                            fat32-in-memory (cdr fs)
;;                                            current-dir-first-cluster)))
;;                    1))
;;                  (fat32-update-lower-28
;;                   (fati
;;                    (nth
;;                     0
;;                     (find-n-free-clusters
;;                      (effective-fat (mv-nth 0
;;                                             (m1-fs-to-fat32-in-memory-helper
;;                                              fat32-in-memory (cdr fs)
;;                                              current-dir-first-cluster)))
;;                      1))
;;                    (mv-nth 0
;;                            (m1-fs-to-fat32-in-memory-helper
;;                             fat32-in-memory (cdr fs)
;;                             current-dir-first-cluster)))
;;                   268435455)
;;                  (mv-nth 0
;;                          (m1-fs-to-fat32-in-memory-helper
;;                           fat32-in-memory (cdr fs)
;;                           current-dir-first-cluster)))
;;                 (m1-file->contents (cdr (car fs)))
;;                 (nth
;;                  0
;;                  (find-n-free-clusters
;;                   (effective-fat (mv-nth 0
;;                                          (m1-fs-to-fat32-in-memory-helper
;;                                           fat32-in-memory (cdr fs)
;;                                           current-dir-first-cluster)))
;;                   1))))))))))
;;         #\  nil)))
;;      '(0)))))

;; (defthm
;;   m1-fs-to-fat32-in-memory-inversion-lemma-15
;;   (implies
;;    (and
;;     (equal
;;      (mv-nth
;;       2
;;       (m1-fs-to-fat32-in-memory-helper
;;        (update-fati
;;         (nth
;;          0
;;          (find-n-free-clusters
;;           (effective-fat
;;            (mv-nth
;;             0
;;             (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                              current-dir-first-cluster)))
;;           1))
;;         (fat32-update-lower-28
;;          (fati
;;           (nth
;;            0
;;            (find-n-free-clusters
;;             (effective-fat
;;              (mv-nth
;;               0
;;               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                current-dir-first-cluster)))
;;             1))
;;           (mv-nth
;;            0
;;            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                             current-dir-first-cluster)))
;;          268435455)
;;         (mv-nth 0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;        (m1-file->contents (cdr (car fs)))
;;        (nth
;;         0
;;         (find-n-free-clusters
;;          (effective-fat
;;           (mv-nth
;;            0
;;            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                             current-dir-first-cluster)))
;;          1))))
;;      0)
;;     (consp fs)
;;     (not (m1-regular-file-p (cdr (car fs))))
;;     (m1-file-alist-p fs))
;;    (equal
;;     (len
;;      (mv-nth
;;       '1
;;       (m1-fs-to-fat32-in-memory-helper
;;        (update-fati
;;         (nth
;;          '0
;;          (find-n-free-clusters
;;           (effective-fat
;;            (mv-nth
;;             '0
;;             (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                              current-dir-first-cluster)))
;;           '1))
;;         (fat32-update-lower-28
;;          (fati
;;           (nth
;;            '0
;;            (find-n-free-clusters
;;             (effective-fat
;;              (mv-nth
;;               '0
;;               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                current-dir-first-cluster)))
;;             '1))
;;           (mv-nth
;;            '0
;;            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                             current-dir-first-cluster)))
;;          '268435455)
;;         (mv-nth '0
;;                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                                  current-dir-first-cluster)))
;;        (m1-file->contents$inline (cdr (car fs)))
;;        (nth
;;         '0
;;         (find-n-free-clusters
;;          (effective-fat
;;           (mv-nth
;;            '0
;;            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
;;                                             current-dir-first-cluster)))
;;          '1)))))
;;     (len (m1-file->contents (cdr (car fs)))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-15
  (implies
   (<
    (+
     (m1-entry-count (cdr fs))
     (m1-entry-count (m1-file->contents (cdr (car fs))))
     (-
      (m1-entry-count
       (mv-nth
        0
        (fat32-in-memory-to-m1-fs-helper
         (mv-nth
          0
          (place-contents
           (mv-nth
            0
            (m1-fs-to-fat32-in-memory-helper
             (update-fati
              (nth
               0
               (find-n-free-clusters
                (effective-fat (mv-nth 0
                                       (m1-fs-to-fat32-in-memory-helper
                                        fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
                1))
              (fat32-update-lower-28
               (fati
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat (mv-nth 0
                                         (m1-fs-to-fat32-in-memory-helper
                                          fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
                  1))
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               268435455)
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             (m1-file->contents (cdr (car fs)))
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               1))))
           (m1-file->dir-ent (cdr (car fs)))
           (nats=>string
            (append
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size
                (m1-file->dir-ent (cdr (car fs)))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat (mv-nth 0
                                         (m1-fs-to-fat32-in-memory-helper
                                          fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
                  1))
                0)
               ".          ")
              t)
             (dir-ent-install-directory-bit
              (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                     (m1-file->dir-ent (cdr (car fs)))
                                     current-dir-first-cluster 0)
                                    "..         ")
              t)
             (flatten
              (mv-nth
               1
               (m1-fs-to-fat32-in-memory-helper
                (update-fati
                 (nth
                  0
                  (find-n-free-clusters
                   (effective-fat (mv-nth 0
                                          (m1-fs-to-fat32-in-memory-helper
                                           fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
                   1))
                 (fat32-update-lower-28
                  (fati
                   (nth
                    0
                    (find-n-free-clusters
                     (effective-fat (mv-nth 0
                                            (m1-fs-to-fat32-in-memory-helper
                                             fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
                     1))
                   (mv-nth 0
                           (m1-fs-to-fat32-in-memory-helper
                            fat32-in-memory (cdr fs)
                            current-dir-first-cluster)))
                  268435455)
                 (mv-nth 0
                         (m1-fs-to-fat32-in-memory-helper
                          fat32-in-memory (cdr fs)
                          current-dir-first-cluster)))
                (m1-file->contents (cdr (car fs)))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat (mv-nth 0
                                         (m1-fs-to-fat32-in-memory-helper
                                          fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
                  1)))))))
           0
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             1))))
         nil
         (+ (m1-entry-count (cdr fs))
            (m1-entry-count (m1-file->contents (cdr (car fs))))))))))
    0)
   (equal
    (flatten
     (mv-nth
      '1
      (m1-fs-to-fat32-in-memory-helper
       (update-fati
        (nth
         '0
         (find-n-free-clusters
          (effective-fat
           (mv-nth
            '0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
          '1))
        (fat32-update-lower-28
         (fati
          (nth
           '0
           (find-n-free-clusters
            (effective-fat
             (mv-nth
              '0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
            '1))
          (mv-nth
           '0
           (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
         '268435455)
        (mv-nth '0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
       (m1-file->contents$inline (cdr (car fs)))
       (nth
        '0
        (find-n-free-clusters
         (effective-fat
          (mv-nth
           '0
           (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
         '1)))))
    nil)))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-16
  (implies
   (<
    (+
     (m1-entry-count (cdr fs))
     (m1-entry-count (m1-file->contents (cdr (car fs))))
     (-
      (m1-entry-count
       (mv-nth
        0
        (fat32-in-memory-to-m1-fs-helper
         (mv-nth
          0
          (place-contents
           (mv-nth
            0
            (m1-fs-to-fat32-in-memory-helper
             (update-fati
              (nth
               0
               (find-n-free-clusters
                (effective-fat (mv-nth 0
                                       (m1-fs-to-fat32-in-memory-helper
                                        fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
                1))
              (fat32-update-lower-28
               (fati
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat (mv-nth 0
                                         (m1-fs-to-fat32-in-memory-helper
                                          fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
                  1))
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               268435455)
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             (m1-file->contents (cdr (car fs)))
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               1))))
           (m1-file->dir-ent (cdr (car fs)))
           (nats=>string
            (append
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size
                (m1-file->dir-ent (cdr (car fs)))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat (mv-nth 0
                                         (m1-fs-to-fat32-in-memory-helper
                                          fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
                  1))
                0)
               ".          ")
              t)
             (dir-ent-install-directory-bit
              (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                     (m1-file->dir-ent (cdr (car fs)))
                                     current-dir-first-cluster 0)
                                    "..         ")
              t)
             (flatten
              (mv-nth
               1
               (m1-fs-to-fat32-in-memory-helper
                (update-fati
                 (nth
                  0
                  (find-n-free-clusters
                   (effective-fat (mv-nth 0
                                          (m1-fs-to-fat32-in-memory-helper
                                           fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
                   1))
                 (fat32-update-lower-28
                  (fati
                   (nth
                    0
                    (find-n-free-clusters
                     (effective-fat (mv-nth 0
                                            (m1-fs-to-fat32-in-memory-helper
                                             fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
                     1))
                   (mv-nth 0
                           (m1-fs-to-fat32-in-memory-helper
                            fat32-in-memory (cdr fs)
                            current-dir-first-cluster)))
                  268435455)
                 (mv-nth 0
                         (m1-fs-to-fat32-in-memory-helper
                          fat32-in-memory (cdr fs)
                          current-dir-first-cluster)))
                (m1-file->contents (cdr (car fs)))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat (mv-nth 0
                                         (m1-fs-to-fat32-in-memory-helper
                                          fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
                  1)))))))
           0
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             1))))
         nil
         (+ (m1-entry-count (cdr fs))
            (m1-entry-count (m1-file->contents (cdr (car fs))))))))))
    0)
   (equal (m1-entry-count (cdr fs)) 0)))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-17
  (implies
   (<
    (+
     (m1-entry-count (m1-file->contents (cdr (car fs))))
     (-
      (m1-entry-count
       (mv-nth
        0
        (fat32-in-memory-to-m1-fs-helper
         (mv-nth
          0
          (place-contents
           (mv-nth
            0
            (m1-fs-to-fat32-in-memory-helper
             (update-fati
              (nth 0
                   (find-n-free-clusters (effective-fat fat32-in-memory)
                                         1))
              (fat32-update-lower-28
               (fati
                (nth 0
                     (find-n-free-clusters (effective-fat fat32-in-memory)
                                           1))
                fat32-in-memory)
               268435455)
              fat32-in-memory)
             (m1-file->contents (cdr (car fs)))
             (nth 0
                  (find-n-free-clusters (effective-fat fat32-in-memory)
                                        1))))
           (m1-file->dir-ent (cdr (car fs)))
           (nats=>string
            (append
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size
                (m1-file->dir-ent (cdr (car fs)))
                (nth 0
                     (find-n-free-clusters (effective-fat fat32-in-memory)
                                           1))
                0)
               ".          ")
              t)
             (dir-ent-install-directory-bit
              (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                     (m1-file->dir-ent (cdr (car fs)))
                                     current-dir-first-cluster 0)
                                    "..         ")
              t)
             (flatten
              (mv-nth
               1
               (m1-fs-to-fat32-in-memory-helper
                (update-fati
                 (nth 0
                      (find-n-free-clusters (effective-fat fat32-in-memory)
                                            1))
                 (fat32-update-lower-28
                  (fati
                   (nth 0
                        (find-n-free-clusters (effective-fat fat32-in-memory)
                                              1))
                   fat32-in-memory)
                  268435455)
                 fat32-in-memory)
                (m1-file->contents (cdr (car fs)))
                (nth 0
                     (find-n-free-clusters (effective-fat fat32-in-memory)
                                           1)))))))
           0
           (nth 0
                (find-n-free-clusters (effective-fat fat32-in-memory)
                                      1))))
         nil
         (m1-entry-count (m1-file->contents (cdr (car fs)))))))))
    0)
   (equal
    (flatten
     (mv-nth
      '1
      (m1-fs-to-fat32-in-memory-helper
       (update-fati
        (nth '0
             (find-n-free-clusters (effective-fat fat32-in-memory)
                                   '1))
        (fat32-update-lower-28
         (fati (nth '0
                    (find-n-free-clusters (effective-fat fat32-in-memory)
                                          '1))
               fat32-in-memory)
         '268435455)
        fat32-in-memory)
       (m1-file->contents$inline (cdr (car fs)))
       (nth '0
            (find-n-free-clusters (effective-fat fat32-in-memory)
                                  '1)))))
    nil)))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-18
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (< current-dir-first-cluster
           (+ 2 (count-of-clusters fat32-in-memory))))
   (<
    (nth
     0
     (find-n-free-clusters
      (effective-fat
       (mv-nth 0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
      1))
    (+ 2
       (count-of-clusters fat32-in-memory)))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-19
  (implies
   (and
    (<
     (nth
      0
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
       1))
     (fat-length fat32-in-memory))
    (compliant-fat32-in-memoryp fat32-in-memory))
   (fat32-entry-p
    (fat32-update-lower-28
     (fati
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
        1))
      (mv-nth 0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
     268435455))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-20
  (implies
   (and
    (equal
     (len
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
       1))
     1)
    (equal
     (mv-nth 2
             (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster))
     0)
    (compliant-fat32-in-memoryp fat32-in-memory))
   (not
    (<
     (nth
      '0
      (find-n-free-clusters
       (effective-fat
        (mv-nth
         '0
         (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr (cdr fs))
                                          current-dir-first-cluster)))
       '1))
     '2))))

(defthmd
  m1-fs-to-fat32-in-memory-inversion-lemma-21
  (implies
   (and (not (zp (cluster-size fat32-in-memory)))
        (dir-ent-p dir-ent))
   (equal
    (mv-nth 2
            (place-contents fat32-in-memory dir-ent
                            contents file-length first-cluster))
    (if
     (equal (length contents) 0)
     0
     (if
      (equal
       (+
        1
        (len
         (stobj-find-n-free-clusters
          fat32-in-memory
          (+
           -1
           (len
            (make-clusters contents
                           (cluster-size fat32-in-memory)))))))
       (len (make-clusters contents
                           (cluster-size fat32-in-memory))))
      0 *enospc*))))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  fat32-build-index-list-of-place-contents-coincident
  (implies
   (and
    (equal
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     0)
    (not (zp (length contents)))
    (<= *ms-first-data-cluster* first-cluster)
    (stringp contents)
    (integerp length)
    (<= (length contents) length)
    (compliant-fat32-in-memoryp fat32-in-memory)
    (not
     (equal
      (fat32-entry-mask (fati first-cluster fat32-in-memory))
      0))
    (< first-cluster
       (+ 2 (count-of-clusters fat32-in-memory)))
    (fat32-masked-entry-p first-cluster)
    (equal cluster-size
           (cluster-size fat32-in-memory)))
   (equal
    (fat32-build-index-list
     (effective-fat
      (mv-nth
       0
       (place-contents fat32-in-memory dir-ent
                       contents file-length first-cluster)))
     first-cluster length cluster-size)
    (mv
     (cons
      first-cluster
      (find-n-free-clusters
       (effective-fat fat32-in-memory)
       (+
        -1
        (len (make-clusters contents
                            (cluster-size fat32-in-memory))))))
     0)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lower-bounded-integer-listp place-contents)
     ((:rewrite
       fat32-build-index-list-of-set-indices-in-fa-table)))
    :do-not-induct t
    :use
    ((:instance
      (:rewrite
       fat32-build-index-list-of-set-indices-in-fa-table)
      (cluster-size (cluster-size fat32-in-memory))
      (file-length length)
      (file-index-list
       (cons
        first-cluster
        (find-n-free-clusters
         (effective-fat fat32-in-memory)
         (+
          -1
          (len
           (make-clusters contents
                          (cluster-size fat32-in-memory)))))))
      (fa-table (effective-fat fat32-in-memory)))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-22
  (implies
   (and (m1-file-alist-p fs)
        (compliant-fat32-in-memoryp fat32-in-memory)
        (equal (mv-nth 2
                       (m1-fs-to-fat32-in-memory-helper
                        fat32-in-memory
                        fs current-dir-first-cluster))
               0)
        (consp fs))
   (equal (mv-nth 2
                  (m1-fs-to-fat32-in-memory-helper
                   fat32-in-memory (cdr fs)
                   current-dir-first-cluster))
          0))
  :hints (("goal" :do-not-induct t
           :expand (m1-fs-to-fat32-in-memory-helper
                    fat32-in-memory
                    fs current-dir-first-cluster))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-23
  (implies
   (and (m1-file-alist-p fs)
        (compliant-fat32-in-memoryp fat32-in-memory)
        (equal (mv-nth 2
                       (m1-fs-to-fat32-in-memory-helper
                        fat32-in-memory
                        fs current-dir-first-cluster))
               0)
        (consp fs)
        (not (m1-regular-file-p (cdr (car fs)))))
   (equal
    (mv-nth
     2
     (m1-fs-to-fat32-in-memory-helper
      (update-fati
       (nth 0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (m1-fs-to-fat32-in-memory-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
       (fat32-update-lower-28
        (fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (m1-fs-to-fat32-in-memory-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         (mv-nth 0
                 (m1-fs-to-fat32-in-memory-helper
                  fat32-in-memory (cdr fs)
                  current-dir-first-cluster)))
        268435455)
       (mv-nth 0
               (m1-fs-to-fat32-in-memory-helper
                fat32-in-memory (cdr fs)
                current-dir-first-cluster)))
      (m1-file->contents (cdr (car fs)))
      (nth 0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (m1-fs-to-fat32-in-memory-helper
                      fat32-in-memory (cdr fs)
                      current-dir-first-cluster)))
            1))))
    0))
  :hints (("goal" :do-not-induct t
           :expand (m1-fs-to-fat32-in-memory-helper
                    fat32-in-memory
                    fs current-dir-first-cluster))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-24
  (equal (fat32-in-memory-to-m1-fs-helper fat32-in-memory nil 0)
         (mv nil 0 nil 0))
  :hints (("goal" :in-theory (disable nth floor mod))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-25
  (implies
   (and
    (equal
     (len
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
       1))
     0)
    (consp fs)
    (compliant-fat32-in-memoryp fat32-in-memory)
    (m1-file-alist-p fs))
   (not
    (equal
     (mv-nth 2
             (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                              fs current-dir-first-cluster))
     0))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-26
  (implies
   (and
    (equal
     (len
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
       1))
     1)
    (equal
     (mv-nth
      2
      (place-contents
       (update-fati
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth
            0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
          1))
        (fat32-update-lower-28
         (fati
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth
              0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
            1))
          (mv-nth
           0
           (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
         268435455)
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
       (m1-file->dir-ent (cdr (car fs)))
       (m1-file->contents (cdr (car fs)))
       (len (explode (m1-file->contents (cdr (car fs)))))
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth
           0
           (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
         1))))
     0)
    (m1-regular-file-p (cdr (car fs)))
    (compliant-fat32-in-memoryp fat32-in-memory)
    (not (equal (len (explode (m1-file->contents (cdr (car fs)))))
                0)))
   (equal
    (+
     1
     (len
      (find-n-free-clusters
       (update-nth
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth
            0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
          1))
        (fat32-update-lower-28
         (fati
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth
              0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
            1))
          (mv-nth
           0
           (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
         268435455)
        (effective-fat
         (mv-nth
          0
          (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster))))
       (+ -1
          (len (make-clusters (m1-file->contents (cdr (car fs)))
                              (cluster-size fat32-in-memory)))))))
    (len (make-clusters (m1-file->contents (cdr (car fs)))
                        (cluster-size fat32-in-memory)))))
  :hints (("goal" :in-theory (e/d (place-contents)
                                  (nth floor mod)))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-27
  (implies
   (and
    (equal
     (mv-nth 2
             (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                              fs current-dir-first-cluster))
     0)
    (m1-regular-file-p (cdr (car fs)))
    (equal
     (mv-nth
      3
      (fat32-in-memory-to-m1-fs-helper
       (mv-nth 0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster))
       (flatten
        (mv-nth 1
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
       (m1-entry-count (cdr fs))))
     0)
    (compliant-fat32-in-memoryp fat32-in-memory)
    (m1-file-alist-p fs))
   (equal
    (mv-nth
     3
     (fat32-in-memory-to-m1-fs-helper
      (mv-nth 0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                               fs current-dir-first-cluster))
      (flatten
       (mv-nth
        1
        (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                         fs current-dir-first-cluster)))
      (+ 1 (m1-entry-count (cdr fs)))))
    0))
  :hints (("goal" :in-theory (e/d (m1-fs-to-fat32-in-memory-inversion-lemma-2)
                                  (nth floor mod))
           :do-not-induct t)))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-28
  (implies
   (and
    (equal
     (mv-nth 2
             (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster))
     0)
    (equal
     (mv-nth
      2
      (place-contents
       (mv-nth
        0
        (m1-fs-to-fat32-in-memory-helper
         (update-fati
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth
              0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
            1))
          (fat32-update-lower-28
           (fati
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth
                0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
              1))
            (mv-nth
             0
             (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
           268435455)
          (mv-nth
           0
           (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
         (m1-file->contents (cdr (car fs)))
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth
             0
             (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
           1))))
       (m1-file->dir-ent (cdr (car fs)))
       (nats=>string
        (append
         (dir-ent-install-directory-bit
          (dir-ent-set-filename
           (dir-ent-set-first-cluster-file-size
            (m1-file->dir-ent (cdr (car fs)))
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth
                0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
              1))
            0)
           ".          ")
          t)
         (dir-ent-install-directory-bit
          (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                 (m1-file->dir-ent (cdr (car fs)))
                                 current-dir-first-cluster 0)
                                "..         ")
          t)
         (flatten
          (mv-nth
           1
           (m1-fs-to-fat32-in-memory-helper
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (effective-fat (mv-nth 0
                                        (m1-fs-to-fat32-in-memory-helper
                                         fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
                 1))
               (mv-nth
                0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
              268435455)
             (mv-nth
              0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
            (m1-file->contents (cdr (car fs)))
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth
                0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
              1)))))))
       0
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth
           0
           (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
         1))))
     0)
    (<
     (nth
      0
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
       1))
     (fat-length fat32-in-memory))
    (not (m1-regular-file-p (cdr (car fs))))
    (compliant-fat32-in-memoryp fat32-in-memory))
   (equal
    (+
     1
     (len
      (find-n-free-clusters
       (effective-fat
        (mv-nth
         0
         (m1-fs-to-fat32-in-memory-helper
          (update-fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               1))
             (mv-nth
              0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
            268435455)
           (mv-nth
            0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
          (m1-file->contents (cdr (car fs)))
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth
              0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
            1)))))
       (+
        -1
        (len
         (make-clusters
          (nats=>string
           (append
            (dir-ent-install-directory-bit
             (dir-ent-set-filename
              (dir-ent-set-first-cluster-file-size
               (m1-file->dir-ent (cdr (car fs)))
               (nth
                0
                (find-n-free-clusters
                 (effective-fat (mv-nth 0
                                        (m1-fs-to-fat32-in-memory-helper
                                         fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
                 1))
               0)
              ".          ")
             t)
            (dir-ent-install-directory-bit
             (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                    (m1-file->dir-ent (cdr (car fs)))
                                    current-dir-first-cluster 0)
                                   "..         ")
             t)
            (flatten
             (mv-nth
              1
              (m1-fs-to-fat32-in-memory-helper
               (update-fati
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat (mv-nth 0
                                         (m1-fs-to-fat32-in-memory-helper
                                          fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
                  1))
                (fat32-update-lower-28
                 (fati
                  (nth
                   0
                   (find-n-free-clusters
                    (effective-fat (mv-nth 0
                                           (m1-fs-to-fat32-in-memory-helper
                                            fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
                    1))
                  (mv-nth 0
                          (m1-fs-to-fat32-in-memory-helper
                           fat32-in-memory (cdr fs)
                           current-dir-first-cluster)))
                 268435455)
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               (m1-file->contents (cdr (car fs)))
               (nth
                0
                (find-n-free-clusters
                 (effective-fat (mv-nth 0
                                        (m1-fs-to-fat32-in-memory-helper
                                         fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
                 1)))))))
          (cluster-size fat32-in-memory)))))))
    (len
     (make-clusters
      (nats=>string
       (append
        (dir-ent-install-directory-bit
         (dir-ent-set-filename
          (dir-ent-set-first-cluster-file-size
           (m1-file->dir-ent (cdr (car fs)))
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             1))
           0)
          ".          ")
         t)
        (dir-ent-install-directory-bit
         (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                (m1-file->dir-ent (cdr (car fs)))
                                current-dir-first-cluster 0)
                               "..         ")
         t)
        (flatten
         (mv-nth
          1
          (m1-fs-to-fat32-in-memory-helper
           (update-fati
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth
                0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
              1))
            (fat32-update-lower-28
             (fati
              (nth
               0
               (find-n-free-clusters
                (effective-fat (mv-nth 0
                                       (m1-fs-to-fat32-in-memory-helper
                                        fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
                1))
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             268435455)
            (mv-nth
             0
             (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
           (m1-file->contents (cdr (car fs)))
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             1)))))))
      (cluster-size fat32-in-memory)))))
  :hints (("goal" :in-theory (e/d (place-contents)
                                  (nth floor mod)))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-29
  (implies
   (and (dir-ent-p dir-ent)
        (not (zp entry-limit))
        (not (equal (nth 0 dir-ent) 0))
        (not (useless-dir-ent-p dir-ent))
        (dir-ent-directory-p dir-ent)
        (<= 2 (dir-ent-first-cluster dir-ent))
        (< (dir-ent-first-cluster dir-ent)
           (+ 2 (count-of-clusters fat32-in-memory))))
   (equal
    (fat32-in-memory-to-m1-fs-helper
     fat32-in-memory
     (append dir-ent dir-contents)
     entry-limit)
    (if
     (equal (mv-nth 1
                    (get-clusterchain-contents
                     fat32-in-memory
                     (dir-ent-first-cluster dir-ent)
                     2097152))
            0)
     (if
      (<
       0
       (mv-nth
        3
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory
         (string=>nats
          (mv-nth 0
                  (get-clusterchain-contents
                   fat32-in-memory
                   (dir-ent-first-cluster dir-ent)
                   2097152)))
         (+ -1 entry-limit))))
      (mv
       (cons
        (cons
         (dir-ent-filename dir-ent)
         (m1-file
          dir-ent
          (mv-nth
           0
           (fat32-in-memory-to-m1-fs-helper
            fat32-in-memory
            (string=>nats
             (mv-nth 0
                     (get-clusterchain-contents
                      fat32-in-memory
                      (dir-ent-first-cluster dir-ent)
                      2097152)))
            (+ -1 entry-limit)))))
        (mv-nth
         0
         (fat32-in-memory-to-m1-fs-helper
          fat32-in-memory dir-contents
          (+
           -1 entry-limit
           (-
            (mv-nth
             1
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              (string=>nats
               (mv-nth 0
                       (get-clusterchain-contents
                        fat32-in-memory
                        (dir-ent-first-cluster dir-ent)
                        2097152)))
              (+ -1 entry-limit))))))))
       (+
        1
        (mv-nth
         1
         (fat32-in-memory-to-m1-fs-helper
          fat32-in-memory
          (string=>nats
           (mv-nth 0
                   (get-clusterchain-contents
                    fat32-in-memory
                    (dir-ent-first-cluster dir-ent)
                    2097152)))
          (+ -1 entry-limit)))
        (mv-nth
         1
         (fat32-in-memory-to-m1-fs-helper
          fat32-in-memory dir-contents
          (+
           -1 entry-limit
           (-
            (mv-nth
             1
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              (string=>nats
               (mv-nth 0
                       (get-clusterchain-contents
                        fat32-in-memory
                        (dir-ent-first-cluster dir-ent)
                        2097152)))
              (+ -1 entry-limit))))))))
       (cons
        (mv-nth 0
                (fat32-build-index-list
                 (effective-fat fat32-in-memory)
                 (dir-ent-first-cluster dir-ent)
                 2097152 (cluster-size fat32-in-memory)))
        (append
         (mv-nth
          2
          (fat32-in-memory-to-m1-fs-helper
           fat32-in-memory
           (string=>nats
            (mv-nth 0
                    (get-clusterchain-contents
                     fat32-in-memory
                     (dir-ent-first-cluster dir-ent)
                     2097152)))
           (+ -1 entry-limit)))
         (mv-nth
          2
          (fat32-in-memory-to-m1-fs-helper
           fat32-in-memory dir-contents
           (+
            -1 entry-limit
            (-
             (mv-nth
              1
              (fat32-in-memory-to-m1-fs-helper
               fat32-in-memory
               (string=>nats
                (mv-nth 0
                        (get-clusterchain-contents
                         fat32-in-memory
                         (dir-ent-first-cluster dir-ent)
                         2097152)))
               (+ -1 entry-limit)))))))))
       (mv-nth
        3
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory
         (string=>nats
          (mv-nth 0
                  (get-clusterchain-contents
                   fat32-in-memory
                   (dir-ent-first-cluster dir-ent)
                   2097152)))
         (+ -1 entry-limit))))
      (mv
       (cons
        (cons
         (dir-ent-filename dir-ent)
         (m1-file
          dir-ent
          (mv-nth
           0
           (fat32-in-memory-to-m1-fs-helper
            fat32-in-memory
            (string=>nats
             (mv-nth 0
                     (get-clusterchain-contents
                      fat32-in-memory
                      (dir-ent-first-cluster dir-ent)
                      2097152)))
            (+ -1 entry-limit)))))
        (mv-nth
         0
         (fat32-in-memory-to-m1-fs-helper
          fat32-in-memory dir-contents
          (+
           -1 entry-limit
           (-
            (mv-nth
             1
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              (string=>nats
               (mv-nth 0
                       (get-clusterchain-contents
                        fat32-in-memory
                        (dir-ent-first-cluster dir-ent)
                        2097152)))
              (+ -1 entry-limit))))))))
       (+
        1
        (mv-nth
         1
         (fat32-in-memory-to-m1-fs-helper
          fat32-in-memory
          (string=>nats
           (mv-nth 0
                   (get-clusterchain-contents
                    fat32-in-memory
                    (dir-ent-first-cluster dir-ent)
                    2097152)))
          (+ -1 entry-limit)))
        (mv-nth
         1
         (fat32-in-memory-to-m1-fs-helper
          fat32-in-memory dir-contents
          (+
           -1 entry-limit
           (-
            (mv-nth
             1
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              (string=>nats
               (mv-nth 0
                       (get-clusterchain-contents
                        fat32-in-memory
                        (dir-ent-first-cluster dir-ent)
                        2097152)))
              (+ -1 entry-limit))))))))
       (cons
        (mv-nth 0
                (fat32-build-index-list
                 (effective-fat fat32-in-memory)
                 (dir-ent-first-cluster dir-ent)
                 2097152 (cluster-size fat32-in-memory)))
        (append
         (mv-nth
          2
          (fat32-in-memory-to-m1-fs-helper
           fat32-in-memory
           (string=>nats
            (mv-nth 0
                    (get-clusterchain-contents
                     fat32-in-memory
                     (dir-ent-first-cluster dir-ent)
                     2097152)))
           (+ -1 entry-limit)))
         (mv-nth
          2
          (fat32-in-memory-to-m1-fs-helper
           fat32-in-memory dir-contents
           (+
            -1 entry-limit
            (-
             (mv-nth
              1
              (fat32-in-memory-to-m1-fs-helper
               fat32-in-memory
               (string=>nats
                (mv-nth 0
                        (get-clusterchain-contents
                         fat32-in-memory
                         (dir-ent-first-cluster dir-ent)
                         2097152)))
               (+ -1 entry-limit)))))))))
       (mv-nth
        3
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory dir-contents
         (+
          -1 entry-limit
          (-
           (mv-nth
            1
            (fat32-in-memory-to-m1-fs-helper
             fat32-in-memory
             (string=>nats
              (mv-nth 0
                      (get-clusterchain-contents
                       fat32-in-memory
                       (dir-ent-first-cluster dir-ent)
                       2097152)))
             (+ -1 entry-limit)))))))))
     (mv
      (cons
       (cons
        (dir-ent-filename dir-ent)
        (m1-file
         dir-ent
         (mv-nth
          0
          (fat32-in-memory-to-m1-fs-helper
           fat32-in-memory
           (string=>nats
            (mv-nth 0
                    (get-clusterchain-contents
                     fat32-in-memory
                     (dir-ent-first-cluster dir-ent)
                     2097152)))
           (+ -1 entry-limit)))))
       (mv-nth
        0
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory dir-contents
         (+
          -1 entry-limit
          (-
           (mv-nth
            1
            (fat32-in-memory-to-m1-fs-helper
             fat32-in-memory
             (string=>nats
              (mv-nth 0
                      (get-clusterchain-contents
                       fat32-in-memory
                       (dir-ent-first-cluster dir-ent)
                       2097152)))
             (+ -1 entry-limit))))))))
      (+
       1
       (mv-nth
        1
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory
         (string=>nats
          (mv-nth 0
                  (get-clusterchain-contents
                   fat32-in-memory
                   (dir-ent-first-cluster dir-ent)
                   2097152)))
         (+ -1 entry-limit)))
       (mv-nth
        1
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory dir-contents
         (+
          -1 entry-limit
          (-
           (mv-nth
            1
            (fat32-in-memory-to-m1-fs-helper
             fat32-in-memory
             (string=>nats
              (mv-nth 0
                      (get-clusterchain-contents
                       fat32-in-memory
                       (dir-ent-first-cluster dir-ent)
                       2097152)))
             (+ -1 entry-limit))))))))
      (cons
       (mv-nth 0
               (fat32-build-index-list
                (effective-fat fat32-in-memory)
                (dir-ent-first-cluster dir-ent)
                2097152 (cluster-size fat32-in-memory)))
       (append
        (mv-nth
         2
         (fat32-in-memory-to-m1-fs-helper
          fat32-in-memory
          (string=>nats
           (mv-nth 0
                   (get-clusterchain-contents
                    fat32-in-memory
                    (dir-ent-first-cluster dir-ent)
                    2097152)))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (fat32-in-memory-to-m1-fs-helper
          fat32-in-memory dir-contents
          (+
           -1 entry-limit
           (-
            (mv-nth
             1
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              (string=>nats
               (mv-nth 0
                       (get-clusterchain-contents
                        fat32-in-memory
                        (dir-ent-first-cluster dir-ent)
                        2097152)))
              (+ -1 entry-limit)))))))))
      *eio*))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable nth floor
                        mod fat32-in-memory-to-m1-fs-helper)
    :expand ((fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              (append dir-ent dir-contents)
              entry-limit)
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory dir-contents 0))
    :use (:theorem (implies (dir-ent-p dir-ent)
                            (equal (true-list-fix dir-ent)
                                   dir-ent))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-30
  (implies
   (and (dir-ent-p dir-ent)
        (not (zp entry-limit))
        (not (equal (nth 0 dir-ent) 0))
        (useless-dir-ent-p dir-ent))
   (equal
    (fat32-in-memory-to-m1-fs-helper
     fat32-in-memory
     (append dir-ent dir-contents)
     entry-limit)
    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                     dir-contents (+ -1 entry-limit))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable nth floor
                        mod fat32-in-memory-to-m1-fs-helper)
    :expand ((fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              (append dir-ent dir-contents)
              entry-limit)
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory dir-contents 0))
    :use (:theorem (implies (dir-ent-p dir-ent)
                            (equal (true-list-fix dir-ent)
                                   dir-ent))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-31
  (implies
   (and
    (equal
     (len
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
       1))
     1)
    (<= 2 current-dir-first-cluster)
    (< current-dir-first-cluster
       (+ 2 (count-of-clusters fat32-in-memory))))
   (not
    (<
     (nth
      '0
      (find-n-free-clusters
       (effective-fat
        (mv-nth '0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
       '1))
     '2)))
  :hints (("goal" :in-theory (disable mod floor nth))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-32
  (implies
   (and
    (equal
     (mv-nth
      2
      (m1-fs-to-fat32-in-memory-helper
       (update-fati
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth
            0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
          1))
        (fat32-update-lower-28
         (fati
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth
              0
              (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
            1))
          (mv-nth
           0
           (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
         268435455)
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
       (m1-file->contents (cdr (car fs)))
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth
           0
           (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
         1))))
     0)
    (consp fs)
    (not (m1-regular-file-p (cdr (car fs))))
    (equal (mod 2097152 (cluster-size fat32-in-memory))
           0)
    (m1-file-alist-p fs)
    (m1-bounded-file-alist-p fs))
   (not
    (<
     2097152
     (*
      (cluster-size fat32-in-memory)
      (len
       (make-clusters
        (nats=>string
         (append
          (dir-ent-install-directory-bit
           (dir-ent-set-filename
            (dir-ent-set-first-cluster-file-size
             (m1-file->dir-ent (cdr (car fs)))
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               1))
             0)
            ".          ")
           t)
          (dir-ent-install-directory-bit
           (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                  (m1-file->dir-ent (cdr (car fs)))
                                  current-dir-first-cluster 0)
                                 "..         ")
           t)
          (flatten
           (mv-nth
            1
            (m1-fs-to-fat32-in-memory-helper
             (update-fati
              (nth
               0
               (find-n-free-clusters
                (effective-fat (mv-nth 0
                                       (m1-fs-to-fat32-in-memory-helper
                                        fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
                1))
              (fat32-update-lower-28
               (fati
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat (mv-nth 0
                                         (m1-fs-to-fat32-in-memory-helper
                                          fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
                  1))
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               268435455)
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             (m1-file->contents (cdr (car fs)))
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth
                 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
               1)))))))
        (cluster-size fat32-in-memory)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable nth floor mod
                        (:linear make-clusters-correctness-3))
    :use
    (:instance
     (:linear make-clusters-correctness-3)
     (max-length *ms-max-dir-size*)
     (text
      (nats=>string
       (append
        (dir-ent-install-directory-bit
         (dir-ent-set-filename
          (dir-ent-set-first-cluster-file-size
           (m1-file->dir-ent (cdr (car fs)))
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             1))
           0)
          ".          ")
         t)
        (dir-ent-install-directory-bit
         (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                (m1-file->dir-ent (cdr (car fs)))
                                current-dir-first-cluster 0)
                               "..         ")
         t)
        (flatten
         (mv-nth
          1
          (m1-fs-to-fat32-in-memory-helper
           (update-fati
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth
                0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
              1))
            (fat32-update-lower-28
             (fati
              (nth
               0
               (find-n-free-clusters
                (effective-fat (mv-nth 0
                                       (m1-fs-to-fat32-in-memory-helper
                                        fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
                1))
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             268435455)
            (mv-nth
             0
             (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
           (m1-file->contents (cdr (car fs)))
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
             1))))))))
     (cluster-size (cluster-size fat32-in-memory))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-33
  (implies
   (dir-ent-p dir-ent)
   (and
    (not
     (equal
      (nth
       '0
       (dir-ent-set-filename dir-ent *current-dir-fat32-name*))
      '0))
    (not
     (equal
      (nth
       '0
       (dir-ent-set-filename dir-ent *parent-dir-fat32-name*))
      '0))))
  :hints
  (("goal" :in-theory
    (e/d (dir-ent-set-filename dir-ent-fix dir-ent-p)))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-34
  (implies
   (dir-ent-p dir-ent)
   (and
    (useless-dir-ent-p
     (dir-ent-set-filename dir-ent *current-dir-fat32-name*))
    (useless-dir-ent-p
     (dir-ent-set-filename dir-ent *parent-dir-fat32-name*))))
  :hints
  (("goal"
    :in-theory (e/d (dir-ent-set-filename
                     dir-ent-fix dir-ent-p
                     useless-dir-ent-p dir-ent-filename)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm m1-fs-to-fat32-in-memory-inversion-lemma-35
    (implies (and (integerp x)
                  (integerp y)
                  (not (zp j))
                  (equal (mod x j) 0))
             (equal (mod (+ x y) j) (mod y j)))
    :hints (("goal" :in-theory (disable floor))))

  (defthm m1-fs-to-fat32-in-memory-inversion-lemma-36
    (implies (and (not (zp y))
                  (integerp x)
                  (equal (mod x y) 0))
             (equal (mod (- x) y) 0))
    :hints (("goal" :expand (mod x y))))

  (defthmd m1-fs-to-fat32-in-memory-inversion-lemma-37
    (implies
     (and (< (len dir-contents) *ms-dir-ent-length*)
          (equal (mod (len dir-contents) *ms-dir-ent-length*) 0))
     (and
      (equal (len dir-contents) 0)
      (equal (append dir-contents y) y)))
    :hints (("Goal" :in-theory (disable mod len) :expand (len dir-contents)) )))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-38
  (implies
   (and (not (zp n))
        (equal (mod (len dir-contents)
                    *ms-dir-ent-length*)
               0))
   (and
    (equal
     (mv-nth 0
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              (append dir-contents (make-list-ac n 0 nil))
              entry-limit))
     (mv-nth 0
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              dir-contents entry-limit)))
    (equal
     (mv-nth 1
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              (append dir-contents (make-list-ac n 0 nil))
              entry-limit))
     (mv-nth 1
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              dir-contents entry-limit)))
    (equal
     (mv-nth 2
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              (append dir-contents (make-list-ac n 0 nil))
              entry-limit))
     (mv-nth 2
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              dir-contents entry-limit)))))
  :hints
  (("goal"
    :induct
    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                     dir-contents entry-limit)
    :in-theory
    (e/d nil
         (fat32-in-memoryp
          get-clusterchain-contents
          mod nth (:definition take-redefinition)
          (:rewrite len-when-dir-ent-p)
          (:rewrite unsigned-byte-listp-when-dir-ent-p)
          (:rewrite fat32-filename-p-correctness-1)))
    :expand (fat32-in-memory-to-m1-fs-helper
             fat32-in-memory
             (append dir-contents (make-list-ac n 0 nil))
             entry-limit))
   ("subgoal *1/1"
    :in-theory
    (e/d (m1-fs-to-fat32-in-memory-inversion-lemma-37)
         (fat32-in-memoryp
          get-clusterchain-contents
          mod nth (:definition take-redefinition)
          (:rewrite len-when-dir-ent-p)
          (:rewrite unsigned-byte-listp-when-dir-ent-p)
          (:rewrite fat32-filename-p-correctness-1)))
    :expand (fat32-in-memory-to-m1-fs-helper
             fat32-in-memory
             (append dir-contents (make-list-ac n 0 nil))
             entry-limit))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-39
  (implies
   (and (dir-ent-p dir-ent)
        (not (zp entry-limit))
        (not (equal (nth 0 dir-ent) 0))
        (not (useless-dir-ent-p dir-ent))
        (not (dir-ent-directory-p dir-ent))
        (< (dir-ent-first-cluster dir-ent)
           (+ 2 (count-of-clusters fat32-in-memory))))
   (equal
    (fat32-in-memory-to-m1-fs-helper
     fat32-in-memory
     (append dir-ent dir-contents)
     entry-limit)
    (if
     (< (dir-ent-first-cluster dir-ent) 2)
     (mv (cons (cons (dir-ent-filename dir-ent)
                     (m1-file dir-ent ""))
               (mv-nth 0
                       (fat32-in-memory-to-m1-fs-helper
                        fat32-in-memory
                        dir-contents (+ -1 entry-limit))))
         (+ 1
            (mv-nth 1
                    (fat32-in-memory-to-m1-fs-helper
                     fat32-in-memory
                     dir-contents (+ -1 entry-limit))))
         (cons nil
               (mv-nth 2
                       (fat32-in-memory-to-m1-fs-helper
                        fat32-in-memory
                        dir-contents (+ -1 entry-limit))))
         (mv-nth 3
                 (fat32-in-memory-to-m1-fs-helper
                  fat32-in-memory
                  dir-contents (+ -1 entry-limit))))
     (if
      (<
       (len
        (explode (mv-nth 0
                         (get-clusterchain-contents
                          fat32-in-memory
                          (dir-ent-first-cluster dir-ent)
                          (dir-ent-file-size dir-ent)))))
       4294967296)
      (if
       (equal (mv-nth 1
                      (get-clusterchain-contents
                       fat32-in-memory
                       (dir-ent-first-cluster dir-ent)
                       (dir-ent-file-size dir-ent)))
              0)
       (mv
        (cons
         (cons
          (dir-ent-filename dir-ent)
          (m1-file dir-ent
                   (mv-nth 0
                           (get-clusterchain-contents
                            fat32-in-memory
                            (dir-ent-first-cluster dir-ent)
                            (dir-ent-file-size dir-ent)))))
         (mv-nth 0
                 (fat32-in-memory-to-m1-fs-helper
                  fat32-in-memory
                  dir-contents (+ -1 entry-limit))))
        (+ 1
           (mv-nth 1
                   (fat32-in-memory-to-m1-fs-helper
                    fat32-in-memory
                    dir-contents (+ -1 entry-limit))))
        (cons (mv-nth 0
                      (fat32-build-index-list
                       (effective-fat fat32-in-memory)
                       (dir-ent-first-cluster dir-ent)
                       (dir-ent-file-size dir-ent)
                       (cluster-size fat32-in-memory)))
              (mv-nth 2
                      (fat32-in-memory-to-m1-fs-helper
                       fat32-in-memory
                       dir-contents (+ -1 entry-limit))))
        (mv-nth 3
                (fat32-in-memory-to-m1-fs-helper
                 fat32-in-memory
                 dir-contents (+ -1 entry-limit))))
       (mv
        (cons
         (cons
          (dir-ent-filename dir-ent)
          (m1-file dir-ent
                   (mv-nth 0
                           (get-clusterchain-contents
                            fat32-in-memory
                            (dir-ent-first-cluster dir-ent)
                            (dir-ent-file-size dir-ent)))))
         (mv-nth 0
                 (fat32-in-memory-to-m1-fs-helper
                  fat32-in-memory
                  dir-contents (+ -1 entry-limit))))
        (+ 1
           (mv-nth 1
                   (fat32-in-memory-to-m1-fs-helper
                    fat32-in-memory
                    dir-contents (+ -1 entry-limit))))
        (cons (mv-nth 0
                      (fat32-build-index-list
                       (effective-fat fat32-in-memory)
                       (dir-ent-first-cluster dir-ent)
                       (dir-ent-file-size dir-ent)
                       (cluster-size fat32-in-memory)))
              (mv-nth 2
                      (fat32-in-memory-to-m1-fs-helper
                       fat32-in-memory
                       dir-contents (+ -1 entry-limit))))
        *eio*))
      (fat32-in-memory-to-m1-fs-helper
       fat32-in-memory
       dir-contents (+ -1 entry-limit))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable nth floor
                        mod fat32-in-memory-to-m1-fs-helper)
    :expand ((fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              (append dir-ent dir-contents)
              entry-limit)
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory dir-contents 0))
    :use (:theorem (implies (dir-ent-p dir-ent)
                            (equal (true-list-fix dir-ent)
                                   dir-ent))))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm m1-fs-to-fat32-in-memory-inversion-lemma-40
    (implies (and (<= 32 (len dir-contents))
                  (equal (mod (len dir-contents) 32) 0)
                  (< (+ -32 (len dir-contents)) 32))
             (equal (len dir-contents) 32))))

(thm
 (implies
  (and
   (not (zp n))
   (not (zp entry-limit))
   (unsigned-byte-listp 8 dir-contents)
   (equal (mod (len dir-contents)
               *ms-dir-ent-length*)
          0)
   (equal (mv-nth 3 (fat32-in-memory-to-m1-fs-helper
                     fat32-in-memory
                     dir-contents entry-limit)) 0))
  (equal
   (fat32-in-memory-to-m1-fs-helper
    fat32-in-memory
    (append dir-contents (make-list-ac n 0 nil))
    entry-limit)
   (fat32-in-memory-to-m1-fs-helper
    fat32-in-memory
    dir-contents
    entry-limit)))
 :hints
 (("goal"
   :induct
   (fat32-in-memory-to-m1-fs-helper
    fat32-in-memory
    dir-contents entry-limit)
   :in-theory
   (e/d (dir-ent-p dir-ent-fix) (nth floor mod)) :expand
   (fat32-in-memory-to-m1-fs-helper
    fat32-in-memory
    (append dir-contents (make-list-ac n 0 nil))
    entry-limit)) ))

(thm-cp
 (implies
  (and
   (compliant-fat32-in-memoryp fat32-in-memory)
   (equal (mod *ms-max-dir-size* (cluster-size fat32-in-memory))
          0)
   (m1-file-alist-p fs)
   (m1-bounded-file-alist-p fs)
   (m1-file-no-dups-p fs)
   (fat32-masked-entry-p current-dir-first-cluster)
   (<= *ms-first-data-cluster* current-dir-first-cluster)
   (< current-dir-first-cluster
      (+ *ms-first-data-cluster*
         (count-of-clusters fat32-in-memory))))
  (b*
      ((x-hypotheses
        (and
         (integerp x)
         (<= 2 x)
         (< x (+ 2 (count-of-clusters fat32-in-memory)))
         (not
          (equal
           (fat32-entry-mask
            (fati x fat32-in-memory))
           0))))
       ((mv fat32-in-memory dir-ent-list error-code)
        (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                         fs current-dir-first-cluster)))
    (implies
     (zp error-code)
     (and
      (equal
       (mv-nth
        3
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory
         (flatten dir-ent-list)
         (m1-entry-count fs)))
       0)
      (implies
       x-hypotheses
       (not-intersectp-list
        (list x)
        (mv-nth
         2
         (fat32-in-memory-to-m1-fs-helper
          fat32-in-memory
          (flatten dir-ent-list)
          (m1-entry-count fs)))))))))
 :hints (("Goal" :induct
          (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                           fs current-dir-first-cluster)
          :in-theory (e/d
                      (m1-fs-to-fat32-in-memory-inversion-lemma-2
                       m1-fs-to-fat32-in-memory-inversion-lemma-21)
                      (floor
                       mod
                       nth
                       (:rewrite make-clusters-correctness-1 . 1)
                       (:rewrite nth-of-nats=>chars)
                       (:rewrite by-slice-you-mean-the-whole-cake-2)
                       (:definition m1-fs-to-fat32-in-memory-helper)
                       (:definition FAT32-IN-MEMORY-TO-M1-FS-HELPER))))
         ("Subgoal *1/4"
          :expand
          (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                           fs current-dir-first-cluster))
         ("Subgoal *1/3"
          :expand
          ((m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                            fs current-dir-first-cluster)
           (:free (y) (intersectp-equal nil y))
           (:free (x1 x2 y) (intersectp-equal (list x1) (cons x2 y)))))))

(thm
 (implies
  (and
   (compliant-fat32-in-memoryp fat32-in-memory)
   (equal (mod *ms-max-dir-size* (cluster-size fat32-in-memory))
          0)
   (m1-file-alist-p fs)
   (m1-bounded-file-alist-p fs)
   (m1-file-no-dups-p fs)
   (fat32-masked-entry-p current-dir-first-cluster)
   (<= *ms-first-data-cluster* current-dir-first-cluster)
   (< current-dir-first-cluster
      (+ *ms-first-data-cluster*
         (count-of-clusters fat32-in-memory)))
   (<= (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory))
       (fat-length fat32-in-memory)))
  (b*
      (((mv fat32-in-memory dir-ent-list error-code)
        (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                         fs current-dir-first-cluster)))
    (implies
     (zp error-code)
     (and
      (equal
       (mv-nth
        3
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory
         (flatten dir-ent-list)
         (m1-entry-count fs)))
       0)
      (m1-dir-equiv
       (mv-nth
        0
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory
         (flatten dir-ent-list)
         (m1-entry-count fs)))
       fs)))))
 :hints (("Goal" :induct
          (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                           fs current-dir-first-cluster)
          :in-theory (disable
                      floor
                      mod
                      nth
                      (:rewrite make-clusters-correctness-1 . 1)
                      (:rewrite nth-of-nats=>chars)
                      (:rewrite by-slice-you-mean-the-whole-cake-2)))
         ("subgoal *1/4" :use lemma-1-4)
         ("subgoal *1/3" :use lemma-1-3)))

;; (defthm
;;   m1-fs-to-fat32-in-memory-inversion-lemma-1
;;   (implies
;;    (and
;;     (bounded-nat-listp index-list
;;                        (+ *ms-first-data-cluster*
;;                           (count-of-clusters fat32-in-memory)))
;;     (compliant-fat32-in-memoryp fat32-in-memory))
;;    (equal
;;     (len
;;      (mv-nth 1
;;              (stobj-set-clusters cluster-list
;;                                  index-list fat32-in-memory)))
;;     (len cluster-list)))
;;   :rule-classes
;;   (:rewrite
;;    (:rewrite
;;     :corollary
;;     (implies
;;      (and (bounded-nat-listp
;;            index-list
;;            (+ *ms-first-data-cluster*
;;               (count-of-clusters fat32-in-memory)))
;;           (compliant-fat32-in-memoryp fat32-in-memory))
;;      (iff
;;       (consp
;;        (mv-nth 1
;;                (stobj-set-clusters cluster-list
;;                                    index-list fat32-in-memory)))
;;       (consp cluster-list))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    m1-fs-to-fat32-in-memory-inversion-lemma-2
    (implies (compliant-fat32-in-memoryp fat32-in-memory)
             (>= (* (bpb_fatsz32 fat32-in-memory)
                    1/4 (bpb_bytspersec fat32-in-memory))
                 128))
    :rule-classes :linear
    :hints
    (("goal" :in-theory (enable compliant-fat32-in-memoryp)))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-3
  (implies
   (< masked-current-cluster
      *ms-first-data-cluster*)
   (equal
    (mv-nth
     0
     (get-clusterchain-contents fat32-in-memory
                                masked-current-cluster length))
    "")))

(encapsulate
  ()

  (local
   (defthm
     m1-fs-to-fat32-in-memory-inversion-lemma-4
     (equal
      (update-fati i2 v2
                   (update-data-regioni i1 v1 fat32-in-memory))
      (update-data-regioni
       i1
       v1 (update-fati i2 v2 fat32-in-memory)))
     :hints
     (("goal"
       :in-theory (enable update-fati update-data-regioni)))))

  (defthm
    m1-fs-to-fat32-in-memory-inversion-lemma-5
    (equal (stobj-set-indices-in-fa-table
            (update-data-regioni i v fat32-in-memory)
            index-list value-list)
           (update-data-regioni
            i v
            (stobj-set-indices-in-fa-table
             fat32-in-memory index-list value-list)))
    :hints
    (("goal" :in-theory (enable stobj-set-indices-in-fa-table)))))

(local
 (defthm
   m1-fs-to-fat32-in-memory-inversion-lemma-6
   (iff
    (equal (len (make-clusters text cluster-size))
           1)
    (and
     (not (zp (length text)))
     (zp (length (subseq text (min cluster-size (length text))
                         nil)))
     (not (zp cluster-size))))
   :hints (("goal" :in-theory (enable make-clusters)))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-7
  (implies
   (and (not (fat32-masked-entry-list-p index-list))
        (<= (+ (count-of-clusters fat32-in-memory)
               *ms-first-data-cluster*)
            *ms-bad-cluster*))
   (not
    (bounded-nat-listp index-list
                       (+ (count-of-clusters fat32-in-memory)
                          *ms-first-data-cluster*))))
  :hints
  (("goal"
    :use ((:instance (:rewrite fat32-masked-entry-list-p-alt)
                     (x index-list))
          (:instance (:rewrite bounded-nat-listp-correctness-5)
                     (x (+ (count-of-clusters fat32-in-memory)
                           *ms-first-data-cluster*))
                     (y *expt-2-28*)
                     (l index-list))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-9
  (implies (and (not (zp cluster-size))
                (stringp text))
           (< (* cluster-size
                 (- (len (make-clusters text cluster-size))
                    1))
              (len (explode text))))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable make-clusters))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-11
  (implies
   (and (<= 2 (car index-list))
        (stringp text)
        (integerp length)
        (>= length (length text))
        (equal (len (make-clusters text (cluster-size fat32-in-memory)))
               (len index-list))
        (compliant-fat32-in-memoryp fat32-in-memory)
        (no-duplicatesp-equal index-list)
        (lower-bounded-integer-listp index-list *ms-first-data-cluster*)
        (bounded-nat-listp index-list
                           (+ *ms-first-data-cluster*
                              (count-of-clusters fat32-in-memory)))
        (fat32-masked-entry-list-p index-list))
   (equal
    (get-clusterchain-contents
     (stobj-set-indices-in-fa-table
      (stobj-set-clusters (make-clusters text (cluster-size fat32-in-memory))
                          index-list fat32-in-memory)
      index-list
      (append (cdr index-list)
              (list 268435455)))
     (car index-list)
     length)
    (mv
     (implode (append (explode text)
                      (make-list (- (min length
                                         (* (len index-list)
                                            (cluster-size fat32-in-memory)))
                                    (length text))
                                 :initial-element (code-char 0))))
     0)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (fat32-masked-entry-p (car index-list))
          (<= 2 (car index-list))
          (< (car index-list)
             (+ (count-of-clusters fat32-in-memory)
                2))
          (<= (+ (count-of-clusters fat32-in-memory)
                 2)
              (fat-length fat32-in-memory))
          (equal (data-region-length fat32-in-memory)
                 (count-of-clusters fat32-in-memory))
          (stringp text)
          (integerp length)
          (>= length (length text))
          (equal (len (make-clusters text (cluster-size fat32-in-memory)))
                 (len index-list))
          (compliant-fat32-in-memoryp fat32-in-memory)
          (no-duplicatesp-equal index-list)
          (lower-bounded-integer-listp index-list *ms-first-data-cluster*)
          (bounded-nat-listp index-list
                             (+ *ms-first-data-cluster*
                                (count-of-clusters fat32-in-memory)))
          (fat32-masked-entry-list-p index-list)
          (equal cluster-size
                 (cluster-size fat32-in-memory))
          (equal head (car index-list))
          (equal tail (cdr index-list)))
     (equal
      (get-clusterchain-contents
       (stobj-set-indices-in-fa-table
        (stobj-set-clusters (make-clusters text cluster-size)
                            index-list fat32-in-memory)
        index-list
        (append tail (list 268435455)))
       head length)
      (mv
       (implode (append (explode text)
                        (make-list (- (min length
                                           (* (len index-list) cluster-size))
                                      (length text))
                                   :initial-element (code-char 0))))
       0)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite get-clusterchain-contents-correctness-1)
                        (:linear make-clusters-correctness-2)
                        (:rewrite get-clusterchain-contents-correctness-3)
                        (:rewrite get-clusterchain-contents-correctness-2))
    :use
    ((:instance
      (:rewrite get-clusterchain-contents-correctness-1)
      (length length)
      (masked-current-cluster (car index-list))
      (fat32-in-memory
       (stobj-set-indices-in-fa-table
        (stobj-set-clusters
         (make-clusters text (cluster-size fat32-in-memory))
         index-list fat32-in-memory)
        index-list
        (append (cdr index-list)
                (list 268435455)))))
     (:instance (:linear make-clusters-correctness-2)
                (cluster-size (cluster-size fat32-in-memory)))
     (:instance
      (:rewrite get-clusterchain-contents-correctness-3)
      (masked-current-cluster (car index-list))
      (fat32-in-memory
       (stobj-set-indices-in-fa-table
        (stobj-set-clusters
         (make-clusters text (cluster-size fat32-in-memory))
         index-list fat32-in-memory)
        index-list
        (append (cdr index-list)
                (list 268435455)))))
     (:instance
      (:rewrite get-clusterchain-contents-correctness-2)
      (masked-current-cluster (car index-list))
      (fat32-in-memory
       (stobj-set-indices-in-fa-table
        (stobj-set-clusters
         (make-clusters text (cluster-size fat32-in-memory))
         index-list fat32-in-memory)
        index-list
        (append (cdr index-list)
                '(268435455)))))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-15
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (equal (mod length 32) 0))
   (equal
    (mod
     (len
      (explode
       (mv-nth 0
               (get-clusterchain-contents fat32-in-memory
                                          masked-current-cluster length))))
     32)
    0))
  :hints (("goal" :in-theory (disable mod))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-18
  (implies (and (m1-bounded-file-alist-p x1)
                (integerp x2)
                (consp x1))
           (< (+ *ms-dir-ent-length*
                 (- (* *ms-dir-ent-length*
                       *ms-max-dir-ent-count*))
                 x2)
              (+ x2
                 (- (* *ms-dir-ent-length* (len (cdr x1)))))))
  :hints
  (("goal"
    :in-theory
    (disable (:linear len-when-m1-bounded-file-alist-p . 3))
    :use
    (:instance (:linear len-when-m1-bounded-file-alist-p . 3)
               (x x1))))
  :rule-classes :linear)

(encapsulate
  ()

  ;; This is currently not in use.

  (local
   (defthm m1-fs-to-fat32-in-memory-inversion-lemma-30
     (implies (and (integerp x) (integerp y) (integerp z) (< x y) (<= y z))
              (iff (< (binary-+ '1 x) z)
                   (or
                    (not (equal x (- y 1)))
                    (not (equal y z)))))))

  (defthm m1-fs-to-fat32-in-memory-inversion-lemma-31
    (implies (<= (+ *ms-first-data-cluster*
                    (count-of-clusters fat32-in-memory))
                 (fat-length fat32-in-memory))
             (not (< (if (< (binary-+ '1 current-dir-first-cluster)
                            (fat-length fat32-in-memory))
                         (fat-length fat32-in-memory)
                         (binary-+ '1 current-dir-first-cluster))
                     (binary-+ '2
                               (count-of-clusters fat32-in-memory)))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-32
  (implies
   (<= (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory))
       (fat-length fat32-in-memory))
   (not
    (<
     (max
      (if
       (equal
        (nth
         '0
         (find-n-free-clusters
          (effective-fat
           (mv-nth
            '0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
          '1))
        (binary-+ '-1
                  (fat-length fat32-in-memory)))
       (binary-+
        '1
        (nth
         '0
         (find-n-free-clusters
          (effective-fat
           (mv-nth
            '0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
          '1)))
       (fat-length fat32-in-memory))
      (binary-+ '1 current-dir-first-cluster))
     (binary-+ '2
               (count-of-clusters fat32-in-memory)))))
  :rule-classes (:rewrite :linear))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-46
  (implies
   (dir-ent-p dir-ent)
   (and
    (equal
     (take *ms-dir-ent-length*
           (append (dir-ent-install-directory-bit dir-ent val)
                   y))
     (dir-ent-install-directory-bit dir-ent val))
    (equal
     (nthcdr *ms-dir-ent-length*
             (append (dir-ent-install-directory-bit dir-ent val)
                     y))
     y))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-51
  (implies (not (consp index-list))
           (equal (stobj-set-indices-in-fa-table
                   fat32-in-memory index-list value-list)
                  fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-53
  (implies
   (natp entry-limit)
   (<= (m1-entry-count (mv-nth 0
                               (fat32-in-memory-to-m1-fs-helper
                                fat32-in-memory
                                dir-contents entry-limit)))
       entry-limit))
  :rule-classes :linear
  :hints
  (("goal"
    :in-theory
    (disable
     (:definition fat32-in-memoryp)
     (:rewrite natp-of-cluster-size . 1)
     (:definition fat32-build-index-list)
     (:definition get-clusterchain-contents)
     (:rewrite by-slice-you-mean-the-whole-cake-2)
     (:rewrite len-when-dir-ent-p)
     (:rewrite
      fat32-in-memory-to-m1-fs-helper-guard-lemma-1)))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-54
  (implies
   (and
    (fat32-masked-entry-p masked-current-cluster)
    (compliant-fat32-in-memoryp fat32-in-memory)
    (equal
     (mv-nth 1
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     masked-current-cluster
                                     length (cluster-size fat32-in-memory)))
     0)
    (fat32-masked-entry-list-p value-list)
    (equal (len index-list)
           (len value-list))
    (nat-listp index-list)
    (not
     (intersectp-equal
      index-list
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster length
                                      (cluster-size fat32-in-memory))))))
   (equal
    (get-clusterchain-contents
     (stobj-set-indices-in-fa-table fat32-in-memory index-list value-list)
     masked-current-cluster length)
    (get-clusterchain-contents fat32-in-memory
                               masked-current-cluster length)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite get-clusterchain-contents-correctness-1)
                        get-clusterchain-contents-correctness-2
                        get-clusterchain-contents-correctness-2
                        get-clusterchain-contents-correctness-3)
    :use
    ((:rewrite get-clusterchain-contents-correctness-1)
     (:instance
      (:rewrite get-clusterchain-contents-correctness-1)
      (fat32-in-memory
       (stobj-set-indices-in-fa-table fat32-in-memory index-list value-list)))
     get-clusterchain-contents-correctness-2
     (:instance
      get-clusterchain-contents-correctness-2
      (fat32-in-memory
       (stobj-set-indices-in-fa-table fat32-in-memory index-list value-list)))
     get-clusterchain-contents-correctness-2
     (:instance
      get-clusterchain-contents-correctness-2
      (fat32-in-memory
       (stobj-set-indices-in-fa-table fat32-in-memory index-list value-list)))
     get-clusterchain-contents-correctness-3
     (:instance
      get-clusterchain-contents-correctness-3
      (fat32-in-memory
       (stobj-set-indices-in-fa-table fat32-in-memory
                                      index-list value-list)))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-58
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list))
        (nat-listp index-list)
        (not-intersectp-list
         index-list
         (mv-nth 2
                 (fat32-in-memory-to-m1-fs-helper
                  fat32-in-memory
                  dir-contents entry-limit)))
        (zp (mv-nth 3
                    (fat32-in-memory-to-m1-fs-helper
                     fat32-in-memory
                     dir-contents entry-limit))))
   (equal (fat32-in-memory-to-m1-fs-helper
           (stobj-set-indices-in-fa-table
            fat32-in-memory index-list value-list)
           dir-contents entry-limit)
          (fat32-in-memory-to-m1-fs-helper
           fat32-in-memory
           dir-contents entry-limit)))
  :hints
  (("goal"
    :in-theory
    (disable (:definition fat32-in-memoryp)
             dir-ent-fix nth
             (:definition get-clusterchain-contents)
             (:rewrite by-slice-you-mean-the-whole-cake-2)
             (:definition fat32-build-index-list))
    :induct
    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                     dir-contents entry-limit)
    :expand (fat32-in-memory-to-m1-fs-helper
             (stobj-set-indices-in-fa-table
              fat32-in-memory index-list value-list)
             dir-contents entry-limit))))

(defthm
  effective-fat-of-stobj-set-clusters
  (equal (effective-fat
          (stobj-set-clusters cluster-list
                              index-list fat32-in-memory))
         (effective-fat fat32-in-memory)))

(defthm
  data-regioni-of-stobj-set-clusters
  (implies
   (and (natp i)
        (not (member-equal (+ i *ms-first-data-cluster*)
                           index-list)))
   (equal (data-regioni i
                        (stobj-set-clusters cluster-list
                                            index-list fat32-in-memory))
          (data-regioni i fat32-in-memory)))
  :hints (("goal" :in-theory (enable lower-bounded-integer-listp))))

(defthm
  get-contents-from-clusterchain-of-stobj-set-clusters
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (lower-bounded-integer-listp clusterchain *ms-first-data-cluster*)
        (not (intersectp-equal clusterchain index-list)))
   (equal (get-contents-from-clusterchain
           (stobj-set-clusters cluster-list index-list fat32-in-memory)
           clusterchain file-size)
          (get-contents-from-clusterchain fat32-in-memory
                                          clusterchain file-size)))
  :hints
  (("goal"
    :induct
    (get-contents-from-clusterchain fat32-in-memory clusterchain file-size)
    :in-theory (enable lower-bounded-integer-listp
                       intersectp-equal))))

(defthm
  get-clusterchain-contents-of-stobj-set-clusters
  (implies
   (and
    (compliant-fat32-in-memoryp fat32-in-memory)
    (fat32-masked-entry-p masked-current-cluster)
    (<= 2 masked-current-cluster)
    (< masked-current-cluster
       (+ (count-of-clusters fat32-in-memory)
          *ms-first-data-cluster*))
    (not
     (intersectp-equal
      index-list
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster length
                                      (cluster-size fat32-in-memory)))))
    (equal (mv-nth 1
                   (get-clusterchain-contents fat32-in-memory
                                              masked-current-cluster length))
           0)
    (lower-bounded-integer-listp index-list *ms-first-data-cluster*)
    (cluster-listp cluster-list
                   (cluster-size fat32-in-memory))
    (equal (len cluster-list)
           (len index-list)))
   (equal (get-clusterchain-contents
           (stobj-set-clusters cluster-list index-list fat32-in-memory)
           masked-current-cluster length)
          (get-clusterchain-contents fat32-in-memory
                                     masked-current-cluster length)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite get-clusterchain-contents-correctness-1)
                        get-clusterchain-contents-correctness-2
                        get-clusterchain-contents-correctness-3)
    :use
    ((:rewrite get-clusterchain-contents-correctness-1)
     (:instance
      (:rewrite get-clusterchain-contents-correctness-1)
      (fat32-in-memory (stobj-set-clusters cluster-list
                                           index-list fat32-in-memory)))
     get-clusterchain-contents-correctness-2
     (:instance
      get-clusterchain-contents-correctness-2
      (fat32-in-memory (stobj-set-clusters cluster-list
                                           index-list fat32-in-memory)))
     get-clusterchain-contents-correctness-3
     (:instance
      get-clusterchain-contents-correctness-3
      (fat32-in-memory (stobj-set-clusters cluster-list
                                           index-list fat32-in-memory)))))))

(defthm
  fat32-in-memory-to-m1-fs-helper-of-stobj-set-clusters
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (not-intersectp-list
         index-list
         (mv-nth 2
                 (fat32-in-memory-to-m1-fs-helper
                  fat32-in-memory
                  dir-contents entry-limit)))
        (lower-bounded-integer-listp
         index-list *ms-first-data-cluster*)
        (cluster-listp cluster-list
                       (cluster-size fat32-in-memory))
        (equal (len cluster-list)
               (len index-list))
        (equal (mv-nth 3
                       (fat32-in-memory-to-m1-fs-helper
                        fat32-in-memory
                        dir-contents entry-limit))
               0))
   (equal
    (fat32-in-memory-to-m1-fs-helper
     (stobj-set-clusters
      cluster-list index-list fat32-in-memory)
     dir-contents entry-limit)
    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                     dir-contents entry-limit)))
  :hints
  (("goal"
    :in-theory
    (e/d (intersectp-equal)
         ((:definition fat32-in-memoryp)
          (:definition fat32-build-index-list)
          (:definition get-clusterchain-contents)
          (:rewrite get-clusterchain-contents-correctness-2)
          (:rewrite by-slice-you-mean-the-whole-cake-2)
          (:linear nth-when-dir-ent-p)
          (:definition m1-entry-count)))
    :induct
    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                     dir-contents entry-limit)
    :expand (fat32-in-memory-to-m1-fs-helper
             (stobj-set-clusters
              cluster-list index-list fat32-in-memory)
             dir-contents entry-limit))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-61
  (implies
   (and
    (compliant-fat32-in-memoryp fat32-in-memory)
    (integerp first-cluster)
    (<= *ms-first-data-cluster* first-cluster)
    (stringp contents)
    (equal (mv-nth 3
                   (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                                    dir-contents entry-limit))
           0)
    (not-intersectp-list
     (list first-cluster)
     (mv-nth 2
             (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                              dir-contents entry-limit))))
   (and
    (m1-dir-equiv
     (mv-nth 0
             (fat32-in-memory-to-m1-fs-helper
              (mv-nth 0
                      (place-contents fat32-in-memory dir-ent
                                      contents file-length first-cluster))
              dir-contents entry-limit))
     (mv-nth 0
             (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                              dir-contents entry-limit)))
    (equal
     (mv-nth 3
             (fat32-in-memory-to-m1-fs-helper
              (mv-nth 0
                      (place-contents fat32-in-memory dir-ent
                                      contents file-length first-cluster))
              dir-contents entry-limit))
     0)))
  :hints
  (("goal"
    :in-theory
    (e/d (place-contents lower-bounded-integer-listp)
         (not-intersectp-list-of-append-2
          (:rewrite fat32-masked-entry-list-p-of-find-n-free-clusters
                    . 1)))
    :use
    ((:instance
      not-intersectp-list-of-append-2
      (l (mv-nth 2
                 (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                                  dir-contents entry-limit)))
      (y (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+ -1
             (len (make-clusters contents
                                 (cluster-size fat32-in-memory))))))
      (x (list first-cluster)))
     (:instance (:rewrite fat32-masked-entry-list-p-of-find-n-free-clusters
                          . 1)
                (n (+ -1
                      (len (make-clusters contents
                                          (cluster-size fat32-in-memory)))))
                (fa-table (effective-fat fat32-in-memory))))
    :do-not-induct t)))

(defthm
  get-clusterchain-contents-of-place-contents-disjoint
  (implies
   (and
    (compliant-fat32-in-memoryp fat32-in-memory)
    (natp length)
    (stringp contents)
    (integerp first-cluster)
    (<= 2 first-cluster)
    (fat32-masked-entry-p masked-current-cluster)
    (<= 2 masked-current-cluster)
    (< masked-current-cluster
       (+ (count-of-clusters fat32-in-memory)
          2))
    (<= (+ 2 (count-of-clusters fat32-in-memory))
        (fat-length fat32-in-memory))
    (equal (data-region-length fat32-in-memory)
           (count-of-clusters fat32-in-memory))
    (equal
     (mv-nth
      1
      (get-clusterchain-contents fat32-in-memory
                                 masked-current-cluster length))
     0)
    (not (member-equal
          first-cluster
          (mv-nth 0
                  (fat32-build-index-list
                   (effective-fat fat32-in-memory)
                   masked-current-cluster length
                   (cluster-size fat32-in-memory))))))
   (equal
    (get-clusterchain-contents
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     masked-current-cluster length)
    (get-clusterchain-contents fat32-in-memory
                               masked-current-cluster length)))
  :hints
  (("goal"
    :in-theory (e/d (place-contents lower-bounded-integer-listp
                                    intersectp-equal)
                    (intersectp-is-commutative)))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-62
  (implies
   (equal (len (find-n-free-clusters fa-table n))
          1)
   (and (equal (list (nth 0 (find-n-free-clusters fa-table n)))
               (find-n-free-clusters fa-table n))
        (equal (cdr (find-n-free-clusters fa-table n))
               nil)))
  :hints
  (("goal"
    :expand ((len (find-n-free-clusters fa-table n))
             (len (cdr (find-n-free-clusters fa-table n))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (equal (len (find-n-free-clusters fa-table n))
            1)
     (equal (cons (nth 0 (find-n-free-clusters fa-table n))
                  y)
            (append (find-n-free-clusters fa-table n)
                    y))))
   (:rewrite
    :corollary
    (implies
     (equal (len (find-n-free-clusters fa-table n))
            1)
     (equal (cons (car (find-n-free-clusters fa-table n))
                  y)
            (append (find-n-free-clusters fa-table n)
                    y))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-63
  (implies
   (and
    (fat32-entry-list-p fa-table)
    (natp n)
    (bounded-nat-listp index-list (len fa-table))
    (fat32-masked-entry-list-p value-list)
    (equal (len index-list)
           (len value-list))
    (natp masked-current-cluster)
    (equal
     (mv-nth
      1
      (fat32-build-index-list fa-table masked-current-cluster
                              length cluster-size))
     0)
    (not
     (intersectp-equal
      index-list
      (mv-nth
       0
       (fat32-build-index-list fa-table masked-current-cluster
                               length cluster-size)))))
   (not
    (intersectp-equal
     (mv-nth
      0
      (fat32-build-index-list fa-table masked-current-cluster
                              length cluster-size))
     (find-n-free-clusters
      (set-indices-in-fa-table fa-table index-list value-list)
      n))))
  :hints
  (("goal" :in-theory (e/d (intersectp-equal)
                           (intersectp-is-commutative)))
   ("subgoal *1/3"
    :use (:instance (:rewrite intersectp-is-commutative)
                    (y (list masked-current-cluster))
                    (x index-list)))
   ("subgoal *1/7"
    :use
    ((:instance
      (:rewrite intersectp-is-commutative)
      (y
       (cons
        masked-current-cluster
        (mv-nth 0
                (fat32-build-index-list
                 fa-table
                 (fat32-entry-mask
                  (nth masked-current-cluster fa-table))
                 (+ (- cluster-size) length)
                 cluster-size))))
      (x index-list))
     (:instance
      (:rewrite intersectp-is-commutative)
      (y
       (mv-nth 0
               (fat32-build-index-list
                fa-table
                (fat32-entry-mask
                 (nth masked-current-cluster fa-table))
                (+ (- cluster-size) length)
                cluster-size)))
      (x index-list))))
   ("subgoal *1/8"
    :use
    (:instance
     (:rewrite intersectp-is-commutative)
     (y
      (cons
       masked-current-cluster
       (mv-nth 0
               (fat32-build-index-list
                fa-table
                (fat32-entry-mask
                 (nth masked-current-cluster fa-table))
                (+ (- cluster-size) length)
                cluster-size))))
     (x index-list))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
  (implies
   (and
    (fat32-entry-list-p fa-table)
    (natp n)
    (bounded-nat-listp index-list (len fa-table))
    (fat32-masked-entry-list-p value-list)
    (equal (len index-list)
           (len value-list))
    (natp masked-current-cluster)
    (equal
     (mv-nth
      1
      (fat32-build-index-list fa-table masked-current-cluster
                              length cluster-size))
     0)
    (not
     (intersectp-equal
      index-list
      (mv-nth
       0
       (fat32-build-index-list fa-table masked-current-cluster
                               length cluster-size)))))
   (not
    (intersectp-equal
     (find-n-free-clusters
      (set-indices-in-fa-table fa-table index-list value-list)
      n)
     (mv-nth
      0
      (fat32-build-index-list fa-table masked-current-cluster
                              length cluster-size))))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-64
  (implies
   (and
    (compliant-fat32-in-memoryp fat32-in-memory)
    (<= (+ (count-of-clusters fat32-in-memory)
           *ms-first-data-cluster*)
        (fat-length fat32-in-memory))
    (natp n)
    (equal (mv-nth 3
                   (fat32-in-memory-to-m1-fs-helper
                    fat32-in-memory
                    dir-contents entry-limit))
           0)
    (bounded-nat-listp index-list
                       (+ *ms-first-data-cluster*
                          (count-of-clusters fat32-in-memory)))
    (fat32-masked-entry-list-p value-list)
    (equal (len index-list)
           (len value-list))
    (not-intersectp-list
     index-list
     (mv-nth 2
             (fat32-in-memory-to-m1-fs-helper
              fat32-in-memory
              dir-contents entry-limit))))
   (not-intersectp-list
    (find-n-free-clusters
     (set-indices-in-fa-table (effective-fat fat32-in-memory)
                              index-list value-list)
     n)
    (mv-nth 2
            (fat32-in-memory-to-m1-fs-helper
             fat32-in-memory
             dir-contents entry-limit))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (intersectp-equal)
     (fat32-in-memoryp (:definition get-clusterchain-contents)
                       (:definition fat32-build-index-list))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-65
  (implies
   (and (fat32-entry-list-p fa-table)
        (>= (len fa-table)
            *ms-first-data-cluster*)
        (natp n)
        (equal (len (find-n-free-clusters fa-table 1))
               1))
   (not
    (intersectp-equal
     (find-n-free-clusters fa-table 1)
     (find-n-free-clusters
      (set-indices-in-fa-table fa-table
                               (find-n-free-clusters fa-table 1)
                               '(268435455))
      n))))
  :hints
  (("goal" :in-theory
    (e/d (intersectp-equal set-indices-in-fa-table)))))

(defthmd
  lemma-1-3
  (implies
   (and
    (<=
     1
     (len
      (stobj-find-n-free-clusters
       (mv-nth 0
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster))
       1)))
    (m1-regular-file-p (cdr (car fs)))
    (implies
     (and (compliant-fat32-in-memoryp fat32-in-memory)
          (equal (data-region-length fat32-in-memory)
                 (count-of-clusters fat32-in-memory))
          (<= (+ (count-of-clusters fat32-in-memory)
                 2)
              (fat-length fat32-in-memory))
          (m1-file-alist-p (cdr fs))
          (m1-bounded-file-alist-p (cdr fs))
          (m1-file-no-dups-p (cdr fs))
          (fat32-masked-entry-p current-dir-first-cluster)
          (<= 2 current-dir-first-cluster)
          (< current-dir-first-cluster
             (+ 2 (count-of-clusters fat32-in-memory)))
          (<= (+ 2 (count-of-clusters fat32-in-memory))
              (fat-length fat32-in-memory)))
     (let
      ((mv (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster))
       (fs (cdr fs)))
      (let
       ((fat32-in-memory (mv-nth 0 mv))
        (dir-ent-list (mv-nth 1 mv))
        (error-code (mv-nth 2 mv)))
       (implies
        (zp error-code)
        (and (equal (mv-nth 3
                            (fat32-in-memory-to-m1-fs-helper
                             fat32-in-memory (flatten dir-ent-list)
                             (m1-entry-count fs)))
                    0)
             (m1-dir-equiv (mv-nth 0
                                   (fat32-in-memory-to-m1-fs-helper
                                    fat32-in-memory (flatten dir-ent-list)
                                    (m1-entry-count fs)))
                           fs))))))
    (compliant-fat32-in-memoryp fat32-in-memory)
    (m1-file-alist-p fs)
    (m1-bounded-file-alist-p fs)
    (m1-file-no-dups-p fs)
    (fat32-masked-entry-p current-dir-first-cluster)
    (<= 2 current-dir-first-cluster)
    (< current-dir-first-cluster
       (+ 2 (count-of-clusters fat32-in-memory))))
   (mv-let
     (fat32-in-memory dir-ent-list error-code)
     (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                      fs current-dir-first-cluster)
     (or (not (zp error-code))
         (and (equal (mv-nth 3
                             (fat32-in-memory-to-m1-fs-helper
                              fat32-in-memory (flatten dir-ent-list)
                              (m1-entry-count fs)))
                     0)
              (m1-dir-equiv (mv-nth 0
                                    (fat32-in-memory-to-m1-fs-helper
                                     fat32-in-memory (flatten dir-ent-list)
                                     (m1-entry-count fs)))
                            fs)))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (place-contents lower-bounded-integer-listp)
                    (nth (:rewrite make-clusters-correctness-1 . 1)
                         (:rewrite m1-directory-file-p-correctness-1)
                         (:rewrite by-slice-you-mean-the-whole-cake-2)
                         (:definition get-clusterchain-contents)
                         (:definition stobj-set-clusters))))))

(defthmd
  m1-fs-to-fat32-in-memory-inversion-lemma-67
  (implies
   (and
    (compliant-fat32-in-memoryp fat32-in-memory)
    (not (equal (len (explode contents)) 0))
    (equal
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     0))
   (equal
    (len (make-clusters contents
                        (cluster-size fat32-in-memory)))
    (len
     (cons
      first-cluster
      (stobj-find-n-free-clusters
       fat32-in-memory
       (+
        -1
        (len
         (make-clusters contents
                        (cluster-size fat32-in-memory)))))))))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  get-clusterchain-contents-of-place-contents-coincident
  (implies
   (and
    (equal
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     0)
    (not (zp (length contents)))
    (<= *ms-first-data-cluster* first-cluster)
    (stringp contents)
    (integerp length)
    (<= (length contents) length)
    (compliant-fat32-in-memoryp fat32-in-memory)
    (not
     (equal
      (fat32-entry-mask (fati first-cluster fat32-in-memory))
      0))
    (< first-cluster
       (+ 2 (count-of-clusters fat32-in-memory)))
    (fat32-masked-entry-p first-cluster))
   (equal
    (get-clusterchain-contents
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     first-cluster length)
    (mv
     (implode
      (append
       (explode contents)
       (make-list
        (+
         (min
          length
          (*
           (len (make-clusters contents
                               (cluster-size fat32-in-memory)))
           (cluster-size fat32-in-memory)))
         (- (length contents)))
        :initial-element (code-char 0))))
     0)))
  :hints
  (("goal" :in-theory (enable lower-bounded-integer-listp
                              place-contents)
    :use m1-fs-to-fat32-in-memory-inversion-lemma-67)))

(defthm
  fat32-in-memory-to-m1-fs-helper-of-place-contents
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (stringp contents)
        (integerp first-cluster)
        (>= first-cluster *ms-first-data-cluster*)
        (equal (mv-nth 3
                       (fat32-in-memory-to-m1-fs-helper
                        fat32-in-memory
                        dir-contents entry-limit))
               0)
        (not-intersectp-list
         (list first-cluster)
         (mv-nth 2
                 (fat32-in-memory-to-m1-fs-helper
                  fat32-in-memory
                  dir-contents entry-limit))))
   (equal
    (fat32-in-memory-to-m1-fs-helper
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     dir-contents entry-limit)
    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                     dir-contents entry-limit)))
  :hints
  (("goal"
    :in-theory
    (e/d nil
         (dir-ent-fix
          (:definition get-clusterchain-contents)
          (:rewrite by-slice-you-mean-the-whole-cake-2)))
    :induct
    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                     dir-contents entry-limit)
    :expand
    ((fat32-in-memory-to-m1-fs-helper
      (mv-nth
       0
       (place-contents fat32-in-memory dir-ent
                       contents file-length first-cluster))
      dir-contents entry-limit)
     (:free (y)
            (intersectp-equal (list first-cluster)
                              y))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-71
  (implies
   (and
    (equal
     (fat32-entry-mask
      (fati
       (nth
        0
        (find-n-free-clusters (effective-fat fat32-in-memory)
                              1))
       fat32-in-memory))
     0)
    (not (equal (fat32-entry-mask (fati x fat32-in-memory))
                0)))
   (not
    (equal
     x
     (nth '0
          (find-n-free-clusters (effective-fat fat32-in-memory)
                                1))))))

(thm
  (implies
   (and (natp x)
        (not (equal (fat32-entry-mask (fati x fat32-in-memory))
                    0)))
   (not-intersectp-list
    (list x)
    (mv-nth 2
            (fat32-in-memory-to-m1-fs-helper
             (mv-nth 0
                     (m1-fs-to-fat32-in-memory-helper
                      fat32-in-memory
                      fs current-dir-first-cluster))
             dir-contents entry-limit))))
  :hints
  (("goal"
    :in-theory (disable m1-fs-to-fat32-in-memory-helper)
    :induct (fat32-in-memory-to-m1-fs-helper
             (mv-nth 0
                     (m1-fs-to-fat32-in-memory-helper
                      fat32-in-memory
                      fs current-dir-first-cluster))
             dir-contents entry-limit)
    :expand ((:free (y) (intersectp-equal nil y))
             (:free (y)
                    (intersectp-equal (list x) y))))))

(local
 (defthm
   m1-fs-to-fat32-in-memory-inversion-lemma-73
   (implies
    (compliant-fat32-in-memoryp fat32-in-memory)
    (equal
     (nfix (binary-+ '2
                     (count-of-clusters fat32-in-memory)))
     (binary-+ '2
               (count-of-clusters fat32-in-memory))))))

(local
 (defthm m1-fs-to-fat32-in-memory-inversion-lemma-74
   (equal (car (find-n-free-clusters fa-table n))
          (nth 0 (find-n-free-clusters fa-table n)))))

(local
 (defthm
   m1-fs-to-fat32-in-memory-inversion-lemma-75
   (implies (compliant-fat32-in-memoryp fat32-in-memory)
            (iff (< (* (cluster-size fat32-in-memory)
                       (len x))
                    32)
                 (atom x)))
   :hints
   (("goal"
     :in-theory
     (disable
      (:linear compliant-fat32-in-memoryp-correctness-1))
     :use (:linear compliant-fat32-in-memoryp-correctness-1)))))

(local
 (defthm
   m1-fs-to-fat32-in-memory-inversion-lemma-76
   (implies (compliant-fat32-in-memoryp fat32-in-memory)
            (< '0 (cluster-size fat32-in-memory)))
   :hints
   (("goal"
     :in-theory
     (disable
      (:linear compliant-fat32-in-memoryp-correctness-1))
     :use (:linear compliant-fat32-in-memoryp-correctness-1)))))

(local
 (defthm m1-fs-to-fat32-in-memory-inversion-lemma-77
   (implies (compliant-fat32-in-memoryp fat32-in-memory)
            (iff (< (+ -64
                       (* (cluster-size fat32-in-memory)
                          (len x)))
                    0)
                 (atom x)))))

(skip-proofs
 (defthmd lemma-1-4
   (implies
    (and
     (consp fs)
     (zp (mv-nth 2
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
     (not (or (equal (car (car fs)) ".          ")
              (equal (car (car fs)) "..         ")))
     (<=
      1
      (len
       (stobj-find-n-free-clusters
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster))
        1)))
     (<
      (nth
       0
       (stobj-find-n-free-clusters
        (mv-nth 0
                (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster))
        1))
      (fat-length fat32-in-memory))
     (not (m1-regular-file-p (cdr (car fs))))
     (zp
      (mv-nth
       2
       (m1-fs-to-fat32-in-memory-helper
        (stobj-set-indices-in-fa-table
         (mv-nth 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster))
         (stobj-find-n-free-clusters
          (mv-nth 0
                  (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                   current-dir-first-cluster))
          1)
         '(268435455))
        (m1-file->contents (cdr (car fs)))
        (nth
         0
         (stobj-find-n-free-clusters
          (mv-nth 0
                  (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                   current-dir-first-cluster))
          1)))))
     (implies
      (and (compliant-fat32-in-memoryp fat32-in-memory)
           (equal (mod 2097152 (cluster-size fat32-in-memory))
                  0)
           (m1-file-alist-p (cdr fs))
           (m1-bounded-file-alist-p (cdr fs))
           (m1-file-no-dups-p (cdr fs))
           (fat32-masked-entry-p current-dir-first-cluster)
           (<= 2 current-dir-first-cluster)
           (< current-dir-first-cluster
              (+ 2 (count-of-clusters fat32-in-memory)))
           (<= (+ 2 (count-of-clusters fat32-in-memory))
               (fat-length fat32-in-memory)))
      (let
          ((mv (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster))
           (fs (cdr fs)))
        (let
            ((fat32-in-memory (mv-nth 0 mv))
             (dir-ent-list (mv-nth 1 mv))
             (error-code (mv-nth 2 mv)))
          (implies
           (zp error-code)
           (and (equal (mv-nth 3
                               (fat32-in-memory-to-m1-fs-helper
                                fat32-in-memory (flatten dir-ent-list)
                                (m1-entry-count fs)))
                       0)
                (m1-dir-equiv (mv-nth 0
                                      (fat32-in-memory-to-m1-fs-helper
                                       fat32-in-memory (flatten dir-ent-list)
                                       (m1-entry-count fs)))
                              fs))))))
     (implies
      (and
       (compliant-fat32-in-memoryp
        (stobj-set-indices-in-fa-table
         (mv-nth 0
                 (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster))
         (stobj-find-n-free-clusters
          (mv-nth 0
                  (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                   current-dir-first-cluster))
          1)
         '(268435455)))
       (m1-directory-file-p (m1-file-fix (cdr (car fs))))
       (m1-bounded-file-alist-p (m1-file->contents (cdr (car fs))))
       (m1-file-no-dups-p (m1-file->contents (cdr (car fs))))
       (fat32-masked-entry-p
        (nth
         0
         (stobj-find-n-free-clusters
          (mv-nth 0
                  (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                   current-dir-first-cluster))
          1)))
       (<=
        2
        (nth
         0
         (stobj-find-n-free-clusters
          (mv-nth 0
                  (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                   current-dir-first-cluster))
          1)))
       (<
        (nth
         0
         (stobj-find-n-free-clusters
          (mv-nth 0
                  (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                   current-dir-first-cluster))
          1))
        (+ 2 (count-of-clusters fat32-in-memory)))
       (<= (+ 2 (count-of-clusters fat32-in-memory))
           (fat-length fat32-in-memory)))
      (let
          ((mv
            (m1-fs-to-fat32-in-memory-helper
             (stobj-set-indices-in-fa-table
              (mv-nth 0
                      (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                       current-dir-first-cluster))
              (stobj-find-n-free-clusters
               (mv-nth 0
                       (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                        current-dir-first-cluster))
               1)
              '(268435455))
             (m1-file->contents (cdr (car fs)))
             (nth
              0
              (stobj-find-n-free-clusters
               (mv-nth 0
                       (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                        current-dir-first-cluster))
               1))))
           (fs (m1-file->contents (cdr (car fs)))))
        (let
            ((fat32-in-memory (mv-nth 0 mv))
             (dir-ent-list (mv-nth 1 mv))
             (error-code (mv-nth 2 mv)))
          (implies
           (zp error-code)
           (and (equal (mv-nth 3
                               (fat32-in-memory-to-m1-fs-helper
                                fat32-in-memory (flatten dir-ent-list)
                                (m1-entry-count fs)))
                       0)
                (m1-dir-equiv (mv-nth 0
                                      (fat32-in-memory-to-m1-fs-helper
                                       fat32-in-memory (flatten dir-ent-list)
                                       (m1-entry-count fs)))
                              fs))))))
     (compliant-fat32-in-memoryp fat32-in-memory)
     (m1-file-alist-p fs)
     (m1-bounded-file-alist-p fs)
     (m1-file-no-dups-p fs)
     (fat32-masked-entry-p current-dir-first-cluster)
     (<= 2 current-dir-first-cluster)
     (< current-dir-first-cluster
        (+ 2 (count-of-clusters fat32-in-memory)))
     (<= (+ 2 (count-of-clusters fat32-in-memory))
         (fat-length fat32-in-memory)))
    (mv-let
      (fat32-in-memory dir-ent-list error-code)
      (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                       fs current-dir-first-cluster)
      (or
       (not (zp error-code))
       (and
        (equal
         (mv-nth
          3
          (fat32-in-memory-to-m1-fs-helper fat32-in-memory (flatten dir-ent-list)
                                           (m1-entry-count fs)))
         0)
        (m1-dir-equiv
         (mv-nth
          0
          (fat32-in-memory-to-m1-fs-helper fat32-in-memory (flatten dir-ent-list)
                                           (m1-entry-count fs)))
         fs)))))
   :hints (("goal" :do-not-induct t
            :in-theory (disable
                        nth floor mod
                        (:definition get-clusterchain-contents)
                        (:definition m1-fs-to-fat32-in-memory-helper))
            :expand
            ((m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                              fs current-dir-first-cluster)))
           ("subgoal 9"
            :in-theory (disable floor mod
                        (:REWRITE FAT32-IN-MEMORY-TO-M1-FS-HELPER-OF-PLACE-CONTENTS)
                        (:definition m1-fs-to-fat32-in-memory-helper))
            :use
            (:instance
             (:REWRITE FAT32-IN-MEMORY-TO-M1-FS-HELPER-OF-PLACE-CONTENTS)
             (ENTRY-LIMIT
              (+ 1 (M1-ENTRY-COUNT (CDR FS))
                 (M1-ENTRY-COUNT (M1-FILE->CONTENTS (CDR (CAR FS))))))
             (DIR-CONTENTS
              (APPEND
               (DIR-ENT-INSTALL-DIRECTORY-BIT
                (DIR-ENT-SET-FILENAME
                 (DIR-ENT-SET-FIRST-CLUSTER-FILE-SIZE
                  (M1-FILE->DIR-ENT (CDR (CAR FS)))
                  (NTH
                   0
                   (FIND-N-FREE-CLUSTERS
                    (EFFECTIVE-FAT
                     (MV-NTH 0
                             (M1-FS-TO-FAT32-IN-MEMORY-HELPER
                              FAT32-IN-MEMORY (CDR FS)
                              CURRENT-DIR-FIRST-CLUSTER)))
                    1))
                  0)
                 (CAR (CAR FS)))
                T)
               (FLATTEN (MV-NTH 1
                                (M1-FS-TO-FAT32-IN-MEMORY-HELPER
                                 FAT32-IN-MEMORY (CDR FS)
                                 CURRENT-DIR-FIRST-CLUSTER)))))
             (FIRST-CLUSTER
              (NTH
               0
               (FIND-N-FREE-CLUSTERS
                (EFFECTIVE-FAT (MV-NTH 0
                                       (M1-FS-TO-FAT32-IN-MEMORY-HELPER
                                        FAT32-IN-MEMORY (CDR FS)
                                        CURRENT-DIR-FIRST-CLUSTER)))
                1)))
             (FILE-LENGTH 0)
             (CONTENTS
              (NATS=>STRING
               (APPEND
                (DIR-ENT-SET-FILENAME
                 (DIR-ENT-SET-FIRST-CLUSTER-FILE-SIZE
                  (M1-FILE->DIR-ENT (CDR (CAR FS)))
                  (NTH
                   0
                   (FIND-N-FREE-CLUSTERS
                    (EFFECTIVE-FAT
                     (MV-NTH 0
                             (M1-FS-TO-FAT32-IN-MEMORY-HELPER
                              FAT32-IN-MEMORY (CDR FS)
                              CURRENT-DIR-FIRST-CLUSTER)))
                    1))
                  0)
                 ".          ")
                (DIR-ENT-SET-FILENAME
                 (DIR-ENT-SET-FIRST-CLUSTER-FILE-SIZE
                  (M1-FILE->DIR-ENT (CDR (CAR FS)))
                  CURRENT-DIR-FIRST-CLUSTER 0)
                 "..         ")
                (FLATTEN
                 (MV-NTH
                  1
                  (M1-FS-TO-FAT32-IN-MEMORY-HELPER
                   (STOBJ-SET-INDICES-IN-FA-TABLE
                    (MV-NTH 0
                            (M1-FS-TO-FAT32-IN-MEMORY-HELPER
                             FAT32-IN-MEMORY (CDR FS)
                             CURRENT-DIR-FIRST-CLUSTER))
                    (FIND-N-FREE-CLUSTERS
                     (EFFECTIVE-FAT
                      (MV-NTH 0
                              (M1-FS-TO-FAT32-IN-MEMORY-HELPER
                               FAT32-IN-MEMORY (CDR FS)
                               CURRENT-DIR-FIRST-CLUSTER)))
                     1)
                    '(268435455))
                   (M1-FILE->CONTENTS (CDR (CAR FS)))
                   (NTH
                    0
                    (FIND-N-FREE-CLUSTERS
                     (EFFECTIVE-FAT
                      (MV-NTH 0
                              (M1-FS-TO-FAT32-IN-MEMORY-HELPER
                               FAT32-IN-MEMORY (CDR FS)
                               CURRENT-DIR-FIRST-CLUSTER)))
                     1))))))))
             (DIR-ENT (M1-FILE->DIR-ENT (CDR (CAR FS))))
             (FAT32-IN-MEMORY
              (MV-NTH
               0
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER
                (STOBJ-SET-INDICES-IN-FA-TABLE
                 (MV-NTH 0
                         (M1-FS-TO-FAT32-IN-MEMORY-HELPER
                          FAT32-IN-MEMORY (CDR FS)
                          CURRENT-DIR-FIRST-CLUSTER))
                 (FIND-N-FREE-CLUSTERS
                  (EFFECTIVE-FAT
                   (MV-NTH 0
                           (M1-FS-TO-FAT32-IN-MEMORY-HELPER
                            FAT32-IN-MEMORY (CDR FS)
                            CURRENT-DIR-FIRST-CLUSTER)))
                  1)
                 '(268435455))
                (M1-FILE->CONTENTS (CDR (CAR FS)))
                (NTH 0
                     (FIND-N-FREE-CLUSTERS
                      (EFFECTIVE-FAT
                       (MV-NTH 0
                               (M1-FS-TO-FAT32-IN-MEMORY-HELPER
                                FAT32-IN-MEMORY (CDR FS)
                                CURRENT-DIR-FIRST-CLUSTER)))
                      1)))))))
           ("subgoal 2"
            :expand
            ((:free (x y fat32-in-memory entry-limit)
                    (fat32-in-memory-to-m1-fs-helper fat32-in-memory
                                                     (append x y) entry-limit))
             (stobj-set-indices-in-fa-table
              (mv-nth '0
                      (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                       current-dir-first-cluster))
              (find-n-free-clusters
               (effective-fat
                (mv-nth '0
                        (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                         current-dir-first-cluster)))
               '1)
              '(268435455))
             (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                              nil current-dir-first-cluster))))))

(defthm
  m1-fs-to-fat32-in-memory-inversion-lemma-70
 (implies
  (and
   (compliant-fat32-in-memoryp fat32-in-memory)
   (m1-file-alist-p fs)
   (m1-bounded-file-alist-p fs)
   (m1-file-no-dups-p fs)
   (fat32-masked-entry-p current-dir-first-cluster)
   (<= *ms-first-data-cluster* current-dir-first-cluster)
   (< current-dir-first-cluster
      (+ *ms-first-data-cluster*
         (count-of-clusters fat32-in-memory)))
   (<= (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory))
       (fat-length fat32-in-memory)))
  (b*
      (((mv fat32-in-memory dir-ent-list error-code)
        (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                         fs current-dir-first-cluster)))
    (implies
     (zp error-code)
     (and
      (equal
       (mv-nth
        3
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory
         (flatten dir-ent-list)
         (m1-entry-count fs)))
       0)
      (m1-dir-equiv
       (mv-nth
        0
        (fat32-in-memory-to-m1-fs-helper
         fat32-in-memory
         (flatten dir-ent-list)
         (m1-entry-count fs)))
       fs)))))
 :hints (("Goal" :induct
          (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                           fs current-dir-first-cluster)
          :in-theory (disable
                      floor
                      mod
                      nth
                      (:rewrite make-clusters-correctness-1 . 1)
                      (:rewrite nth-of-nats=>chars)
                      (:rewrite by-slice-you-mean-the-whole-cake-2)))
         ("subgoal *1/4" :use lemma-1-4)
         ("subgoal *1/3" :use lemma-1-3)))

(local
 (defun-nx induction-scheme (CURRENT-DIR-FIRST-CLUSTER
                             FAT32-IN-MEMORY FS reverse-dir-ent-list)
   (declare (xargs :hints (("Goal" :in-theory (enable
                                               M1-FILE->CONTENTS
                                               m1-file-contents-fix)) )))
 (cond
  ((NOT (CONSP FS))
   (list 1))
 ((AND
   (CONSP FS)
   (NOT
    (ZP
       (MV-NTH 2
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                CURRENT-DIR-FIRST-CLUSTER)))))
  (induction-scheme CURRENT-DIR-FIRST-CLUSTER
                    FAT32-IN-MEMORY (CDR FS)
                    (append reverse-dir-ent-list (list (m1-file->dir-ent (cdar fs))))))
 ((AND
   (CONSP FS)
   (ZP (MV-NTH 2
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                CURRENT-DIR-FIRST-CLUSTER)))
   (NOT (OR (EQUAL (CAR (CAR FS)) ".          ")
            (EQUAL (CAR (CAR FS)) "..         ")))
   (<=
    1
    (LEN
     (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1)))
   (<=
    (FAT-LENGTH
        (MV-NTH 0
                (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                 CURRENT-DIR-FIRST-CLUSTER)))
    (NTH
     0
     (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1))))
  (induction-scheme CURRENT-DIR-FIRST-CLUSTER
                    FAT32-IN-MEMORY (CDR FS)
                    (append reverse-dir-ent-list (list (m1-file->dir-ent (cdar fs))))))
 ((AND
   (CONSP FS)
   (ZP (MV-NTH 2
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                CURRENT-DIR-FIRST-CLUSTER)))
   (NOT (OR (EQUAL (CAR (CAR FS)) ".          ")
            (EQUAL (CAR (CAR FS)) "..         ")))
   (<=
    1
    (LEN
     (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1)))
   (<
    (NTH
     0
     (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1))
    (FAT-LENGTH
       (MV-NTH 0
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                CURRENT-DIR-FIRST-CLUSTER))))
   (NOT (M1-REGULAR-FILE-P (CDR (CAR FS))))
   (NOT
    (ZP
     (MV-NTH
      2
      (M1-FS-TO-FAT32-IN-MEMORY-HELPER
       (UPDATE-FATI
        (NTH
         0
         (STOBJ-FIND-N-FREE-CLUSTERS
            (MV-NTH
                 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
            1))
        268435455
        (MV-NTH 0
                (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                 CURRENT-DIR-FIRST-CLUSTER)))
       (M1-FILE->CONTENTS (CDR (CAR FS)))
       (NTH
        0
        (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1)))))))
  (append
   (induction-scheme CURRENT-DIR-FIRST-CLUSTER
                     FAT32-IN-MEMORY (CDR FS)
                     (append reverse-dir-ent-list (list (m1-file->dir-ent (cdar fs)))))
   (induction-scheme
    (NTH
     0
     (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1))
    (UPDATE-FATI
     (NTH
      0
      (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1))
     268435455
     (MV-NTH 0
             (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                              CURRENT-DIR-FIRST-CLUSTER)))
    (M1-FILE->CONTENTS (CDR (CAR FS)))
    nil)))
 ((AND
   (CONSP FS)
   (ZP (MV-NTH 2
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                CURRENT-DIR-FIRST-CLUSTER)))
   (NOT (OR (EQUAL (CAR (CAR FS)) ".          ")
            (EQUAL (CAR (CAR FS)) "..         ")))
   (<=
    1
    (LEN
     (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1)))
   (<
    (NTH
     0
     (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1))
    (FAT-LENGTH
       (MV-NTH 0
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                CURRENT-DIR-FIRST-CLUSTER))))
   (NOT (M1-REGULAR-FILE-P (CDR (CAR FS))))
   (ZP
    (MV-NTH
     2
     (M1-FS-TO-FAT32-IN-MEMORY-HELPER
      (UPDATE-FATI
       (NTH
        0
        (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1))
       268435455
       (MV-NTH 0
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                CURRENT-DIR-FIRST-CLUSTER)))
      (M1-FILE->CONTENTS (CDR (CAR FS)))
      (NTH
       0
       (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1))))))
  (append
   (induction-scheme CURRENT-DIR-FIRST-CLUSTER
                     FAT32-IN-MEMORY (CDR FS)
                     (append reverse-dir-ent-list (list (m1-file->dir-ent (cdar fs)))))
   (induction-scheme
    (NTH
     0
     (STOBJ-FIND-N-FREE-CLUSTERS
      (MV-NTH 0
              (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                               CURRENT-DIR-FIRST-CLUSTER))
      1))
    (UPDATE-FATI
     (NTH
      0
      (STOBJ-FIND-N-FREE-CLUSTERS
       (MV-NTH 0
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                CURRENT-DIR-FIRST-CLUSTER))
       1))
     268435455
     (MV-NTH 0
             (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                              CURRENT-DIR-FIRST-CLUSTER)))
    (M1-FILE->CONTENTS (CDR (CAR FS)))
    nil)))
 ((AND
   (CONSP FS)
   (ZP (MV-NTH 2
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                CURRENT-DIR-FIRST-CLUSTER)))
   (NOT (OR (EQUAL (CAR (CAR FS)) ".          ")
            (EQUAL (CAR (CAR FS)) "..         ")))
   (<=
    1
    (LEN
     (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1)))
   (<
    (NTH
     0
     (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1))
    (FAT-LENGTH
       (MV-NTH 0
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                CURRENT-DIR-FIRST-CLUSTER))))
   (M1-REGULAR-FILE-P (CDR (CAR FS)))
   (equal (len (explode (m1-file->contents (cdr (car fs)))))
          0))
  (induction-scheme CURRENT-DIR-FIRST-CLUSTER
                    FAT32-IN-MEMORY (CDR FS)
                    (append
                     reverse-dir-ent-list
                     (list
                      (DIR-ENT-INSTALL-DIRECTORY-BIT
                       (DIR-ENT-SET-FILENAME (DIR-ENT-SET-FIRST-CLUSTER-FILE-SIZE
                                              (M1-FILE->DIR-ENT (CDR (CAR FS)))
                                              0 0)
                                             (CAR (CAR FS)))
                       NIL)))))
 ((AND
   (CONSP FS)
   (ZP (MV-NTH 2
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                CURRENT-DIR-FIRST-CLUSTER)))
   (NOT (OR (EQUAL (CAR (CAR FS)) ".          ")
            (EQUAL (CAR (CAR FS)) "..         ")))
   (<=
    1
    (LEN
     (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1)))
   (<
    (NTH
     0
     (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1))
    (FAT-LENGTH
       (MV-NTH 0
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                CURRENT-DIR-FIRST-CLUSTER))))
   (M1-REGULAR-FILE-P (CDR (CAR FS)))
   (not (equal (len (explode (m1-file->contents (cdr (car fs)))))
               0)))
  (induction-scheme CURRENT-DIR-FIRST-CLUSTER
                    FAT32-IN-MEMORY (CDR FS)
                    (append
                     reverse-dir-ent-list
                     (list
                      (dir-ent-install-directory-bit
                       (dir-ent-set-filename
                        (dir-ent-set-first-cluster-file-size
                         (m1-file->dir-ent (cdr (car fs)))
                         (nth
                          0
                          (find-n-free-clusters
                           (effective-fat
                            (mv-nth
                             0
                             (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                              current-dir-first-cluster)))
                           1))
                         (len (explode (m1-file->contents (cdr (car fs))))))
                        (car (car fs)))
                       nil)))))
 ((AND
   (CONSP FS)
   (ZP (MV-NTH 2
               (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                CURRENT-DIR-FIRST-CLUSTER)))
   (NOT (OR (EQUAL (CAR (CAR FS)) ".          ")
            (EQUAL (CAR (CAR FS)) "..         ")))
   (<
    (LEN
     (STOBJ-FIND-N-FREE-CLUSTERS
         (MV-NTH 0
                 (M1-FS-TO-FAT32-IN-MEMORY-HELPER FAT32-IN-MEMORY (CDR FS)
                                                  CURRENT-DIR-FIRST-CLUSTER))
         1))
    1))
  (induction-scheme CURRENT-DIR-FIRST-CLUSTER
                    FAT32-IN-MEMORY (CDR FS)
                    (append reverse-dir-ent-list (list (m1-file->dir-ent (cdar fs))))))
 ((and
   (consp fs)
   (zp (mv-nth 2
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
   (or (equal (car (car fs)) ".          ")
       (equal (car (car fs)) "..         ")))
  (induction-scheme current-dir-first-cluster
                    fat32-in-memory (cdr fs)
                    reverse-dir-ent-list))
 ;; Unreachable
 (t nil))))

(thm
 (implies
  (and
   (compliant-fat32-in-memoryp fat32-in-memory)
   (equal (data-region-length fat32-in-memory)
          (count-of-clusters fat32-in-memory))
   (<= (+ (count-of-clusters fat32-in-memory)
          2)
       (fat-length fat32-in-memory))
   (m1-file-alist-p fs)
   (m1-bounded-file-alist-p fs)
   (m1-file-no-dups-p fs)
   (fat32-masked-entry-p current-dir-first-cluster)
   (<= *ms-first-data-cluster* current-dir-first-cluster)
   (< current-dir-first-cluster
      (+ *ms-first-data-cluster*
         (count-of-clusters fat32-in-memory)))
   (<= (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory))
       (fat-length fat32-in-memory)))
  (b*
      ((cluster-size (cluster-size fat32-in-memory))
       ((mv fat32-in-memory dir-ent-list error-code)
        (m1-fs-to-fat32-in-memory-helper fat32-in-memory
                                         fs current-dir-first-cluster))
       (effective-fat (effective-fat fat32-in-memory)))
    (implies
     (zp error-code)
     (m1-dir-equiv
      (mv-nth
       0
       (fat32-in-memory-to-m1-fs-helper
        (stobj-set-indices-in-fa-table
         (stobj-set-clusters
          (make-clusters
           (nats=>string
            (flatten (append reverse-dir-ent-list dir-ent-list)))
           cluster-size)
          (cons
           current-dir-first-cluster
           (find-n-free-clusters
            (update-nth
             current-dir-first-cluster
             268435455
             effective-fat)
            (+
             -1
             (len
              (make-clusters
               (nats=>string
                (flatten (append reverse-dir-ent-list dir-ent-list)))
               cluster-size)))))
          (update-fati
           current-dir-first-cluster
           *ms-end-of-clusterchain* fat32-in-memory))
         (cons
          current-dir-first-cluster
          (find-n-free-clusters
           (update-nth
            current-dir-first-cluster
            268435455
            effective-fat)
           (+
            -1
            (len
             (make-clusters
              (nats=>string
               (flatten (append reverse-dir-ent-list dir-ent-list)))
              cluster-size)))))
         (append
          (find-n-free-clusters
           (update-nth
            current-dir-first-cluster
            268435455
            effective-fat)
           (+
            -1
            (len
             (make-clusters
              (nats=>string
               (flatten (append reverse-dir-ent-list dir-ent-list)))
              cluster-size))))
          '(268435455)))
        (append
         (flatten (append reverse-dir-ent-list dir-ent-list))
         (make-list-ac (+ 2097152 (- (* 32 (len fs))))
                       0 nil))
        (m1-entry-count fs)))
      fs))))
 :hints (("Goal" :induct
          (induction-scheme CURRENT-DIR-FIRST-CLUSTER
                            FAT32-IN-MEMORY FS reverse-dir-ent-list)
          :in-theory (disable floor mod
                              (:REWRITE BY-SLICE-YOU-MEAN-THE-WHOLE-CAKE-2)
                              (:DEFINITION GET-CLUSTERCHAIN-CONTENTS)
                              (:REWRITE NTH-OF-NATS=>CHARS)
                              nth
                              (:DEFINITION FAT32-IN-MEMORYP)
                              (:DEFINITION BINARY-APPEND)
                              (:REWRITE CONSP-OF-NTHCDR)
                              (:REWRITE M1-DIRECTORY-FILE-P-CORRECTNESS-1)
                              (:REWRITE NTHCDR-OF-APPEND)
                              (:REWRITE TAKE-OF-APPEND)))
         ("Subgoal *1/7.2'" :in-theory (e/d
                                        (place-contents-regular-file)
                                        (floor mod
                                               (:REWRITE BY-SLICE-YOU-MEAN-THE-WHOLE-CAKE-2)
                                               (:DEFINITION GET-CLUSTERCHAIN-CONTENTS)
                                               (:REWRITE NTH-OF-NATS=>CHARS)
                                               nth
                                               (:DEFINITION FAT32-IN-MEMORYP)
                                               (:DEFINITION BINARY-APPEND)
                                               (:REWRITE CONSP-OF-NTHCDR)
                                               (:REWRITE M1-DIRECTORY-FILE-P-CORRECTNESS-1)
                                               (:REWRITE NTHCDR-OF-APPEND)
                                               (:REWRITE TAKE-OF-APPEND)))
           :expand
           (fat32-in-memory-to-m1-fs-helper
            (stobj-set-indices-in-fa-table
             (stobj-set-clusters
              (make-clusters
               (nats=>string
                (append
                 (flatten reverse-dir-ent-list)
                 (dir-ent-install-directory-bit
                  (dir-ent-set-filename
                   (dir-ent-set-first-cluster-file-size
                    (m1-file->dir-ent (cdr (car fs)))
                    (nth
                     0
                     (find-n-free-clusters
                      (effective-fat
                       (mv-nth
                        0
                        (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                         current-dir-first-cluster)))
                      1))
                    (len (explode (m1-file->contents (cdr (car fs))))))
                   (car (car fs)))
                  nil)
                 (flatten
                  (mv-nth
                   1
                   (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                    current-dir-first-cluster)))))
               (cluster-size fat32-in-memory))
              (cons
               current-dir-first-cluster
               (find-n-free-clusters
                (update-nth
                 current-dir-first-cluster 268435455
                 (effective-fat
                  (mv-nth
                   0
                   (place-contents
                    (update-fati
                     (nth
                      0
                      (find-n-free-clusters
                       (effective-fat (mv-nth 0
                                              (m1-fs-to-fat32-in-memory-helper
                                               fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
                       1))
                     268435455
                     (mv-nth
                      0
                      (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                       current-dir-first-cluster)))
                    (m1-file->dir-ent (cdr (car fs)))
                    (m1-file->contents (cdr (car fs)))
                    (len (explode (m1-file->contents (cdr (car fs)))))
                    (nth
                     0
                     (find-n-free-clusters
                      (effective-fat
                       (mv-nth
                        0
                        (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                         current-dir-first-cluster)))
                      1))))))
                (+
                 -1
                 (len
                  (make-clusters
                   (nats=>string
                    (append
                     (flatten reverse-dir-ent-list)
                     (dir-ent-install-directory-bit
                      (dir-ent-set-filename
                       (dir-ent-set-first-cluster-file-size
                        (m1-file->dir-ent (cdr (car fs)))
                        (nth
                         0
                         (find-n-free-clusters
                          (effective-fat (mv-nth 0
                                                 (m1-fs-to-fat32-in-memory-helper
                                                  fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
                          1))
                        (len (explode (m1-file->contents (cdr (car fs))))))
                       (car (car fs)))
                      nil)
                     (flatten (mv-nth 1
                                      (m1-fs-to-fat32-in-memory-helper
                                       fat32-in-memory (cdr fs)
                                       current-dir-first-cluster)))))
                   (cluster-size fat32-in-memory))))))
              (update-fati
               current-dir-first-cluster 268435455
               (mv-nth
                0
                (place-contents
                 (update-fati
                  (nth
                   0
                   (find-n-free-clusters
                    (effective-fat
                     (mv-nth
                      0
                      (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                       current-dir-first-cluster)))
                    1))
                  268435455
                  (mv-nth
                   0
                   (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                    current-dir-first-cluster)))
                 (m1-file->dir-ent (cdr (car fs)))
                 (m1-file->contents (cdr (car fs)))
                 (len (explode (m1-file->contents (cdr (car fs)))))
                 (nth
                  0
                  (find-n-free-clusters
                   (effective-fat
                    (mv-nth
                     0
                     (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                      current-dir-first-cluster)))
                   1))))))
             (cons
              current-dir-first-cluster
              (find-n-free-clusters
               (update-nth
                current-dir-first-cluster 268435455
                (effective-fat
                 (mv-nth
                  0
                  (place-contents
                   (update-fati
                    (nth
                     0
                     (find-n-free-clusters
                      (effective-fat
                       (mv-nth
                        0
                        (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                         current-dir-first-cluster)))
                      1))
                    268435455
                    (mv-nth
                     0
                     (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                      current-dir-first-cluster)))
                   (m1-file->dir-ent (cdr (car fs)))
                   (m1-file->contents (cdr (car fs)))
                   (len (explode (m1-file->contents (cdr (car fs)))))
                   (nth
                    0
                    (find-n-free-clusters
                     (effective-fat
                      (mv-nth
                       0
                       (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                        current-dir-first-cluster)))
                     1))))))
               (+
                -1
                (len
                 (make-clusters
                  (nats=>string
                   (append
                    (flatten reverse-dir-ent-list)
                    (dir-ent-install-directory-bit
                     (dir-ent-set-filename
                      (dir-ent-set-first-cluster-file-size
                       (m1-file->dir-ent (cdr (car fs)))
                       (nth
                        0
                        (find-n-free-clusters
                         (effective-fat (mv-nth 0
                                                (m1-fs-to-fat32-in-memory-helper
                                                 fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
                         1))
                       (len (explode (m1-file->contents (cdr (car fs))))))
                      (car (car fs)))
                     nil)
                    (flatten
                     (mv-nth
                      1
                      (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                       current-dir-first-cluster)))))
                  (cluster-size fat32-in-memory))))))
             (append
              (find-n-free-clusters
               (update-nth
                current-dir-first-cluster 268435455
                (effective-fat
                 (mv-nth
                  0
                  (place-contents
                   (update-fati
                    (nth
                     0
                     (find-n-free-clusters
                      (effective-fat
                       (mv-nth
                        0
                        (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                         current-dir-first-cluster)))
                      1))
                    268435455
                    (mv-nth
                     0
                     (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                      current-dir-first-cluster)))
                   (m1-file->dir-ent (cdr (car fs)))
                   (m1-file->contents (cdr (car fs)))
                   (len (explode (m1-file->contents (cdr (car fs)))))
                   (nth
                    0
                    (find-n-free-clusters
                     (effective-fat
                      (mv-nth
                       0
                       (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                        current-dir-first-cluster)))
                     1))))))
               (+
                -1
                (len
                 (make-clusters
                  (nats=>string
                   (append
                    (flatten reverse-dir-ent-list)
                    (dir-ent-install-directory-bit
                     (dir-ent-set-filename
                      (dir-ent-set-first-cluster-file-size
                       (m1-file->dir-ent (cdr (car fs)))
                       (nth
                        0
                        (find-n-free-clusters
                         (effective-fat (mv-nth 0
                                                (m1-fs-to-fat32-in-memory-helper
                                                 fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
                         1))
                       (len (explode (m1-file->contents (cdr (car fs))))))
                      (car (car fs)))
                     nil)
                    (flatten
                     (mv-nth
                      1
                      (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                       current-dir-first-cluster)))))
                  (cluster-size fat32-in-memory)))))
              '(268435455)))
            (append
             (flatten reverse-dir-ent-list)
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size
                (m1-file->dir-ent (cdr (car fs)))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth
                    0
                    (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                     current-dir-first-cluster)))
                  1))
                (len (explode (m1-file->contents (cdr (car fs))))))
               (car (car fs)))
              nil)
             (flatten
              (mv-nth 1
                      (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)
                                                       current-dir-first-cluster)))
             (make-list-ac (+ 2097120 (- (* 32 (len (cdr fs)))))
                           0 nil))
            (+ 1 (m1-entry-count (cdr fs)))))))

(encapsulate
  ()

  (local
   (in-theory
    (disable
     floor
     (:DEFINITION NTH)
     (:REWRITE NTH-OF-STRING=>NATS)
     (:REWRITE BY-SLICE-YOU-MEAN-THE-WHOLE-CAKE-2))))

  (defthm
    m1-fs-to-fat32-in-memory-inversion
    (implies (and
              (compliant-fat32-in-memoryp fat32-in-memory)
              (equal (* (bpb_fatsz32 fat32-in-memory)
                        1/4 (bpb_bytspersec fat32-in-memory))
                     (fat-length fat32-in-memory))
              (<= (+ (count-of-clusters fat32-in-memory) *ms-first-data-cluster*)
                  (fat-length fat32-in-memory))
              (equal (data-region-length fat32-in-memory)
                     (count-of-clusters fat32-in-memory))
              (m1-file-alist-p fs)
              (m1-bounded-file-alist-p fs)
              (atom (assoc-equal *current-dir-fat32-name* fs))
              (atom (assoc-equal *parent-dir-fat32-name* fs)))
             (b*
                 (((mv fat32-in-memory errno)
                   (m1-fs-to-fat32-in-memory
                    fat32-in-memory fs)))
               (implies
                (zp errno)
                (m1-dir-equiv
                 (FAT32-IN-MEMORY-TO-M1-FS fat32-in-memory)
                 fs))))
    :hints (("Goal" :do-not-induct t)
            ("Subgoal 2.2'"
             :expand ((:free (fat32-in-memory)
                             (fat32-in-memory-to-m1-fs
                              fat32-in-memory)))
             :in-theory
             (e/d (lower-bounded-integer-listp)
                  ((:LINEAR LEN-WHEN-M1-BOUNDED-FILE-ALIST-P . 2)
                   (:LINEAR MAKE-CLUSTERS-CORRECTNESS-2)))
             :use
             ((:instance
               (:linear make-clusters-correctness-2)
               (text
                (nats=>string
                 (flatten
                  (mv-nth
                   1
                   (m1-fs-to-fat32-in-memory-helper
                    (stobj-set-indices-in-fa-table
                     fat32-in-memory
                     (remove-equal
                      (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                      (generate-index-list
                       2 (+ -2 (fat-length fat32-in-memory))))
                     (make-list-ac (+ -3 (fat-length fat32-in-memory))
                                   0 nil))
                    fs
                    (fat32-entry-mask (bpb_rootclus fat32-in-memory)))))))
               (cluster-size (cluster-size fat32-in-memory)))
              (:instance
               (:LINEAR LEN-WHEN-M1-BOUNDED-FILE-ALIST-P . 2)
               (x fs)))))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-1
  (implies
   (and (< (nfix n)
           (* (bpb_rsvdseccnt fat32-in-memory)
              (bpb_bytspersec fat32-in-memory)))
        (compliant-fat32-in-memoryp fat32-in-memory))
   (equal
    (nth
     n
     (append
      (explode (reserved-area-string fat32-in-memory))
      (explode (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                   fat32-in-memory ""))
      (data-region-string-helper
       fat32-in-memory
       (data-region-length fat32-in-memory)
       nil)))
    (nth n
         (explode (reserved-area-string fat32-in-memory))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-2
    (implies (fat32-in-memoryp fat32-in-memory)
             (>= (+ (data-region-length fat32-in-memory)
                    (* (bpb_bytspersec fat32-in-memory)
                       (bpb_rsvdseccnt fat32-in-memory))
                    (* (bpb_numfats fat32-in-memory)
                       4 (fat-length fat32-in-memory)))
                 (* (bpb_bytspersec fat32-in-memory)
                    (bpb_rsvdseccnt fat32-in-memory))))
    :hints (("goal" :in-theory (enable bpb_numfats)) )
    :rule-classes :linear)

  (defthm
    fat32-in-memory-to-string-inversion-lemma-3
    (implies
     (equal (* (bpb_fatsz32 fat32-in-memory)
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
   (in-theory (e/d (fat32-in-memory-to-string get-initial-bytes get-remaining-rsvdbyts)
                   (logtail loghead fat32-in-memoryp floor
                            ;; the splitter-note suggests these could usefully
                            ;; be disabled
                            nth-of-append nthcdr-of-append take-of-append))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-4
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth 11
            (get-initial-bytes
             (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_bytspersec fat32-in-memory)))
      (equal
       (nth 12
            (get-initial-bytes
             (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_bytspersec fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-5
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth 13
           (get-initial-bytes
            (fat32-in-memory-to-string fat32-in-memory)))
      (bpb_secperclus fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-6
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth 14
            (get-initial-bytes
             (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_rsvdseccnt fat32-in-memory)))
      (equal
       (nth 15
            (get-initial-bytes
             (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_rsvdseccnt fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-7
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth 0
           (get-remaining-rsvdbyts
            (fat32-in-memory-to-string fat32-in-memory)))
      (bpb_numfats fat32-in-memory)))
    :hints
    (("goal" :in-theory (e/d (string=>nats) (nth)))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-8
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        1
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_rootentcnt fat32-in-memory)))
      (equal
       (nth
        2
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_rootentcnt fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-9
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        3
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_totsec16 fat32-in-memory)))
      (equal
       (nth
        4
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_totsec16 fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-10
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth
       5
       (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
      (bpb_media fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-11
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        6
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_fatsz16 fat32-in-memory)))
      (equal
       (nth
        7
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_fatsz16 fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-12
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        8
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_secpertrk fat32-in-memory)))
      (equal
       (nth
        9
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_secpertrk fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-13
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        10
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_numheads fat32-in-memory)))
      (equal
       (nth
        11
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_numheads fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-14
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        12
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_hiddsec fat32-in-memory)))
      (equal
       (nth
        13
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bpb_hiddsec fat32-in-memory))))
      (equal
       (nth
        14
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_hiddsec fat32-in-memory))))
      (equal
       (nth
        15
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 24 (bpb_hiddsec fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-15
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        16
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_totsec32 fat32-in-memory)))
      (equal
       (nth
        17
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bpb_totsec32 fat32-in-memory))))
      (equal
       (nth
        18
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_totsec32 fat32-in-memory))))
      (equal
       (nth
        19
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 24 (bpb_totsec32 fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-16
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        20
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_fatsz32 fat32-in-memory)))
      (equal
       (nth
        21
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail 8 (bpb_fatsz32 fat32-in-memory))))
      (equal
       (nth
        22
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_fatsz32 fat32-in-memory))))
      (equal
       (nth
        23
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 24 (bpb_fatsz32 fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-17
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        24
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_extflags fat32-in-memory)))
      (equal
       (nth
        25
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_extflags fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-18
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth
       26
       (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
      (bpb_fsver_minor fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-19
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth
       27
       (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
      (bpb_fsver_major fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-20
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        28
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_rootclus fat32-in-memory)))
      (equal
       (nth
        29
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bpb_rootclus fat32-in-memory))))
      (equal
       (nth
        30
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_rootclus fat32-in-memory))))
      (equal
       (nth
        31
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 24 (bpb_rootclus fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-21
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        32
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_fsinfo fat32-in-memory)))
      (equal
       (nth
        33
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_fsinfo fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-22
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        34
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_bkbootsec fat32-in-memory)))
      (equal
       (nth
        35
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_bkbootsec fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-23
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth
       48
       (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
      (bs_drvnum fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-24
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth
       49
       (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
      (bs_reserved1 fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-25
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth
       50
       (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
      (bs_bootsig fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-26
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        51
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bs_volid fat32-in-memory)))
      (equal
       (nth
        52
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bs_volid fat32-in-memory))))
      (equal
       (nth
        53
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bs_volid fat32-in-memory))))
      (equal
       (nth
        54
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 24 (bs_volid fat32-in-memory)))))))

(encapsulate
  ()

  (local
   (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-27
    (implies
     (and (compliant-fat32-in-memoryp fat32-in-memory)
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
          (take (cluster-size fat32-in-memory)
                (coerce (data-regioni index fat32-in-memory)
                        'list))
        (take (cluster-size fat32-in-memory)
              (nthcdr (* (cluster-size fat32-in-memory)
                         (- index (nfix len)))
                      (make-character-list ac))))))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-28
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (natp len)
        (<= len
            (data-region-length fat32-in-memory))
        (equal (count-of-clusters fat32-in-memory)
               (data-region-length fat32-in-memory)))
   (equal (update-data-region
           fat32-in-memory
           (implode (data-region-string-helper
                     fat32-in-memory
                     (count-of-clusters fat32-in-memory)
                     nil))
           len)
          fat32-in-memory))
  :hints
  (("goal" :in-theory (disable data-region-string-helper))
   ("subgoal *1/2"
    :in-theory
    (disable fat32-in-memory-to-string-inversion-lemma-27)
    :use
    (:instance fat32-in-memory-to-string-inversion-lemma-27
               (index (- (count-of-clusters fat32-in-memory)
                         len))
               (len (count-of-clusters fat32-in-memory))
               (ac nil)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-30
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
    :instructions
    (:promote (:rewrite product-greater-than-zero-2)
              (:change-goal nil t)
              :bash :s-prop
              (:rewrite product-greater-than-zero-2)
              (:change-goal nil t)
              :bash :s-prop
              (:use (:instance fat32-in-memory-to-string-inversion-lemma-29
                               (i (+ (- (bpb_rsvdseccnt fat32-in-memory))
                                     (bpb_totsec32 fat32-in-memory)
                                     (- (* (bpb_fatsz32 fat32-in-memory)
                                           (bpb_numfats fat32-in-memory)))))
                               (j (bpb_secperclus fat32-in-memory))))
              :promote (:demote 1)
              (:dive 1 1)
              (:= t)
              :top :bash))

  (defthm fat32-in-memory-to-string-inversion-lemma-31
    (implies (compliant-fat32-in-memoryp fat32-in-memory)
             (<=
              (* 4 (fat-length fat32-in-memory))
              (* (bpb_numfats fat32-in-memory)
                 4 (fat-length fat32-in-memory))))
    :rule-classes :linear))

(defthm
  fat32-in-memory-to-string-inversion-lemma-33
  (implies (fat32-in-memoryp fat32-in-memory)
           (equal (resize-fat (fat-length fat32-in-memory)
                              fat32-in-memory)
                  fat32-in-memory))
  :hints (("goal" :in-theory (enable resize-fat fat-length))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-34
  (implies (fat32-in-memoryp fat32-in-memory)
           (equal (resize-data-region (data-region-length fat32-in-memory)
                                      fat32-in-memory)
                  fat32-in-memory))
  :hints (("goal" :in-theory (enable resize-data-region data-region-length)))
  :rule-classes (:rewrite
                 (:rewrite :corollary
                           (implies
                            (and
                             (fat32-in-memoryp fat32-in-memory)
                             (EQUAL (COUNT-OF-CLUSTERS FAT32-IN-MEMORY)
                                    (DATA-REGION-LENGTH FAT32-IN-MEMORY)))
                            (equal (resize-data-region
                                    (COUNT-OF-CLUSTERS FAT32-IN-MEMORY)
                                    fat32-in-memory)
                                   fat32-in-memory))
                           :hints (("Goal" :in-theory (enable resize-data-region))))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-35
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
  fat32-in-memory-to-string-inversion-lemma-36
  (implies
   (and (fat32-entry-p current)
        (< (nfix n) 4))
   (unsigned-byte-p 8
                    (nth n
                         (list (loghead 8 current)
                               (loghead 8 (logtail 8 current))
                               (loghead 8 (logtail 16 current))
                               (logtail 24 current)))))
  :hints
  (("goal" :in-theory (e/d (fat32-entry-p)
                           (unsigned-byte-p loghead logtail))))
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
  fat32-in-memory-to-string-inversion-lemma-37
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
    fat32-in-memory-to-string-inversion-lemma-38
    (implies
     (and (compliant-fat32-in-memoryp fat32-in-memory)
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
    :hints (("goal" :in-theory (disable loghead logtail)
             :induct
             (stobj-fa-table-to-string-helper fat32-in-memory
                                              length
                                              ac))
            ("subgoal *1/2" :expand (:free (n x y) (nth n (cons x y)))))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-39
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
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
  :hints (("goal" :in-theory (e/d (stobj-fa-table-to-string) (logtail loghead)))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-40
  (implies (and (fat32-in-memoryp fat32-in-memory)
                (< (nfix i)
                   (fat-length fat32-in-memory)))
           (equal (update-fati i (fati i fat32-in-memory)
                               fat32-in-memory)
                  fat32-in-memory))
  :hints
  (("goal" :in-theory (enable fati update-fati fat-length))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-41
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
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
     pos)
    :in-theory (e/d (compliant-fat32-in-memoryp)
                    (loghead logtail fat32-in-memoryp)))))

(encapsulate
  ()

  (local (in-theory (disable bs_jmpbooti update-bs_jmpbooti
                             bs_oemnamei bpb_reservedi bs_vollabi
                             bs_filsystypei loghead logtail)))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-42
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
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
        :initial-element 0)))) :hints (("Goal" :in-theory (e/d (chars=>nats
                                                                reserved-area-string
                                                                reserved-area-chars)
                                                               (loghead
                                                                logtail
                                                                unsigned-byte-p)))))

  (local (in-theory (enable chars=>nats-of-take)))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-43
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (update-bs_jmpboot
       (take 3
             (get-initial-bytes
              (fat32-in-memory-to-string fat32-in-memory)))
       fat32-in-memory)
      fat32-in-memory))
    :hints
    (("goal" :in-theory
      (e/d (get-initial-bytes fat32-in-memory-to-string
                              compliant-fat32-in-memoryp)
           (fat32-in-memoryp)))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-44
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (update-bs_oemname
       (take
        8
        (nthcdr
         3
         (get-initial-bytes
          (fat32-in-memory-to-string fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory))
    :hints
    (("goal" :in-theory
      (e/d (get-initial-bytes fat32-in-memory-to-string
                              compliant-fat32-in-memoryp)
           (fat32-in-memoryp)))))

  (local (in-theory (enable chars=>nats-of-nthcdr)))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-45
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (update-bs_vollab
       (take
        11
        (nthcdr
         55
         (get-remaining-rsvdbyts
          (fat32-in-memory-to-string fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory))
    :hints
    (("goal" :in-theory
      (e/d (get-initial-bytes get-remaining-rsvdbyts
                              fat32-in-memory-to-string
                              compliant-fat32-in-memoryp)
           (fat32-in-memoryp)))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-46
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (update-bs_filsystype
       (take
        8
        (nthcdr
         66
         (get-remaining-rsvdbyts
          (fat32-in-memory-to-string fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory))
    :hints
    (("goal" :in-theory
      (e/d (get-initial-bytes get-remaining-rsvdbyts
                              fat32-in-memory-to-string
                              compliant-fat32-in-memoryp)
           (fat32-in-memoryp))))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-47
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
  fat32-in-memory-to-string-inversion-lemma-48
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
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
     pos)
    :in-theory (e/d (compliant-fat32-in-memoryp)
                    (loghead logtail fat32-in-memoryp)))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-49
  (equal
   (nthcdr
    n
    (explode (fat32-in-memory-to-string fat32-in-memory)))
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
    (e/d (fat32-in-memory-to-string)
         (fat32-in-memoryp
          length-of-reserved-area-string
          nth-of-explode-of-reserved-area-string)))))

(defthm
  fat32-in-memory-to-string-inversion
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (equal (* (bpb_fatsz32 fat32-in-memory)
                  1/4 (bpb_bytspersec fat32-in-memory))
               (fat-length fat32-in-memory))
        (equal (count-of-clusters fat32-in-memory)
               (data-region-length fat32-in-memory)))
   (equal
    (mv-nth 0
            (string-to-fat32-in-memory
             fat32-in-memory
             (fat32-in-memory-to-string fat32-in-memory)))
    fat32-in-memory))
  :hints
  (("goal"
    :in-theory
    (e/d (string-to-fat32-in-memory painful-debugging-lemma-4
                                    painful-debugging-lemma-5)
         (floor loghead logtail)))))

#|
Some (rather awful) testing forms are
(b* (((mv contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*)))
  (get-dir-filenames fat32-in-memory contents *ms-max-dir-size*))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*)))
  (fat32-in-memory-to-m1-fs fat32-in-memory))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory)))
  (m1-open (list "INITRD  IMG")
           fs nil nil))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory))
     ((mv fd-table file-table & &)
      (m1-open (list "INITRD  IMG")
               fs nil nil)))
  (m1-pread 0 6 49 fs fd-table file-table))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory))
     ((mv fd-table file-table & &)
      (m1-open (list "INITRD  IMG")
               fs nil nil)))
  (m1-pwrite 0 "ornery" 49 fs fd-table file-table))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory))
     ((mv fd-table file-table & &)
      (m1-open (list "INITRD  IMG")
               fs nil nil))
     ((mv fs & &)
      (m1-pwrite 0 "ornery" 49 fs fd-table file-table))
     ((mv fat32-in-memory dir-ent-list)
      (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs)))
  (mv fat32-in-memory dir-ent-list))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory))
     ((mv fd-table file-table & &)
      (m1-open (list "INITRD  IMG")
               fs nil nil))
     ((mv fs & &)
      (m1-pwrite 0 "ornery" 49 fs fd-table file-table)))
  (m1-fs-to-fat32-in-memory fat32-in-memory fs))
(time$
 (b*
     ((str (fat32-in-memory-to-string
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
          (fat32-in-memory-to-string fat32-in-memory)
          channel state))
      (state
       (close-output-channel channel state)))
   (mv fat32-in-memory state)))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory))
     ((mv fs & &)
      (m1-mkdir fs (list "" "TMP        "))))
  (m1-fs-to-fat32-in-memory fat32-in-memory fs))
|#

(defun m2-statfs (fat32-in-memory)
  (declare (xargs :stobjs (fat32-in-memory)
                  :verify-guards nil))
  (b*
      ((total_blocks (count-of-clusters fat32-in-memory))
       (available_blocks
        (- (+ total_blocks
              2
              (len (stobj-find-n-free-clusters
                    fat32-in-memory
                    (fat-length fat32-in-memory))))
           (fat-length fat32-in-memory))))
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
