(in-package "ACL2")

;  file-system-m2.lisp                                  Mihir Mehta

; This is a stobj model of the FAT32 filesystem.

(include-book "file-system-lemmas")
(include-book "fat32")
(include-book "std/io/read-ints" :dir :system)
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/lists/resize-list" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(local (include-book "rtl/rel9/arithmetic/top"
                     :dir :system))
(include-book "kestrel/utilities/strings" :dir :system)

;; This was moved to one of the main books, but still kept
(defthm unsigned-byte-listp-of-update-nth
  (implies (and (unsigned-byte-listp n l)
                (< key (len l)))
           (equal (unsigned-byte-listp n (update-nth key val l))
                  (unsigned-byte-p n val)))
  :hints (("goal" :in-theory (enable unsigned-byte-listp))))

;; This was taken from Alessandro Coglio's book at
;; books/kestrel/utilities/typed-list-theorems.lisp
(defthm unsigned-byte-listp-of-rev
  (equal (unsigned-byte-listp n (rev bytes))
         (unsigned-byte-listp n (list-fix bytes)))
  :hints (("goal" :in-theory (enable unsigned-byte-listp rev))))

(defthm nth-of-unsigned-byte-list
  (implies (and (unsigned-byte-listp bits l)
                (natp n)
                (< n (len l)))
           (unsigned-byte-p bits (nth n l))))

(defthm len-of-chars=>nats
  (implies (character-listp chars)
           (equal (len (chars=>nats chars))
                  (len chars)))
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

(in-theory (disable bs_oemnamep bs_jmpbootp bs_filsystypep fatp data-regionp))

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
                    update-bpb_totsec16 update-bs_volid))

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
     ("Subgoal 8" :in-theory (disable nth-of-unsigned-byte-list)
      :use (:instance
            nth-of-unsigned-byte-list
            (n 13)
            (l (string=>nats (implode (take 16 (explode str)))))
            (bits 8)))
     ("Subgoal 7" :in-theory (disable nth-of-unsigned-byte-list)
      :use (:instance
            nth-of-unsigned-byte-list
            (n 0)
            (l
             (STRING=>NATS
              (IMPLODE
               (TAKE
                (+
                 -16
                 (*
                  (COMBINE16U (NTH 12
                                   (STRING=>NATS (IMPLODE (TAKE 16 (EXPLODE STR)))))
                              (NTH 11
                                   (STRING=>NATS (IMPLODE (TAKE 16 (EXPLODE STR))))))
                  (COMBINE16U (NTH 15
                                   (STRING=>NATS (IMPLODE (TAKE 16 (EXPLODE STR)))))
                              (NTH 14
                                   (STRING=>NATS (IMPLODE (TAKE 16 (EXPLODE STR))))))))
                (NTHCDR 16 (EXPLODE STR))))))
            (bits 8)))
     ("subgoal 5"
      :in-theory (disable nth-of-unsigned-byte-list)
      :use
      (:instance
       nth-of-unsigned-byte-list (bits 8)
       (n 13)
       (l (string=>nats (implode (take 16 (explode str)))))))
     ("subgoal 4"
      :in-theory (disable nth-of-unsigned-byte-list)
      :use
      (:instance
       nth-of-unsigned-byte-list (bits 8)
       (n 0)
       (l
        (string=>nats
         (implode
          (take
           (+
            -16
            (*
             (combine16u
              (nth
               12
               (string=>nats (implode (take 16 (explode str)))))
              (nth 11
                   (string=>nats
                    (implode (take 16 (explode str))))))
             (combine16u
              (nth
               15
               (string=>nats (implode (take 16 (explode str)))))
              (nth 14
                   (string=>nats
                    (implode (take 16 (explode str))))))))
           (nthcdr 16 (explode str)))))))))
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
        (string=>nats (subseq str 0 *initialbytcnt*)))
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
       (remaining_rsvdbyts
        (string=>nats (subseq str *initialbytcnt* tmp_rsvdbytcnt)))
       (tmp_numfats (nth (- 16 *initialbytcnt*) remaining_rsvdbyts))
       ((unless (>= tmp_numfats 1))
        (mv fat32-in-memory -1))
       (fat32-in-memory
        (update-bpb_numfats tmp_numfats
                            fat32-in-memory))
       (fat32-in-memory
        (update-bpb_rootentcnt
         (combine16u (nth (+ 17 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 17 0 (- *initialbytcnt*)) remaining_rsvdbyts))
         fat32-in-memory))
       (fat32-in-memory
        (update-bpb_totsec16
         (combine16u (nth (+ 19 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 19 0 (- *initialbytcnt*)) remaining_rsvdbyts))
         fat32-in-memory))
       (fat32-in-memory
        (update-bpb_media (nth (- 21 *initialbytcnt*) remaining_rsvdbyts)
                          fat32-in-memory))
       (fat32-in-memory
        (update-bpb_fatsz16
         (combine16u (nth (+ 22 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 22 0 (- *initialbytcnt*)) remaining_rsvdbyts))
         fat32-in-memory))
       (fat32-in-memory
        (update-bpb_secpertrk
         (combine16u (nth (+ 24 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 24 0 (- *initialbytcnt*)) remaining_rsvdbyts))
         fat32-in-memory))
       (fat32-in-memory
        (update-bpb_numheads
         (combine16u (nth (+ 26 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 26 0 (- *initialbytcnt*)) remaining_rsvdbyts))
         fat32-in-memory))
       (fat32-in-memory
        (update-bpb_hiddsec
         (combine32u (nth (+ 28 3 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 28 2 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 28 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 28 0 (- *initialbytcnt*)) remaining_rsvdbyts))
         fat32-in-memory))
       (fat32-in-memory
        (update-bpb_totsec32
         (combine32u (nth (+ 32 3 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 32 2 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 32 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 32 0 (- *initialbytcnt*)) remaining_rsvdbyts))
         fat32-in-memory))
       ;; fat32-specific stuff
       (tmp_fatsz32
        (combine32u (nth (+ 36 3 (- *initialbytcnt*)) remaining_rsvdbyts)
                    (nth (+ 36 2 (- *initialbytcnt*)) remaining_rsvdbyts)
                    (nth (+ 36 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                    (nth (+ 36 0 (- *initialbytcnt*)) remaining_rsvdbyts)))
       ((unless (>= tmp_fatsz32 1))
        (mv fat32-in-memory -1))
       (fat32-in-memory
        (update-bpb_fatsz32
         tmp_fatsz32
         fat32-in-memory))
       (fat32-in-memory
        (update-bpb_extflags
         (combine16u (nth (+ 40 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 40 0 (- *initialbytcnt*)) remaining_rsvdbyts))
         fat32-in-memory))
       (fat32-in-memory
        (update-bpb_fsver_minor (nth (- 42 *initialbytcnt*) remaining_rsvdbyts)
                                fat32-in-memory))
       (fat32-in-memory
        (update-bpb_fsver_major (nth (- 43 *initialbytcnt*) remaining_rsvdbyts)
                                fat32-in-memory))
       (fat32-in-memory
        (update-bpb_rootclus
         (combine32u (nth (+ 44 3 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 44 2 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 44 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 44 0 (- *initialbytcnt*)) remaining_rsvdbyts))
         fat32-in-memory))
       (fat32-in-memory
        (update-bpb_fsinfo
         (combine16u (nth (+ 48 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 48 0 (- *initialbytcnt*)) remaining_rsvdbyts))
         fat32-in-memory))
       (fat32-in-memory
        (update-bpb_bkbootsec
         (combine16u (nth (+ 50 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 50 0 (- *initialbytcnt*)) remaining_rsvdbyts))
         fat32-in-memory))
       ;; skipping bpb_reserved for now
       (fat32-in-memory
        (update-bs_drvnum (nth (- 64 *initialbytcnt*) remaining_rsvdbyts)
                          fat32-in-memory))
       (fat32-in-memory
        (update-bs_reserved1 (nth (- 65 *initialbytcnt*) remaining_rsvdbyts)
                             fat32-in-memory))
       (fat32-in-memory
        (update-bs_bootsig (nth (- 66 *initialbytcnt*) remaining_rsvdbyts)
                           fat32-in-memory))
       (fat32-in-memory
        (update-bs_volid
         (combine32u (nth (+ 67 3 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 67 2 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 67 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 67 0 (- *initialbytcnt*)) remaining_rsvdbyts))
         fat32-in-memory))
       (fat32-in-memory
        (update-bs_vollab (subseq remaining_rsvdbyts
                                      (+ 71 (- *initialbytcnt*) 0)
                                      (+ 71 (- *initialbytcnt*) 11)) fat32-in-memory))
       (fat32-in-memory
        (update-bs_filsystype (subseq remaining_rsvdbyts
                                      (+ 82 (- *initialbytcnt*) 0)
                                      (+ 82 (- *initialbytcnt*) 8)) fat32-in-memory)))
    (mv fat32-in-memory 0)))

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
          (("goal" :in-theory (disable fat32-in-memoryp)))
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
          (("goal" :in-theory (disable fat32-in-memoryp)))
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
  :hints (("goal" :in-theory (enable update-fat))))

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
  (<= 512
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable fat32-in-memoryp nth subseq))))

(defthm
  read-reserved-area-correctness-1
  (implies (and (fat32-in-memoryp fat32-in-memory)
                (stringp str))
           (fat32-in-memoryp
            (mv-nth 0
                    (read-reserved-area fat32-in-memory str))))
  :hints
  (("Goal" :in-theory (disable fat32-in-memoryp))))

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
                                            (* (bpb_rsvdseccnt fat32-in-memory)
                                               (bpb_bytspersec
                                                fat32-in-memory))
                                            (+
                                             (* (bpb_rsvdseccnt fat32-in-memory)
                                                (bpb_bytspersec fat32-in-memory))
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
  (implies (and (fat32-in-memoryp fat32-in-memory)
                (integerp i)
                (<= 0 i)
                (< i (data-region-length fat32-in-memory)))
           (unsigned-byte-p 8 (data-regioni i fat32-in-memory)))
  :hints (("goal" :in-theory (disable unsigned-byte-p))))

(defthm
  get-dir-ent-helper-correctness-1
  (implies
   (and (fat32-in-memoryp fat32-in-memory)
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
  (implies (and (fat32-in-memoryp fat32-in-memory)
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

(defun dir-ent-first-cluster (dir-ent)
  (declare
   (xargs :guard (and (equal (len dir-ent) *ms-dir-ent-length*)
                      (unsigned-byte-listp 8 dir-ent))))
  (combine32u (nth 21 dir-ent)
              (nth 20 dir-ent)
              (nth 27 dir-ent)
              (nth 26 dir-ent)))

(defun dir-ent-file-size (dir-ent)
  (declare
   (xargs :guard (and (equal (len dir-ent) *ms-dir-ent-length*)
                      (unsigned-byte-listp 8 dir-ent))))
  (combine32u (nth 31 dir-ent)
              (nth 30 dir-ent)
              (nth 29 dir-ent)
              (nth 28 dir-ent)))

(defund
  get-clusterchain
  (fat32-in-memory masked-current-cluster length)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :measure (nfix length)
    :guard (and (fat32-in-memoryp fat32-in-memory)
                (fat32-masked-entry-p masked-current-cluster)
                (natp length)
                (>= masked-current-cluster 2)
                (< masked-current-cluster
                   (fat-length fat32-in-memory))
                (> (* (bpb_secperclus fat32-in-memory)
                      (bpb_bytspersec fat32-in-memory))
                   0))))
  (let
   ((cluster-size (* (bpb_secperclus fat32-in-memory)
                     (bpb_bytspersec fat32-in-memory))))
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

(defthm get-clusterchain-alt
  (equal (get-clusterchain fat32-in-memory
                           masked-current-cluster length)
         (fat32-build-index-list (nth *fati* fat32-in-memory)
                                 masked-current-cluster length
                                 (* (bpb_secperclus fat32-in-memory)
                                    (bpb_bytspersec fat32-in-memory))))
  :rule-classes :definition
  :hints (("Goal" :in-theory (enable get-clusterchain))))

(defun
  get-contents-from-clusterchain
  (fat32-in-memory clusterchain file-size)
  (declare
   (xargs
    :stobjs (fat32-in-memory)
    :guard
    (and (fat32-in-memoryp fat32-in-memory)
         (fat32-masked-entry-list-p clusterchain)
         (natp file-size)
         (< 0
            (* (bpb_bytspersec fat32-in-memory)
               (bpb_secperclus fat32-in-memory)))
         (bounded-nat-listp
          clusterchain
          (floor (data-region-length fat32-in-memory)
                 (* (bpb_bytspersec fat32-in-memory)
                    (bpb_secperclus fat32-in-memory))))
         (lower-bounded-integer-listp
          clusterchain *ms-first-data-cluster*))
    :guard-hints
    (("goal" :in-theory (e/d (lower-bounded-integer-listp)
                             (fat32-in-memoryp))))))
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
    :guard (and (fat32-in-memoryp fat32-in-memory)
                (fat32-masked-entry-p masked-current-cluster)
                (natp length)
                (>= masked-current-cluster *ms-first-data-cluster*)
                (> (* (bpb_secperclus fat32-in-memory)
                      (bpb_bytspersec fat32-in-memory))
                   0)
                (< masked-current-cluster
                   (floor (data-region-length fat32-in-memory)
                          (* (bpb_bytspersec fat32-in-memory)
                             (bpb_secperclus fat32-in-memory))))
                (<=
                 (floor (data-region-length fat32-in-memory)
                        (* (bpb_bytspersec fat32-in-memory)
                           (bpb_secperclus fat32-in-memory)))
                 (fat-length fat32-in-memory)))
    :guard-debug t
    :guard-hints (("Goal" :do-not-induct t :in-theory (disable
                                                       fat32-in-memoryp))
                  ("Subgoal 1.10'" :in-theory (disable
                                               SET-INDICES-IN-FA-TABLE-GUARD-LEMMA-3)
                   :use (:instance SET-INDICES-IN-FA-TABLE-GUARD-LEMMA-3
                                   (n MASKED-CURRENT-CLUSTER)
                                   (l
                                    (NTH *FATI* FAT32-IN-MEMORY)))))))
  (b*
      ((cluster-size (* (bpb_secperclus fat32-in-memory)
                        (bpb_bytspersec fat32-in-memory)))
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
                           (* (bpb_bytspersec fat32-in-memory)
                              (bpb_secperclus fat32-in-memory))))))
        (mv current-cluster-contents 0))
       ((mv tail-character-list tail-error)
        (get-clusterchain-contents fat32-in-memory masked-next-cluster
                                   (nfix (- length cluster-size))))
       ((unless (equal tail-error 0)) (mv nil (- *eio*))))
    (mv
     (append
      current-cluster-contents
      tail-character-list)
     0)))

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
                      (* (bpb_bytspersec fat32-in-memory)
                         (bpb_secperclus fat32-in-memory)))
               (fat-length fat32-in-memory)))
   (equal (mv-nth 1
                  (fat32-build-index-list
                   (nth *fati* fat32-in-memory)
                   masked-current-cluster length
                   (* (bpb_secperclus fat32-in-memory)
                      (bpb_bytspersec fat32-in-memory))))
          (mv-nth 1
                  (get-clusterchain-contents
                   fat32-in-memory
                   masked-current-cluster length))))
  :hints (("goal" :in-theory (disable fat32-in-memoryp))))

(defthm
  get-clusterchain-contents-correctness-1
  (implies
   (and
    (fat32-masked-entry-p masked-current-cluster)
    (>= masked-current-cluster
        *ms-first-data-cluster*)
    (fat32-in-memoryp fat32-in-memory)
    (equal (floor (data-region-length fat32-in-memory)
                  (* (bpb_bytspersec fat32-in-memory)
                     (bpb_secperclus fat32-in-memory)))
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
  (("goal" :in-theory (disable min nth fat32-in-memoryp))))

(fty::defprod m1-file
  ((dir-ent any-p)
   (contents any-p)))

(defund m1-regular-file-p (file)
  (declare (xargs :guard t))
  (and
   (m1-file-p file)
   (stringp (m1-file->contents file))))

(fty::deflist m1-file-list
              :elt-type m1-file)

(defun m1-directory-file-p (file)
  (declare (xargs :guard t))
  (and
   (m1-file-p file)
   (m1-file-list-p (m1-file->contents file))))

;; Currently the function call to test out this function is
;; (b* (((mv contents &)
;;       (get-clusterchain-contents
;;        fat32-in-memory 2 (ash 1 21))))
;;   (get-dir-filenames
;;    fat32-in-memory contents (ash 1 21)))
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

(in-theory (enable update-fat bpb_secperclus bpb_fatsz32 bpb_rsvdseccnt
                   bpb_numfats bpb_bytspersec bpb_rootclus bpb_fsinfo
                   bpb_bkbootsec bs_drvnum bs_reserved1 bs_bootsig
                   bpb_media bpb_fsver_major bpb_fsver_major bpb_fatsz16
                   bpb_secpertrk bpb_numheads bpb_rootentcnt
                   bpb_extflags bpb_hiddsec bpb_totsec32 bpb_fatsz32
                   bpb_rootentcnt bpb_totsec16
                   update-bpb_secperclus update-bpb_rsvdseccnt
                   update-bpb_bytspersec update-bpb_numfats
                   update-bpb_rootclus update-bpb_fsinfo update-bpb_bkbootsec
                   update-bs_drvnum update-bs_reserved1 update-bs_bootsig
                   update-bpb_media update-bpb_fsver_minor
                   update-bpb_fsver_major update-bpb_fatsz16
                   update-bpb_secpertrk update-bpb_numheads
                   update-bpb_extflags update-bpb_hiddsec update-bpb_totsec32
                   update-bpb_fatsz32 update-bpb_rootentcnt
                   update-bpb_totsec16))
