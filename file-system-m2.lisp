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

;; This was moved to one of the main books, but still kept
(defthm unsigned-byte-listp-of-update-nth
  (implies (and (unsigned-byte-listp n l)
                (< key (len l)))
           (equal (unsigned-byte-listp n (update-nth key val l))
                  (unsigned-byte-p n val)))
  :hints (("goal" :in-theory (enable unsigned-byte-listp))))

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

(defthm bs_filsystypep-alt
  (equal (bs_filsystypep x)
         (unsigned-byte-listp 8 x))
  :rule-classes :definition)

(defthm fatp-alt
  (equal (fatp x)
         (unsigned-byte-listp 32 x))
  :rule-classes :definition)

(in-theory (disable bs_oemnamep bs_jmpbootp bs_filsystypep fatp))

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

(defconst *initialbytcnt* 16)

(defmacro
  update-stobj-array
  (name array-length bit-width array-updater
        stobj stobj-recogniser lemma-name)
  (declare (ignore))
  (list
   'encapsulate
   'nil
   (list
    'defun
    name (list 'v stobj)
    (list
     'declare
     (list 'xargs
           ':guard
           (list 'and
                 (list 'unsigned-byte-listp bit-width 'v)
                 (list '<=
                       '(len v)
                       (list array-length stobj))
                 (list stobj-recogniser stobj))
           ':guard-hints
           (list (list '"goal"
                       ':in-theory
                       (list 'disable
                             stobj-recogniser 'unsigned-byte-p
                             'nth)))
           ':stobjs
           (list stobj)))
    (list
     'if
     '(atom v)
     stobj
     (list 'let*
           (list (list stobj
                       (list array-updater
                             (list '-
                                   (list array-length stobj)
                                   '(len v))
                             '(car v)
                             stobj))
                 (list stobj (list name '(cdr v) stobj)))
           stobj)))
   (list 'defthm
         lemma-name
         (list 'implies
               (list 'and
                     (list 'unsigned-byte-listp bit-width 'v)
                     (list '<=
                           (list 'len 'v)
                           (list array-length stobj))
                     (list stobj-recogniser stobj))
               (list stobj-recogniser (list name 'v stobj)))
         ':hints
         (list (list '"goal"
                     ':in-theory
                     (list 'disable stobj-recogniser))
               (list '"subgoal *1/4"
                     ':in-theory
                     (list 'enable stobj-recogniser))))))

(update-stobj-array
 update-bs_jmpboot
 bs_jmpboot-length
 8 update-bs_jmpbooti fat32-in-memory fat32-in-memoryp
 update-bs_jmpboot-correctness-1)

(update-stobj-array
 update-bs_oemname
 bs_oemname-length
 8 update-bs_oemnamei fat32-in-memory fat32-in-memoryp
 update-bs_oemname-correctness-1)

(update-stobj-array
 update-bs_filsystype
 bs_filsystype-length
 8 update-bs_filsystypei fat32-in-memory fat32-in-memoryp
 update-bs_filsystype-correctness-1)

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
  read-reserved-area
  (fat32-in-memory channel state)
  (declare
   (xargs
    :guard (and (state-p state)
                (symbolp channel)
                (open-input-channel-p channel
                                      :byte state)
                (fat32-in-memoryp fat32-in-memory))
    :guard-debug t
    :guard-hints
    (("goal"
      :do-not-induct t
      :in-theory (disable fat32-in-memoryp
                          state-p unsigned-byte-p nth)
      :use
      ((:instance
        unsigned-byte-listp-of-take (width 8)
        (n 3)
        (x (mv-nth 0 (read-byte$-n 16 channel state))))))
     ("subgoal 6'"
      :use
      (:instance
       unsigned-byte-p-forward-to-nonnegative-integerp
       (n 8)
       (x (nth 13
               (mv-nth 0 (read-byte$-n 16 channel state))))))
     ("Subgoal 5'"
      :use
      (:instance
       unsigned-byte-p-forward-to-nonnegative-integerp
       (n 8)
       (x
        (nth
         0
         (mv-nth
          0
          (read-byte$-n
           (+ -16
              (* (combine16u (nth 12
                                  (mv-nth 0 (read-byte$-n 16 channel state)))
                             (nth 11
                                  (mv-nth 0 (read-byte$-n 16 channel state))))
                 (combine16u (nth 15
                                  (mv-nth 0 (read-byte$-n 16 channel state)))
                             (nth 14
                                  (mv-nth 0 (read-byte$-n 16 channel state))))))
           channel
           (mv-nth 1 (read-byte$-n 16 channel state))))))))
     ("subgoal 2'"
      :use
      (:instance
       unsigned-byte-p-forward-to-nonnegative-integerp
       (n 8)
       (x
        (nth
         0
         (mv-nth
          0
          (read-byte$-n
           (+
            -16
            (*
             (combine16u
              (nth 12
                   (mv-nth 0 (read-byte$-n 16 channel state)))
              (nth 11
                   (mv-nth 0 (read-byte$-n 16 channel state))))
             (combine16u
              (nth 15
                   (mv-nth 0 (read-byte$-n 16 channel state)))
              (nth
               14
               (mv-nth 0 (read-byte$-n 16 channel state))))))
           channel
           (mv-nth 1
                   (read-byte$-n 16 channel state)))))))))
    :stobjs (state fat32-in-memory)))
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
       ;; common stuff for fat filesystems
       ((mv initial-bytes state)
        (read-byte$-n *initialbytcnt* channel state))
       ((unless (not (equal initial-bytes 'fail)))
        (mv fat32-in-memory state -1))
       (fat32-in-memory
        (update-bs_jmpboot (subseq initial-bytes 0 3) fat32-in-memory))
       (fat32-in-memory
        (update-bs_oemname (subseq initial-bytes 3 8) fat32-in-memory))
       (tmp_bytspersec (combine16u (nth (+ 11 1) initial-bytes)
                                   (nth (+ 11 0) initial-bytes)))
       ((unless (>= tmp_bytspersec 512))
        (mv fat32-in-memory state -1))
       (fat32-in-memory
        (update-bpb_bytspersec tmp_bytspersec fat32-in-memory))
       (tmp_secperclus (nth 13 initial-bytes))
       ;; this is actually a proxy for testing membership in the set {1, 2, 4,
       ;; 8, 16, 32, 64, 128}
       ((unless (>= tmp_secperclus 1))
        (mv fat32-in-memory state -1))
       (fat32-in-memory
        (update-bpb_secperclus tmp_secperclus
                               fat32-in-memory))
       (tmp_rsvdseccnt (combine16u (nth (+ 14 1) initial-bytes)
                                   (nth (+ 14 0) initial-bytes)))
       ((unless (>= tmp_rsvdseccnt 1))
        (mv fat32-in-memory state -1))
       (fat32-in-memory
        (update-bpb_rsvdseccnt tmp_rsvdseccnt fat32-in-memory))
       (tmp_rsvdbytcnt (* tmp_rsvdseccnt tmp_bytspersec))
       ((unless (>= tmp_rsvdbytcnt *initialbytcnt*))
        (mv fat32-in-memory state -1))
       ((mv remaining_rsvdbyts state)
        (read-bytes$-n (- tmp_rsvdbytcnt *initialbytcnt*)
                       channel
                       :end :little))
       ((unless (not (equal remaining_rsvdbyts 'fail)))
        (mv fat32-in-memory state -1))
       (tmp_numfats (nth (- 16 *initialbytcnt*) remaining_rsvdbyts))
       ((unless (>= tmp_numfats 1))
        (mv fat32-in-memory state -1))
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
        (mv fat32-in-memory state -1))
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
        (update-bpb_rootclus
         (combine32u (nth (+ 67 3 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 67 2 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 67 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                     (nth (+ 67 0 (- *initialbytcnt*)) remaining_rsvdbyts))
         fat32-in-memory))
       ;; skipping bs_vollab for now
       (fat32-in-memory
        (update-bs_filsystype (subseq remaining_rsvdbyts
                                      (+ 82 (- *initialbytcnt*) 0)
                                      (+ 82 (- *initialbytcnt*) 8)) fat32-in-memory)))
    (mv fat32-in-memory state 0)))

(update-stobj-array
 update-fat
 fat-length
 32 update-fati fat32-in-memory fat32-in-memoryp
 update-fat-correctness-1)

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
  (fat32-in-memory str str-init pos)
  (declare
   (xargs
    :measure (nfix (- (data-region-length fat32-in-memory)
                      pos))
    :guard (and (natp pos)
                (stringp str)
                (natp str-init)
                (<= (+ str-init (data-region-length fat32-in-memory))
                    (length str))
                (fat32-in-memoryp fat32-in-memory))
    :guard-hints
    (("goal" :in-theory (disable fat32-in-memoryp nth)))
    :stobjs (fat32-in-memory)))
  (if
   (mbe :logic (or (not (natp pos))
                   (zp (- (data-region-length fat32-in-memory)
                          pos)))
        :exec (>= pos
                  (data-region-length fat32-in-memory)))
   fat32-in-memory
   (let*
    ((fat32-in-memory
      (update-data-regioni
       pos
       (the (unsigned-byte 8)
            (char-code (char str (+ str-init pos))))
       fat32-in-memory))
     (fat32-in-memory
      (update-data-region fat32-in-memory str str-init (+ pos 1))))
    fat32-in-memory)))

(defun
  read-fat (fat32-in-memory channel state)
  (declare
   (xargs
    :guard (and (state-p state)
                (symbolp channel)
                (open-input-channel-p channel
                                      :byte state)
                (fat32-in-memoryp fat32-in-memory))
    :guard-hints
    (("goal" :do-not-induct t
      :in-theory (disable state-p unsigned-byte-p nth)))
    :stobjs (state fat32-in-memory)))
  (b*
      ((tmp_datasz (bpb_fatsz32 fat32-in-memory))
       (tmp_bytspersec (bpb_bytspersec fat32-in-memory))
       (tmp_secperclus (bpb_secperclus fat32-in-memory))
       (tmp_databytcnt (* tmp_datasz tmp_secperclus tmp_bytspersec))
       ((mv fa-table state)
        (read-32ule-n tmp_datasz
                      channel state))
       ((unless (not (equal fa-table 'fail)))
        (mv fat32-in-memory state -1))
       ((mv data-region state)
        (read-byte$-n tmp_databytcnt
                      channel state))
       ((unless (not (equal data-region 'fail)))
        (mv fat32-in-memory state -1))
       (fat32-in-memory (resize-fat tmp_datasz
                                    fat32-in-memory))
       (fat32-in-memory (update-fat fa-table fat32-in-memory))
       (fat32-in-memory (resize-data-region tmp_databytcnt
                                            fat32-in-memory))
       )
    (mv fat32-in-memory state 0)))

(defthm slurp-disk-image-guard-lemma-1
  (implies
   (and (state-p state)
                  (symbolp channel)
                  (open-input-channel-p channel
                                        :byte state)
                  (fat32-in-memoryp fat32-in-memory))
  (state-p1 (mv-nth 1
                   (read-reserved-area
                    fat32-in-memory channel state))))
  :hints
    (("goal" :do-not-induct t
      :in-theory (disable fat32-in-memoryp)
        :use ((:instance
               read-byte$-n-state
               (n *initialbytcnt*))
              (:instance
               read-byte$-n-state
               (n
                (+ -16
                   (* (COMBINE16U (NTH 12
                                       (MV-NTH 0 (READ-BYTE$-N 16 CHANNEL STATE)))
                                  (NTH 11
                                       (MV-NTH 0 (READ-BYTE$-N 16 CHANNEL STATE))))
                      (COMBINE16U (NTH 15
                                       (MV-NTH 0 (READ-BYTE$-N 16 CHANNEL STATE)))
                                  (NTH 14
                                       (MV-NTH 0 (READ-BYTE$-N 16 CHANNEL STATE)))))))
               (state
                (MV-NTH 1 (READ-BYTE$-N 16 CHANNEL STATE))))))))

(in-theory (disable update-fat bpb_secperclus bpb_fatsz32 bpb_rsvdseccnt
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

(defthm
  slurp-disk-image-guard-lemma-2
  (implies (member n
                   (list *bpb_secperclus*
                         *bpb_fatsz32* *bpb_numfats*
                         *bpb_rsvdseccnt* *data-regioni*))
           (equal (nth n (update-fat v fat32-in-memory))
                  (nth n fat32-in-memory)))
  :hints (("goal" :in-theory (enable update-fat))))

(defthm slurp-disk-image-guard-lemma-3
  (equal (bpb_secperclus
              (update-fat v fat32-in-memory))
         (bpb_secperclus fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_secperclus)) ))

(defthm slurp-disk-image-guard-lemma-4
  (equal (bpb_fatsz32
              (update-fat v fat32-in-memory))
         (bpb_fatsz32 fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_fatsz32)) ))

(defthm slurp-disk-image-guard-lemma-5
  (equal (bpb_numfats
              (update-fat v fat32-in-memory))
         (bpb_numfats fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_numfats)) ))

(defthm slurp-disk-image-guard-lemma-6
  (equal (bpb_rsvdseccnt
              (update-fat v fat32-in-memory))
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
        (list
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
         (cons 'update-bpb_numfats *bpb_numfats*))
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
        (list
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
         (cons 'update-bpb_fatsz32 *bpb_fatsz32*)
         (cons 'update-bpb_totsec32 *bpb_totsec32*)
         (cons 'update-bpb_hiddsec *bpb_hiddsec*)
         (cons 'update-bpb_numheads *bpb_numheads*)
         (cons 'update-bpb_secpertrk *bpb_secpertrk*)
         (cons 'update-bpb_fatsz16 *bpb_fatsz16*)
         (cons 'update-bpb_media *bpb_media*)
         (cons 'update-bpb_totsec16 *bpb_totsec16*)
         (cons 'update-bpb_rootentcnt *bpb_rootentcnt*)
         (cons 'update-bpb_numfats *bpb_numfats*))
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
        (list
         (cons 'update-bpb_bytspersec *bpb_bytspersec*)
         (cons 'update-bpb_secperclus *bpb_secperclus*)
         (cons 'update-bpb_rootclus *bpb_rootclus*)
         (cons 'update-bs_bootsig *bs_bootsig*)
         (cons 'update-bs_reserved1 *bs_reserved1*)
         (cons 'update-bs_drvnum *bs_drvnum*)
         (cons 'update-bpb_bkbootsec *bpb_bkbootsec*)
         (cons 'update-bpb_fsinfo *bpb_fsinfo*)
         (cons 'update-bpb_fsver_major *bpb_fsver_major*)
         (cons 'update-bpb_fsver_minor *bpb_fsver_minor*)
         (cons 'update-bpb_extflags *bpb_extflags*)
         (cons 'update-bpb_fatsz32 *bpb_fatsz32*)
         (cons 'update-bpb_totsec32 *bpb_totsec32*)
         (cons 'update-bpb_hiddsec *bpb_hiddsec*)
         (cons 'update-bpb_numheads *bpb_numheads*)
         (cons 'update-bpb_secpertrk *bpb_secpertrk*)
         (cons 'update-bpb_fatsz16 *bpb_fatsz16*)
         (cons 'update-bpb_media *bpb_media*)
         (cons 'update-bpb_totsec16 *bpb_totsec16*)
         (cons 'update-bpb_rootentcnt *bpb_rootentcnt*)
         (cons 'update-bpb_numfats *bpb_numfats*))
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
        (list
         (cons 'update-bpb_bytspersec *bpb_bytspersec*)
         (cons 'update-bpb_secperclus *bpb_secperclus*)
         (cons 'update-bpb_rootclus *bpb_rootclus*)
         (cons 'update-bs_bootsig *bs_bootsig*)
         (cons 'update-bs_reserved1 *bs_reserved1*)
         (cons 'update-bs_drvnum *bs_drvnum*)
         (cons 'update-bpb_bkbootsec *bpb_bkbootsec*)
         (cons 'update-bpb_fsinfo *bpb_fsinfo*)
         (cons 'update-bpb_fsver_major *bpb_fsver_major*)
         (cons 'update-bpb_fsver_minor *bpb_fsver_minor*)
         (cons 'update-bpb_extflags *bpb_extflags*)
         (cons 'update-bpb_fatsz32 *bpb_fatsz32*)
         (cons 'update-bpb_totsec32 *bpb_totsec32*)
         (cons 'update-bpb_hiddsec *bpb_hiddsec*)
         (cons 'update-bpb_numheads *bpb_numheads*)
         (cons 'update-bpb_secpertrk *bpb_secpertrk*)
         (cons 'update-bpb_fatsz16 *bpb_fatsz16*)
         (cons 'update-bpb_media *bpb_media*)
         (cons 'update-bpb_totsec16 *bpb_totsec16*)
         (cons 'update-bpb_rootentcnt *bpb_rootentcnt*)
         (cons 'update-bpb_rsvdseccnt *bpb_rsvdseccnt*))
        'fat32-in-memory))))

;; Check out Subgoal 1.3.3'

(defthm
  slurp-disk-image-guard-lemma-11
  (implies (and (integerp x) (integerp y))
           (integerp (+ x y))))

(defthm
  slurp-disk-image-guard-lemma-12
  (implies (and (integerp x) (integerp y))
           (integerp (* x y))))

(defthm
  slurp-disk-image-guard-lemma-13
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (<= 0 (bpb_bytspersec fat32-in-memory)))
  :hints (("Goal" :use update-bpb_bytspersec-correctness-2) )
  :rule-classes :linear)

(defthm
  slurp-disk-image-guard-lemma-14
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (<= 0 (bpb_fatsz32 fat32-in-memory)))
  :hints (("Goal" :use update-bpb_fatsz32-correctness-2) )
  :rule-classes :linear)

(defthm
  slurp-disk-image-guard-lemma-15
  (equal (bpb_secperclus (update-bs_oemname v fat32-in-memory))
         (bpb_secperclus fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_secperclus)) ))

(defthm
  slurp-disk-image-guard-lemma-16
  (equal (bpb_secperclus (update-bs_jmpboot v fat32-in-memory))
         (bpb_secperclus fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_secperclus)) ))

(defthm
  slurp-disk-image-guard-lemma-17
  (equal (bpb_secperclus (update-bs_filsystype v fat32-in-memory))
         (bpb_secperclus fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_secperclus)) ))

;; Look, we're going to have to keep re-visiting this as we make sure there are
;; at least 512 bytes per sector and so on. Let's just pause and do it right.
(defthm
  slurp-disk-image-guard-lemma-18
  (<= 1
      (bpb_secperclus
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory channel state))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t :in-theory (disable fat32-in-memoryp))))

(defthm
  slurp-disk-image-guard-lemma-19
  (equal (bpb_rsvdseccnt (update-bs_oemname v fat32-in-memory))
         (bpb_rsvdseccnt fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_rsvdseccnt)) ))

(defthm
  slurp-disk-image-guard-lemma-20
  (equal (bpb_rsvdseccnt (update-bs_jmpboot v fat32-in-memory))
         (bpb_rsvdseccnt fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_rsvdseccnt)) ))

(defthm
  slurp-disk-image-guard-lemma-21
  (equal (bpb_rsvdseccnt (update-bs_filsystype v fat32-in-memory))
         (bpb_rsvdseccnt fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_rsvdseccnt)) ))

(defthm
  slurp-disk-image-guard-lemma-22
  (<= 1
      (bpb_rsvdseccnt
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory channel state))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t :in-theory (disable fat32-in-memoryp))))

(defthm
  slurp-disk-image-guard-lemma-23
  (equal (bpb_numfats (update-bs_oemname v fat32-in-memory))
         (bpb_numfats fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_numfats)) ))

(defthm
  slurp-disk-image-guard-lemma-24
  (equal (bpb_numfats (update-bs_jmpboot v fat32-in-memory))
         (bpb_numfats fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_numfats)) ))

(defthm
  slurp-disk-image-guard-lemma-25
  (equal (bpb_numfats (update-bs_filsystype v fat32-in-memory))
         (bpb_numfats fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_numfats)) ))

(defthm
  slurp-disk-image-guard-lemma-26
  (<= 1
      (bpb_numfats
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory channel state))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t :in-theory (disable fat32-in-memoryp))))

(defthm
  slurp-disk-image-guard-lemma-27
  (equal (bpb_fatsz32 (update-bs_oemname v fat32-in-memory))
         (bpb_fatsz32 fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_fatsz32)) ))

(defthm
  slurp-disk-image-guard-lemma-28
  (equal (bpb_fatsz32 (update-bs_jmpboot v fat32-in-memory))
         (bpb_fatsz32 fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_fatsz32)) ))

(defthm
  slurp-disk-image-guard-lemma-29
  (equal (bpb_fatsz32 (update-bs_filsystype v fat32-in-memory))
         (bpb_fatsz32 fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_fatsz32)) ))

(defthm
  slurp-disk-image-guard-lemma-30
  (<= 1
      (bpb_fatsz32
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory channel state))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t :in-theory (disable fat32-in-memoryp))))

(defthm
  read-reserved-area-correctness-1
  (implies (and (state-p state)
                (symbolp channel)
                (open-input-channel-p channel
                                      :byte state)
                (fat32-in-memoryp fat32-in-memory))
           (fat32-in-memoryp
            (mv-nth 0
                    (read-reserved-area fat32-in-memory channel state))))
  :instructions
  ((:in-theory (disable fat32-in-memoryp))
   :bash
   (:use
    (:instance
     read-byte$-n-data
     (state (mv-nth 1 (read-byte$-n 16 channel state)))
     (n (+ -16
           (* (combine16u (nth 12
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth 11
                               (mv-nth 0 (read-byte$-n 16 channel state))))
              (combine16u (nth 15
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth 14
                               (mv-nth 0
                                       (read-byte$-n 16 channel state)))))))))
   :promote (:demote 1)
   (:dive 1 1)
   :s :up
   :s :top
   :promote :bash))

;; state-p actually needs to be enabled for this guard proof because all the
;; lemmas are in terms of state-p1
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
                          read-reserved-area))
     ("Subgoal 25"
      :use
      ((:instance
        slurp-disk-image-guard-lemma-14
        (fat32-in-memory
         (mv-nth 0
                 (read-reserved-area fat32-in-memory
                                     (mv-nth 0
                                             (open-input-channel image-path
                                                                 :byte state))
                                     (mv-nth 1
                                             (open-input-channel image-path
                                                                 :byte
                                                                 state))))))
       (:instance
        slurp-disk-image-guard-lemma-18
        (channel
         (mv-nth 0
                 (open-input-channel image-path
                                     :byte state)))
        (state
         (mv-nth 1
                 (open-input-channel image-path
                                     :byte state))))
       (:instance
        slurp-disk-image-guard-lemma-22
        (channel
         (mv-nth 0
                 (open-input-channel image-path
                                     :byte state)))
        (state
         (mv-nth 1
                 (open-input-channel image-path
                                     :byte state))))
       (:instance
        slurp-disk-image-guard-lemma-26
        (channel
         (mv-nth 0
                 (open-input-channel image-path
                                     :byte state)))
        (state
         (mv-nth 1
                 (open-input-channel image-path
                                     :byte state)))))))
    :stobjs (state fat32-in-memory)))
  (b* (((mv channel state)
        (open-input-channel image-path
                            :byte state))
       ((unless channel)
        (mv fat32-in-memory state -1))
       ((mv fat32-in-memory state error-code)
        (read-reserved-area fat32-in-memory channel state))
       ((unless (and (equal error-code 0) (open-input-channel-p channel :byte state)))
        (mv fat32-in-memory state error-code))
       ((mv fat32-in-memory state error-code)
        (read-fat fat32-in-memory channel state))
       ((unless (equal error-code 0))
        (mv fat32-in-memory state error-code))
       (state (close-input-channel channel state))
       (tmp_secperclus (bpb_secperclus fat32-in-memory))
       (tmp_init (* tmp_secperclus
                    (+ (bpb_rsvdseccnt fat32-in-memory)
                       (* (bpb_numfats fat32-in-memory) (bpb_fatsz32
                                                         fat32-in-memory)))))
       (str
        (read-file-into-string image-path
                               :bytes
                               (data-region-length fat32-in-memory)))
       ((unless (stringp str))
        (mv fat32-in-memory state -1))
       (fat32-in-memory
        (update-data-region
         fat32-in-memory
         str
         tmp_init
         0)))
    (mv fat32-in-memory state error-code)))

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
