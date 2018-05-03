(in-package "ACL2")

;  file-system-m2.lisp                                  Mihir Mehta

; This is a stobj model of the FAT32 filesystem.

(include-book "file-system-lemmas")
(include-book "fat32")
(include-book "std/io/read-ints" :dir :system)
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/lists/resize-list" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)

;; Consider moving this to one of the main books
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

;; This must be called after the file is opened.
(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top"
                       :dir :system))

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
      :guard-hints
      (("goal" :do-not-induct t
        :in-theory (disable fat32-in-memoryp
                            state-p unsigned-byte-p nth)
        :use ((:instance
               read-byte$-n-data
               (n *initialbytcnt*))
              (:instance
               read-byte$-n-data
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
                (MV-NTH 1 (READ-BYTE$-N 16 CHANNEL STATE))))
              (:instance
               unsigned-byte-listp-of-take
               (width 8)
               (n 3)
               (x
                (MV-NTH 0 (READ-BYTE$-N 16 CHANNEL STATE)))))))
      :stobjs (state fat32-in-memory)))
    (b*
        (;; common stuff for FAT filesystems
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
         (fat32-in-memory
          (update-bpb_secperclus (nth 13 initial-bytes)
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
         (fat32-in-memory
          (update-bpb_numfats (nth (- 16 *initialbytcnt*) remaining_rsvdbyts)
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
         ;; FAT32-specific stuff
         (fat32-in-memory
          (update-bpb_fatsz32
           (combine32u (nth (+ 36 3 (- *initialbytcnt*)) remaining_rsvdbyts)
                       (nth (+ 36 2 (- *initialbytcnt*)) remaining_rsvdbyts)
                       (nth (+ 36 1 (- *initialbytcnt*)) remaining_rsvdbyts)
                       (nth (+ 36 0 (- *initialbytcnt*)) remaining_rsvdbyts))
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
      (mv fat32-in-memory state 0))))

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
  (fat32-in-memory str pos)
  (declare
   (xargs
    :measure (nfix (- (data-region-length fat32-in-memory)
                      pos))
    :guard (and (natp pos)
                (stringp str)
                (<= (data-region-length fat32-in-memory)
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
            (char-code (char str pos)))
       fat32-in-memory))
     (fat32-in-memory
      (update-data-region fat32-in-memory str (+ pos 1))))
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
       ;; (fat32-in-memory (update-data-region data-region fat32-in-memory))
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
                    bpb_numfats bpb_bytspersec update-bpb_secperclus
                    update-bpb_rsvdseccnt update-bpb_bytspersec
                    update-bpb_numfats))

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

(defthm
  slurp-disk-image-guard-lemma-7
  (implies
   (not (equal key *bpb_fatsz32*))
   (equal
    (bpb_fatsz32 (update-nth key val fat32-in-memory))
    (bpb_fatsz32 fat32-in-memory)))
  :hints (("goal" :in-theory (enable bpb_fatsz32))))

(defthm
  slurp-disk-image-guard-lemma-8
  (implies
   (not (equal key *bpb_secperclus*))
   (equal
    (bpb_secperclus (update-nth key val fat32-in-memory))
    (bpb_secperclus fat32-in-memory)))
  :hints (("goal" :in-theory (enable bpb_secperclus))))

(defthm
  slurp-disk-image-guard-lemma-9
  (implies
   (not (equal key *bpb_rsvdseccnt*))
   (equal
    (bpb_rsvdseccnt (update-nth key val fat32-in-memory))
    (bpb_rsvdseccnt fat32-in-memory)))
  :hints (("goal" :in-theory (enable bpb_rsvdseccnt))))

(defthm
  slurp-disk-image-guard-lemma-10
  (implies
   (not (equal key *bpb_numfats*))
   (equal
    (bpb_numfats (update-nth key val fat32-in-memory))
    (bpb_numfats fat32-in-memory)))
  :hints (("goal" :in-theory (enable bpb_numfats))))

;; Check out Subgoal 1.3.3'

(defthm
  slurp-disk-image-guard-lemma-11
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (integerp
    (bpb_secperclus fat32-in-memory)))
  :hints (("goal" :in-theory (enable bpb_secperclus))))

(defthm
  slurp-disk-image-guard-lemma-12
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (integerp
    (bpb_rsvdseccnt fat32-in-memory)))
  :hints (("goal" :in-theory (enable bpb_rsvdseccnt))))

(defthm
  slurp-disk-image-guard-lemma-13
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (integerp
    (bpb_numfats fat32-in-memory)))
  :hints (("goal" :in-theory (enable bpb_numfats))))

(defthm
  slurp-disk-image-guard-lemma-14
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (integerp
    (bpb_fatsz32 fat32-in-memory)))
  :hints (("goal" :in-theory (enable bpb_fatsz32))))

(defthm
  slurp-disk-image-guard-lemma-15
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (integerp
    (bpb_bytspersec fat32-in-memory)))
  :hints (("goal" :in-theory (enable bpb_bytspersec))))

(defthm
  slurp-disk-image-guard-lemma-16
  (implies (and (integerp x) (integerp y))
           (integerp (+ x y))))

(defthm
  slurp-disk-image-guard-lemma-17
  (implies (and (integerp x) (integerp y))
           (integerp (* x y))))

(defthm
  slurp-disk-image-guard-lemma-20
  (implies (and (unsigned-byte-p 16 v)
                (fat32-in-memoryp fat32-in-memory))
           (fat32-in-memoryp
            (update-bpb_rsvdseccnt v fat32-in-memory)))
  :hints (("Goal" :in-theory (enable update-bpb_rsvdseccnt)) ))

(defthm
  slurp-disk-image-guard-lemma-21
  (implies (and (unsigned-byte-p 8 v)
                (fat32-in-memoryp fat32-in-memory))
           (fat32-in-memoryp
            (update-bpb_secperclus v fat32-in-memory)))
  :hints (("Goal" :in-theory (enable update-bpb_secperclus)) ))

(defthm
  slurp-disk-image-guard-lemma-22
  (implies (and (unsigned-byte-p 16 v)
                (fat32-in-memoryp fat32-in-memory))
           (fat32-in-memoryp
            (update-bpb_bytspersec v fat32-in-memory)))
  :hints (("Goal" :in-theory (enable update-bpb_bytspersec)) ))

(defthm
  slurp-disk-image-guard-lemma-23
  (implies (and (unsigned-byte-p 8 v)
                (fat32-in-memoryp fat32-in-memory))
           (fat32-in-memoryp
            (update-bpb_numfats v fat32-in-memory)))
  :hints (("Goal" :in-theory (enable update-bpb_numfats)) ))

(defthm
  slurp-disk-image-guard-lemma-24
  (equal (stringp (mv-nth 0 (read-byte$-n n channel state)))
         nil)
  :hints (("goal" :in-theory (disable read-byte$-n-data)
           :use read-byte$-n-data)))

(verify
 (implies
  (and (state-p state)
       (symbolp channel)
       (open-input-channel-p channel
                             :byte state)
       (fat32-in-memoryp fat32-in-memory))
  (fat32-in-memoryp
   (mv-nth 0
           (read-reserved-area
            fat32-in-memory channel state))))
 :instructions
 ((:in-theory (disable fat32-in-memoryp))
  :promote (:dive 1 2)
  (:expand t)
  :top :split
  (:claim
   (and
    (unsigned-byte-listp
     8
     (subseq (mv-nth 0 (read-byte$-n 16 channel state))
             3 8))
    (<= (len (subseq (mv-nth 0 (read-byte$-n 16 channel state))
                     3 8))
        (bs_oemname-length
         (update-bs_jmpboot
          (subseq (mv-nth 0 (read-byte$-n 16 channel state))
                  0 3)
          fat32-in-memory)))
    (fat32-in-memoryp
     (update-bs_jmpboot (subseq (mv-nth 0 (read-byte$-n 16 channel state))
                                0 3)
                        fat32-in-memory)))
   :hints :none)
  (:rewrite update-bs_oemname-correctness-1)
  :bash
  (:use (:instance read-byte$-n-data (n 16)))
  :bash :bash :bash
  (:claim
   (and
    (unsigned-byte-listp
     8
     (subseq
      (mv-nth
       0
       (read-byte$-n
        (+
         (* (combine16u (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
            (combine16u (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
         -16)
        channel
        (mv-nth 1 (read-byte$-n 16 channel state))))
      66 74))
    (<=
     (len
      (subseq
       (mv-nth
        0
        (read-byte$-n
         (+
          (*
           (combine16u (nth 15
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 14
                            (mv-nth 0 (read-byte$-n 16 channel state))))
           (combine16u (nth 12
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 11
                            (mv-nth 0 (read-byte$-n 16 channel state)))))
          -16)
         channel
         (mv-nth 1 (read-byte$-n 16 channel state))))
       66 74))
     (bs_filsystype-length
      (update-bpb_rootclus
       (combine32u
        (nth
         54
         (mv-nth
          0
          (read-byte$-n
           (+
            (*
             (combine16u (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
             (combine16u
              (nth 12
                   (mv-nth 0 (read-byte$-n 16 channel state)))
              (nth 11
                   (mv-nth 0 (read-byte$-n 16 channel state)))))
            -16)
           channel
           (mv-nth 1 (read-byte$-n 16 channel state)))))
        (nth
         53
         (mv-nth
          0
          (read-byte$-n
           (+
            (*
             (combine16u (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
             (combine16u
              (nth 12
                   (mv-nth 0 (read-byte$-n 16 channel state)))
              (nth 11
                   (mv-nth 0 (read-byte$-n 16 channel state)))))
            -16)
           channel
           (mv-nth 1 (read-byte$-n 16 channel state)))))
        (nth
         52
         (mv-nth
          0
          (read-byte$-n
           (+
            (*
             (combine16u (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
             (combine16u
              (nth 12
                   (mv-nth 0 (read-byte$-n 16 channel state)))
              (nth 11
                   (mv-nth 0 (read-byte$-n 16 channel state)))))
            -16)
           channel
           (mv-nth 1 (read-byte$-n 16 channel state)))))
        (nth
         51
         (mv-nth
          0
          (read-byte$-n
           (+
            (*
             (combine16u (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
             (combine16u
              (nth 12
                   (mv-nth 0 (read-byte$-n 16 channel state)))
              (nth 11
                   (mv-nth 0 (read-byte$-n 16 channel state)))))
            -16)
           channel
           (mv-nth 1 (read-byte$-n 16 channel state))))))
       (update-bs_bootsig
        (nth
         50
         (mv-nth
          0
          (read-byte$-n
           (+
            (*
             (combine16u (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
             (combine16u
              (nth 12
                   (mv-nth 0 (read-byte$-n 16 channel state)))
              (nth 11
                   (mv-nth 0 (read-byte$-n 16 channel state)))))
            -16)
           channel
           (mv-nth 1 (read-byte$-n 16 channel state)))))
        (update-bs_reserved1
         (nth
          49
          (mv-nth
           0
           (read-byte$-n
            (+ (* (combine16u
                   (nth 15
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 14
                        (mv-nth 0 (read-byte$-n 16 channel state))))
                  (combine16u
                   (nth 12
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 11
                        (mv-nth 0 (read-byte$-n 16 channel state)))))
               -16)
            channel
            (mv-nth 1 (read-byte$-n 16 channel state)))))
         (update-bs_drvnum
          (nth
           48
           (mv-nth
            0
            (read-byte$-n
             (+ (* (combine16u
                    (nth 15
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 14
                         (mv-nth 0 (read-byte$-n 16 channel state))))
                   (combine16u
                    (nth 12
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 11
                         (mv-nth 0 (read-byte$-n 16 channel state)))))
                -16)
             channel
             (mv-nth 1 (read-byte$-n 16 channel state)))))
          (update-bpb_bkbootsec
           (combine16u
            (nth
             35
             (mv-nth
              0
              (read-byte$-n
               (+
                (* (combine16u
                    (nth 15
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 14
                         (mv-nth 0 (read-byte$-n 16 channel state))))
                   (combine16u
                    (nth 12
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 11
                         (mv-nth 0 (read-byte$-n 16 channel state)))))
                -16)
               channel
               (mv-nth 1 (read-byte$-n 16 channel state)))))
            (nth
             34
             (mv-nth
              0
              (read-byte$-n
               (+
                (* (combine16u
                    (nth 15
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 14
                         (mv-nth 0 (read-byte$-n 16 channel state))))
                   (combine16u
                    (nth 12
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 11
                         (mv-nth 0 (read-byte$-n 16 channel state)))))
                -16)
               channel
               (mv-nth 1 (read-byte$-n 16 channel state))))))
           (update-bpb_fsinfo
            (combine16u
             (nth
              33
              (mv-nth
               0
               (read-byte$-n
                (+
                 (*
                  (combine16u
                   (nth 15
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 14
                        (mv-nth 0 (read-byte$-n 16 channel state))))
                  (combine16u
                   (nth 12
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 11
                        (mv-nth 0 (read-byte$-n 16 channel state)))))
                 -16)
                channel
                (mv-nth 1 (read-byte$-n 16 channel state)))))
             (nth
              32
              (mv-nth
               0
               (read-byte$-n
                (+
                 (*
                  (combine16u
                   (nth 15
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 14
                        (mv-nth 0 (read-byte$-n 16 channel state))))
                  (combine16u
                   (nth 12
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 11
                        (mv-nth 0 (read-byte$-n 16 channel state)))))
                 -16)
                channel
                (mv-nth 1 (read-byte$-n 16 channel state))))))
            (update-bpb_rootclus
             (combine32u
              (nth
               31
               (mv-nth
                0
                (read-byte$-n
                 (+
                  (*
                   (combine16u
                    (nth 15
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 14
                         (mv-nth 0 (read-byte$-n 16 channel state))))
                   (combine16u
                    (nth 12
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 11
                         (mv-nth 0 (read-byte$-n 16 channel state)))))
                  -16)
                 channel
                 (mv-nth 1 (read-byte$-n 16 channel state)))))
              (nth
               30
               (mv-nth
                0
                (read-byte$-n
                 (+
                  (*
                   (combine16u
                    (nth 15
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 14
                         (mv-nth 0 (read-byte$-n 16 channel state))))
                   (combine16u
                    (nth 12
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 11
                         (mv-nth 0 (read-byte$-n 16 channel state)))))
                  -16)
                 channel
                 (mv-nth 1 (read-byte$-n 16 channel state)))))
              (nth
               29
               (mv-nth
                0
                (read-byte$-n
                 (+
                  (*
                   (combine16u
                    (nth 15
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 14
                         (mv-nth 0 (read-byte$-n 16 channel state))))
                   (combine16u
                    (nth 12
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 11
                         (mv-nth 0 (read-byte$-n 16 channel state)))))
                  -16)
                 channel
                 (mv-nth 1 (read-byte$-n 16 channel state)))))
              (nth
               28
               (mv-nth
                0
                (read-byte$-n
                 (+
                  (*
                   (combine16u
                    (nth 15
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 14
                         (mv-nth 0 (read-byte$-n 16 channel state))))
                   (combine16u
                    (nth 12
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 11
                         (mv-nth 0 (read-byte$-n 16 channel state)))))
                  -16)
                 channel
                 (mv-nth 1 (read-byte$-n 16 channel state))))))
             (update-bpb_fsver_major
              (nth
               27
               (mv-nth
                0
                (read-byte$-n
                 (+
                  (*
                   (combine16u
                    (nth 15
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 14
                         (mv-nth 0 (read-byte$-n 16 channel state))))
                   (combine16u
                    (nth 12
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 11
                         (mv-nth 0 (read-byte$-n 16 channel state)))))
                  -16)
                 channel
                 (mv-nth 1 (read-byte$-n 16 channel state)))))
              (update-bpb_fsver_minor
               (nth
                26
                (mv-nth
                 0
                 (read-byte$-n
                  (+
                   (*
                    (combine16u
                     (nth 15
                          (mv-nth 0 (read-byte$-n 16 channel state)))
                     (nth 14
                          (mv-nth 0 (read-byte$-n 16 channel state))))
                    (combine16u
                     (nth 12
                          (mv-nth 0 (read-byte$-n 16 channel state)))
                     (nth 11
                          (mv-nth 0 (read-byte$-n 16 channel state)))))
                   -16)
                  channel
                  (mv-nth 1 (read-byte$-n 16 channel state)))))
               (update-bpb_extflags
                (combine16u
                 (nth
                  25
                  (mv-nth
                   0
                   (read-byte$-n
                    (+
                     (*
                      (combine16u
                       (nth 15
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 14
                            (mv-nth 0 (read-byte$-n 16 channel state))))
                      (combine16u
                       (nth 12
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 11
                            (mv-nth 0 (read-byte$-n 16 channel state)))))
                     -16)
                    channel
                    (mv-nth 1 (read-byte$-n 16 channel state)))))
                 (nth
                  24
                  (mv-nth
                   0
                   (read-byte$-n
                    (+
                     (*
                      (combine16u
                       (nth 15
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 14
                            (mv-nth 0 (read-byte$-n 16 channel state))))
                      (combine16u
                       (nth 12
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 11
                            (mv-nth 0 (read-byte$-n 16 channel state)))))
                     -16)
                    channel
                    (mv-nth 1 (read-byte$-n 16 channel state))))))
                (update-bpb_fatsz32
                 (combine32u
                  (nth
                   23
                   (mv-nth
                    0
                    (read-byte$-n
                     (+
                      (*
                       (combine16u
                        (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                       (combine16u
                        (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
                      -16)
                     channel
                     (mv-nth 1 (read-byte$-n 16 channel state)))))
                  (nth
                   22
                   (mv-nth
                    0
                    (read-byte$-n
                     (+
                      (*
                       (combine16u
                        (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                       (combine16u
                        (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
                      -16)
                     channel
                     (mv-nth 1 (read-byte$-n 16 channel state)))))
                  (nth
                   21
                   (mv-nth
                    0
                    (read-byte$-n
                     (+
                      (*
                       (combine16u
                        (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                       (combine16u
                        (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
                      -16)
                     channel
                     (mv-nth 1 (read-byte$-n 16 channel state)))))
                  (nth
                   20
                   (mv-nth
                    0
                    (read-byte$-n
                     (+
                      (*
                       (combine16u
                        (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                       (combine16u
                        (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
                      -16)
                     channel
                     (mv-nth 1 (read-byte$-n 16 channel state))))))
                 (update-bpb_totsec32
                  (combine32u
                   (nth
                    19
                    (mv-nth
                     0
                     (read-byte$-n
                      (+
                       (*
                        (combine16u
                         (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
                        (combine16u
                         (nth 12
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth
                          11
                          (mv-nth 0 (read-byte$-n 16 channel state)))))
                       -16)
                      channel
                      (mv-nth 1 (read-byte$-n 16 channel state)))))
                   (nth
                    18
                    (mv-nth
                     0
                     (read-byte$-n
                      (+
                       (*
                        (combine16u
                         (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
                        (combine16u
                         (nth 12
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth
                          11
                          (mv-nth 0 (read-byte$-n 16 channel state)))))
                       -16)
                      channel
                      (mv-nth 1 (read-byte$-n 16 channel state)))))
                   (nth
                    17
                    (mv-nth
                     0
                     (read-byte$-n
                      (+
                       (*
                        (combine16u
                         (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
                        (combine16u
                         (nth 12
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth
                          11
                          (mv-nth 0 (read-byte$-n 16 channel state)))))
                       -16)
                      channel
                      (mv-nth 1 (read-byte$-n 16 channel state)))))
                   (nth
                    16
                    (mv-nth
                     0
                     (read-byte$-n
                      (+
                       (*
                        (combine16u
                         (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
                        (combine16u
                         (nth 12
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth
                          11
                          (mv-nth 0 (read-byte$-n 16 channel state)))))
                       -16)
                      channel
                      (mv-nth 1 (read-byte$-n 16 channel state))))))
                  (update-bpb_hiddsec
                   (combine32u
                    (nth
                     15
                     (mv-nth
                      0
                      (read-byte$-n
                       (+
                        (*
                         (combine16u
                          (nth 15
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth
                           14
                           (mv-nth 0 (read-byte$-n 16 channel state))))
                         (combine16u
                          (nth 12
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth
                           11
                           (mv-nth 0 (read-byte$-n 16 channel state)))))
                        -16)
                       channel
                       (mv-nth 1 (read-byte$-n 16 channel state)))))
                    (nth
                     14
                     (mv-nth
                      0
                      (read-byte$-n
                       (+
                        (*
                         (combine16u
                          (nth 15
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth
                           14
                           (mv-nth 0 (read-byte$-n 16 channel state))))
                         (combine16u
                          (nth 12
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth
                           11
                           (mv-nth 0 (read-byte$-n 16 channel state)))))
                        -16)
                       channel
                       (mv-nth 1 (read-byte$-n 16 channel state)))))
                    (nth
                     13
                     (mv-nth
                      0
                      (read-byte$-n
                       (+
                        (*
                         (combine16u
                          (nth 15
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth
                           14
                           (mv-nth 0 (read-byte$-n 16 channel state))))
                         (combine16u
                          (nth 12
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth
                           11
                           (mv-nth 0 (read-byte$-n 16 channel state)))))
                        -16)
                       channel
                       (mv-nth 1 (read-byte$-n 16 channel state)))))
                    (nth
                     12
                     (mv-nth
                      0
                      (read-byte$-n
                       (+
                        (*
                         (combine16u
                          (nth 15
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth
                           14
                           (mv-nth 0 (read-byte$-n 16 channel state))))
                         (combine16u
                          (nth 12
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth
                           11
                           (mv-nth 0 (read-byte$-n 16 channel state)))))
                        -16)
                       channel
                       (mv-nth 1 (read-byte$-n 16 channel state))))))
                   (update-bpb_numheads
                    (combine16u
                     (nth
                      11
                      (mv-nth
                       0
                       (read-byte$-n
                        (+
                         (*
                          (combine16u
                           (nth
                            15
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                           (nth
                            14
                            (mv-nth 0 (read-byte$-n 16 channel state))))
                          (combine16u
                           (nth
                            12
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                           (nth
                            11
                            (mv-nth 0 (read-byte$-n 16 channel state)))))
                         -16)
                        channel
                        (mv-nth 1 (read-byte$-n 16 channel state)))))
                     (nth
                      10
                      (mv-nth
                       0
                       (read-byte$-n
                        (+
                         (*
                          (combine16u
                           (nth
                            15
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                           (nth
                            14
                            (mv-nth 0 (read-byte$-n 16 channel state))))
                          (combine16u
                           (nth
                            12
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                           (nth
                            11
                            (mv-nth 0 (read-byte$-n 16 channel state)))))
                         -16)
                        channel
                        (mv-nth 1 (read-byte$-n 16 channel state))))))
                    (update-bpb_secpertrk
                     (combine16u
                      (nth
                       9
                       (mv-nth
                        0
                        (read-byte$-n
                         (+
                          (*
                           (combine16u
                            (nth
                             15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                            (nth
                             14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                           (combine16u
                            (nth
                             12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                            (nth
                             11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
                          -16)
                         channel
                         (mv-nth 1 (read-byte$-n 16 channel state)))))
                      (nth
                       8
                       (mv-nth
                        0
                        (read-byte$-n
                         (+
                          (*
                           (combine16u
                            (nth
                             15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                            (nth
                             14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                           (combine16u
                            (nth
                             12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                            (nth
                             11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
                          -16)
                         channel
                         (mv-nth 1 (read-byte$-n 16 channel state))))))
                     (update-bpb_fatsz16
                      (combine16u
                       (nth
                        7
                        (mv-nth
                         0
                         (read-byte$-n
                          (+
                           (*
                            (combine16u
                             (nth
                              15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                             (nth
                              14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
                            (combine16u
                             (nth
                              12
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                             (nth
                              11
                              (mv-nth
                               0 (read-byte$-n 16 channel state)))))
                           -16)
                          channel
                          (mv-nth 1 (read-byte$-n 16 channel state)))))
                       (nth
                        6
                        (mv-nth
                         0
                         (read-byte$-n
                          (+
                           (*
                            (combine16u
                             (nth
                              15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                             (nth
                              14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
                            (combine16u
                             (nth
                              12
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                             (nth
                              11
                              (mv-nth
                               0 (read-byte$-n 16 channel state)))))
                           -16)
                          channel
                          (mv-nth 1 (read-byte$-n 16 channel state))))))
                      (update-bpb_media
                       (nth
                        5
                        (mv-nth
                         0
                         (read-byte$-n
                          (+
                           (*
                            (combine16u
                             (nth
                              15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                             (nth
                              14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
                            (combine16u
                             (nth
                              12
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                             (nth
                              11
                              (mv-nth
                               0 (read-byte$-n 16 channel state)))))
                           -16)
                          channel
                          (mv-nth 1 (read-byte$-n 16 channel state)))))
                       (update-bpb_totsec16
                        (combine16u
                         (nth
                          4
                          (mv-nth
                           0
                           (read-byte$-n
                            (+
                             (*
                              (combine16u
                               (nth
                                15
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))
                               (nth
                                14
                                (mv-nth
                                 0 (read-byte$-n 16 channel state))))
                              (combine16u
                               (nth
                                12
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))
                               (nth
                                11
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))))
                             -16)
                            channel
                            (mv-nth 1 (read-byte$-n 16 channel state)))))
                         (nth
                          3
                          (mv-nth
                           0
                           (read-byte$-n
                            (+
                             (*
                              (combine16u
                               (nth
                                15
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))
                               (nth
                                14
                                (mv-nth
                                 0 (read-byte$-n 16 channel state))))
                              (combine16u
                               (nth
                                12
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))
                               (nth
                                11
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))))
                             -16)
                            channel
                            (mv-nth 1 (read-byte$-n 16 channel state))))))
                        (update-bpb_rootentcnt
                         (combine16u
                          (nth
                           2
                           (mv-nth
                            0
                            (read-byte$-n
                             (+
                              (*
                               (combine16u
                                (nth
                                 15
                                 (mv-nth
                                  0 (read-byte$-n 16 channel state)))
                                (nth
                                 14
                                 (mv-nth
                                  0 (read-byte$-n 16 channel state))))
                               (combine16u
                                (nth
                                 12
                                 (mv-nth
                                  0 (read-byte$-n 16 channel state)))
                                (nth
                                 11
                                 (mv-nth
                                  0 (read-byte$-n 16 channel state)))))
                              -16)
                             channel
                             (mv-nth 1 (read-byte$-n 16 channel state)))))
                          (nth
                           1
                           (mv-nth
                            0
                            (read-byte$-n
                             (+
                              (*
                               (combine16u
                                (nth
                                 15
                                 (mv-nth
                                  0 (read-byte$-n 16 channel state)))
                                (nth
                                 14
                                 (mv-nth
                                  0 (read-byte$-n 16 channel state))))
                               (combine16u
                                (nth
                                 12
                                 (mv-nth
                                  0 (read-byte$-n 16 channel state)))
                                (nth
                                 11
                                 (mv-nth
                                  0 (read-byte$-n 16 channel state)))))
                              -16)
                             channel
                             (mv-nth
                              1 (read-byte$-n 16 channel state))))))
                         (update-bpb_numfats
                          (nth
                           0
                           (mv-nth
                            0
                            (read-byte$-n
                             (+
                              (*
                               (combine16u
                                (nth
                                 15
                                 (mv-nth
                                  0 (read-byte$-n 16 channel state)))
                                (nth
                                 14
                                 (mv-nth
                                  0 (read-byte$-n 16 channel state))))
                               (combine16u
                                (nth
                                 12
                                 (mv-nth
                                  0 (read-byte$-n 16 channel state)))
                                (nth
                                 11
                                 (mv-nth
                                  0 (read-byte$-n 16 channel state)))))
                              -16)
                             channel
                             (mv-nth 1 (read-byte$-n 16 channel state)))))
                          (update-bpb_rsvdseccnt
                           (combine16u
                            (nth
                             15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                            (nth
                             14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                           (update-bpb_secperclus
                            (nth
                             13
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                            (update-bpb_bytspersec
                             (combine16u
                              (nth
                               12
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                              (nth
                               11
                               (mv-nth
                                0 (read-byte$-n 16 channel state))))
                             (update-bs_oemname
                              (subseq
                               (mv-nth 0 (read-byte$-n 16 channel state))
                               3 8)
                              (update-bs_jmpboot
                               (subseq
                                (mv-nth 0 (read-byte$-n 16 channel state))
                                0 3)
                               fat32-in-memory)))))))))))))))))))))))))))
    (fat32-in-memoryp
     (update-bpb_rootclus
      (combine32u
       (nth
        54
        (mv-nth
         0
         (read-byte$-n
          (+
           (*
            (combine16u (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
            (combine16u (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
           -16)
          channel
          (mv-nth 1 (read-byte$-n 16 channel state)))))
       (nth
        53
        (mv-nth
         0
         (read-byte$-n
          (+
           (*
            (combine16u (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
            (combine16u (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
           -16)
          channel
          (mv-nth 1 (read-byte$-n 16 channel state)))))
       (nth
        52
        (mv-nth
         0
         (read-byte$-n
          (+
           (*
            (combine16u (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
            (combine16u (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
           -16)
          channel
          (mv-nth 1 (read-byte$-n 16 channel state)))))
       (nth
        51
        (mv-nth
         0
         (read-byte$-n
          (+
           (*
            (combine16u (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
            (combine16u (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
           -16)
          channel
          (mv-nth 1 (read-byte$-n 16 channel state))))))
      (update-bs_bootsig
       (nth
        50
        (mv-nth
         0
         (read-byte$-n
          (+
           (*
            (combine16u (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
            (combine16u (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
           -16)
          channel
          (mv-nth 1 (read-byte$-n 16 channel state)))))
       (update-bs_reserved1
        (nth
         49
         (mv-nth
          0
          (read-byte$-n
           (+
            (*
             (combine16u (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
             (combine16u
              (nth 12
                   (mv-nth 0 (read-byte$-n 16 channel state)))
              (nth 11
                   (mv-nth 0 (read-byte$-n 16 channel state)))))
            -16)
           channel
           (mv-nth 1 (read-byte$-n 16 channel state)))))
        (update-bs_drvnum
         (nth
          48
          (mv-nth
           0
           (read-byte$-n
            (+ (* (combine16u
                   (nth 15
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 14
                        (mv-nth 0 (read-byte$-n 16 channel state))))
                  (combine16u
                   (nth 12
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 11
                        (mv-nth 0 (read-byte$-n 16 channel state)))))
               -16)
            channel
            (mv-nth 1 (read-byte$-n 16 channel state)))))
         (update-bpb_bkbootsec
          (combine16u
           (nth
            35
            (mv-nth
             0
             (read-byte$-n
              (+
               (* (combine16u
                   (nth 15
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 14
                        (mv-nth 0 (read-byte$-n 16 channel state))))
                  (combine16u
                   (nth 12
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 11
                        (mv-nth 0 (read-byte$-n 16 channel state)))))
               -16)
              channel
              (mv-nth 1 (read-byte$-n 16 channel state)))))
           (nth
            34
            (mv-nth
             0
             (read-byte$-n
              (+
               (* (combine16u
                   (nth 15
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 14
                        (mv-nth 0 (read-byte$-n 16 channel state))))
                  (combine16u
                   (nth 12
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 11
                        (mv-nth 0 (read-byte$-n 16 channel state)))))
               -16)
              channel
              (mv-nth 1 (read-byte$-n 16 channel state))))))
          (update-bpb_fsinfo
           (combine16u
            (nth
             33
             (mv-nth
              0
              (read-byte$-n
               (+
                (* (combine16u
                    (nth 15
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 14
                         (mv-nth 0 (read-byte$-n 16 channel state))))
                   (combine16u
                    (nth 12
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 11
                         (mv-nth 0 (read-byte$-n 16 channel state)))))
                -16)
               channel
               (mv-nth 1 (read-byte$-n 16 channel state)))))
            (nth
             32
             (mv-nth
              0
              (read-byte$-n
               (+
                (* (combine16u
                    (nth 15
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 14
                         (mv-nth 0 (read-byte$-n 16 channel state))))
                   (combine16u
                    (nth 12
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 11
                         (mv-nth 0 (read-byte$-n 16 channel state)))))
                -16)
               channel
               (mv-nth 1 (read-byte$-n 16 channel state))))))
           (update-bpb_rootclus
            (combine32u
             (nth
              31
              (mv-nth
               0
               (read-byte$-n
                (+
                 (*
                  (combine16u
                   (nth 15
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 14
                        (mv-nth 0 (read-byte$-n 16 channel state))))
                  (combine16u
                   (nth 12
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 11
                        (mv-nth 0 (read-byte$-n 16 channel state)))))
                 -16)
                channel
                (mv-nth 1 (read-byte$-n 16 channel state)))))
             (nth
              30
              (mv-nth
               0
               (read-byte$-n
                (+
                 (*
                  (combine16u
                   (nth 15
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 14
                        (mv-nth 0 (read-byte$-n 16 channel state))))
                  (combine16u
                   (nth 12
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 11
                        (mv-nth 0 (read-byte$-n 16 channel state)))))
                 -16)
                channel
                (mv-nth 1 (read-byte$-n 16 channel state)))))
             (nth
              29
              (mv-nth
               0
               (read-byte$-n
                (+
                 (*
                  (combine16u
                   (nth 15
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 14
                        (mv-nth 0 (read-byte$-n 16 channel state))))
                  (combine16u
                   (nth 12
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 11
                        (mv-nth 0 (read-byte$-n 16 channel state)))))
                 -16)
                channel
                (mv-nth 1 (read-byte$-n 16 channel state)))))
             (nth
              28
              (mv-nth
               0
               (read-byte$-n
                (+
                 (*
                  (combine16u
                   (nth 15
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 14
                        (mv-nth 0 (read-byte$-n 16 channel state))))
                  (combine16u
                   (nth 12
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 11
                        (mv-nth 0 (read-byte$-n 16 channel state)))))
                 -16)
                channel
                (mv-nth 1 (read-byte$-n 16 channel state))))))
            (update-bpb_fsver_major
             (nth
              27
              (mv-nth
               0
               (read-byte$-n
                (+
                 (*
                  (combine16u
                   (nth 15
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 14
                        (mv-nth 0 (read-byte$-n 16 channel state))))
                  (combine16u
                   (nth 12
                        (mv-nth 0 (read-byte$-n 16 channel state)))
                   (nth 11
                        (mv-nth 0 (read-byte$-n 16 channel state)))))
                 -16)
                channel
                (mv-nth 1 (read-byte$-n 16 channel state)))))
             (update-bpb_fsver_minor
              (nth
               26
               (mv-nth
                0
                (read-byte$-n
                 (+
                  (*
                   (combine16u
                    (nth 15
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 14
                         (mv-nth 0 (read-byte$-n 16 channel state))))
                   (combine16u
                    (nth 12
                         (mv-nth 0 (read-byte$-n 16 channel state)))
                    (nth 11
                         (mv-nth 0 (read-byte$-n 16 channel state)))))
                  -16)
                 channel
                 (mv-nth 1 (read-byte$-n 16 channel state)))))
              (update-bpb_extflags
               (combine16u
                (nth
                 25
                 (mv-nth
                  0
                  (read-byte$-n
                   (+
                    (*
                     (combine16u
                      (nth 15
                           (mv-nth 0 (read-byte$-n 16 channel state)))
                      (nth 14
                           (mv-nth 0 (read-byte$-n 16 channel state))))
                     (combine16u
                      (nth 12
                           (mv-nth 0 (read-byte$-n 16 channel state)))
                      (nth 11
                           (mv-nth 0 (read-byte$-n 16 channel state)))))
                    -16)
                   channel
                   (mv-nth 1 (read-byte$-n 16 channel state)))))
                (nth
                 24
                 (mv-nth
                  0
                  (read-byte$-n
                   (+
                    (*
                     (combine16u
                      (nth 15
                           (mv-nth 0 (read-byte$-n 16 channel state)))
                      (nth 14
                           (mv-nth 0 (read-byte$-n 16 channel state))))
                     (combine16u
                      (nth 12
                           (mv-nth 0 (read-byte$-n 16 channel state)))
                      (nth 11
                           (mv-nth 0 (read-byte$-n 16 channel state)))))
                    -16)
                   channel
                   (mv-nth 1 (read-byte$-n 16 channel state))))))
               (update-bpb_fatsz32
                (combine32u
                 (nth
                  23
                  (mv-nth
                   0
                   (read-byte$-n
                    (+
                     (*
                      (combine16u
                       (nth 15
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 14
                            (mv-nth 0 (read-byte$-n 16 channel state))))
                      (combine16u
                       (nth 12
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 11
                            (mv-nth 0 (read-byte$-n 16 channel state)))))
                     -16)
                    channel
                    (mv-nth 1 (read-byte$-n 16 channel state)))))
                 (nth
                  22
                  (mv-nth
                   0
                   (read-byte$-n
                    (+
                     (*
                      (combine16u
                       (nth 15
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 14
                            (mv-nth 0 (read-byte$-n 16 channel state))))
                      (combine16u
                       (nth 12
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 11
                            (mv-nth 0 (read-byte$-n 16 channel state)))))
                     -16)
                    channel
                    (mv-nth 1 (read-byte$-n 16 channel state)))))
                 (nth
                  21
                  (mv-nth
                   0
                   (read-byte$-n
                    (+
                     (*
                      (combine16u
                       (nth 15
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 14
                            (mv-nth 0 (read-byte$-n 16 channel state))))
                      (combine16u
                       (nth 12
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 11
                            (mv-nth 0 (read-byte$-n 16 channel state)))))
                     -16)
                    channel
                    (mv-nth 1 (read-byte$-n 16 channel state)))))
                 (nth
                  20
                  (mv-nth
                   0
                   (read-byte$-n
                    (+
                     (*
                      (combine16u
                       (nth 15
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 14
                            (mv-nth 0 (read-byte$-n 16 channel state))))
                      (combine16u
                       (nth 12
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                       (nth 11
                            (mv-nth 0 (read-byte$-n 16 channel state)))))
                     -16)
                    channel
                    (mv-nth 1 (read-byte$-n 16 channel state))))))
                (update-bpb_totsec32
                 (combine32u
                  (nth
                   19
                   (mv-nth
                    0
                    (read-byte$-n
                     (+
                      (*
                       (combine16u
                        (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                       (combine16u
                        (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
                      -16)
                     channel
                     (mv-nth 1 (read-byte$-n 16 channel state)))))
                  (nth
                   18
                   (mv-nth
                    0
                    (read-byte$-n
                     (+
                      (*
                       (combine16u
                        (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                       (combine16u
                        (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
                      -16)
                     channel
                     (mv-nth 1 (read-byte$-n 16 channel state)))))
                  (nth
                   17
                   (mv-nth
                    0
                    (read-byte$-n
                     (+
                      (*
                       (combine16u
                        (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                       (combine16u
                        (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
                      -16)
                     channel
                     (mv-nth 1 (read-byte$-n 16 channel state)))))
                  (nth
                   16
                   (mv-nth
                    0
                    (read-byte$-n
                     (+
                      (*
                       (combine16u
                        (nth 15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                       (combine16u
                        (nth 12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                        (nth 11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
                      -16)
                     channel
                     (mv-nth 1 (read-byte$-n 16 channel state))))))
                 (update-bpb_hiddsec
                  (combine32u
                   (nth
                    15
                    (mv-nth
                     0
                     (read-byte$-n
                      (+
                       (*
                        (combine16u
                         (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
                        (combine16u
                         (nth 12
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth
                          11
                          (mv-nth 0 (read-byte$-n 16 channel state)))))
                       -16)
                      channel
                      (mv-nth 1 (read-byte$-n 16 channel state)))))
                   (nth
                    14
                    (mv-nth
                     0
                     (read-byte$-n
                      (+
                       (*
                        (combine16u
                         (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
                        (combine16u
                         (nth 12
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth
                          11
                          (mv-nth 0 (read-byte$-n 16 channel state)))))
                       -16)
                      channel
                      (mv-nth 1 (read-byte$-n 16 channel state)))))
                   (nth
                    13
                    (mv-nth
                     0
                     (read-byte$-n
                      (+
                       (*
                        (combine16u
                         (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
                        (combine16u
                         (nth 12
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth
                          11
                          (mv-nth 0 (read-byte$-n 16 channel state)))))
                       -16)
                      channel
                      (mv-nth 1 (read-byte$-n 16 channel state)))))
                   (nth
                    12
                    (mv-nth
                     0
                     (read-byte$-n
                      (+
                       (*
                        (combine16u
                         (nth 15
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth 14
                              (mv-nth 0 (read-byte$-n 16 channel state))))
                        (combine16u
                         (nth 12
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                         (nth
                          11
                          (mv-nth 0 (read-byte$-n 16 channel state)))))
                       -16)
                      channel
                      (mv-nth 1 (read-byte$-n 16 channel state))))))
                  (update-bpb_numheads
                   (combine16u
                    (nth
                     11
                     (mv-nth
                      0
                      (read-byte$-n
                       (+
                        (*
                         (combine16u
                          (nth 15
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth
                           14
                           (mv-nth 0 (read-byte$-n 16 channel state))))
                         (combine16u
                          (nth 12
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth
                           11
                           (mv-nth 0 (read-byte$-n 16 channel state)))))
                        -16)
                       channel
                       (mv-nth 1 (read-byte$-n 16 channel state)))))
                    (nth
                     10
                     (mv-nth
                      0
                      (read-byte$-n
                       (+
                        (*
                         (combine16u
                          (nth 15
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth
                           14
                           (mv-nth 0 (read-byte$-n 16 channel state))))
                         (combine16u
                          (nth 12
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                          (nth
                           11
                           (mv-nth 0 (read-byte$-n 16 channel state)))))
                        -16)
                       channel
                       (mv-nth 1 (read-byte$-n 16 channel state))))))
                   (update-bpb_secpertrk
                    (combine16u
                     (nth
                      9
                      (mv-nth
                       0
                       (read-byte$-n
                        (+
                         (*
                          (combine16u
                           (nth
                            15
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                           (nth
                            14
                            (mv-nth 0 (read-byte$-n 16 channel state))))
                          (combine16u
                           (nth
                            12
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                           (nth
                            11
                            (mv-nth 0 (read-byte$-n 16 channel state)))))
                         -16)
                        channel
                        (mv-nth 1 (read-byte$-n 16 channel state)))))
                     (nth
                      8
                      (mv-nth
                       0
                       (read-byte$-n
                        (+
                         (*
                          (combine16u
                           (nth
                            15
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                           (nth
                            14
                            (mv-nth 0 (read-byte$-n 16 channel state))))
                          (combine16u
                           (nth
                            12
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                           (nth
                            11
                            (mv-nth 0 (read-byte$-n 16 channel state)))))
                         -16)
                        channel
                        (mv-nth 1 (read-byte$-n 16 channel state))))))
                    (update-bpb_fatsz16
                     (combine16u
                      (nth
                       7
                       (mv-nth
                        0
                        (read-byte$-n
                         (+
                          (*
                           (combine16u
                            (nth
                             15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                            (nth
                             14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                           (combine16u
                            (nth
                             12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                            (nth
                             11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
                          -16)
                         channel
                         (mv-nth 1 (read-byte$-n 16 channel state)))))
                      (nth
                       6
                       (mv-nth
                        0
                        (read-byte$-n
                         (+
                          (*
                           (combine16u
                            (nth
                             15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                            (nth
                             14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                           (combine16u
                            (nth
                             12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                            (nth
                             11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
                          -16)
                         channel
                         (mv-nth 1 (read-byte$-n 16 channel state))))))
                     (update-bpb_media
                      (nth
                       5
                       (mv-nth
                        0
                        (read-byte$-n
                         (+
                          (*
                           (combine16u
                            (nth
                             15
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                            (nth
                             14
                             (mv-nth 0 (read-byte$-n 16 channel state))))
                           (combine16u
                            (nth
                             12
                             (mv-nth 0 (read-byte$-n 16 channel state)))
                            (nth
                             11
                             (mv-nth 0 (read-byte$-n 16 channel state)))))
                          -16)
                         channel
                         (mv-nth 1 (read-byte$-n 16 channel state)))))
                      (update-bpb_totsec16
                       (combine16u
                        (nth
                         4
                         (mv-nth
                          0
                          (read-byte$-n
                           (+
                            (*
                             (combine16u
                              (nth
                               15
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                              (nth
                               14
                               (mv-nth
                                0 (read-byte$-n 16 channel state))))
                             (combine16u
                              (nth
                               12
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                              (nth
                               11
                               (mv-nth
                                0 (read-byte$-n 16 channel state)))))
                            -16)
                           channel
                           (mv-nth 1 (read-byte$-n 16 channel state)))))
                        (nth
                         3
                         (mv-nth
                          0
                          (read-byte$-n
                           (+
                            (*
                             (combine16u
                              (nth
                               15
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                              (nth
                               14
                               (mv-nth
                                0 (read-byte$-n 16 channel state))))
                             (combine16u
                              (nth
                               12
                               (mv-nth 0 (read-byte$-n 16 channel state)))
                              (nth
                               11
                               (mv-nth
                                0 (read-byte$-n 16 channel state)))))
                            -16)
                           channel
                           (mv-nth 1 (read-byte$-n 16 channel state))))))
                       (update-bpb_rootentcnt
                        (combine16u
                         (nth
                          2
                          (mv-nth
                           0
                           (read-byte$-n
                            (+
                             (*
                              (combine16u
                               (nth
                                15
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))
                               (nth
                                14
                                (mv-nth
                                 0 (read-byte$-n 16 channel state))))
                              (combine16u
                               (nth
                                12
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))
                               (nth
                                11
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))))
                             -16)
                            channel
                            (mv-nth 1 (read-byte$-n 16 channel state)))))
                         (nth
                          1
                          (mv-nth
                           0
                           (read-byte$-n
                            (+
                             (*
                              (combine16u
                               (nth
                                15
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))
                               (nth
                                14
                                (mv-nth
                                 0 (read-byte$-n 16 channel state))))
                              (combine16u
                               (nth
                                12
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))
                               (nth
                                11
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))))
                             -16)
                            channel
                            (mv-nth 1 (read-byte$-n 16 channel state))))))
                        (update-bpb_numfats
                         (nth
                          0
                          (mv-nth
                           0
                           (read-byte$-n
                            (+
                             (*
                              (combine16u
                               (nth
                                15
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))
                               (nth
                                14
                                (mv-nth
                                 0 (read-byte$-n 16 channel state))))
                              (combine16u
                               (nth
                                12
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))
                               (nth
                                11
                                (mv-nth
                                 0 (read-byte$-n 16 channel state)))))
                             -16)
                            channel
                            (mv-nth 1 (read-byte$-n 16 channel state)))))
                         (update-bpb_rsvdseccnt
                          (combine16u
                           (nth
                            15
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                           (nth
                            14
                            (mv-nth 0 (read-byte$-n 16 channel state))))
                          (update-bpb_secperclus
                           (nth
                            13
                            (mv-nth 0 (read-byte$-n 16 channel state)))
                           (update-bpb_bytspersec
                            (combine16u
                             (nth
                              12
                              (mv-nth 0 (read-byte$-n 16 channel state)))
                             (nth
                              11
                              (mv-nth 0 (read-byte$-n 16 channel state))))
                            (update-bs_oemname
                             (subseq
                              (mv-nth 0 (read-byte$-n 16 channel state))
                              3 8)
                             (update-bs_jmpboot
                              (subseq
                               (mv-nth 0 (read-byte$-n 16 channel state))
                               0 3)
                              fat32-in-memory)))))))))))))))))))))))))))
   :hints :none)
  (:rewrite update-bs_filsystype-correctness-1)))

;; state-p actually needs to be enabled for this guard proof because all the
;; lemmas are in terms of state-p1
(defun
  slurp-disk-image
  (fat32-in-memory image-path state)
  (declare
   (xargs
    :guard (and (stringp image-path)
                (fat32-in-memoryp fat32-in-memory))
    :guard-hints
    (("goal" :do-not-induct t
      :in-theory (disable fat32-in-memoryp state-p
                          read-reserved-area)))
    :stobjs (state fat32-in-memory)))
  (b* (((mv channel state)
        (open-input-channel image-path
                            :byte state))
       ((unless channel)
        (mv fat32-in-memory state -1))
       ((mv fat32-in-memory state error-code)
        (read-reserved-area fat32-in-memory channel state))
       ((unless (equal error-code 0))
        (mv fat32-in-memory state error-code))
       ((mv fat32-in-memory state error-code)
        (read-fat fat32-in-memory channel state))
       ((unless (equal error-code 0))
        (mv fat32-in-memory state error-code))
       (state (close-input-channel channel state))
       (tmp_secperclus (bpb_secperclus fat32-in-memory))
       (tmp_init (* tmp_secperclus
                    (+ (bpb_rsvdseccnt fat32-in-memory)
                       (* (BPB_NumFATs fat32-in-memory) (BPB_FATSz32
                                                         fat32-in-memory)))))
       (str
                (read-file-into-string image-path :start
                                       tmp_INIT
                                       :bytes
                                       (data-region-LENGTH fat32-in-memory)))
       ((unless (stringp str))
        (mv fat32-in-memory state -1))
       (fat32-in-memory
               (UPDATE-DATA-REGION
                FAT32-IN-MEMORY
                str
                0)))
    (mv fat32-in-memory state error-code)))

(in-theory (enable update-fat bpb_secperclus bpb_fatsz32 bpb_rsvdseccnt
                   bpb_numfats bpb_bytspersec update-bpb_secperclus
                   update-bpb_rsvdseccnt update-bpb_bytspersec
                   update-bpb_numfats))
