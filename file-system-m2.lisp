(in-package "ACL2")

;  file-system-m2.lisp                                  Mihir Mehta

; This is a stobj model of the FAT32 filesystem.

(include-book "file-system-lemmas")
(include-book "fat32")
(include-book "std/io/read-ints" :dir :system)

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
    (bpb_fsver :type (unsigned-byte 16)
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
    (bpb_drvnum :type (unsigned-byte 8)
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

    (data_region :type (array (unsigned-byte 8) (*ms-min-data-region-size*))
         :resizable t
         ;; per spec
         :initially 0)))

(defconst *initialbytcnt* 16)

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
                           state-p unsigned-byte-p nth)))
     :stobjs (state fat32-in-memory)))
   (b*
       (((mv initial-bytes state)
         (read-byte$-n *initialbytcnt* channel state))
        ((unless (not (equal initial-bytes 'fail)))
         (mv fat32-in-memory state -1))
        (fat32-in-memory (update-bs_jmpbooti 0 (nth 0 initial-bytes)
                                             fat32-in-memory))
        (fat32-in-memory (update-bs_jmpbooti 1 (nth 1 initial-bytes)
                                             fat32-in-memory))
        (fat32-in-memory (update-bs_jmpbooti 2 (nth 2 initial-bytes)
                                             fat32-in-memory))
        (fat32-in-memory
         (update-bs_oemnamei 0 (nth (+ 3 0) initial-bytes)
                             fat32-in-memory))
        (fat32-in-memory
         (update-bs_oemnamei 1 (nth (+ 3 1) initial-bytes)
                             fat32-in-memory))
        (fat32-in-memory
         (update-bs_oemnamei 2 (nth (+ 3 2) initial-bytes)
                             fat32-in-memory))
        (fat32-in-memory
         (update-bs_oemnamei 3 (nth (+ 3 3) initial-bytes)
                             fat32-in-memory))
        (fat32-in-memory
         (update-bs_oemnamei 4 (nth (+ 3 4) initial-bytes)
                             fat32-in-memory))
        (fat32-in-memory
         (update-bs_oemnamei 5 (nth (+ 3 5) initial-bytes)
                             fat32-in-memory))
        (fat32-in-memory
         (update-bs_oemnamei 6 (nth (+ 3 6) initial-bytes)
                             fat32-in-memory))
        (fat32-in-memory
         (update-bs_oemnamei 7 (nth (+ 3 7) initial-bytes)
                             fat32-in-memory))
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
          fat32-in-memory)))
     (mv fat32-in-memory state 0))))

(defun
  slurp-disk-image
  (fat32-in-memory image-path state)
  (declare
   (xargs
    :guard (and (state-p state)
                (stringp image-path)
                (fat32-in-memoryp fat32-in-memory))
    :guard-hints
    (("goal" :do-not-induct t
      :in-theory (disable fat32-in-memoryp state-p)))
    :stobjs (state fat32-in-memory)))
  (b* (((mv channel state)
        (open-input-channel image-path
                            :byte state))
       ((unless channel)
        (mv fat32-in-memory state -1))
       ((mv fat32-in-memory state error-code)
        (read-reserved-area fat32-in-memory channel state))
       (state (close-input-channel channel state)))
    (mv fat32-in-memory state error-code)))
