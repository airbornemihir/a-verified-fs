(in-package "ACL2")

;  file-system-m2.lisp                                  Mihir Mehta

; This is a stobj model of the FAT32 filesystem.

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

;; This must be called after the file is opened.
(defun read-reserved-area (fat32-in-memory channel state)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel
                                                    :byte state)
                              (FAT32-IN-MEMORYP FAT32-IN-MEMORY))
                  :guard-hints (("Goal" :do-not-induct t :in-theory (disable
                                                                     BYTEP-OF-READ-BYTE$
                                                                     FAT32-IN-MEMORYP
                                                                     STATE-P
                                                                     UNSIGNED-BYTE-P)
                                 :use BYTEP-OF-READ-BYTE$)
                                ("Goal'''" :expand (READ-BYTE$ CHANNEL STATE))
                                ("Goal'6'" :expand (OPEN-INPUT-CHANNEL-P1 CHANNEL
                                     :BYTE STATE)) )
                  :stobjs (state
                           fat32-in-memory)))
  (b*
      (((mv byte state) (read-byte$ channel state))
       ((unless byte) (mv fat32-in-memory channel state -1))
       (fat32-in-memory
        (update-bs_jmpbooti 0 byte fat32-in-memory)))
    (mv fat32-in-memory channel state 0)))
