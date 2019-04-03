(include-book "../lofat")

(b*
    (((mv & disk state)
      (getenv$ "DISK" state))
     ((unless (stringp disk)) (mv fat32-in-memory state))
     ((mv fat32-in-memory error-code)
      (disk-image-to-lofat
       fat32-in-memory disk state))
     ((unless (equal error-code 0)) (mv fat32-in-memory state))
     ((mv & output_file state)
      (getenv$ "MKFS_OUTPUT" state))
     ((unless (stringp output_file)) (mv fat32-in-memory state))
     ((mv channel state)
      (open-output-channel output_file :character state))
     (state
      (pprogn
       (princ$ "mkfs.fat 4.1 (2017-01-24)" channel state)
       (newline channel state)
       (princ$ disk channel state)
       (princ$ " has " channel state)
       (princ$ (bpb_numheads fat32-in-memory) channel state)
       (princ$ " heads and " channel state)
       (princ$ (bpb_secpertrk fat32-in-memory) channel state)
       (princ$ " sectors per track," channel state)
       (newline channel state)
       (princ$ "hidden sectors 0x" channel state)
       (set-print-base 16 state)
       (princ$ (logand #xf (ash (bpb_hiddsec fat32-in-memory) -12)) channel state)
       (princ$ (logand #xf (ash (bpb_hiddsec fat32-in-memory) -8)) channel state)
       (princ$ (logand #xf (ash (bpb_hiddsec fat32-in-memory) -4)) channel state)
       (princ$ (logand #xf (ash (bpb_hiddsec fat32-in-memory) 0)) channel state)
       (set-print-base 10 state)
       (princ$ ";" channel state)
       (newline channel state)
       (princ$ "logical sector size is " channel state)
       (princ$ (bpb_bytspersec fat32-in-memory) channel state)
       (princ$ "," channel state)
       (newline channel state)
       (princ$ "using 0x" channel state)
       (set-print-base 16 state)
       (princ$ (logand #xf (ash (bpb_media fat32-in-memory) -4)) channel state)
       (princ$ (logand #xf (ash (bpb_media fat32-in-memory) 0)) channel state)
       (set-print-base 10 state)
       (princ$ " media descriptor, with " channel state)
       (princ$ (bpb_totsec32 fat32-in-memory) channel state)
       (princ$ " sectors;" channel state)
       (newline channel state)
       (princ$ "drive number 0x" channel state)
       (set-print-base 16 state)
       (princ$ (logand #xf (ash (bs_drvnum fat32-in-memory) -4)) channel state)
       (princ$ (logand #xf (ash (bs_drvnum fat32-in-memory) 0)) channel state)
       (set-print-base 10 state)
       (princ$ ";" channel state)
       (newline channel state)
       (princ$ "filesystem has " channel state)
       (princ$ (bpb_numfats fat32-in-memory) channel state)
       (princ$ " 32-bit FATs and " channel state)
       (princ$ (bpb_secperclus fat32-in-memory) channel state)
       (princ$
        (if (<= (bpb_secperclus fat32-in-memory) 1)
            " sector per cluster."
          " sectors per cluster.")
        channel
        state)
       (newline channel state)
       (princ$ "FAT size is " channel state)
       (princ$ (bpb_fatsz32 fat32-in-memory) channel state)
       (princ$ " sectors, and provides " channel state)
       (princ$ (floor (- (bpb_totsec32 fat32-in-memory)
                         (+ (bpb_rsvdseccnt fat32-in-memory)
                            (* (bpb_numfats fat32-in-memory)
                               (bpb_fatsz32 fat32-in-memory))))
                      (bpb_secperclus fat32-in-memory))
               channel
               state)
       (princ$ " clusters." channel state)
       (newline channel state)
       (princ$ "There are " channel state)
       (princ$ (bpb_rsvdseccnt fat32-in-memory) channel state)
       (princ$ " reserved sectors." channel state)
       (newline channel state)
       (princ$ "Volume ID is " channel state)
       (set-print-base 16 state)
       (princ$ (logand #xf (ash (bs_volid fat32-in-memory) -28)) channel state)
       (princ$ (logand #xf (ash (bs_volid fat32-in-memory) -24)) channel state)
       (princ$ (logand #xf (ash (bs_volid fat32-in-memory) -20)) channel state)
       (princ$ (logand #xf (ash (bs_volid fat32-in-memory) -16)) channel state)
       (princ$ (logand #xf (ash (bs_volid fat32-in-memory) -12)) channel state)
       (princ$ (logand #xf (ash (bs_volid fat32-in-memory) -8)) channel state)
       (princ$ (logand #xf (ash (bs_volid fat32-in-memory) -4)) channel state)
       (princ$ (logand #xf (ash (bs_volid fat32-in-memory) 0)) channel state)
       (set-print-base 10 state)
       (princ$ ", no volume label." channel state)
       (newline channel state)
       (close-output-channel channel state))))
  (mv fat32-in-memory state))
