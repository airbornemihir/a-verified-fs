(include-book "../file-system-m2")
(include-book "centaur/getopt/top" :dir :system)
(include-book "oslib/argv" :dir :system)

(encapsulate
  ()
  (local (include-book "arithmetic-3/top" :dir :system))
  (defun
      fixed-width-print-helper (x n)
    (declare
     (xargs :hints (("goal" :in-theory (disable floor mod)))))
    (if
        (or (zp n) (zp x))
        nil
      (append
       (fixed-width-print-helper (floor x 10) (- n 1))
       (list (code-char (+ (mod x 10) (char-code #\0))))))))

(defthm len-of-fixed-width-print-helper
  (<= (len (fixed-width-print-helper x n))
      (nfix n))
  :rule-classes :linear
  :hints (("goal" :in-theory (disable ceiling floor))))

(defun fixed-width-print (x n)
  (coerce (if (zp x)
              (cons #\0
                    (make-list (- n 1) :initial-element #\space))
            (append (fixed-width-print-helper x n)
                    (make-list (- n (len (fixed-width-print-helper x n)))
                               :initial-element #\space)))
          'string))

(defthm
  length-of-fixed-width-print
  (implies (not (zp n))
           (equal (len (explode (fixed-width-print x n)))
                  n))
  :hints (("goal" :in-theory (enable fixed-width-print))))

(defoptions stat-opts
  :parents (demo2)
  :tag :demo2

  ((file-system "Provide filesystem parameters"
                booleanp
                :rule-classes :type-prescription
                :alias #\f)))

(b*
    (((mv argv state)              (oslib::argv))
     ((mv errmsg opts ?extra-args) (parse-stat-opts argv))
     ((when errmsg)
      (mv fat32-in-memory state))
     ((stat-opts opts) opts)
     ((unless opts.file-system)
      (mv fat32-in-memory state))
     ((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (slurp-disk-image
       fat32-in-memory val state))
     ((mv & val state)
      (getenv$ "STAT_OUTPUT" state))
     ((mv channel state)
      (open-output-channel val :character state))
     ((mv & pathname state)
      (getenv$ "STAT_INPUT" state))
     (total_blocks (- (fat-length fat32-in-memory) 2))
     (available_blocks (len (stobj-find-n-free-clusters fat32-in-memory total_blocks)))
     (state
      (pprogn
       (princ$ "  File: \"" channel state)
       (princ$ pathname channel state)
       (princ$"\"" channel state)
       (newline channel state)
       (princ$ "    ID: " channel state)
       (princ$ (fixed-width-print 0 8) channel state)
       (princ$ " Namelen: " channel state)
       (princ$ (fixed-width-print 72 7) channel state)
       (princ$ " Type: fuseblk" channel state)
       (newline channel state)
       (princ$ "Block size: " channel state)
       (princ$ (fixed-width-print (cluster-size fat32-in-memory) 10) channel
               state)
       (princ$ " Fundamental block size: " channel state)
       (princ$ (cluster-size fat32-in-memory) channel state)
       (newline channel state)
       (princ$ "Blocks: Total: " channel state)
       (princ$ (fixed-width-print total_blocks 10) channel state)
       (princ$ " Free: " channel state)
       (princ$ (fixed-width-print available_blocks 10) channel state)
       (princ$ " Available: " channel state)
       (princ$ (fixed-width-print available_blocks 10) channel state)
       (newline channel state)
       (princ$ "Inodes: Total: " channel state)
       (princ$ (fixed-width-print 0 10) channel state)
       (princ$ " Free: " channel state)
       (princ$ 0 channel state)
       (newline channel state)
       (close-output-channel channel state))))
  (mv fat32-in-memory state))
