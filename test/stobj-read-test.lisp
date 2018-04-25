(in-package "ACL2")

;  file-system-m2.lisp                                  Mihir Mehta

; This is a stobj model of the FAT32 filesystem.

(include-book "../file-system-lemmas")
(include-book "../fat32")
(include-book "std/io/read-ints" :dir :system)
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/lists/resize-list" :dir :system)

(defstobj fat32-in-memory
  (data-region :type (array (unsigned-byte 8) (512000000))
               ;; :resizable t
               ;; per spec
               :initially 0))

(defmacro
  update-stobj
  (name array-length bit-width
        array-updater stobj stobj-recogniser)
  (declare (ignore))
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
   (list 'if
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
               stobj))))

(update-stobj
 update-data-region
 data-region-length
 8 update-data-regioni fat32-in-memory fat32-in-memoryp)

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
      ((tmp_databytcnt 512000000)
       ((mv data-region state)
        (read-byte$-n tmp_databytcnt
                      channel state))
       ((unless (not (equal data-region 'fail)))
        (mv fat32-in-memory state -1))
       (fat32-in-memory (update-data-region data-region fat32-in-memory)))
    (mv fat32-in-memory state 0)))

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
        (read-fat fat32-in-memory channel state))
       ((unless (equal error-code 0))
        (mv fat32-in-memory state error-code))
       (state (close-input-channel channel state)))
    (mv fat32-in-memory state error-code)))
