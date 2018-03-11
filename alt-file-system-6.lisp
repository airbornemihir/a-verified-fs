;; I don't think blocks are 8 characters long in any system; I simply set this
;; in order to actually get fragmentation without having to make unreasonably
;; large examples.
(defconst *blocksize* 8)

(defund insert-text (oldtext start text)
  (declare (xargs :guard (and (character-listp oldtext)
                              (natp start)
                              (stringp text))))
  (let* (
         (end (+ start (length text)))
         (newtext (append (make-character-list (take start oldtext))
                          (coerce text 'list)
                          (nthcdr end oldtext))))
    newtext))

(encapsulate
  ()

  (local (include-book "std/lists/nthcdr" :dir :system))

  (local
   (defun make-blocks (text)
     (declare (xargs :guard (character-listp text)
                     :measure (len text)))
     (if (atom text)
         nil
       (cons (make-character-list (take *blocksize* text))
             (make-blocks (nthcdr *blocksize* text))))))

  ;; This fragments a character-list into blocks that are *blocksize*-character
  ;; long. If the character-list is not exactly aligned to a block boundary, we
  ;; fill the space with null characters.
  ;; It will be used in wrchs.
  (defun make-blocks (text)
    (declare (xargs :guard (character-listp text)
                    :measure (:? text)))
    (if (atom text)
        nil
      (cons (make-character-list (take *blocksize* text))
            (make-blocks (nthcdr *blocksize* text))))))

;; Characterisation of a disk, which is a list of blocks as described before.
(defun block-listp (block-list)
  (declare (xargs :guard t))
  (if (atom block-list)
      (eq block-list nil)
    (and (character-listp (car block-list))
         (equal (len (car block-list)) *blocksize*)
         (block-listp (cdr block-list)))))

;; This is a constant that might be needed later.
;; This is to be returned when a block is not found. It's full of null
;; characters and is *blocksize* long.
(defconst *nullblock* (make-character-list (take *blocksize* nil)))

(defun
  fetch-blocks-by-indices
  (block-list index-list)
  (declare (xargs :guard (and (block-listp block-list)
                              (nat-listp index-list))))
  (if
   (atom index-list)
   nil
   (let
    ((tail
      (fetch-blocks-by-indices block-list (cdr index-list))))
    (if (>= (car index-list) (len block-list))
        (cons *nullblock* tail)
        (cons (nth (car index-list) block-list)
              tail)))))

(defun set-indices (v index-list value-list)
  (declare (xargs :guard (and (true-listp v)
                              (nat-listp index-list)
                              (true-listp value-list)
                              (equal (len index-list) (len value-list)))))
  (if (atom index-list)
      v
    (set-indices (update-nth (car index-list) (car value-list) v)
                        (cdr index-list)
                        (cdr value-list))))

(include-book "centaur/fty/top" :dir :system)

(defconst *expt-2-28* (expt 2 28))
;; from page 18 of the FAT specification
(defconst *MS-EOC* (- *expt-2-28* 1))
;; from include/uapi/asm-generic/errno-base.h
(defconst *EIO* 5) ;; I/O error
(defconst *ENOSPC* 28) ;; No space left on device
(defconst *ENOENT* 2) ;; No such file or directory

(defund fat32-entry-p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 32 x))

(defund fat32-masked-entry-p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 28 x))

;; 0 is chosen as the default value based on this comment from Microsoft's FAT
;; overview:
;; The only time that the high 4 bits of FAT32 FAT entries should ever be
;; changed is when the volume is formatted, at which time the whole 32-bit FAT
;; entry should be zeroed, including the high 4 bits.
(defund fat32-entry-fix (x)
  (declare (xargs :guard t))
  (if (fat32-entry-p x)
      x 0))

(defund fat32-masked-entry-fix (x)
  (declare (xargs :guard t))
  (if (fat32-masked-entry-p x)
      x 0))

(in-theory (enable fat32-entry-p fat32-entry-fix fat32-masked-entry-p fat32-masked-entry-fix))

(defthm fat32-masked-entry-p-correctness-1
  (implies (fat32-masked-entry-p x)
           (natp x))
  :rule-classes :forward-chaining)

;; Use a mask to take the low 28 bits.
(defund fat32-entry-mask (x)
  (declare (xargs :guard (fat32-entry-p x)))
  (logand x (- (ash 1 28) 1)))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm
    logand-ash-lemma-1
    (implies (and (natp c))
             (unsigned-byte-p c (logand i (- (ash 1 c) 1)))))
  )

(defthm
  fat32-entry-mask-correctness-1
  (fat32-masked-entry-p (fat32-entry-mask x))
  :hints (("goal" :in-theory (e/d (fat32-entry-mask fat32-masked-entry-p)
                                  (unsigned-byte-p logand-ash-lemma-1))
           :use (:instance logand-ash-lemma-1 (c 28)
                           (i x)))))

(fty::deffixtype fat32-entry
                 :pred   fat32-entry-p
                 :fix    fat32-entry-fix
                 :equiv  fat32-entry-equiv
                 :define t
                 :forward t
                 )

(fty::deffixtype fat32-masked-entry
                 :pred   fat32-masked-entry-p
                 :fix    fat32-masked-entry-fix
                 :equiv  fat32-masked-entry-equiv
                 :define t
                 :forward t
                 )

(fty::deflist fat32-entry-list :elt-type fat32-entry-p :true-listp t)

(fty::deflist fat32-masked-entry-list :elt-type fat32-masked-entry-p :true-listp t)

(defund
  fat32-update-lower-28
  (entry masked-entry)
  (declare
   (xargs
    :guard-hints
    (("goal"
      :in-theory (enable fat32-entry-p fat32-masked-entry-p)))
    :guard (and (fat32-entry-p entry)
                (fat32-masked-entry-p masked-entry))))
  (logior (logand entry (- (ash 1 32) (ash 1 28)))
          masked-entry))

(defun
  set-indices-in-fa-table
  (v index-list value-list)
  (declare
   (xargs :guard (and (fat32-entry-list-p v)
                      (nat-listp index-list)
                      (fat32-masked-entry-list-p value-list)
                      (equal (len index-list)
                             (len value-list)))))
  (if
   (atom index-list)
   v
   (let
    ((current-index (car index-list)))
    (if (or (not (natp current-index))
            (>= current-index (len v)))
        v
        (update-nth current-index
                    (fat32-update-lower-28 (nth current-index v)
                                           (car value-list))
                    v)))))

;; question: if fat entries are 28 bits long, then how is the maximum size
;; determined to be 4 GB?
;; also, how are we gonna do this without a feasible length restriction?
(defund l6-regular-file-entry-p (entry)
  (declare (xargs :guard t))
  (and (consp entry)
       ;; fat entries are effectively 28 bits long
       (fat32-masked-entry-p (car entry))
       (natp (cdr entry))))

(defund l6-regular-file-first-cluster (entry)
  (declare (xargs :guard (l6-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l6-regular-file-entry-p)))))
  (car entry))

(defund l6-regular-file-length (entry)
  (declare (xargs :guard (l6-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l6-regular-file-entry-p)))))
  (cdr entry))

(defund
  l6-make-regular-file
  (first-cluster length)
  (declare
   (xargs :guard (and (fat32-masked-entry-p first-cluster)
                      (natp length))))
  (cons first-cluster length))

; This function defines a valid filesystem. It's an alist where all the cars
; are symbols and all the cdrs are either further filesystems or regular files.
(defun l6-fs-p (fs)
  (declare (xargs :guard t))
  (if (atom fs)
      (null fs)
    (and (let ((directory-or-file-entry (car fs)))
           (if (atom directory-or-file-entry)
               nil
             (let ((name (car directory-or-file-entry))
                   (entry (cdr directory-or-file-entry)))
               (and (symbolp name)
                    (or (l6-regular-file-entry-p entry)
                        (l6-fs-p entry))))))
         (l6-fs-p (cdr fs)))))

;; taken from page 18 of the fat overview - the constant 268435448 is written
;; out as 0xFFFFFF8 therein
(defund l6-is-eof (fat-content)
  (declare (xargs :guard (fat32-masked-entry-p fat-content)
                  :guard-hints (("Goal'" :in-theory (enable fat32-masked-entry-p)))))
  (>= fat-content 268435448))

;; we have what we need to define a disk traversal to get the contents of the
;; file

;; we're going to make this return a rather literal exit status, as the second
;; element of the mv. that will be 0 if we successfully got a list of indices,
;; and -EIO if we did not for reasons shown in the function
;; fs/fat/cache.c:fat_get_cluster
(defun
    l6-build-index-list
    (fa-table masked-current-cluster length)
  (declare
   (xargs
    :measure (acl2-count length)))
  (if
      (or (not (integerp length))
          (<= length 0))
      ;; This represents a problem case because masked-current-cluster is a
      ;; valid non-free cluster, but the length is 0. This loosely corresponds
      ;; to the infinite loop protection in the function
      ;; fs/fat/cache.c:fat_get_cluster
      (mv nil (- *eio*))
    (let
        ((masked-next-cluster
          (fat32-entry-mask (nth masked-current-cluster fa-table))))
      (if
          (< masked-next-cluster 2)
          (mv (list masked-current-cluster)
              (- *eio*))
        (if
            (or (l6-is-eof masked-next-cluster)
                (>= masked-next-cluster (len fa-table)))
            (mv (list masked-current-cluster) 0)
          (b*
              (((mv tail-index-list tail-error)
                (l6-build-index-list fa-table masked-next-cluster
                                     (nfix (- length *blocksize*)))))
            (mv (list* masked-current-cluster tail-index-list)
                tail-error)))))))

(defund find-n-free-clusters-helper (fa-table n start)
  (if (or (atom fa-table) (zp n))
      nil
    (if (not (equal (fat32-entry-mask (car fa-table)) 0))
        ;; this block is taken
        (find-n-free-clusters-helper (cdr fa-table) n (+ start 1))
      ;; this block isn't taken
      (cons start (find-n-free-clusters-helper (cdr fa-table) (- n 1) (+ start 1))))))

(defund find-n-free-clusters (fa-table n)
  ;; the first 2 clusters are excluded
  (find-n-free-clusters-helper (nthcdr 2 fa-table) n 2))

;; This function allows a file or directory to be found in a filesystem given a
;; path.
(defun l6-stat (hns fs disk)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l6-fs-p fs)
                              (block-listp disk))))
  (if (atom hns)
      fs
    (if (atom fs)
        nil
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            nil
          (if (l6-regular-file-entry-p (cdr sd))
              (and (null (cdr hns))
                   (cdr sd))
            (l6-stat (cdr hns) (cdr sd) disk)))))))

;; a note on why this function needs to exist and why it should not replace
;; unmake-blocks
;; unmake-blocks has been used thus far in contexts where the length of the
;; file can be checked to line up with the contents of the file (with only the
;; assumption that the disk satisfies block-listp, nothing more - this is
;; what's checked by feasible-file-length-p)
;; i could have replaced the unmake-blocks function with this one, given that
;; its guard is less restrictive (these clauses are a strict subset of those
;; clauses)
;; i opted not to do so because, in my opinion, the guard verification that
;; takes place with the more restrictive guard is valuable - it shows that
;; we're not leaving room for more than (*blocksize* - 1) characters of junk
;; being added anywhere, as long as we can still verify these things with
;; "local" checks (by which i mean, checks that don't refer too much to the
;; disk, which i consider "not local" for these purposes)
(defun
  unmake-blocks-without-feasibility
  (blocks n)
  (declare (xargs :guard (and (block-listp blocks) (natp n))))
  (mbe
   :exec
   (if
    (atom blocks)
    (make-character-list (take n nil))
    (if
     (< n *blocksize*)
     (take n (car blocks))
     (binary-append
      (car blocks)
      (unmake-blocks-without-feasibility (cdr blocks)
                                         (- n *blocksize*)))))
   :logic
   (if
    (atom blocks)
    (make-character-list (take n nil))
    (let ((head (make-character-list (car blocks))))
         (if (or (not (integerp n)) (< n (len head)))
             (take n head)
             (binary-append head
                            (unmake-blocks-without-feasibility
                             (cdr blocks)
                             (- n (len (car blocks))))))))))

(defund
  l6-file-index-list (file fa-table)
  (let
      ((first-cluster (l6-regular-file-first-cluster file)))
    (if (or (< first-cluster 2)
            (>= first-cluster (len fa-table)))
        (mv nil 0)
      (l6-build-index-list fa-table first-cluster
                           (l6-regular-file-length file)))))

;; This function finds a text file given its path and reads a segment of
;; that text file.
(defun
  l6-rdchs (hns fs disk fa-table start n)
  (let
   ((file (l6-stat hns fs disk)))
   (if
    (not (l6-regular-file-entry-p file))
    (mv nil (- *EIO*))
    (b*
     (((mv index-list error-code)
       (l6-file-index-list file fa-table))
      (file-text
       (coerce (unmake-blocks-without-feasibility
                (fetch-blocks-by-indices disk index-list)
                (l6-regular-file-length file))
               'string))
      (file-length (length file-text))
      (end (+ start n)))
     (if (< file-length end)
         (mv nil error-code)
         (mv (subseq file-text start (+ start n)) error-code))))))

; This function writes a specified text string to a specified position to a
; text file at a specified path.
(defun
    l6-wrchs
    (hns fs disk fa-table start text)
  (declare
   (xargs))
  (if (atom hns)
      (mv fs disk fa-table (- *enoent*)) ;; error - showed up at fs with no
    ;; name  - so leave fs unchanged
    (if (atom fs)
        (mv nil disk fa-table (- *enoent*)) ;; error, so leave fs unchanged
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            (mv fs disk fa-table (- *enoent*)) ;; file-not-found error, so leave fs unchanged
          (if (l6-regular-file-entry-p (cdr sd))
              (if (cdr hns)
                  (mv (cons (cons (car sd) (cdr sd))
                            (delete-assoc (car hns) fs))
                      disk
                      fa-table (- *enoent*)) ;; error, so leave fs unchanged
                (b* (((mv old-indices read-error-code)
                      (l6-file-index-list (cdr sd) fa-table))
                     (old-text
                      (unmake-blocks-without-feasibility
                       (fetch-blocks-by-indices disk old-indices)
                       (l6-regular-file-length (cdr sd))))
                     (fa-table-after-free
                      (set-indices-in-fa-table
                       fa-table
                       old-indices
                       (make-list (len old-indices) :initial-element 0)))
                     (new-text (insert-text old-text start text))
                     (new-blocks (make-blocks new-text))
                     (new-indices
                      (find-n-free-clusters fa-table-after-free (len new-blocks))))
                  (if (not (equal (len new-indices) (len new-blocks)))
                      ;; we have an error because of insufficient disk space
                      ;; - so we leave the fs unchanged
                      (mv (cons (cons (car sd) (cdr sd))
                                (delete-assoc (car hns) fs))
                          disk
                          fa-table (- *enospc*))
                    (if (consp new-indices)
                        (mv (cons (cons (car sd)
                                        (l6-make-regular-file
                                         (car new-indices)
                                         (len new-text)))
                                  (delete-assoc (car hns) fs))
                            (set-indices disk new-indices new-blocks)
                            (set-indices-in-fa-table fa-table-after-free
                                                     new-indices
                                                     (binary-append
                                                      (cdr new-indices)
                                                      (list *MS-EOC*))) read-error-code)
                      (mv (cons (cons (car sd)
                                      (l6-make-regular-file
                                       ;; 0 is chosen by default
                                       0
                                       (len new-text)))
                                (delete-assoc (car hns) fs))
                          disk
                          fa-table-after-free
                          read-error-code)))))
            (mv-let (new-contents new-disk new-fa-table error-code)
              (l6-wrchs (cdr hns) (cdr sd) disk fa-table start text)
              (mv (cons (cons (car sd) new-contents)
                        (delete-assoc (car hns) fs))
                  new-disk
                  new-fa-table
                  error-code))))))))

(defun
  l6-create (hns fs disk fa-table text)
  (if (atom hns)
      (mv fs disk fa-table) ;; error - showed up at fs with no name  - so leave fs unchanged
    (let ((sd (assoc (car hns) fs)))
      (if (atom sd)
          (if (atom (cdr hns))
              (let* ((blocks (make-blocks (coerce text 'list)))
                     (indices (find-n-free-clusters fa-table (len blocks))))
                (if (not (equal (len indices) (len blocks)))
                    ;; we have an error because of insufficient disk space
                    ;; - so we leave the fs unchanged
                    (mv sd disk fa-table)
                  (if (consp indices)
                      (mv (cons (cons (car hns)
                                      (l6-make-regular-file
                                       (car indices)
                                       (length text)))
                                fs)
                          (set-indices disk indices blocks)
                          (set-indices-in-fa-table fa-table
                                                   indices
                                                   (binary-append
                                                    (cdr indices)
                                                    (list *MS-EOC*))))
                    (mv (cons (cons (car hns)
                                    (cons indices
                                          (length text)))
                              fs)
                        disk
                        fa-table))))
            (mv-let (new-fs new-disk new-fa-table)
              (l6-create (cdr hns) nil disk fa-table text)
              (mv (cons (cons (car hns) new-fs) fs) new-disk new-fa-table)))
        (let ((contents (cdr sd)))
          (if (l6-regular-file-entry-p contents)
              (mv (cons (cons (car sd) contents) ;; file already exists, so leave fs unchanged
                        (delete-assoc (car hns) fs))
                  disk
                  fa-table)
            (mv-let (new-fs new-disk new-fa-table)
              (l6-create (cdr hns) contents disk fa-table text)
              (mv (cons (cons (car sd)
                              new-fs)
                        (delete-assoc (car hns) fs))
                  new-disk
                  new-fa-table)))
          )))))

(defconst *sample-fs-1* nil)
(defconst *sample-disk-1* (make-list 6 :initial-element *nullblock*))
(defconst *sample-fa-table-1* (make-list 6 :initial-element 0))
(assert-event (and
               (l6-fs-p *sample-fs-1*)
               (fat32-entry-list-p *sample-fa-table-1*)
               (block-listp *sample-disk-1*)
               (equal (len *sample-disk-1*) (len *sample-fa-table-1*))))

(defconst *sample-fs-2*
  (mv-let (fs disk fa-table)
    (l6-create (list :tmp :ticket1) *sample-fs-1*
               *sample-disk-1*
               *sample-fa-table-1* "good for the goose")
    (declare (ignore disk fa-table))
    fs))
(defconst *sample-disk-2*
  (mv-let (fs disk fa-table)
    (l6-create (list :tmp :ticket1) *sample-fs-1*
               *sample-disk-1*
               *sample-fa-table-1* "good for the goose")
    (declare (ignore fs fa-table))
    disk))
(defconst *sample-fa-table-2*
  (mv-let (fs disk fa-table)
    (l6-create (list :tmp :ticket1) *sample-fs-1*
               *sample-disk-1*
               *sample-fa-table-1* "good for the goose")
    (declare (ignore disk fs))
    fa-table))

(defconst *sample-fs-3*
  (mv-let (fs disk fa-table error-code)
    (l6-wrchs (list :tmp :ticket1) *sample-fs-2*
               *sample-disk-2*
               *sample-fa-table-2* 0 "good for the gander")
    (declare (ignore disk fa-table error-code))
    fs))
(defconst *sample-disk-3*
  (mv-let (fs disk fa-table error-code)
    (l6-wrchs (list :tmp :ticket1) *sample-fs-2*
               *sample-disk-2*
               *sample-fa-table-2* 0 "good for the gander")
    (declare (ignore fs fa-table error-code))
    disk))
(defconst *sample-fa-table-3*
  (mv-let (fs disk fa-table error-code)
    (l6-wrchs (list :tmp :ticket1) *sample-fs-2*
               *sample-disk-2*
               *sample-fa-table-2* 0 "good for the gander")
    (declare (ignore disk fs error-code))
    fa-table))
