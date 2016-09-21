(include-book "centaur/bitops/part-install" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/strings/hex" :dir :system)
(include-book "std/strings/octal" :dir :system)
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)

;; these are the values after a call to diskdefReadSuper
;; more info below:
;; (gdb) p drive
;; $1 = {dev = {opened = 0, secLength = 512, tracks = 160, sectrk = 18, offset = 0, fd = 0}, secLength = 512, tracks = 160, sectrk = 18, blksiz = 4096, maxdir = 256, skew = 1, boottrk = 2, offset = 0, type = 7, size = 355, extents = 2, dir = 0x60d0a0, alvSize = 12, alv = 0x60d060, skewtab = 0x60d010, cnotatime = 1, label = 0x0, labelLength = 0, passwd = 0x0, passwdLength = 0, root = 0x7fffffffdfd0, dirtyDirectory = 0, ds = 0x0, dirtyDs = 0}
(defconst *d-secLength* 512)
(defconst *d-sectrk* 18)
(defconst *d-tracks* 160)
(defconst *d-offset* 0)
(defconst *d-boottrk* 2)
(defconst *d-blksiz* 4096)
(defconst *d-maxdir* 256)
(defconst *d-size* 355)
(defconst *d-extents* 2)
;; from #define INTBITS ((int)(sizeof(int)*8))
(defconst *INTBITS* 32)
;; d->alvSize=((d->secLength*d->sectrk*(d->tracks-d->boottrk))/d->blksiz+INTBITS-1)/INTBITS;
(defconst *d-alvSize*
  (truncate (+ (truncate (* *d-secLength* *d-sectrk* (- *d-tracks* *d-boottrk*))
                         *d-blksiz*)
               *INTBITS* -1)
            *INTBITS*))

;; struct PhysDirectoryEntry
;; {
;;   char status;
;;   char name[8];b
;;   char ext[3];
;;   char extnol;
;;   char lrc;
;;   char extnoh;
;;   char blkcnt;
;;   char pointers[16];
;; };
(defconst *pde-pointercnt* 16)
(defconst *pde-free-extent-magic* (str::strval16 "e5"))

(std::defaggregate
 cpmdir-PhysDirectoryEntry
 (status
  name
  ext
  extnol
  lrc
  extnoh
  blkcnt
  pointers)
 :tag :cpmdir-PhysDirectoryEntry)

(defconst *pde-default*
  (make-cpmdir-PhysDirectoryEntry :status *pde-free-extent-magic*))

(defconst *floppy-byte-count* 1474560)

;; (d->alv=malloc(d->alvSize*sizeof(int)))
(defstobj d-alv
  (alv-bytes :type (array (unsigned-byte 32) (*d-alvSize*)) :initially 0)
  (alv-dir :type (array (satisfies cpmdir-PhysDirectoryEntry-p) (*d-maxdir*))
           :initially #.*pde-default*)
  (disk-bytes :type (array (unsigned-byte 8) (*floppy-byte-count*)) :initially 0))

(defun alv-alvInit (d-alv)
  (declare (xargs :stobjs (d-alv)))
  (let* (
         ;;  memset(d->alv,0,d->alvSize*sizeof(int));
         ;;  *d->alv=(1<<((d->maxdir*32+d->blksiz-1)/d->blksiz))-1;
         (d-alv
          (update-alv-bytesi 0
                             (- (ash 1
                                     (truncate (+ (* *d-maxdir* 32) *d-blksiz* -1)
                                               *d-blksiz*)) 1)
                             d-alv)))
    d-alv))

(thm (implies (and (integerp a) (integerp i) (<= 0 i) (< i a))
              (not (equal 0 (logand (ash 1 i) (1- (ash 1 a)))))))

(thm
 (implies (and (integerp i) (<= 0 i)
               (< i (truncate (+ (* *d-maxdir* 32) *d-blksiz* -1)
                              *d-blksiz*)))
          (not (equal 0 (logand (ash 1 i)
                                (let* ((d-alv (alv-alvInit d-alv)))
                                  (alv-bytesi 0 d-alv)))))))

;; given that this doesn't come up in the running example of a 1.44 MB floppy,
;; i feel OK leaving it alone for now. we'll return later.
;; (defun alv-block-allocation-loop (i1 j1 d-alv)
;;   (declare (xargs :stobjs (d-alv)
;;                   :guard (and (integerp i1)
;;                               (integerp j1)
;;                               (<= j1 *pde-pointercnt*)
;;                               (>= i1 0) (< i1 *d-maxdir*))
;;                   :verify-guards nil
;;                   :measure (if (and (integerp j1) (<= j1 *pde-pointercnt*))
;;                                (- *pde-pointercnt* j1)
;;                              0)
;;                   :measure-debug t))
;;   (if (or (not (integerp j1)) (>= j1 *pde-pointercnt*))
;;       d-alv
;;     (stobj-let
;;      ((PhysDirectoryEntry (alv-diri i1 d-alv)))
;;      (PhysDirectoryEntry)
;;      PhysDirectoryEntry
;;      (alv-block-allocation-loop i1 (+ j1 1) d-alv))))

(defun bitmap-block-used-p (d-alv block)
  (declare (xargs :stobjs (d-alv)
                  :verify-guards nil))
  (let* ((i1 (ash block -5))
         (j1 (part-select block :high 4 :low 0))
         (thisbit (part-select (alv-bytesi i1 d-alv) :low j1 :high j1)))
    (not (equal thisbit 0))))

(defun bitmap-set-block-used (d-alv block)
  (declare (xargs :stobjs (d-alv)
                  :verify-guards nil))
  (let* ((i1 (ash block -5))
         (j1 (part-select block :high 4 :low 0)))
    (let
        ((d-alv (update-alv-bytesi i1 (part-install 1 (alv-bytesi i1 d-alv)
                                                    :low j1 :high j1) d-alv)))
      d-alv)))

(defun alv-allocBlock-loop (d-alv startblock)
  (declare (xargs :stobjs (d-alv)
                  :measure (if (and (integerp startblock) (<= startblock (* *INTBITS* *d-alvsize*)))
                               (- (* *INTBITS* *d-alvsize*) startblock)
                             0)
                  :verify-guards nil))
  (if (or (not (natp startblock)) (>= startblock (* *INTBITS* *d-alvsize*)))
      (mv d-alv -1)
    (let* ((i1 (ash startblock -5))
           (j1 (part-select startblock :high 4 :low 0))
           (thisbit (part-select (alv-bytesi i1 d-alv) :low j1 :high j1)))
      (if (equal thisbit 0)
          (let
              ((d-alv (update-alv-bytesi i1 (part-install 1 (alv-bytesi i1 d-alv)
                                                          :low j1 :high j1) d-alv)))
            (mv
             d-alv
             startblock))
        (alv-allocBlock-loop d-alv (+ startblock 1))))
    ))

(defun alv-allocBlock (d-alv)
  (declare (xargs :stobjs (d-alv)
                  :verify-guards nil))
  (let ((startblock 0)) (alv-allocBlock-loop d-alv startblock)))

(defthm allocBlock-return-value-upper-bound
  (mv-let
    (new-d-alv block) (alv-allocBlock-loop d-alv startblock) (declare (ignore new-d-alv))
    (and (integerp block) (< block (* *INTBITS* *d-alvsize*)))))

(defthm allocBlock-return-value-lower-bound
  (mv-let
    (new-d-alv block) (alv-allocBlock-loop d-alv startblock) (declare (ignore new-d-alv))
    (implies (>= block 0) (>= block startblock))))

(defun alv-full-p-loop (d-alv endblock)
  (declare (xargs :stobjs (d-alv)
                  :verify-guards nil))
  (if (or (not (integerp endblock)) (<= endblock 0) (> endblock (* *INTBITS* *d-alvsize*)))
      t
    (let* ((i1 (ash (- endblock 1) -5))
           (j1 (part-select (- endblock 1) :high 4 :low 0))
           (thisbit (part-select (alv-bytesi i1 d-alv) :low j1 :high j1)))
      (if (equal thisbit 0)
          nil
        (alv-full-p-loop d-alv (- endblock 1))))))

(defun alv-full-p (d-alv)
  (declare (xargs :stobjs (d-alv)
                  :verify-guards nil))
  (let ((endblock (* *INTBITS* *d-alvsize*))) (alv-full-p-loop d-alv endblock)))

(defthm allocBlock-succeeds-only-after-full-blocks
  (mv-let
    (new-d-alv block) (alv-allocBlock-loop d-alv startblock) (declare (ignore new-d-alv))
    (implies (and (natp startblock) (>= block startblock) (d-alvp d-alv)
                  (alv-full-p-loop d-alv startblock))
             (alv-full-p-loop d-alv block)))
  :hints (("Goal" :in-theory (disable d-alvp)) ))

(defthm allocBlock-fails-only-when-all-blocks-full-lemma-1
  (mv-let
    (new-d-alv block) (alv-allocBlock-loop d-alv startblock) (declare (ignore new-d-alv))
    (implies (and (natp startblock) (<= startblock (* *INTBITS* *d-alvsize*))
                  (< block 0) (d-alvp d-alv)
                  (alv-full-p-loop d-alv startblock))
             (alv-full-p d-alv)))
  :hints (("Goal" :in-theory (disable d-alvp)) ))

(defthm allocBlock-fails-only-when-all-blocks-full
  (mv-let
    (new-d-alv block) (alv-allocBlock d-alv) (declare (ignore new-d-alv))
    (implies (and (< block 0) (d-alvp d-alv))
             (alv-full-p d-alv)))
  :hints (("Goal" :in-theory (disable d-alvp allocblock-fails-only-when-all-blocks-full-lemma-1)
           :use
           (:instance allocblock-fails-only-when-all-blocks-full-lemma-1 (startblock 0))) ))

;; struct cpmInode
;; {
;;   ino_t ino;
;;   mode_t mode;
;;   off_t size;
;;   cpm_attr_t attr;
;;   time_t atime;
;;   time_t mtime;
;;   time_t ctime;
;;   struct cpmSuperBlock *sb;
;; };
(std::defaggregate cpmfs-cpmInode
                   (ino mode size)
                   :tag :cpmfs-cpmInode)

;; #define EXTENT(low,high) (((low)&0x1f)|(((high)&0x3f)<<5))
(defun cpmdir-EXTENT (low high)
  (logior (logand low  (- (ash 1 5) 1))
          (logand high (- (ash 1 6) 1))))

(defun matchFileExtent (user name ext extent extno d-alv)
  (declare (xargs :stobjs (d-alv)
                  :verify-guards nil))
  (let* ((pde-extent (alv-diri extent d-alv)) )
    (and (< (cpmdir-PhysDirectoryEntry->status pde-extent) (ash 1 5))
         (or (< extno 0)
             (equal (cpmdir-EXTENT
                     (cpmdir-PhysDirectoryEntry->extnol pde-extent)
                     (cpmdir-PhysDirectoryEntry->extnoh pde-extent))
                    (truncate extno *d-extents*)))
         ;; and inside an and to keep things clear
         (and
          (equal user (cpmdir-PhysDirectoryEntry->status pde-extent))
          (equal name (cpmdir-PhysDirectoryEntry->name pde-extent))
          (equal ext (cpmdir-PhysDirectoryEntry->ext pde-extent))))))

(defun cpmfs-findFileExtent (user name ext start extno d-alv)
  (declare (xargs :stobjs (d-alv)
                  :verify-guards nil
                  :measure
                  (if (or (not (natp start)) (>= start *d-maxdir*))
                      0
                    (- *d-maxdir* start))))
  (if (or (not (natp start)) (>= start *d-maxdir*))
      -1
    (if (matchFileExtent user name ext start extno d-alv)
        start
      (cpmfs-findFileExtent user name ext (+ start 1) extno d-alv))))

(defun no-matching-fileExtent-loop (user name ext end extno d-alv)
  (declare (xargs :stobjs (d-alv)
                  :verify-guards nil))
  (or (not (integerp end))
      (<= end 0)
      (> end *d-maxdir*)
      (if (matchFileExtent user name ext (- end 1) extno d-alv)
          nil
        (no-matching-fileExtent-loop user name ext (- end 1) extno d-alv))))

(defthm cpmfs-findFileExtent-correctness-1
 (let ((extent (cpmfs-findFileExtent user name ext start extno d-alv))
       )
   (implies (and (d-alvp d-alv) (natp extent)
                 (no-matching-fileExtent-loop user name ext start extno d-alv))
            (no-matching-fileExtent-loop user name ext extent extno d-alv))))

(defun cpmfs-splitFilename (fullname)
  ;; char name[2+8+1+3+1]; /* 00foobarxy.zzy\0 */
  (if (and (character-listp fullname) (equal (len fullname) (+ 2 8 1 3 1)))
      (mv
       0 ;; return value
       (+ (* 10 (- (char-code (nth 0 fullname)) (char-code #\0)))
          (- (char-code (nth 1 fullname)) (char-code #\0))) ;; user
       (take 8 (nthcdr 2 fullname)) ;; name
       (take 3 (nthcdr (+ 2 8 1) fullname))) ;; ext
    (mv -1 nil nil nil)))

(defun cpmfs-findFreeExtent-loop (i1 d-alv)
  (declare (xargs :stobjs (d-alv)
                  :measure (if (or (not (natp i1)) (>= i1 *d-maxdir*))
                               0
                             (- *d-maxdir* i1))
                  :verify-guards nil))
  (if (or (not (natp i1)) (>= i1 *d-maxdir*))
      -1
    (if (equal (cpmdir-PhysDirectoryEntry->status (alv-diri i1 d-alv))
               *pde-free-extent-magic*)
        i1
      (cpmfs-findFreeExtent-loop (+ i1 1) d-alv))))

(defthm cpmfs-findFreeExtent-loop-correctness-1
  (implies (and (d-alvp d-alv)
                (equal extent (cpmfs-findFreeExtent-loop i1 d-alv)))
           (and (integerp extent)
                (< extent *d-maxdir*))))

(defun cpmfs-findFreeExtent (d-alv)
  (declare (xargs :stobjs d-alv
                  :verify-guards nil))
  (cpmfs-findFreeExtent-loop 0 d-alv))

;; this isn't exactly in compliance with the C code - that remains to be
;; checked
(defconst *cpmfs-cpmCreat-default-ino* (make-cpmfs-cpmInode))

(defconst *s_ifdir* (ash 1 14))
(defconst *s_ifreg* (ash 1 15))

(defun cpmfs-S_ISDIR (mode)
  (not (equal (logand mode *s_ifdir*) 0)))

(defun cpmfs-S_ISREG (mode)
  (not (equal (logand mode *s_ifreg*) 0)))

(defun cpmfs-cpmCreat (dir fname mode d-alv)
  (declare (xargs :stobjs d-alv
                  :verify-guards nil))
  (if (not (cpmfs-S_ISDIR (cpmfs-cpmInode->mode dir)))
      (mv -1 *cpmfs-cpmCreat-default-ino* d-alv)
    (mv-let (retval user name ext)
      (cpmfs-splitFilename fname)
      (if (< retval 0)
          (mv -1 *cpmfs-cpmCreat-default-ino* d-alv)
        (if (>= (cpmfs-findFileExtent user name ext 0 -1 d-alv) 0)
            (mv -1 *cpmfs-cpmCreat-default-ino* d-alv)
          (let* ((extent (cpmfs-findFreeExtent d-alv)) )
            (if (< extent 0)
                (mv -1 *cpmfs-cpmCreat-default-ino* d-alv)
              (let* ((ent (alv-diri extent d-alv))
                     (d-alv (update-alv-diri extent
                                             (change-cpmdir-PhysDirectoryEntry ent
                                                                               :status user
                                                                               :name name
                                                                               :ext ext)
                                             d-alv))
                     (ino (change-cpmfs-cpmInode
                           *cpmfs-cpmCreat-default-ino*
                           ;; to be replaced by ino->mode=s_ifreg|mode;
                           :ino extent
                           :mode (logior *s_ifreg* mode)
                           :size 0)))
                (mv 0 ino d-alv)))))))))

(defthm cpmfs-cpmCreat-correctness-1-lemma-1
  (mv-let (retval ino new-d-alv)
    (cpmfs-cpmCreat dir fname mode d-alv)
    (declare (ignore new-d-alv))
    (implies
     (>= retval 0)
     (and (cpmfs-cpmInode-p ino)
          (natp (cpmfs-cpmInode->ino ino)))))
  :hints (("Goal" :in-theory (disable (:rewrite take-of-too-many)
                                      (:definition take-redefinition)
                                      (:rewrite take-of-len-free)
                                      (:definition len)))
          ))

(defthm cpmfs-cpmCreat-correctness-1-lemma-3
 (implies (cpmfs-S_ISDIR ino)
          (equal (cpmfs-S_ISDIR ino) t)))

(in-theory (disable CPMFS-S_ISDIR))

(defthmd cpmfs-cpmCreat-correctness-1-lemma-6
  (implies
   (and
    (matchfileextent
     user name ext extent -1
     (update-alv-diri
      extent
      (let
       ((change-cpmdir-physdirectoryentry (alv-diri extent d-alv))
        (cpmdir-physdirectoryentry->status user)
        (cpmdir-physdirectoryentry->name name)
        (cpmdir-physdirectoryentry->ext ext))
       (cpmdir-physdirectoryentry
        cpmdir-physdirectoryentry->status
        cpmdir-physdirectoryentry->name
        cpmdir-physdirectoryentry->ext
        (cpmdir-physdirectoryentry->extnol change-cpmdir-physdirectoryentry)
        (cpmdir-physdirectoryentry->lrc change-cpmdir-physdirectoryentry)
        (cpmdir-physdirectoryentry->extnoh change-cpmdir-physdirectoryentry)
        (cpmdir-physdirectoryentry->blkcnt change-cpmdir-physdirectoryentry)
        (cpmdir-physdirectoryentry->pointers
         change-cpmdir-physdirectoryentry)))
      d-alv))
    (d-alvp d-alv)
    (natp extent)
    (< extent 256)
    (natp user)
    (< user (ash 1 5))
    (no-matching-fileextent-loop user name ext extent -1 d-alv))
   (equal
    (cpmfs-findfileextent
     user name ext extent -1
     (update-alv-diri
      extent
      (let
       ((change-cpmdir-physdirectoryentry (alv-diri extent d-alv))
        (cpmdir-physdirectoryentry->status user)
        (cpmdir-physdirectoryentry->name name)
        (cpmdir-physdirectoryentry->ext ext))
       (cpmdir-physdirectoryentry
        cpmdir-physdirectoryentry->status
        cpmdir-physdirectoryentry->name
        cpmdir-physdirectoryentry->ext
        (cpmdir-physdirectoryentry->extnol change-cpmdir-physdirectoryentry)
        (cpmdir-physdirectoryentry->lrc change-cpmdir-physdirectoryentry)
        (cpmdir-physdirectoryentry->extnoh change-cpmdir-physdirectoryentry)
        (cpmdir-physdirectoryentry->blkcnt change-cpmdir-physdirectoryentry)
        (cpmdir-physdirectoryentry->pointers
         change-cpmdir-physdirectoryentry)))
      d-alv))
    extent)))

(verify (implies
         (and (d-alvp d-alv)
              (natp extent)
              (< extent 256)
              (natp start)
              (<= start extent)
              (natp user)
              (< user (ash 1 5))
              (no-matching-fileextent-loop user name ext extent -1 d-alv))
         (equal
          (cpmfs-findfileextent
           user name ext start -1
           (update-nth
            *alv-diri*
            (update-nth
             extent
             (cpmdir-physdirectoryentry
              user name ext
              (cpmdir-physdirectoryentry->extnol (nth extent (nth *alv-diri* d-alv)))
              (cpmdir-physdirectoryentry->lrc (nth extent (nth *alv-diri* d-alv)))
              (cpmdir-physdirectoryentry->extnoh (nth extent (nth *alv-diri* d-alv)))
              (cpmdir-physdirectoryentry->blkcnt (nth extent (nth *alv-diri* d-alv)))
              (cpmdir-physdirectoryentry->pointers
               (nth extent (nth *alv-diri* d-alv))))
             (nth *alv-diri* d-alv))
            d-alv))
          extent))
        :instructions (promote induct bash promote
                               (claim (equal start extent))
                               bash bash
                               (exit cpmfs-cpmcreat-correctness-1-lemma-5 (:rewrite) t))
        :rule-classes (:rewrite))

;; (defthm cpmfs-cpmCreat-correctness-1-lemma-4
;;   (implies
;;    (and (d-alvp d-alv)
;;         (natp extent)
;;         (< extent 256)
;;         (natp start)
;;         (<= start extent)
;;         (natp user)
;;         (< user (ash 1 5))
;;         (no-matching-fileextent-loop user name ext extent -1 d-alv))
;;    (let*
;;        ((ent (alv-diri extent d-alv))
;;         (new-d-alv (update-alv-diri extent
;;                                     (change-cpmdir-physdirectoryentry ent
;;                                                                       :status user
;;                                                                       :name name
;;                                                                       :ext ext)
;;                                     d-alv)))
;;      (equal (cpmfs-findfileextent user name ext start -1 new-d-alv)
;;             extent))))

(defthm cpmfs-cpmCreat-correctness-1
  (implies
   (and (character-listp fullname) (equal (len fullname) (+ 2 8 1 3 1))
        (d-alvp d-alv)
        (integerp mode)
        (cpmfs-cpmInode-p dir) (cpmfs-S_ISDIR (cpmfs-cpmInode->mode dir)))
   (mv-let (retval user name ext)
     (cpmfs-splitFilename fullname)
     (implies (>= retval 0)
              (mv-let (retval ino new-d-alv)
                (cpmfs-cpmCreat dir fullname mode d-alv)
                (implies
                 (>= retval 0)
                 (equal (cpmfs-findFileExtent user name ext
                                              (cpmfs-cpmInode->ino ino) -1
                                              new-d-alv)
                        (cpmfs-cpmInode->ino ino))))))))

(thm (IMPLIES
 (AND (CHARACTER-LISTP FULLNAME)
      (EQUAL (LEN FULLNAME) (+ 2 8 1 3 1))
      (D-ALVP D-ALV)
      (CPMFS-CPMINODE-P DIR)
      (CPMFS-S_ISDIR (CPMFS-CPMINODE->MODE DIR))
      (<= 0
          (MV-NTH 0 (CPMFS-SPLITFILENAME FULLNAME)))
      (<= 0
          (MV-NTH 0
                  (CPMFS-CPMCREAT DIR FULLNAME MODE D-ALV))))
 (=
  (CPMFS-FINDFILEEXTENT
      (MV-NTH 1 (CPMFS-SPLITFILENAME FULLNAME))
      (MV-NTH 2 (CPMFS-SPLITFILENAME FULLNAME))
      (MV-NTH 3 (CPMFS-SPLITFILENAME FULLNAME))
      (CPMFS-CPMINODE->INO (MV-NTH 1
                                   (CPMFS-CPMCREAT DIR FULLNAME MODE D-ALV)))
      -1
      (MV-NTH 2
              (CPMFS-CPMCREAT DIR FULLNAME MODE D-ALV)))
  (CPMFS-CPMINODE->INO (MV-NTH 1
                               (CPMFS-CPMCREAT DIR FULLNAME MODE D-ALV))))))

(in-theory (enable CPMFS-S_ISDIR))

;; (defthm cpmfs-cpmCreat-well-formed-output
;;   (mv-let (retval ino d-alv)
;;     (cpmfs-cpmCreat dir fname mode d-alv)
;;     (if ()
;;         ()
;;       ())))

;; leaving out ino for now, because pointers are a mess
(std::defaggregate cpmfs-cpmFile
                   (mode pos))

(defconst *O_WRONLY* (ash 1 0))

(defun cpmfs-cpmOpen (ino file mode)
  (if (or (not (cpmfs-cpmInode-p ino))
          (not (cpmfs-cpmFile-p file))
          (not (cpmfs-S_ISREG (cpmfs-cpmInode->mode ino))))
      (mv -1 file)
    (if (and (not (equal (logand mode *O_WRONLY*) 0))
             (equal (logand (cpmfs-cpmInode->mode ino) (str::strval8 "222")) 0))
        (mv -1 file)
      (let* ((file (change-cpmfs-cpmFile file
                    :pos 0
                    :mode mode))
             )
        (mv 0 file)))))

(defun cpmfs-cpmWrite (file ino buf count)
  (if (or (not (cpmfs-cpmInode-p ino))
          (not (cpmfs-cpmFile-p file))
          (not (unsigned-byte-listp 8 buf))
          (not (natp count)))
      -1
    ()))
