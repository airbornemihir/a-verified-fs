(include-book "centaur/bitops/part-install" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/strings/hex" :dir :system)

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

;; (d->alv=malloc(d->alvSize*sizeof(int)))
(defstobj d-alv
  (alv-bytes :type (array (unsigned-byte 32) (*d-alvSize*)) :initially 0)
  (alv-dir :type (array (satisfies cpmdir-PhysDirectoryEntry-p) (*d-maxdir*))
           :initially #.*pde-default*))

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

(defun cpmfs-findFileExtent (user name ext start extno d-alv)
  (declare (xargs :stobjs (d-alv)
                  :verify-guards nil
                  :measure
                  (if (or (not (natp start)) (>= start *d-maxdir*))
                      0
                    (- *d-maxdir* start))))
  (if (or (not (natp start)) (>= start *d-maxdir*))
      -1
    (if (let* ((dir-start (alv-diri start d-alv)) )
          (and (< (cpmdir-PhysDirectoryEntry->status dir-start) (ash 1 5))
               (or (< extno 0)
                   (equal (cpmdir-EXTENT
                           (cpmdir-PhysDirectoryEntry->extnol dir-start)
                           (cpmdir-PhysDirectoryEntry->extnoh dir-start))
                          (truncate extno *d-extents*)))
               ;; and inside an and to keep things clear
               (and
                (equal user (cpmdir-PhysDirectoryEntry->status dir-start))
                (equal name (cpmdir-PhysDirectoryEntry->name dir-start))
                (equal ext (cpmdir-PhysDirectoryEntry->ext dir-start)))))
        start
      (cpmfs-findFileExtent user name ext (+ start 1) extno d-alv))))

(defun cpmfs-splitFilename(fullname)
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

(defun cpmfs-findFreeExtent (d-alv)
  (declare (xargs :stobjs d-alv
                  :verify-guards nil))
  (cpmfs-findFreeExtent-loop 0 d-alv))

;; this isn't exactly in compliance with the C code - that remains to be
;; checked
(defconst *cpmfs-cpmCreat-default-ino* (make-cpmfs-cpmInode))

(defun cpmfs-cpmCreat (dir fname mode d-alv)
  (declare (xargs :stobjs d-alv
                  :verify-guards nil))
  (if (and nil (cpmfs-cpmInode->mode dir)) ;; to be replaced by (!S_ISDIR(dir->mode))
      (mv -1 *cpmfs-cpmCreat-default-ino* d-alv)
    (mv-let (retval user name ext)
      (cpmfs-splitFilename fname)
      (if (< retval 0)
        (mv -1 *cpmfs-cpmCreat-default-ino* d-alv)
      (if (< (cpmfs-findFileExtent user name ext 0 -1 d-alv) 0)
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
                         :ino extent :mode mode :size 0)))
              (mv 0 ino d-alv)))))))
    ))

;; leaving out ino for now, because pointers are a mess
(std::defaggregate cpmfs-cpmFile
                   (mode pos))

