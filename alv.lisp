(include-book "centaur/bitops/part-install" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(include-book "make-event/proof-by-arith" :dir :system)

;; these are the values after a call to diskdefReadSuper
(defconst *d-secLength* 512)
(defconst *d-sectrk* 18)
(defconst *d-tracks* 160)
(defconst *d-offset* 0)
(defconst *d-boottrk* 2)
(defconst *d-blksiz* 4096)
(defconst *d-maxdir* 256)
(defconst *d-size* 355)
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
;;   char name[8];
;;   char ext[3];
;;   char extnol;
;;   char lrc;
;;   char extnoh;
;;   char blkcnt;
;;   char pointers[16];
;; };
(defconst *pde-pointercnt* 16)

(defstobj PhysDirectoryEntry
  (pde-status :type (signed-byte 8) :initially 0)
  (pde-name :type (array character (8)) :initially #\X)
  (pde-ext :type (array character (3)) :initially #\X)
  (pde-extnol :type character :initially #\X)
  (pde-lrc :type character :initially #\X)
  (pde-extnoh :type character :initially #\X)
  (pde-blkcnt :type character :initially #\X)
  (pde-pointers :type (array character (*pde-pointercnt*)) :initially #\X))

;; (d->alv=malloc(d->alvSize*sizeof(int)))
(defstobj d-alv
  (alv-bytes :type (array (unsigned-byte 32) (*d-alvSize*)) :initially 0)
  (alv-dir :type (array PhysDirectoryEntry (*d-maxdir*))))

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
(defun alv-block-allocation-loop (i1 j1 d-alv)
  (declare (xargs :stobjs (d-alv)
                  :guard (and (integerp i1)
                              (integerp j1)
                              (<= j1 *pde-pointercnt*)
                              (>= i1 0) (< i1 *d-maxdir*))
                  :verify-guards nil
                  :measure (if (and (integerp j1) (<= j1 *pde-pointercnt*))
                               (- *pde-pointercnt* j1)
                             0)
                  :measure-debug t))
  (if (or (not (integerp j1)) (>= j1 *pde-pointercnt*))
      d-alv
    (stobj-let
     ((PhysDirectoryEntry (alv-diri i1 d-alv)))
     (PhysDirectoryEntry)
     PhysDirectoryEntry
     (alv-block-allocation-loop i1 (+ j1 1) d-alv))))

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

(defthm allocBlock-succeeds-only-after-full-blocks
  (mv-let
    (new-d-alv block) (alv-allocBlock-loop d-alv startblock) (declare (ignore new-d-alv))
    (implies (and (natp startblock) (>= block startblock) (d-alvp d-alv)
                  (alv-full-p-loop d-alv startblock))
             (alv-full-p-loop d-alv block)))
  :hints (("Goal" :in-theory (disable d-alvp)) ))
