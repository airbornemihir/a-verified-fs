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

(defun alv-allocBlock-loop (d-alv block)
  (declare (xargs :stobjs (d-alv)
                  :measure (if (and (integerp block) (<= block (* *INTBITS* *d-alvsize*)))
                               (- (* *INTBITS* *d-alvsize*) block)
                             0)
                  :verify-guards nil))
  (if (or (not (natp block)) (>= block (* *INTBITS* *d-alvsize*)))
      (mv d-alv -1)
    (let* ((i (ash block -5))
           (j (part-select block :high 4 :low 0))
           (thisbit (part-select (alv-bytesi i d-alv) :low j :high j)))
      (if (equal thisbit 0)
          (let
              ((d-alv (update-alv-bytesi i (part-install 1 (alv-bytesi i d-alv)
                                                         :low j :high j) d-alv)))
            (mv
             d-alv
             block))
          
        (alv-allocBlock-loop d-alv (+ block 1))))
    ))

(defun alv-allocBlock (d-alv)
  (declare (xargs :stobjs (d-alv)
                  :verify-guards nil))
  (alv-allocBlock-loop d-alv 0))

(defun is-full-p-loop (d-alv i)
  (declare (xargs :stobjs (d-alv)
                  :measure (if (and (integerp i) (<= i *d-alvsize*))
                               (- *d-alvsize* i)
                             0)
                  ))
  (and (natp i)
       (or (>= i *d-alvsize*)
           (and (equal (alv-bytesi i d-alv) (- (ash 1 *INTBITS*) 1))
                (is-full-p-loop d-alv (+ i 1))))))

(defun is-full-p (d-alv)
  (declare (xargs :stobjs (d-alv)))
  (is-full-p-loop d-alv 0))

(defthm allocBlock-succeeds-only-after-full-blocks-lemma-1
  (implies (and (integerp block) (d-alvp d-alv))
           (integerp (mv-nth 1 (alv-allocblock-loop d-alv block)))))

(defthm allocBlock-succeeds-only-after-full-blocks-lemma-2
  (implies (and (integerp x) (<= 32 x))
              (<= 1 (floor x 32))))

(defthm allocblock-succeeds-only-after-full-blocks-lemma-5
  (implies (and (natp i1) (< i1 (len alv-bytes)) (alv-bytesp alv-bytes))
           (integerp (nth i1 alv-bytes))))

(defthm allocblock-succeeds-only-after-full-blocks-lemma-6
  (implies (and (integerp block) (d-alvp d-alv))
           (< (mv-nth 1 (alv-allocblock-loop d-alv block)) (* *INTBITS* *d-alvsize*))))

(defthm allocblock-succeeds-only-after-full-blocks-lemma-7
 (implies (and (natp x) (integerp y) (> y 0))
          (natp (floor x y))))

(proof-by-arith
 (defthm allocblock-succeeds-only-after-full-blocks-lemma-8
   (implies (and (natp x) (integerp y) (> y 0) (integerp z) (> z 0) (< x (* y z)))
            (< (floor x y) z))))

(defthm allocblock-succeeds-only-after-full-blocks-lemma-9
 (implies (and (d-alvp d-alv)
               (not (integerp (* 1/2 (ifix (car (car d-alv))))))
               (<= 0
                   (mv-nth 1 (alv-allocblock-loop d-alv 1)))
               (integerp j2)
               (<= 0 j2)
               (consp (car d-alv))
               (< j2
                  (mod (mv-nth 1 (alv-allocblock-loop d-alv 1))
                       32))
               (consp d-alv))
          (integerp (nth (floor (mv-nth 1 (alv-allocblock-loop d-alv 1))
                                32)
                         (car d-alv)))))

(defthm allocBlock-succeeds-only-after-full-blocks-lemma-4
 (mv-let
   (new-d-alv block) (alv-allocBlock d-alv) (declare (ignore new-d-alv))
   (implies (and (d-alvp d-alv) (>= block 0) (natp j2) (< j2 (part-select block :high 4 :low 0)))
            (not (equal 0 (logand (alv-bytesi (ash block -5) d-alv) (ash 1 j2))))))
 :hints (("Goal" :in-theory (disable d-alvp))
         ("Subgoal 4.4''"
          :in-theory (disable
                      allocblock-succeeds-only-after-full-blocks-lemma-9)
          :use allocblock-succeeds-only-after-full-blocks-lemma-9)))

(defthm allocBlock-succeeds-only-after-full-blocks-lemma-3
  (mv-let
    (new-d-alv block) (alv-allocblock-loop d-alv startblock) (declare (ignore new-d-alv))
    (implies (and (not (equal 0
                              (part-select (car (car d-alv)) :low 0 :high 0)))
                  (integerp block)
                  (integerp startblock)
                  (>= startblock *INTBITS*)
                  (< startblock (* *INTBITS* *d-alvsize*))
                  (consp d-alv)
                  (consp (car d-alv))
                  (<= 32
                      block)
                  (d-alvp d-alv)
                  (< (floor block
                            32)
                     13))
             (is-full-p-loop d-alv
                             (floor block
                                    *INTBITS*)))))

(defthm allocBlock-succeeds-only-after-full-blocks
  (mv-let
    (new-d-alv block) (alv-allocBlock d-alv) (declare (ignore new-d-alv))
    (implies (and (>= block *INTBITS*) (d-alvp d-alv))
             (is-full-p-loop d-alv (- (ash block -5) 1))))
  :hints (("Goal" :in-theory (disable d-alvp)) ))

(defthm allocBlock-fails-only-when-blocks-full
  (implies (and
            (d-alvp d-alv)
            (mv-let
              (d-alv ret) (alv-allocBlock d-alv)
              (declare (ignore d-alv)) (< ret 0)))
           (is-full-p d-alv))
  :otf-flg t)

