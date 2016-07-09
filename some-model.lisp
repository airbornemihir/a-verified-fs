(include-book "std/lists/update-nth" :dir :system)

(defund bounded-int-listp (units min max)
  (declare (xargs :guard (integer-listp (list min max))))
  (if (atom units)
      (not units)
    (and (integerp (car units)) (<= min (car units)) (<= (car units) max)
         (bounded-int-listp (cdr units) min max))))

(defthm bounded-int-listp-implies-integer-listp
  (implies (bounded-int-listp units min max) (integer-listp units))
  :hints (("Goal" :in-theory (enable bounded-int-listp))))

(defnd valid-block-p (mb)
  (let ((units (cdr (hons-get :units mb)))
        (min (cdr (hons-get :min mb)))
        (max (cdr (hons-get :max mb))))
    (and (integer-listp (list min max))
         (<= min max)
         (bounded-int-listp units min max))))

(defund build-block (units min max)
  (declare (xargs :guard
                  (and (integer-listp (list min max))
                       (<= min max)
                       (bounded-int-listp units min max))))
  (hons-acons :units units
              (hons-acons :min min
                          (hons-acons :max max
                                      nil))))

;; we're going to be making some changes here
;; this doesn't have an error code as its return value, so we won't attempt to
;; establish one - but we will move some implicit assumptions into the guards
;; because it's crappy to silently fail when we can't memset
(defund block-memset (s-mb s-offset c n)
  (declare (xargs :guard (and (integer-listp (list s-offset c n))
                              (valid-block-p s-mb)
                              (>= s-offset 0)
                              (>= n 0)
                              (<= (+ s-offset n)
                                  (len (cdr (hons-get :units s-mb))))
                              (< c (cdr (hons-get :min s-mb)))
                              (> c (cdr (hons-get :max s-mb))))
                  :verify-guards nil))
  
  (build-block
   (append (take s-offset (cdr (hons-get :units s-mb)))
           (repeat n c)
           (nthcdr (+ s-offset n) (cdr (hons-get :units s-mb))))
   (cdr (hons-get :min s-mb))
   (cdr (hons-get :max s-mb))))

(in-theory (enable bounded-int-listp valid-block-p))

(defthm block-memset-guard-lemma-2
  (implies (and (bounded-int-listp u1 min max) (bounded-int-listp u2 min max))
           (bounded-int-listp (append u1 u2) min max))
  :hints (("Goal" :in-theory (enable bounded-int-listp))))

(defthm block-memset-guard-lemma-3
  (implies (and (integerp min)
                (integerp max)
                (<= min max)
                (bounded-int-listp units min max)
                (integerp m)
                (<= 0 m)
                (<= m (len units)))
           (bounded-int-listp (nthcdr m units)
                              min max)))

(defthm block-memset-guard-lemma-5
  (implies (and (integerp min)
                (integerp max)
                (<= min max)
                (bounded-int-listp u1 min max)
                (bounded-int-listp u2 min max))
           (bounded-int-listp (revappend u1 u2)
                              min max)))

(defthm block-memset-guard-lemma-4
  (implies (and (integerp min)
                (integerp max)
                (<= min max)
                (bounded-int-listp u1 min max)
                (bounded-int-listp u2 min max)
                (integerp m)
                (<= 0 m)
                (<= m (len u1)))
           (bounded-int-listp (first-n-ac m u1 u2)
                              min max)))

(defthm block-memset-guard-lemma-6
  (implies
   (and (integerp min)
        (integerp max)
        (<= min max)
        (integerp c)
        (integerp n)
        (<= 0 n)
        (<= min c)
        (<= c max))
   (bounded-int-listp (repeat n c) min max))
  :hints (("Goal" :in-theory (enable bounded-int-listp repeat))))

(defthm block-memset-guard-lemma-1
  (implies
   (and (integerp min)
        (integerp max)
        (<= min max)
        (bounded-int-listp units min max)
        (integerp s-offset)
        (integerp c)
        (integerp n)
        (<= 0 s-offset)
        (<= 0 n)
        (<= (+ n s-offset) (len units))
        (<= min c)
        (<= c max))
   (bounded-int-listp (append (take s-offset units)
                              (repeat n c)
                              (nthcdr (+ n s-offset) units))
                      min
                      max))
  :hints (("Goal" :in-theory (enable bounded-int-listp repeat))
          ("Subgoal *1/1'''" :in-theory (disable block-memset-guard-lemma-2)
           :use ((:instance block-memset-guard-lemma-2
                            (u1 (repeat n c))
                            (u2 (nthcdr n units)))) )))

(verify-guards block-memset
  :hints (("goal")
          ))

(in-theory (disable bounded-int-listp valid-block-p))

#||
example
(let ((s-mb (build-block (repeat 20 7) 0 20)))
  (block-memset s-mb 7 5 5))
||#

(defund block-memcpy (src-mb src-offset dst-mb dst-offset n)
  (declare (xargs :guard (and (integer-listp (list src-offset dst-offset n))
                              (valid-block-p src-mb)
                              (valid-block-p dst-mb))
                  :verify-guards nil))
  (if (or (< src-offset 0)
          (< dst-offset 0)
          (< n 0)
          (> (+ src-offset n) (len (cdr (hons-get :units src-mb))))
          (> (+ dst-offset n) (len (cdr (hons-get :units dst-mb))))
          (< (cdr (hons-get :min src-mb)) (cdr (hons-get :min dst-mb)))
          (> (cdr (hons-get :max src-mb)) (cdr (hons-get :max dst-mb))))
      dst-mb
    (build-block
     (append (take dst-offset (cdr (hons-get :units dst-mb)))
             (nthcdr src-offset (take (+ src-offset n) (cdr (hons-get :units src-mb))))
             (nthcdr (+ dst-offset n) (cdr (hons-get :units dst-mb))))
     (cdr (hons-get :min dst-mb))
     (cdr (hons-get :max dst-mb)))))

#||
example
(block-memcpy (build-block (repeat 20 7) 0 20) 5 (build-block (repeat 20 5) 0 20) 10 3)
||#

(in-theory (enable bounded-int-listp valid-block-p))

(defthm block-memcpy-guard-lemma-2
  (implies (and (<= dst-min src-min)
                (<= src-max dst-max)
                (integerp dst-min)
                (integerp dst-max)
                (<= dst-min dst-max)
                (integerp src-min)
                (integerp src-max)
                (<= src-min src-max)
                (bounded-int-listp src-units src-min src-max))
           (bounded-int-listp src-units dst-min dst-max)))

(defthm block-memcpy-guard-lemma-4
  (equal (len (revappend l2 l1))
         (+ (len l1) (len l2))))

(defthm block-memcpy-guard-lemma-3
  (implies (and  (integerp m) (>= m 0))
           (equal (len (first-n-ac m l1 l2))
                  (+ (len l2) m)))
  :hints (("Goal" :induct (first-n-ac m l1 l2)) ))

(defthm block-memcpy-guard-lemma-1
  (implies (and (integer-listp (list src-offset dst-offset n))
                (<= 0 src-offset)
                (<= 0 dst-offset)
                (<= 0 n)
                (<= (+ n src-offset) (len src-units))
                (<= (+ dst-offset n) (len dst-units))
                (<= dst-min src-min)
                (<= src-max dst-max)
                (integerp dst-min)
                (integerp dst-max)
                (<= dst-min dst-max)
                (bounded-int-listp dst-units dst-min dst-max)
                (integerp src-min)
                (integerp src-max)
                (<= src-min src-max)
                (bounded-int-listp src-units src-min src-max))
           (bounded-int-listp (append (first-n-ac dst-offset dst-units nil)
                                      (nthcdr src-offset
                                              (first-n-ac (+ n src-offset)
                                                          src-units nil))
                                      (nthcdr (+ dst-offset n) dst-units))
                              dst-min dst-max)))

(verify-guards block-memcpy :guard-debug t)

(in-theory (disable bounded-int-listp valid-block-p))

;; ok, it's time to talk
;; there's no sense trying to model blocks of the disk as, you know, numbers
;; ranging from 0 to 4194303 for instance (for blocks of size 512 kilobytes.)
;; the logical thing is to make the read and write operations like memcpy, and
;; enforce the block nature by making sure the size and offset of the byte is
;; compatible with the disk (that is, reads and writes should begin and end on
;; a block boundary)

(defund block-write (src-mb src-offset dst-mb dst-offset n blocksize)
  (declare (xargs :guard (and (integer-listp (list src-offset dst-offset n blocksize))
                              (>= blocksize 1)
                              (valid-block-p src-mb)
                              (valid-block-p dst-mb)
                              (equal (rem dst-offset blocksize) 0)
                              (equal (rem n blocksize) 0))
                  :verify-guards nil)
           (ignore blocksize))
  (block-memcpy src-mb src-offset dst-mb dst-offset n))

(verify-guards block-write :guard-debug t)

(defund block-read (src-mb src-offset dst-mb dst-offset n blocksize)
  (declare (xargs :guard (and (integer-listp (list src-offset dst-offset n blocksize))
                              (>= blocksize 1)
                              (valid-block-p src-mb)
                              (valid-block-p dst-mb)
                              (equal (rem src-offset blocksize) 0)
                              (equal (rem n blocksize) 0))
                  :verify-guards nil)
           (ignore blocksize))
  (block-memcpy src-mb src-offset dst-mb dst-offset n))

(verify-guards block-read :guard-debug t)
