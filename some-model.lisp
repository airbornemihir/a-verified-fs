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

(defund block-memset (s-mb s-offset c n)
  (declare (xargs :guard (and (integer-listp (list s-offset c n))
                              (valid-block-p s-mb))
                  :verify-guards nil))
  (if (or (< s-offset 0)
          (< n 0)
          (> (+ s-offset n) (len (cdr (hons-get :units s-mb))))
          (< c (cdr (hons-get :min s-mb)))
          (> c (cdr (hons-get :max s-mb))))
      s-mb
    (build-block
     (append (take s-offset (cdr (hons-get :units s-mb)))
             (repeat n c)
             (nthcdr (+ s-offset n) (cdr (hons-get :units s-mb))))
     (cdr (hons-get :min s-mb))
     (cdr (hons-get :max s-mb)))))

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
                (integerp c)
                (<= 0 m)
                (<= m (len units))
                (<= min c)
                (<= c max))
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
  :guard-debug t
  :hints (("goal")
          ))

(in-theory (disable bounded-int-listp valid-block-p))

#||
example
(let ((s-mb (build-block (repeat 20 7) 0 20)))
  (block-memset s-mb 7 5 5))
||#

