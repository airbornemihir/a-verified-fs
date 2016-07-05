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

(defthm block-memset-guard-lemma-2
  (implies (and (bounded-int-listp u1 min max) (bounded-int-listp u2 min max))
           (bounded-int-listp (append u1 u2) min max))
  :hints (("Goal" :in-theory (enable bounded-int-listp))))

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
          ("Subgoal 8'" :use ((:instance bounded-int-listp-implies-integer-listp
                                         (units (cdr (hons-assoc-equal :units s-mb)))
                                         (min (cdr (hons-assoc-equal :min s-mb)))
                                         (max (cdr (hons-assoc-equal :max
                                                                     s-mb))))))
          ("Subgoal *1/1.2'" :expand ((repeat 0 c) ))))

(verify-guards block-memset
  :guard-debug t
  :hints (("goal" :in-theory (enable valid-block-p))
          ))

(let ((s-mb (build-block (repeat 20 7) 20 0 20)))
  (let ((s (hons-get :s s-mb))
      (size (hons-get :size s-mb))
      (min (hons-get :min s-mb))
      (max (hons-get :max s-mb)))
  (and (integer-listp (list size min max))
       (<= min max)
       (bounded-int-listp s size min max))))
