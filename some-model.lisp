(include-book "std/lists/update-nth" :dir :system)

(defund bounded-int-listp (s size min max)
  (declare (xargs :guard (integer-listp (list size min max))))
  (if (atom s)
      (and (not s) (equal size 0))
    (and (integerp (car s)) (< min (car s)) (< (car s) max)
         (bounded-int-listp (cdr s) (- size 1) min max))))

(defthm bounded-int-listp-implies-integer-listp
  (implies (bounded-int-listp s size min max) (integer-listp s))
  :hints (("Goal" :in-theory (enable bounded-int-listp))))

(defthm len-if-bounded-int-listp
  (implies (bounded-int-listp s size min max) (equal (len s) size))
  :hints (("Goal" :in-theory (enable bounded-int-listp))))

(defnd valid-block-p (mb)
  (let ((s (cdr (hons-get :s mb)))
        (size (cdr (hons-get :size mb)))
        (min (cdr (hons-get :min mb)))
        (max (cdr (hons-get :max mb))))
    (and (integer-listp (list size min max))
         (<= min max)
         (bounded-int-listp s size min max))))

(defund build-block (s size min max)
  (declare (xargs :guard
                  (and (integer-listp (list size min max))
                       (<= min max)
                       (bounded-int-listp s size min max))))
  (hons-acons :s s
              (hons-acons :size size
                          (hons-acons :min min
                                      (hons-acons :max max
                                                  nil)))))

(defund block-memset (s-mb s-offset c n)
  (declare (xargs :guard (and (integer-listp (list s-offset c n))
                              (valid-block-p s-mb))
                  :verify-guards nil))
  (if (or (< s-offset 0)
          (< n 0)
          (> (+ s-offset n) (cdr (hons-get :size s-mb)))
          (< c (cdr (hons-get :min s-mb)))
          (> c (cdr (hons-get :max s-mb))))
      s-mb
    (build-block
     (append (take s-offset (cdr (hons-get :s s-mb)))
             (repeat n c)
             (nthcdr (+ s-offset n) (cdr (hons-get :s s-mb))))
     (cdr (hons-get :size s-mb))
     (cdr (hons-get :min s-mb))
     (cdr (hons-get :max s-mb)))))

(defthm block-memset-guard-lemma-1
  (implies
   (and (integerp size)
        (integerp min)
        (integerp max)
        (<= min max)
        (bounded-int-listp s size min max)
        (integerp s-offset)
        (integerp c)
        (integerp n)
        (<= 0 s-offset)
        (<= 0 n)
        (<= (+ n s-offset) size)
        (<= min c)
        (<= c max))
   (bounded-int-listp (append (take s-offset s)
                              (repeat n c)
                              (nthcdr (+ n s-offset) s))
                      size
                      min
                      max)))

(verify-guards block-memset
  :guard-debug t
  :hints (("goal" :in-theory (enable valid-block-p))
          ("Subgoal 9'" :use ((:instance bounded-int-listp-implies-integer-listp
                                         (s (cdr (hons-assoc-equal :s s-mb)))
                                         (size (cdr (hons-assoc-equal :size s-mb)))
                                         (min (cdr (hons-assoc-equal :min s-mb)))
                                         (max (cdr (hons-assoc-equal :max s-mb)))
                                         ))
           :in-theory (disable bounded-int-listp-implies-integer-listp))
          ))

(let ((s-mb (build-block (repeat 20 7) 20 0 20)))
  (let ((s (hons-get :s s-mb))
      (size (hons-get :size s-mb))
      (min (hons-get :min s-mb))
      (max (hons-get :max s-mb)))
  (and (integer-listp (list size min max))
       (<= min max)
       (bounded-int-listp s size min max))))
