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
  (let ((s (hons-get :s mb))
        (size (hons-get :size mb))
        (min (hons-get :min mb))
        (max (hons-get :max mb)))
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
          (> (+ s-offset n) (hons-get :size s-mb))
          (< c (hons-get :min s-mb))
          (> c (hons-get :max s-mb)))
      s-mb
    (build-block
     (append (take s-offset (hons-get :s s-mb))
             (repeat n c)
             (nthcdr (+ s-offset n) (hons-get :s s-mb)))
     (hons-get :size s-mb)
     (hons-get :min s-mb)
     (hons-get :max s-mb))))

(verify-guards block-memset
  :hints (("Goal" :in-theory (enable valid-block-p))))
