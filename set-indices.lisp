(in-package "ACL2")

(include-book "file-system-lemmas")
(include-book "bounded-nat-listp")

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

(defthm set-indices-correctness-1
  (implies (and (natp n)
                (nat-listp index-list)
                (not (member-equal n index-list)))
           (equal (nth n (set-indices v index-list value-list))
                  (nth n v))))

(defthm set-indices-correctness-2
        (implies (and (true-listp v)
                      (nat-listp index-list)
                      (true-listp value-list)
                      (equal (len index-list)
                             (len value-list))
                      (no-duplicatesp-equal index-list)
                      (natp m)
                      (< m (len index-list)))
                 (equal (nth (nth m index-list)
                             (set-indices v index-list value-list))
                        (nth m value-list))))

(defthm set-indices-correctness-3
  (implies (bounded-nat-listp index-list (len v))
           (equal (len (set-indices v index-list value-list))
                  (len v))))

(defthm set-indices-correctness-4
  (implies (and (boolean-listp v)
                (nat-listp index-list)
                (boolean-listp value-list)
                (equal (len index-list)
                       (len value-list)))
           (boolean-listp (set-indices v index-list value-list))))

;; the name set-indices-correctness-5 is probably never going to be used
;; because the function is enabled and the property is too obvious.

(defund set-indices-in-alv (alv index-list value)
  (declare (xargs :guard (and (boolean-listp alv)
                              (nat-listp index-list)
                              (booleanp value))))
  (set-indices alv index-list (make-list (len index-list) :initial-element value)))

(defthm
  set-indices-in-alv-correctness-1
  (implies
   (and (boolean-listp alv)
        (booleanp value))
   (boolean-listp (set-indices-in-alv alv index-list value)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable set-indices-in-alv))))

(defthm
  set-indices-in-alv-correctness-2
  (implies
   (and (boolean-listp alv)
        (booleanp value)
        (bounded-nat-listp index-list (len alv)))
   (equal (len (set-indices-in-alv alv index-list value))
          (len alv)))
  :hints (("Goal" :in-theory (enable set-indices-in-alv))))

(defthm
  set-indices-in-alv-correctness-3
  (implies
   (and (boolean-listp alv)
        (nat-listp index-list)
        (booleanp value)
        (member-equal n index-list)
        (< n (len alv)))
   (equal (nth n
               (set-indices-in-alv alv index-list value))
          value))
  :hints (("Goal" :in-theory (enable set-indices-in-alv))))

(defthm
  set-indices-in-alv-correctness-4
  (implies
   (and (boolean-listp alv)
        (nat-listp index-list)
        (booleanp value)
        (natp n)
        (not (member-equal n index-list))
        (< n (len alv)))
   (equal (nth n
               (set-indices-in-alv alv index-list value))
          (nth n alv)))
  :hints (("Goal" :in-theory (enable set-indices-in-alv))))

(defthm
  set-indices-in-alv-correctness-5
  (equal (set-indices-in-alv alv nil value) alv)
  :hints (("Goal" :in-theory (enable set-indices-in-alv))))
