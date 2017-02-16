(in-package "ACL2")

(defthm make-character-list-makes-character-list
  (character-listp (make-character-list x)))

(defthm len-of-binary-append
  (equal (len (binary-append x y)) (+ (len x) (len y))))

(defthm len-of-make-character-list
  (equal (len (make-character-list x)) (len x)))

(defthm len-of-revappend
  (equal (len (revappend x y)) (+ (len x) (len y))))

(defthm len-of-first-n-ac
  (implies (natp i) (equal (len (first-n-ac i l ac)) (+ i (len ac)))))

(defthm nthcdr-of-binary-append-1
  (implies (and (integerp n) (>= n (len x)))
           (equal (nthcdr n (binary-append x y))
                  (nthcdr (- n (len x)) y)))
  :hints (("Goal" :induct (nthcdr n x)) ))

(defthm first-n-ac-of-binary-append-1
  (implies (and (natp i) (<= i (len x)))
           (equal (first-n-ac i (binary-append x y) ac)
                  (first-n-ac i x ac))))

(defthm by-slice-you-mean-the-whole-cake
  (implies (true-listp l)
           (equal (first-n-ac (len l) l ac)
                  (revappend ac l)))
  :hints (("Goal" :induct (revappend l ac)) )
  :rule-classes ((:rewrite :corollary
                           (implies (and (true-listp l) (equal i (len l)))
                                    (equal (first-n-ac i l ac) (revappend ac l)))) ))

(defthm assoc-after-delete-assoc
  (implies (not (equal name1 name2))
           (equal (assoc-equal name1 (delete-assoc name2 alist))
                  (assoc-equal name1 alist))))

(defthm character-listp-of-first-n-ac
  (implies (and (character-listp l) (character-listp acc) (<= n (len l)))
           (character-listp (first-n-ac n l acc))))

(defthm character-listp-of-nthcdr
  (implies (and (character-listp l))
           (character-listp (nthcdr n l))))

(defthm already-a-character-list
  (implies (character-listp x) (equal (make-character-list x) x)))
