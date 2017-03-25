(in-package "ACL2")

(include-book "file-system-lemmas")
(include-book "std/lists/flatten" :dir :system)

(defthm no-duplicatesp-of-member
  (implies (and (member-equal x lst)
                (no-duplicatesp (flatten lst)))
           (no-duplicatesp x)))

(defun not-intersectp-list (x l)
  (or (atom l)
      (and (not (intersectp x (car l)))
           (not-intersectp-list x (cdr l)))))

(defthm not-intersectp-list-correctness-1
  (equal (intersectp-equal x (flatten l))
         (not (not-intersectp-list x l))))

(defthm not-intersectp-list-correctness-2
  (implies (and (not-intersectp-list x l)
                (member-equal y l))
           (not (intersectp-equal x y))))

(defthm flatten-subset-no-duplicatesp-lemma-1
  (implies (and (consp z)
                (no-duplicatesp (flatten z))
                (member-equal y z)
                (not (equal y (car z))))
           (not (intersectp-equal (car z) y))))

(defthm
  flatten-subset-no-duplicatesp-lemma-2
  (implies (and (no-duplicatesp (flatten z))
                (consp z)
                (member-equal x z)
                (member-equal y z)
                (not (equal y x)))
           (not (intersectp-equal x y)))
  :hints (("Subgoal *1/2''" :use (:instance intersectp-is-commutative
                                            (y (car z))))))

(defthm flatten-subset-no-duplicatesp-lemma-3
  (implies (and (member-equal z y)
                (not (member-equal z x))
                (subsetp-equal x y)
                (no-duplicatesp-equal (flatten y)))
           (not-intersectp-list z x)))

;; This is sort of the main lemma
(defthm flatten-subset-no-duplicatesp
  (implies (and (subsetp-equal x y)
                (no-duplicatesp-equal (flatten y))
                (no-duplicatesp-equal x))
           (no-duplicatesp-equal (flatten x))))

(defun only-nil-duplicatesp-equal (l)
  (declare (xargs :guard (true-list-listp l)))
  (cond ((endp l) t)
        ((and (car l) (member-equal (car l) (cdr l))) nil)
        (t (only-nil-duplicatesp-equal (cdr l)))))

(defthm only-nil-duplicatesp-equal-correctness-1
  (implies (no-duplicatesp l)
           (only-nil-duplicatesp-equal l)))

(defthm only-nil-duplicatesp-if-no-duplicatesp-of-flatten
  (implies (and (true-list-listp x)
                (no-duplicatesp (flatten x)))
           (only-nil-duplicatesp-equal x)))
