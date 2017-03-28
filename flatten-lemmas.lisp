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

(defthm not-intersectp-list-of-append
  (equal (not-intersectp-list x (binary-append l1 l2))
         (and (not-intersectp-list x l1)
              (not-intersectp-list x l2))))

(defthm not-intersectp-equal-if-subset
  (implies (and (not-intersectp-list x l2)
                (subsetp-equal l1 l2))
           (not-intersectp-list x l1)))

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

(defun disjoint-list-listp (x)
  (or (atom x)
      (and (not-intersectp-list (car x) (cdr x))
           (disjoint-list-listp (cdr x)))))

(defthm flatten-disjoint-lists
  (implies (no-duplicatesp (flatten (double-rewrite l)))
           (disjoint-list-listp l)))

;; This theorem won't go through because both
;; (disjoint-list-listp '((1 2) (3 4))) and
;; (subsetp-equal '((1 2) (1 2)) '((1 2) (3 4))) are t.
;; (verify (implies (and (subsetp-equal x y) (disjoint-list-listp y)) (disjoint-list-listp x)))

(defun member-intersectp-equal (x y)
  (and (consp x)
       (or (not (not-intersectp-list (car x) y))
           (member-intersectp-equal (cdr x) y))))

(defthm when-append-is-disjoint-list-listp
  (equal (disjoint-list-listp (binary-append x y))
         (and (disjoint-list-listp x)
              (disjoint-list-listp y) (not (member-intersectp-equal x y)))))

(defthm member-intersectp-with-subset
  (implies (and (member-intersectp-equal z x)
                (subsetp-equal x y))
           (member-intersectp-equal z y)))

(defthm member-intersectp-binary-append
  (implies (and (member-equal x lst2)
                (disjoint-list-listp (binary-append lst1 lst2)))
           (not-intersectp-list x lst1))
  :hints (("Subgoal *1/5''" :use (:instance intersectp-is-commutative (y (car lst1)))) ))
