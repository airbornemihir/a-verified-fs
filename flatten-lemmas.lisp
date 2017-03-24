(in-package "ACL2")

(include-book "file-system-lemmas")
(include-book "std/lists/flatten" :dir :system)

(defthm l4-wrchs-returns-stricter-fs-lemma-6
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

(defthm l4-wrchs-returns-stricter-fs-lemma-7
  (implies (and (consp z)
                (no-duplicatesp (flatten z))
                (member-equal y z)
                (not (equal y (car z))))
           (not (intersectp-equal (car z) y))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-8
  (implies (and (no-duplicatesp (flatten z))
                (consp z)
                (member-equal x z)
                (member-equal y z)
                (not (equal y x)))
           (not (intersectp-equal x y)))
  :hints (("Subgoal *1/2''" :use (:instance intersectp-is-commutative
                                            (y (car z))))))

(defthm l4-wrchs-returns-stricter-fs-lemma-9
  (implies (and (member-equal z y)
                (not (member-equal z x))
                (subsetp-equal x y)
                (no-duplicatesp-equal (flatten y)))
           (not-intersectp-list z x)))

;; This is sort of the main lemma
(defthm l4-wrchs-returns-stricter-fs-lemma-10
  (implies (and (subsetp-equal x y)
                (no-duplicatesp-equal (flatten y))
                (no-duplicatesp-equal x))
           (no-duplicatesp-equal (flatten x))))
