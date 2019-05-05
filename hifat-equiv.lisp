(in-package "ACL2")

;  hifat-equiv.lisp                                    Mihir Mehta

; Some definitions and theorems for the equivalence relation hifat-equiv.

(include-book "hifat")

(defun
    hifat-subsetp
    (m1-file-alist1 m1-file-alist2)
  (declare
   (xargs
    :guard (and (m1-file-alist-p m1-file-alist1)
                (m1-file-alist-p m1-file-alist2))
    :hints (("goal" :in-theory (enable m1-file->contents
                                       m1-directory-file-p)))))
  (b*
      (((when (atom m1-file-alist1)) t)
       ((unless (mbt (and (consp (car m1-file-alist1))
                          (stringp (car (car m1-file-alist1))))))
        (and (member-equal (car m1-file-alist1)
                           m1-file-alist2)
             (hifat-subsetp (cdr m1-file-alist1)
                            m1-file-alist2)))
       (name (caar m1-file-alist1))
       (file1 (cdar m1-file-alist1))
       ((unless (consp (assoc-equal name m1-file-alist2)))
        nil)
       (file2 (cdr (assoc-equal name m1-file-alist2))))
    (if (not (m1-directory-file-p file1))
        (and (not (m1-directory-file-p file2))
             (hifat-subsetp (cdr m1-file-alist1)
                            m1-file-alist2)
             (equal (m1-file->contents file1)
                    (m1-file->contents file2)))
      (and (m1-directory-file-p file2)
           (hifat-subsetp (cdr m1-file-alist1)
                          m1-file-alist2)
           (hifat-subsetp (m1-file->contents file1)
                          (m1-file->contents file2))))))

;; It's tempting to remove this predicate, because it makes the fixing of
;; certain functions hard... but it does give us the desirable property of
;; maintaining equality for hifat-entry-count between two directory trees whenever
;; it holds for the two trees. I'm not sure that property is currently used,
;; but it makes a good argument for keeping it. One other argument is the proof
;; of anti-reflexivity for hifat-subsetp - if we are to prove that y is a
;; subset of y under this definition of subsetp (that is, this definition which
;; doesn't do remove-equal), then we need to make sure there are no duplicate
;; bindings for the same filename within a directory. The third argument
;; pertains to the generally understood semantics for filesystems, where there
;; is generally no valid way of dealing with two directory entries referring to
;; the same filename (not the same inode, which is OK in filesystems with hard
;; linking.) There doesn't seem to be much in the literature supporting this,
;; but there are folks on StackOverflow
;; (https://unix.stackexchange.com/a/227370,
;; https://unix.stackexchange.com/a/227361).
(defund
  hifat-no-dups-p (m1-file-alist)
  (declare (xargs :guard (m1-file-alist-p m1-file-alist)))
  (cond ((atom m1-file-alist) t)
        ((not (hifat-no-dups-p (cdr m1-file-alist)))
         nil)
        ((not (mbt (and (consp (car m1-file-alist))
                        (stringp (car (car m1-file-alist))))))
         (not (member-equal (car m1-file-alist)
                            (cdr m1-file-alist))))
        ((consp (assoc-equal (caar m1-file-alist)
                             (cdr m1-file-alist)))
         nil)
        ((m1-directory-file-p (cdar m1-file-alist))
         (hifat-no-dups-p
          (m1-file->contents (cdar m1-file-alist))))
        (t t)))

(defthm hifat-no-dups-p-of-cdr
  (implies (hifat-no-dups-p fs)
           (hifat-no-dups-p (cdr fs)))
  :hints (("goal" :in-theory (enable hifat-no-dups-p))))

(defthm
  hifat-no-dups-p-of-m1-file-contents-of-cdar
  (implies (and (hifat-no-dups-p hifat-file-alist)
                (m1-file-alist-p hifat-file-alist)
                (m1-directory-file-p (cdr (car hifat-file-alist))))
           (hifat-no-dups-p (m1-file->contents (cdr (car hifat-file-alist)))))
  :hints (("goal" :in-theory (enable hifat-no-dups-p))))

(defun hifat-file-alist-fix (hifat-file-alist)
  (declare (xargs :guard (and (m1-file-alist-p hifat-file-alist)
                              (hifat-no-dups-p hifat-file-alist))
                  :verify-guards nil))
  (mbe
   :exec
   hifat-file-alist
   :logic
   (b*
       (((when (atom hifat-file-alist)) nil)
        (head (cons
               (fat32-filename-fix (caar hifat-file-alist))
               (m1-file-fix (cdar hifat-file-alist))))
        (tail (hifat-file-alist-fix (cdr hifat-file-alist)))
        ((when (consp (assoc-equal (car head) tail)))
         tail))
     (if
         (m1-directory-file-p (cdr head))
         (cons
          (cons (car head)
                (make-m1-file :dir-ent (m1-file->dir-ent (cdr head))
                              :contents (hifat-file-alist-fix (m1-file->contents (cdr head)))))
          tail)
       (cons head tail)))))

(defthm m1-file-alist-p-of-hifat-file-alist-fix
  (m1-file-alist-p (hifat-file-alist-fix hifat-file-alist)))

(defthm
  hifat-file-alist-fix-when-hifat-no-dups-p
  (implies (and (hifat-no-dups-p hifat-file-alist)
                (m1-file-alist-p hifat-file-alist))
           (equal (hifat-file-alist-fix hifat-file-alist)
                  hifat-file-alist))
  :hints (("goal" :in-theory (enable hifat-no-dups-p))))

(defthm
  hifat-no-dups-p-of-hifat-file-alist-fix
  (hifat-no-dups-p (hifat-file-alist-fix hifat-file-alist))
  :hints
  (("goal"
    :in-theory (e/d (hifat-no-dups-p)
                    (alistp-when-m1-file-alist-p))
    :induct (hifat-file-alist-fix hifat-file-alist))
   ("subgoal *1/4"
    :use
    (:instance
     alistp-when-m1-file-alist-p
     (x (hifat-file-alist-fix (cdr hifat-file-alist)))))
   ("subgoal *1/3"
    :use
    (:instance
     alistp-when-m1-file-alist-p
     (x (hifat-file-alist-fix (cdr hifat-file-alist)))))))

(defthm
  hifat-file-alist-fix-guard-lemma-1
  (implies (and (hifat-no-dups-p hifat-file-alist)
                (m1-file-alist-p hifat-file-alist)
                (consp hifat-file-alist)
                (consp (car hifat-file-alist)))
           (not (consp (assoc-equal (car (car hifat-file-alist))
                                    (cdr hifat-file-alist)))))
  :hints (("goal" :in-theory (enable hifat-no-dups-p))))

(verify-guards hifat-file-alist-fix)

(defthm hifat-subsetp-of-remove1-assoc-1
  (implies (and (m1-file-alist-p m1-file-alist1)
                (atom (assoc-equal key m1-file-alist1)))
           (equal (hifat-subsetp m1-file-alist1
                                 (remove1-assoc key m1-file-alist2))
                  (hifat-subsetp m1-file-alist1 m1-file-alist2))))

(defthm
  hifat-no-dups-p-of-remove1-assoc-equal
  (implies
   (hifat-no-dups-p m1-file-alist)
   (hifat-no-dups-p (remove1-assoc-equal key m1-file-alist)))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p))))

(defthm hifat-subsetp-preserves-assoc-equal
  (implies (and (hifat-subsetp x y)
                (stringp file)
                (consp (assoc-equal file x)))
           (consp (assoc-equal file y))))

(defthm
  hifat-subsetp-transitive-lemma-1
  (implies
   (and (m1-file-alist-p y)
        (consp (assoc-equal key y))
        (hifat-subsetp y z))
   (iff (m1-directory-file-p (cdr (assoc-equal key z)))
        (m1-directory-file-p (cdr (assoc-equal key y)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (m1-file-alist-p y)
          (consp (assoc-equal key y))
          (hifat-subsetp y z)
          (m1-directory-file-p (cdr (assoc-equal key y))))
     (m1-directory-file-p (cdr (assoc-equal key z)))))))

(defthm
  hifat-subsetp-transitive-lemma-2
  (implies (and (m1-file-alist-p z)
                (hifat-no-dups-p z)
                (m1-directory-file-p (cdr (assoc-equal key z))))
           (hifat-no-dups-p (m1-file->contents (cdr (assoc-equal key z)))))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p)) ))

(defthm
  hifat-subsetp-transitive-lemma-3
  (implies (and (m1-file-alist-p y)
                (m1-directory-file-p (cdr (assoc-equal key y)))
                (hifat-subsetp y z))
           (hifat-subsetp (m1-file->contents (cdr (assoc-equal key y)))
                          (m1-file->contents (cdr (assoc-equal key z))))))

(local
 (defthm
   hifat-subsetp-transitive-lemma-4
   (implies
    (and (m1-file-alist-p y)
         (consp (assoc-equal key y))
         (not (m1-directory-file-p (cdr (assoc-equal key y))))
         (hifat-subsetp y z))
    (equal (m1-file->contents (cdr (assoc-equal key y)))
           (m1-file->contents (cdr (assoc-equal key z)))))))

(defthm
  hifat-subsetp-transitive
  (implies (and (hifat-subsetp x y)
                (hifat-subsetp y z)
                (m1-file-alist-p x)
                (m1-file-alist-p y))
           (hifat-subsetp x z))
  :hints
  (("goal" :induct (mv (hifat-subsetp x z)
                       (hifat-subsetp x y)))
   ("subgoal *1/5" :in-theory (disable hifat-subsetp-transitive-lemma-1)
    :use (:instance hifat-subsetp-transitive-lemma-1
                    (key (car (car x)))))
   ("subgoal *1/2" :in-theory (disable hifat-subsetp-transitive-lemma-1)
    :use (:instance hifat-subsetp-transitive-lemma-1
                    (key (car (car x)))))))

(defthm
  hifat-subsetp-when-atom
  (implies (atom m1-file-alist2)
           (equal (hifat-subsetp m1-file-alist1 m1-file-alist2)
                  (atom m1-file-alist1))))

(defthm hifat-subsetp-reflexive-lemma-1
  (implies (and (m1-file-alist-p x)
                (hifat-no-dups-p (append x y)))
           (equal (assoc-equal (car (car y)) (append x y))
                  (car y)))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p)) ))

(defthm hifat-subsetp-reflexive-lemma-2
  (implies (not (hifat-no-dups-p y))
           (not (hifat-no-dups-p (append x y))))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p)) ))

(defthm hifat-subsetp-reflexive-lemma-3
  (implies (and (m1-file-alist-p y)
                (hifat-no-dups-p y)
                (m1-directory-file-p (cdr (car y))))
           (hifat-no-dups-p (m1-file->contents (cdr (car y)))))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p)) ))

(encapsulate
  ()

  (local
   (defun
       induction-scheme (x y)
     (declare
      (xargs
       :hints
       (("goal" :in-theory (enable m1-file->contents
                                   m1-file-contents-fix)))))
     (if
         (atom y)
         x
       (append
        (induction-scheme nil (m1-file->contents (cdr (car y))))
        (induction-scheme (append x (list (car y)))
                          (cdr y))))))

  (defthm hifat-subsetp-reflexive-lemma-4
    (implies (and (m1-file-alist-p x)
                  (m1-file-alist-p y)
                  (hifat-no-dups-p (append x y)))
             (hifat-subsetp y (append x y)))
    :hints (("goal" :induct (induction-scheme x y)
             :in-theory (enable hifat-no-dups-p)))))

(defthm
  hifat-subsetp-reflexive-lemma-5
  (implies
   (m1-file-p file)
   (equal (m1-directory-file-p
           (m1-file dir-ent (m1-file->contents file)))
          (m1-directory-file-p file)))
  :hints (("goal" :in-theory (enable m1-directory-file-p))))

(defthm
  hifat-subsetp-reflexive
  (implies (and (m1-file-alist-p y)
                (hifat-no-dups-p y))
           (hifat-subsetp y y))
  :hints
  (("goal"
    :in-theory
    (disable hifat-subsetp-reflexive-lemma-4)
    :use (:instance hifat-subsetp-reflexive-lemma-4
                    (x nil)))))

(defund hifat-equiv (m1-file-alist1 m1-file-alist2)
  (declare (xargs :guard (and (m1-file-alist-p m1-file-alist1)
                              (hifat-no-dups-p m1-file-alist1)
                              (m1-file-alist-p m1-file-alist2)
                              (hifat-no-dups-p m1-file-alist2))))
  (b* ((m1-file-alist1 (hifat-file-alist-fix m1-file-alist1))
       (m1-file-alist2 (hifat-file-alist-fix m1-file-alist2)))
    (and (hifat-subsetp m1-file-alist1 m1-file-alist2)
         (hifat-subsetp m1-file-alist2 m1-file-alist1))))

;; A bug was here: after we changed the definition of hifat-equiv, we placed
;; this defequiv form somewhat later in the file, with the result that two
;; rules which should have rewritten in an hifat-equiv context instead began
;; to rewrite in an equal context. Moving this defequiv form up here fixed the
;; issue.
(defequiv hifat-equiv
  :hints (("Goal" :in-theory (enable hifat-equiv)
           :do-not-induct t)))

(defthm
  hifat-equiv-of-cons-lemma-1
  (implies
   (and (m1-file-alist-p fs)
        (hifat-no-dups-p fs)
        (m1-regular-file-p (cdar fs)))
   (hifat-equiv
    (cons (cons (caar fs)
                (m1-file dir-ent (m1-file->contents (cdar fs))))
          (cdr fs))
    fs))
  :hints
  (("goal"
    :expand
    (hifat-equiv
     (cons
      (cons (caar fs)
            (m1-file dir-ent (m1-file->contents (cdar fs))))
      (cdr fs))
     fs)
    :in-theory (e/d (hifat-no-dups-p)
                    (hifat-subsetp-reflexive-lemma-4))
    :use
    ((:instance
      hifat-subsetp-reflexive-lemma-4
      (x
       (list
        (cons (car (car fs))
              (m1-file dir-ent
                       (m1-file->contents (cdr (car fs)))))))
      (y (cdr fs)))
     (:instance hifat-subsetp-reflexive-lemma-4
                (x (list (car fs)))
                (y (cdr fs)))))))

(defthm
  hifat-equiv-of-cons-lemma-2
  (implies (and (fat32-filename-p (car head))
                (m1-regular-file-p (cdr head))
                (equal contents (m1-file->contents (cdr head)))
                (m1-file-alist-p tail)
                (hifat-no-dups-p (cons head tail)))
           (hifat-equiv (cons (cons (car head)
                                    (m1-file dir-ent contents))
                              tail)
                        (cons head tail)))
  :hints
  (("goal"
    :in-theory
    (disable hifat-equiv-of-cons-lemma-1)
    :use (:instance hifat-equiv-of-cons-lemma-1
                    (fs (cons head tail))))))

;; (local
;;  (defthm
;;    hifat-equiv-of-cons-lemma-3
;;    (implies (and (m1-file-alist-p contents1)
;;                  (hifat-no-dups-p contents1)
;;                  (not (hifat-no-dups-p (m1-file-contents-fix contents2))))
;;             (not (hifat-equiv contents1 contents2)))
;;    :hints (("goal" :expand (hifat-equiv contents1 contents2)))))

;; (local
;;  (defthm
;;    hifat-equiv-of-cons-lemma-4
;;    (implies (and (m1-file-alist-p contents1)
;;                  (hifat-no-dups-p contents1)
;;                  (not (hifat-subsetp contents1
;;                                      (m1-file-contents-fix contents2))))
;;             (not (hifat-equiv contents1 contents2)))
;;    :hints (("goal" :expand (hifat-equiv contents1 contents2)))))

;; (local
;;  (defthm
;;    hifat-equiv-of-cons-lemma-5
;;    (implies
;;     (and (m1-file-alist-p contents1)
;;          (hifat-no-dups-p contents1)
;;          (not (hifat-subsetp (m1-file-contents-fix contents2)
;;                              contents1)))
;;     (not (hifat-equiv contents1 contents2)))
;;    :hints (("goal" :expand (hifat-equiv contents1 contents2)))))

;; (local
;;  (defthm
;;    hifat-equiv-of-cons-lemma-6
;;    (implies (and (m1-file-alist-p contents1)
;;                  (hifat-no-dups-p contents1)
;;                  (not (m1-file-alist-p contents2)))
;;             (not (hifat-equiv contents1 contents2)))
;;    :hints (("goal" :expand (hifat-equiv contents1 contents2)))))

(defthm
  hifat-equiv-of-cons-lemma-7
  (implies (and (m1-directory-file-p (cdr head))
                (m1-file-alist-p (cons head tail))
                (hifat-no-dups-p (cons head tail))
                (hifat-no-dups-p contents)
                (hifat-equiv (m1-file->contents (cdr head))
                             contents)
                (m1-file-alist-p contents))
           (hifat-equiv (cons (cons (car head)
                                    (m1-file dir-ent contents))
                              tail)
                        (cons head tail)))
  :hints
  (("goal"
    :expand
    ((hifat-equiv (cons (cons (car head)
                              (m1-file dir-ent contents))
                        tail)
                  (cons head tail))
     (hifat-equiv (m1-file->contents (cdr head))
                  contents))
    :in-theory (e/d (hifat-no-dups-p)
                    (hifat-subsetp-reflexive-lemma-4
                     m1-directory-file-p-of-m1-file))
    :use
    ((:instance hifat-subsetp-reflexive-lemma-4
                (x (list head))
                (y tail))
     (:instance hifat-subsetp-reflexive-lemma-4
                (x (list (cons (car head)
                               (m1-file dir-ent contents))))
                (y tail))
     (:instance m1-directory-file-p-of-m1-file
                (contents contents)
                (dir-ent dir-ent))))))

(defthm hifat-equiv-of-cons-lemma-8
  (implies (and (not (assoc-equal (car head) tail1))
                (hifat-subsetp tail2 tail1)
                (fat32-filename-p (car head)))
           (not (assoc-equal (car head) tail2))))

(defthm hifat-equiv-of-cons-lemma-9
  (implies (and (hifat-no-dups-p (cons head tail1))
                (hifat-subsetp tail2 tail1))
           (hifat-subsetp tail2 (cons head tail1)))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p)) ))

;; This rule had a problem earlier - no loop-stopper could be defined on it,
;; because it was an hifat-equiv rule, not an equal rule. Without a
;; loop-stopper, we were going round and round in a big induction proof. By
;; explicitly stipulating equality as the equivalence relation, we get around
;; this.
(defthm hifat-equiv-of-cons
  (implies (and (hifat-equiv tail1 tail2)
                (fat32-filename-p (car head))
                (hifat-no-dups-p tail2))
           (equal (hifat-equiv (cons head tail1)
                               (cons head tail2))
                  t))
  :hints (("goal" :in-theory (e/d (hifat-equiv hifat-no-dups-p)))))
