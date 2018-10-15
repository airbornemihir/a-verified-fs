(in-package "ACL2")

(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(defconst *ms-dir-ent-length* 32)

(defun dir-ent-p (x)
  (declare (xargs :guard t))
  (and (unsigned-byte-listp 8 x)
       (equal (len x) *ms-dir-ent-length*)))

(defun dir-ent-fix (x)
  (declare (xargs :guard t))
  (if
      (dir-ent-p x)
      x
    (make-list *ms-dir-ent-length* :initial-element 0)))

(fty::deffixtype
 dir-ent
 :pred dir-ent-p
 :fix dir-ent-fix
 :equiv dir-ent-equiv
 :define t
 :forward t)

(fty::defprod m1-file
              ((dir-ent dir-ent-p :default (dir-ent-fix nil))
               (contents any-p :default nil)))

(fty::defalist m1-file-alist
      :key-type string
      :val-type m1-file
      :true-listp t)

(defund m1-directory-file-p (file)
  (declare (xargs :guard t))
  (and
   (m1-file-p file)
   (m1-file-alist-p (m1-file->contents file))))

(defthm m1-directory-file-p-correctness-1
  (implies (m1-directory-file-p file)
           (m1-file-alist-p (m1-file->contents file)))
  :hints (("Goal" :in-theory (enable m1-directory-file-p))))

(defthm lstat-guard-lemma-1
  (implies (and (m1-file-alist-p fs)
                (consp (assoc-equal filename fs)))
           (m1-file-p (cdr (assoc-equal filename fs)))))

(defun m1-dir-subsetp (m1-file-alist1 m1-file-alist2)
  (declare
   (xargs
    :guard (and (m1-file-alist-p m1-file-alist1)
                (m1-file-alist-p m1-file-alist2))
    :hints (("goal" :in-theory (enable m1-file->contents)))))
  (b* (((when (atom m1-file-alist1))
        t)
       ((when (or (atom (car m1-file-alist1))
                  (not (stringp (car (car m1-file-alist1))))))
        (and (member-equal (car m1-file-alist1)
                           m1-file-alist2)
             (m1-dir-subsetp
              (cdr m1-file-alist1)
              m1-file-alist2)))
       (name (caar m1-file-alist1))
       (file1 (cdar m1-file-alist1))
       ((unless (consp (assoc-equal name m1-file-alist2)))
        nil)
       (file2 (cdr (assoc-equal name m1-file-alist2))))
    (if (not (m1-directory-file-p file1))
        (and (not (m1-directory-file-p file2))
             (m1-dir-subsetp (cdr m1-file-alist1) m1-file-alist2)
             (equal (m1-file->contents file1)
                    (m1-file->contents file2)))
      (and (m1-directory-file-p file2)
           (m1-dir-subsetp (cdr m1-file-alist1) m1-file-alist2)
           (m1-dir-subsetp (m1-file->contents file1)
                           (m1-file->contents file2))))))

(defun m1-file-no-dups-p (m1-file-alist)
  (declare
   (xargs
    :guard (m1-file-alist-p m1-file-alist)
    :hints (("goal" :in-theory (enable m1-file->contents)))))
  (cond ((atom m1-file-alist)
         t)
        ((not (m1-file-no-dups-p (cdr m1-file-alist)))
         nil)
        ((or (atom (car m1-file-alist))
             (not (stringp (car (car m1-file-alist)))))
         (not (member-equal (car m1-file-alist)
                            (cdr m1-file-alist))))
        ((assoc-equal (caar m1-file-alist) (cdr m1-file-alist))
         nil)
        ((m1-directory-file-p (cdar m1-file-alist))
         (m1-file-no-dups-p (m1-file->contents (cdar m1-file-alist))))
        (t t)))

(defun m1-dir-equiv (m1-file-alist1 m1-file-alist2)
  (declare (xargs :guard t))
  (or (equal m1-file-alist1 m1-file-alist2)
      (let ((good1 (and (m1-file-alist-p m1-file-alist1)
                        (m1-file-no-dups-p m1-file-alist1)))
            (good2 (and (m1-file-alist-p m1-file-alist2)
                        (m1-file-no-dups-p m1-file-alist2))))
        (cond ((not good1) (not good2)) ; all bad objects are equivalent
              ((not good2) nil) ; one good, one bad; hence, not equivalent
              (t                ; both good
               (and (m1-dir-subsetp m1-file-alist1 m1-file-alist2)
                    (m1-dir-subsetp m1-file-alist2 m1-file-alist1)))))))

(defthm m1-dir-subsetp-preserves-assoc-equal
  (implies (and (m1-dir-subsetp x y)
                (stringp file)
                (consp (assoc-equal file x)))
           (consp (assoc-equal file y))))

(defthm
  m1-dir-subsetp-transitive-lemma-1
  (implies
   (and (m1-file-alist-p y)
        (consp (assoc-equal key y))
        (m1-dir-subsetp y z))
   (iff (m1-directory-file-p (cdr (assoc-equal key z)))
        (m1-directory-file-p (cdr (assoc-equal key y)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (m1-file-alist-p y)
          (consp (assoc-equal key y))
          (m1-dir-subsetp y z)
          (m1-directory-file-p (cdr (assoc-equal key y))))
     (m1-directory-file-p (cdr (assoc-equal key z)))))))

(defthm
  m1-dir-subsetp-transitive-lemma-2
  (implies (and (m1-file-alist-p z)
                (m1-file-no-dups-p z)
                (consp (assoc-equal key z))
                (m1-directory-file-p (cdr (assoc-equal key z))))
           (m1-file-no-dups-p
            (m1-file->contents (cdr (assoc-equal key z))))))

(defthm
  m1-dir-subsetp-transitive-lemma-3
  (implies (and (m1-file-alist-p y)
                (consp (assoc-equal key y))
                (m1-directory-file-p (cdr (assoc-equal key y)))
                (m1-dir-subsetp y z))
           (m1-dir-subsetp
            (m1-file->contents (cdr (assoc-equal key y)))
            (m1-file->contents (cdr (assoc-equal key z))))))

(defthm
  m1-dir-subsetp-transitive-lemma-4
  (implies
   (and (m1-file-alist-p y)
        (consp (assoc-equal key y))
        (not (m1-directory-file-p (cdr (assoc-equal key y))))
        (m1-dir-subsetp y z))
   (equal (m1-file->contents (cdr (assoc-equal key y)))
          (m1-file->contents (cdr (assoc-equal key z))))))

(defthm
  m1-dir-subsetp-transitive
  (implies (and (m1-file-alist-p x)
                (m1-file-no-dups-p x)
                (m1-file-alist-p y)
                (m1-file-no-dups-p y)
                (m1-file-alist-p z)
                (m1-file-no-dups-p z)
                (m1-dir-subsetp x y)
                (m1-dir-subsetp y z))
           (m1-dir-subsetp x z))
  :hints
  (("subgoal *1/6'''"
    :in-theory (disable m1-dir-subsetp-transitive-lemma-1)
    :use (:instance m1-dir-subsetp-transitive-lemma-1
                    (key (car (car x)))))))

(defequiv
  m1-dir-equiv)
