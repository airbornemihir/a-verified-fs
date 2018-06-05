(in-package "ACL2")

(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/io/read-ints" :dir :system)
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "rtl/rel9/arithmetic/top"
                     :dir :system))

(include-book "fat32")

;; This was moved to one of the main books, but still kept
(defthm unsigned-byte-listp-of-update-nth
  (implies (and (unsigned-byte-listp n l)
                (< key (len l)))
           (equal (unsigned-byte-listp n (update-nth key val l))
                  (unsigned-byte-p n val)))
  :hints (("goal" :in-theory (enable unsigned-byte-listp))))

;; This was taken from Alessandro Coglio's book at
;; books/kestrel/utilities/typed-list-theorems.lisp
(defthm unsigned-byte-listp-of-rev
  (equal (unsigned-byte-listp n (rev bytes))
         (unsigned-byte-listp n (list-fix bytes)))
  :hints (("goal" :in-theory (enable unsigned-byte-listp rev))))

(defthm nth-of-unsigned-byte-list
  (implies (and (unsigned-byte-listp bits l)
                (natp n)
                (< n (len l)))
           (unsigned-byte-p bits (nth n l))))

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

(defun dir-ent-first-cluster (dir-ent)
  (declare
   (xargs :guard (dir-ent-p dir-ent)))
  (combine32u (nth 21 dir-ent)
              (nth 20 dir-ent)
              (nth 27 dir-ent)
              (nth 26 dir-ent)))

(defun dir-ent-file-size (dir-ent)
  (declare
   (xargs :guard (dir-ent-p dir-ent)))
  (combine32u (nth 31 dir-ent)
              (nth 30 dir-ent)
              (nth 29 dir-ent)
              (nth 28 dir-ent)))

(defund dir-ent-directory-p (dir-ent)
  (declare
   (xargs :guard (dir-ent-p dir-ent)
          :guard-hints (("Goal" :in-theory (disable unsigned-byte-p)
                         :use (:instance unsigned-byte-p-logand
                                         (size 8)
                                         (i #x10)
                                         (j (nth 11 dir-ent)))) )))
  (not (zp (logand #x10 (nth 11 dir-ent)))))

(fty::defprod m1-file
  ((dir-ent dir-ent-p :default (dir-ent-fix nil))
   (contents any-p :default nil)))

(defund m1-regular-file-p (file)
  (declare (xargs :guard t))
  (and
   (m1-file-p file)
   (stringp (m1-file->contents file))))

(fty::defalist m1-file-alist
      :key-type string
      :val-type m1-file
      :true-listp t)

(defun m1-directory-file-p (file)
  (declare (xargs :guard t))
  (and
   (m1-file-p file)
   (m1-file-alist-p (m1-file->contents file))))

(fty::defprod
 struct-stat
 ;; Currently, this is the only thing I can decipher.
 ((st_size natp :default 0)))

;; This data structure may change later.
(fty::defalist fd-table
               :key-type nat
               :val-type m1-file
               :true-listp t)

(defthm lstat-guard-lemma-1
  (implies (and (m1-file-alist-p fs)
                (consp (assoc-equal filename fs)))
           (m1-file-p (cdr (assoc-equal filename fs)))))

(defthm lstat-guard-lemma-2
  (implies (m1-file-alist-p fs)
           (alistp fs)))

(defun find-file-by-pathname (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (string-listp pathname))
                  :guard-debug t
                  :measure (acl2-count pathname)))
  (let
      ((fs (m1-file-alist-fix fs)))
    (if (atom pathname)
        (mv (make-m1-file) *enoent*)
      (let
          ((alist-elem (assoc-equal (car pathname) fs)) )
        (if
            (atom alist-elem)
            (mv (make-m1-file) *enoent*)
          (if (not (m1-directory-file-p (cdr alist-elem)))
              (if (consp (cdr pathname))
                  (mv (make-m1-file) *enotdir*)
                (mv (cdr alist-elem) 0))
            (find-file-by-pathname
             (m1-file->contents (cdr alist-elem))
             (cdr pathname))))))))

(local
 (defun
   lstat-old (fs pathname)
   (declare (xargs :guard (and (m1-file-alist-p fs)
                               (string-listp pathname))
                   :measure (acl2-count pathname)))
   (let
    ((fs (m1-file-alist-fix fs)))
    (if
     (atom pathname)
     (mv (make-struct-stat) -1 *enoent*)
     (let
      ((alist-elem (assoc-equal (car pathname) fs)))
      (if
       (atom alist-elem)
       (mv (make-struct-stat) -1 *enoent*)
       (if
        (not (m1-directory-file-p (cdr alist-elem)))
        (if
         (consp (cdr pathname))
         (mv (make-struct-stat) -1 *enotdir*)
         (mv
          (make-struct-stat
           :st_size (dir-ent-file-size
                     (m1-file->dir-ent (cdr alist-elem))))
          0 0))
        (lstat-old (m1-file->contents (cdr alist-elem))
                   (cdr pathname)))))))))

(defun m1-lstat (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (string-listp pathname))))
  (mv-let
    (file errno)
    (find-file-by-pathname fs pathname)
    (if (not (equal errno 0))
        (mv (make-struct-stat) -1 errno)
      (mv
       (make-struct-stat
        :st_size (dir-ent-file-size
                  (m1-file->dir-ent file)))
       0 0))))

(local
 (defthm lstat-equivalence
   (equal (lstat-old fs pathname) (m1-lstat fs pathname))))

(defun
  find-new-fd-helper (fd-list ac)
  (declare (xargs :guard (and (nat-listp fd-list) (natp ac))
                  :measure (len fd-list)))
  (let ((snipped-list (remove ac fd-list)))
       (if (equal (len snipped-list) (len fd-list))
           ac
           (find-new-fd-helper snipped-list (+ ac 1)))))

(defthm find-new-fd-helper-correctness-1-lemma-1
  (>= (find-new-fd-helper fd-list ac) ac)
  :rule-classes :linear)

(encapsulate
  ()

  (local (include-book "std/lists/remove" :dir :system))
  (local (include-book "std/lists/duplicity" :dir :system))

  (defthm
    find-new-fd-helper-correctness-1
    (not (member-equal
          (find-new-fd-helper fd-list ac)
          fd-list))))

(defun
  find-new-fd (fd-list)
  (declare (xargs :guard (nat-listp fd-list)))
  (find-new-fd-helper fd-list 0))

(defthm m1-open-guard-lemma-1
  (implies (fd-table-p fd-table)
           (alistp fd-table)))

(defun m1-open (pathname fs fd-table)
   (declare (xargs :guard (and (m1-file-alist-p fs)
                               (string-listp pathname)
                               (fd-table-p fd-table))))
   (mv-let
     (file errno)
     (find-file-by-pathname fs pathname)
     (if (not (equal errno 0))
         (mv fd-table -1 errno)
       (mv
        (cons
         (cons
          (find-new-fd (strip-cars fd-table)) file)
         fd-table)
        0 0))))
