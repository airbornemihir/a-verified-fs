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
  ((dir-ent dir-ent-p)
   (contents any-p)))

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

(defthm lstat-guard-lemma-1
  (implies (and (m1-file-alist-p fs)
                (consp (assoc-equal filename fs)))
           (m1-file-p (cdr (assoc-equal filename fs)))))

(defthm lstat-guard-lemma-2
  (implies (m1-file-alist-p fs)
           (alistp fs)))

(defun
  lstat (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (string-listp pathname))
                  :measure (acl2-count pathname)))
  (let
      ((fs (m1-file-alist-fix fs)))
    (if (atom pathname)
        (mv (make-struct-stat) -1 *enoent*)
      (let
          ((alist-elem (assoc-equal (car pathname) fs)) )
        (if
            (atom alist-elem)
            (mv (make-struct-stat) -1 *enoent*)
          (if (not (m1-directory-file-p (cdr alist-elem)))
              (if (consp (cdr pathname))
                  (mv (make-struct-stat) -1 *enotdir*)
                (mv
                 (make-struct-stat
                  :st_size
                  (dir-ent-file-size
                   (m1-file->dir-ent (cdr alist-elem))))
                 0 0))
            (lstat (m1-file->contents (cdr alist-elem)) (cdr pathname))))))))
