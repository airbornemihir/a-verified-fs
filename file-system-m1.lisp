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

(defthm
  m1-regular-file-p-correctness-1
  (implies (m1-regular-file-p file)
           (stringp (m1-file->contents file)))
  :hints (("goal" :in-theory (enable m1-regular-file-p))))

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

;; Not happy at having to include this, but at least I got it from :doc
;; fty::deflist.
;; (deflist string-list :pred string-listp :elt-type stringp)

;; This data structure may change later.
(fty::defprod
 file-table-element
 ((pos natp) ;; index within the file
  ;; mode ?
  (fid string-listp) ;; pathname of the file
  ))

(fty::defalist
 file-table
 :key-type nat
 :val-type file-table-element
 :true-listp t)

;; This data structure may change later.
(fty::defalist fd-table
               :key-type nat ;; index into the fd-table
               :val-type nat ;; index into the file-table
               :true-listp t)

(defthm lstat-guard-lemma-1
  (implies (and (m1-file-alist-p fs)
                (consp (assoc-equal filename fs)))
           (m1-file-p (cdr (assoc-equal filename fs)))))

(defthm lstat-guard-lemma-2
  (implies (m1-file-alist-p fs)
           (alistp fs)))

(defun
    find-file-by-pathname (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (string-listp pathname))
                  :measure (acl2-count pathname)))
  (b*
      ((fs (m1-file-alist-fix fs))
       ((unless (consp pathname))
        (mv (make-m1-file) *enoent*))
       (alist-elem (assoc-equal (car pathname) fs))
       ((unless (consp alist-elem))
        (mv (make-m1-file) *enoent*))
       ((when (m1-directory-file-p (cdr alist-elem)))
        (find-file-by-pathname (m1-file->contents (cdr alist-elem))
                               (cdr pathname)))
       ((unless (atom (cdr pathname)))
        (mv (make-m1-file) *enotdir*)))
      (mv (cdr alist-elem) 0)))

(defthm find-file-by-pathname-correctness-1
  (mv-let (file error-code)
    (find-file-by-pathname fs pathname)
    (and (m1-file-p file)
         (integerp error-code)))
  :hints (("Goal" :induct (find-file-by-pathname fs pathname)) ))

(defun place-file-by-pathname
  (fs pathname file)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (string-listp pathname)
                              (m1-file-p file))
                  :measure (acl2-count pathname)))
  (b* ((fs (m1-file-alist-fix fs))
       (file (m1-file-fix file))
       ((unless (consp pathname))
        (mv fs *enoent*))
       (name (str-fix (car pathname)))
       (alist-elem (assoc-equal name fs))
       ((when (consp alist-elem))
        (if (m1-directory-file-p (cdr alist-elem))
            (place-file-by-pathname
             (m1-file->contents (cdr alist-elem))
             (cdr pathname)
             file)
            (mv fs *enoent*)))
       ((unless (atom (cdr pathname)))
        (mv fs *enotdir*)))
    (mv (put-assoc-equal name file fs)
        0)))

(defthm
  place-file-by-pathname-correctness-1-lemma-1
  (implies
   (m1-file-alist-p alist)
   (equal (m1-file-alist-p (put-assoc-equal name val alist))
          (and (stringp name) (m1-file-p val)))))

(defthm
  place-file-by-pathname-correctness-1
  (mv-let (fs error-code)
    (place-file-by-pathname fs pathname file)
    (and (m1-file-alist-p fs)
         (integerp error-code)))
  :hints
  (("goal" :induct (place-file-by-pathname fs pathname file))))


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
  find-new-index-helper (fd-list ac)
  (declare (xargs :guard (and (nat-listp fd-list) (natp ac))
                  :measure (len fd-list)))
  (let ((snipped-list (remove ac fd-list)))
       (if (equal (len snipped-list) (len fd-list))
           ac
           (find-new-index-helper snipped-list (+ ac 1)))))

(defthm find-new-index-helper-correctness-1-lemma-1
  (>= (find-new-index-helper fd-list ac) ac)
  :rule-classes :linear)

(encapsulate
  ()

  (local (include-book "std/lists/remove" :dir :system))
  (local (include-book "std/lists/duplicity" :dir :system))

  (defthm
    find-new-index-helper-correctness-1
    (not (member-equal
          (find-new-index-helper fd-list ac)
          fd-list))))

(defun
  find-new-index (fd-list)
  (declare (xargs :guard (nat-listp fd-list)))
  (find-new-index-helper fd-list 0))

(defthm m1-open-guard-lemma-1
  (implies (fd-table-p fd-table)
           (alistp fd-table)))

;; (defthm m1-open-guard-lemma-2
;;   (implies (and (fd-table-p fd-table)
;;                 (consp (assoc-equal fd fd-table)))
;;            (m1-file-p (cdr (assoc-equal fd fd-table)))))

(defun m1-open (pathname fs fd-table file-table)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (string-listp pathname)
                              (fd-table-p fd-table)
                              (file-table-p file-table))))
  (b*
      (((mv & errno)
        (find-file-by-pathname fs pathname))
       ((unless (equal errno 0))
        (mv fd-table file-table -1 errno))
       (file-table-index
        (find-new-index (strip-cars file-table)))
       (fd-table-index
        (find-new-index (strip-cars fd-table))))
    (mv
     (cons
      (cons file-table-index (make-file-table-element :pos 0 :fid pathname))
      file-table)
     (cons
      (cons fd-table-index file-table-index)
      fd-table)
     0 0)))

(defthm
  m1-pread-guard-lemma-1
  (implies
   (and (file-table-p file-table)
        (consp (assoc-equal x file-table)))
   (file-table-element-p (cdr (assoc-equal x file-table)))))

(defun
    m1-pread (fd count offset fs fd-table file-table)
  (declare (xargs :guard (and (natp fd)
                              (natp count)
                              (natp offset)
                              (fd-table-p fd-table)
                              (file-table-p file-table)
                              (m1-file-alist-p fs))
                  :guard-debug t))
  (b*
      ((fs (m1-file-alist-fix fs))
       (fd-table-entry (assoc-equal fd fd-table))
       ((unless (consp fd-table-entry)) (mv "" file-table -1 *ebadf*))
       (file-table-entry (assoc-equal (cdr fd-table-entry) file-table))
       ((unless (consp file-table-entry)) (mv "" file-table -1 *ebadf*))
       (pathname (file-table-element->fid (cdr file-table-entry)))
       ((mv file error-code)
        (find-file-by-pathname fs pathname))
       ((unless (and (equal error-code 0) (m1-regular-file-p file)))
        (mv "" file-table -1 error-code))
       (new-offset
        (min (+ offset count)
             (length (m1-file->contents file)))))
    (mv
     (subseq
      (m1-file->contents file)
      (min offset
           (length (m1-file->contents file)))
      new-offset)
     (put-assoc
      (car file-table-entry)
      (make-file-table-element :pos new-offset :fid pathname)
      file-table)
     0 0)))
