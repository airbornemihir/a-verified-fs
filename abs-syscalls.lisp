;  abs-syscalls.lisp                                    Mihir Mehta

; This is a model of the FAT32 filesystem, related to HiFAT but with abstract
; variables.

(in-package "ACL2")

(include-book "abs-find-file")
(include-book "hifat-syscalls")
(local (include-book "std/lists/prefixp" :dir :system))

(local (in-theory (e/d (abs-file-p-when-m1-regular-file-p)
                       nil)))

;; Let's try to do this intuitively first...

(defund
  abs-place-file (frame pathname file)
  (declare
   (xargs :guard (and (frame-p frame)
                      (fat32-filename-list-p pathname))
          :guard-debug t
          :guard-hints (("Goal" :do-not-induct t) )
          :verify-guards nil))
  (b*
      (((when (atom frame))
        (mv frame *enoent*))
       (pathname (mbe :exec pathname
                      :logic (fat32-filename-list-fix pathname)))
       ((mv tail tail-error-code)
        (abs-place-file (cdr frame) pathname file))
       ((unless (and (equal tail-error-code *ENOENT*)
                     (prefixp (frame-val->path (cdar frame))
                              pathname)))
        (mv (list* (car frame) tail) tail-error-code))
       ;; Look up the parent directory - it has to be in one of the variables,
       ;; or else we must return ENOENT.
       ((mv & error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 (butlast 1 pathname))))
       ((when (or (equal error-code *enoent*)
                  (not (abs-complete (frame-val->dir (cdar frame))))))
        (mv (list* (car frame) tail) tail-error-code))
       ((mv head head-error-code)
        (hifat-place-file (frame-val->dir (cdar frame)) pathname file)))
    (mv
     (list* (cons (caar frame) (change-frame-val (cdar frame) :dir head))
            (cdr frame))
     head-error-code)))

;; Move later.
(defthm intersectp-of-cons-2
  (iff (intersectp-equal x1 (cons x2 y))
       (or (member-equal x2 x1)
           (intersectp-equal y x1)))
  :hints (("goal" :in-theory (e/d (intersectp-equal)
                                  (intersectp-is-commutative))
           :expand (:with intersectp-is-commutative
                          (intersectp-equal x1 (cons x2 y))))))

(defund
  pathname-clear (pathname frame)
  (declare (xargs :guard (and (fat32-filename-list-p pathname)
                              (frame-p frame))
                  :guard-debug t))
  (b*
      (((when (atom frame)) t)
       ((unless
            (pathname-clear pathname (cdr frame)))
        nil)
       (pathname (mbe :exec pathname :logic (fat32-filename-list-fix
                                             pathname))))
    (and
     (or
      (not (prefixp
            pathname
            (frame-val->path (cdar frame))))
      (equal
       (frame-val->path (cdar frame))
       pathname))
     (or
      (not (prefixp
            (frame-val->path (cdar frame))
            pathname))
      (atom
       (names-at (frame-val->dir (cdar frame))
                 (nthcdr
                  (len (frame-val->path (cdar frame)))
                  pathname)))))))

(defthm
  dist-names-when-pathname-clear
  (implies (pathname-clear pathname frame)
           (dist-names dir pathname frame))
  :hints (("goal" :in-theory (enable dist-names
                                     pathname-clear prefixp intersectp-equal)
           :induct (pathname-clear pathname frame)
           :expand (dist-names dir pathname frame))))

(defthm
  absfat-place-file-correctness-lemma-1
  (implies (and (consp (assoc-equal x frame))
                (abs-complete (frame-val->dir (cdr (assoc-equal x frame))))
                (abs-complete (frame-val->dir val)))
           (equal (1st-complete (put-assoc-equal x val frame))
                  (1st-complete frame)))
  :hints (("goal" :in-theory (enable 1st-complete))))

(defthm
  hifat-subsetp-of-put-assoc-1
  (implies
   (and (m1-file-alist-p x)
        (hifat-no-dups-p x)
        (stringp name))
   (equal
    (hifat-subsetp (put-assoc-equal name val x)
                   y)
    (and
     (hifat-subsetp (remove-assoc-equal name x)
                    y)
     (consp (assoc-equal name y))
     (or
      (and (not (m1-directory-file-p (cdr (assoc-equal name y))))
           (not (m1-directory-file-p val))
           (equal (m1-file->contents val)
                  (m1-file->contents (cdr (assoc-equal name y)))))
      (and (m1-directory-file-p (cdr (assoc-equal name y)))
           (m1-directory-file-p val)
           (hifat-subsetp (m1-file->contents val)
                          (m1-file->contents (cdr (assoc-equal name y)))))))))
  :hints (("goal" :in-theory (enable hifat-subsetp)
           :induct (mv (put-assoc-equal name val x)
                       (remove-assoc-equal name x)))))

(defthm hifat-subsetp-of-put-assoc-2
  (implies (and (m1-file-alist-p x)
                (hifat-subsetp x (remove-assoc-equal name y)))
           (hifat-subsetp x (put-assoc-equal name val y)))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm hifat-subsetp-of-remove-assoc-1
  (implies (and (m1-file-alist-p x)
                (atom (assoc-equal name x))
                (hifat-subsetp x y))
           (hifat-subsetp x (remove-assoc-equal name y)))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm hifat-subsetp-of-remove-assoc-2
  (implies (hifat-subsetp x y)
           (hifat-subsetp (remove-assoc-equal name x)
                          y))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm
  hifat-place-file-correctness-lemma-1
  (implies (and (m1-file-alist-p x)
                (m1-file-alist-p y)
                (hifat-no-dups-p x)
                (hifat-no-dups-p y)
                (hifat-subsetp x y)
                (hifat-subsetp y x)
                (or (hifat-no-dups-p (m1-file->contents file))
                    (m1-regular-file-p file)))
           (and
            (hifat-subsetp (mv-nth 0 (hifat-place-file y pathname file))
                           (mv-nth 0 (hifat-place-file x pathname file)))
            (equal (mv-nth 1 (hifat-place-file y pathname file))
                   (mv-nth 1 (hifat-place-file x pathname file)))))
  :hints (("goal" :in-theory (enable hifat-place-file hifat-subsetp))))

;; This isn't a congruence rule, so it may have to be left disabled...
(defthm
  hifat-place-file-correctness-4
  (implies
   (and (hifat-equiv m1-file-alist2 m1-file-alist1)
        (or (hifat-no-dups-p (m1-file->contents file))
            (m1-regular-file-p file)))
   (and
    (equal (mv-nth 1
                   (hifat-place-file m1-file-alist2 pathname file))
           (mv-nth 1
                   (hifat-place-file m1-file-alist1 pathname file)))
    (hifat-equiv (mv-nth 0
                         (hifat-place-file m1-file-alist2 pathname file))
                 (mv-nth 0
                         (hifat-place-file m1-file-alist1 pathname file)))))
  :hints
  (("goal" :in-theory (enable hifat-place-file hifat-equiv)
    :use ((:instance (:rewrite hifat-place-file-correctness-lemma-1)
                     (x (hifat-file-alist-fix m1-file-alist2))
                     (file file)
                     (pathname pathname)
                     (y (hifat-file-alist-fix m1-file-alist1)))
          (:instance (:rewrite hifat-place-file-correctness-lemma-1)
                     (x (hifat-file-alist-fix m1-file-alist1))
                     (file file)
                     (pathname pathname)
                     (y (hifat-file-alist-fix m1-file-alist2))))
    :do-not-induct t)))

;; Probably tricky to get a refinement relationship (in the defrefinement
;; sense) between literally absfat-equiv and hifat-equiv. But we can still have
;; some kind of substitute...
(encapsulate
  ()

  (local
   (defthmd lemma
     (implies (and (m1-file-alist-p abs-file-alist1)
                   (m1-file-alist-p abs-file-alist2)
                   (hifat-no-dups-p abs-file-alist1)
                   (hifat-no-dups-p abs-file-alist2))
              (equal (absfat-equiv abs-file-alist1 abs-file-alist2)
                     (hifat-equiv abs-file-alist1 abs-file-alist2)))
     :hints (("goal" :in-theory (enable absfat-equiv hifat-equiv abs-fs-p
                                        absfat-subsetp-correctness-1)))))

  (defthm
    hifat-equiv-when-absfat-equiv
    (implies (and (m1-file-alist-p (abs-fs-fix abs-file-alist1))
                  (m1-file-alist-p (abs-fs-fix abs-file-alist2)))
             (equal (absfat-equiv abs-file-alist1 abs-file-alist2)
                    (hifat-equiv (abs-fs-fix abs-file-alist1)
                                 (abs-fs-fix abs-file-alist2))))
    :hints
    (("goal" :use (:instance lemma
                             (abs-file-alist1 (abs-fs-fix abs-file-alist1))
                             (abs-file-alist2 (abs-fs-fix abs-file-alist2)))))))

(defthm abs-fs-p-when-hifat-no-dups-p
  (implies (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs))
           (abs-fs-p fs))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-fs-p))))

;; Move later.
(defthm
  hifat-place-file-correctness-5
  (implies (hifat-no-dups-p (m1-file->contents file))
           (hifat-no-dups-p (mv-nth 0 (hifat-place-file fs pathname file))))
  :hints
  (("goal"
    :in-theory (enable hifat-place-file)
    :induct (hifat-place-file fs pathname file)
    :expand
    (:with
     (:rewrite hifat-no-dups-p-of-put-assoc-equal-2)
     (hifat-no-dups-p
      (put-assoc-equal
       (fat32-filename-fix (car pathname))
       (m1-file
        (m1-file->dir-ent
         (cdr (assoc-equal (fat32-filename-fix (car pathname))
                           (hifat-file-alist-fix fs))))
        (mv-nth
         0
         (hifat-place-file
          (m1-file->contents
           (cdr (assoc-equal (fat32-filename-fix (car pathname))
                             (hifat-file-alist-fix fs))))
          (cdr pathname)
          file)))
       (hifat-file-alist-fix fs)))))))

(defthm
  absfat-place-file-correctness-lemma-3
  (implies
   (and
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (abs-fs-p dir)
    (not (consp (abs-addrs dir)))
    (pathname-clear nil frame)
    (not (consp (names-at root nil)))
    (abs-fs-p root)
    (not (zp x))
    (not (consp (assoc-equal 0 frame)))
    (frame-p frame)
    (not (consp (assoc-equal x frame)))
    (no-duplicatesp-equal (strip-cars frame))
    (subsetp-equal
     (abs-addrs root)
     (frame-addrs-root
      (cons (cons x
                  (frame-val nil
                             (put-assoc-equal (car (last pathname))
                                              file dir)
                             src))
            frame)))
    (mv-nth 1
            (collapse (frame-with-root root
                                       (cons (cons x (frame-val nil dir src))
                                             frame))))
    (absfat-equiv
     (mv-nth 0
             (collapse (frame-with-root root
                                        (cons (cons x (frame-val nil dir src))
                                              frame))))
     fs)
    (no-duplicatesp-equal (abs-addrs root))
    (not (intersectp-equal nil (names-at dir nil)))
    (abs-separate frame))
   (hifat-equiv
    fs
    (mv-nth 0
            (collapse (frame-with-root root
                                       (cons (cons x (frame-val nil dir src))
                                             frame))))))
  :hints (("goal" :in-theory (enable abs-separate
                                     dist-names hifat-equiv-when-absfat-equiv
                                     frame-addrs-root))))

(defthm
  absfat-place-file-correctness-lemma-4
  (implies
   (subsetp-equal
    (abs-addrs root)
    (frame-addrs-root
     (cons (cons x
                 (frame-val nil
                            (put-assoc-equal (car (last pathname))
                                             file dir)
                            src))
           frame)))
   (subsetp-equal (abs-addrs root)
                  (frame-addrs-root (cons (cons x (frame-val 'nil dir src))
                                          frame))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (hifat-equiv-when-absfat-equiv dist-names
                                        abs-separate frame-addrs-root)
         nil)))
  :otf-flg t)

(defthm
  absfat-place-file-correctness-lemma-5
  (implies
   (and
    (hifat-equiv
     (mv-nth
      0
      (collapse
       (frame-with-root
        root
        (cons (cons x
                    (frame-val nil
                               (put-assoc-equal (car (last pathname))
                                                file dir)
                               src))
              frame))))
     (mv-nth
      0
      (hifat-place-file
       fs nil
       (m1-file
        (m1-file->dir-ent
         (mv-nth
          0
          (hifat-find-file
           (mv-nth
            0
            (collapse (frame-with-root root
                                       (cons (cons x (frame-val nil dir src))
                                             frame))))
           nil)))
        (put-assoc-equal (car (last pathname))
                         file dir)))))
    (equal (mv-nth 1
                   (hifat-place-file fs nil
                                     (put-assoc-equal (car (last pathname))
                                                      file dir)))
           0))
   (hifat-equiv
    (mv-nth
     0
     (collapse
      (frame-with-root
       root
       (cons (cons x
                   (frame-val nil
                              (put-assoc-equal (car (last pathname))
                                               file dir)
                              src))
             frame))))
    (mv-nth 0 (hifat-place-file fs pathname file))))
  :instructions
  (:promote
   (:=
    (mv-nth
     0
     (collapse
      (frame-with-root
       root
       (cons (cons x
                   (frame-val nil
                              (put-assoc-equal (car (last pathname))
                                               file dir)
                              src))
             frame))))
    (mv-nth
     0
     (hifat-place-file
      fs nil
      (m1-file
       (m1-file->dir-ent
        (mv-nth
         0
         (hifat-find-file
          (mv-nth
           0
           (collapse (frame-with-root root
                                      (cons (cons x (frame-val nil dir src))
                                            frame))))
          nil)))
       (put-assoc-equal (car (last pathname))
                        file dir))))
    :equiv hifat-equiv)
   (:bash ("goal" :in-theory (enable hifat-place-file)))))

(defthm
  absfat-place-file-correctness-lemma-6
  (implies
   (and
    (mv-nth
     1
     (collapse
      (frame-with-root
       root
       (cons (cons x
                   (frame-val nil
                              (put-assoc-equal (car (last pathname))
                                               file dir)
                              src))
             frame))))
    (absfat-equiv
     (mv-nth
      0
      (collapse
       (frame-with-root
        root
        (cons (cons x
                    (frame-val nil
                               (put-assoc-equal (car (last pathname))
                                                file dir)
                               src))
              frame))))
     (mv-nth
      0
      (hifat-place-file
       (mv-nth
        0
        (collapse (frame-with-root root
                                   (cons (cons x (frame-val nil dir src))
                                         frame))))
       nil
       (m1-file
        (m1-file->dir-ent
         (mv-nth
          0
          (hifat-find-file
           (mv-nth
            0
            (collapse (frame-with-root root
                                       (cons (cons x (frame-val nil dir src))
                                             frame))))
           nil)))
        (put-assoc-equal (car (last pathname))
                         file dir)))))
    (equal
     (mv-nth
      1
      (hifat-place-file
       (mv-nth
        0
        (collapse (frame-with-root root
                                   (cons (cons x (frame-val nil dir src))
                                         frame))))
       nil
       (put-assoc-equal (car (last pathname))
                        file dir)))
     0)
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (fat32-filename-list-p pathname)
    (m1-regular-file-p file)
    (abs-fs-p dir)
    (not (consp (abs-addrs dir)))
    (pathname-clear nil frame)
    (not (consp (names-at root nil)))
    (abs-fs-p root)
    (not (zp x))
    (not (consp (assoc-equal 0 frame)))
    (frame-p frame)
    (not (consp (assoc-equal x frame)))
    (no-duplicatesp-equal (strip-cars frame))
    (subsetp-equal
     (abs-addrs root)
     (frame-addrs-root
      (cons (cons x
                  (frame-val nil
                             (put-assoc-equal (car (last pathname))
                                              file dir)
                             src))
            frame)))
    (mv-nth 1
            (collapse (frame-with-root root
                                       (cons (cons x (frame-val nil dir src))
                                             frame))))
    (absfat-equiv
     (mv-nth 0
             (collapse (frame-with-root root
                                        (cons (cons x (frame-val nil dir src))
                                              frame))))
     fs)
    (no-duplicatesp-equal (abs-addrs root))
    (not (intersectp-equal nil (names-at dir nil)))
    (abs-separate frame)
    (consp pathname))
   (absfat-equiv
    (mv-nth
     0
     (collapse
      (frame-with-root
       root
       (cons (cons x
                   (frame-val nil
                              (put-assoc-equal (car (last pathname))
                                               file dir)
                              src))
             frame))))
    (mv-nth 0 (hifat-place-file fs pathname file))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (hifat-equiv-when-absfat-equiv dist-names abs-separate)
                    nil))
   ("subgoal 1.2" :in-theory (enable names-at)))
  :otf-flg t)

(defthm
  abs-addrs-when-absfat-equiv
  (implies (absfat-equiv x y)
           (set-equiv (abs-addrs (abs-fs-fix x))
                      (abs-addrs (abs-fs-fix y))))
  :hints (("goal" :in-theory (e/d (absfat-equiv set-equiv abs-fs-p)
                                  (absfat-equiv-of-ctx-app-lemma-4))
           :use ((:instance absfat-equiv-of-ctx-app-lemma-4
                            (abs-file-alist1 (abs-fs-fix x))
                            (abs-file-alist2 (abs-fs-fix y)))
                 (:instance absfat-equiv-of-ctx-app-lemma-4
                            (abs-file-alist2 (abs-fs-fix x))
                            (abs-file-alist1 (abs-fs-fix y))))))
  :rule-classes :congruence)

(encapsulate
  ()

  (local (defun foo-equiv (fs1 fs2)
           (b* ((good1 (and (m1-file-alist-p fs1) (hifat-no-dups-p fs1)))
                (good2 (and (m1-file-alist-p fs2) (hifat-no-dups-p fs2))))
             (or (not (or good1 good2))
                 (and good1 good2
                      (hifat-subsetp fs1 fs2)
                      (hifat-subsetp fs2 fs1))))))

  (local (defequiv foo-equiv))

  (local (defun bar-equiv (fs1 fs2)
           (b* ((good1 (abs-fs-p fs1))
                (good2 (abs-fs-p fs2)))
             (or (not (or good1 good2))
                 (and good1 good2
                      (absfat-subsetp fs1 fs2)
                      (absfat-subsetp fs2 fs1))))))

  (local (defequiv bar-equiv))

  (thm (implies (and
                 (abs-file-alist-p x)
                 (abs-file-alist-p y)
                 (absfat-subsetp x y))
                (subsetp-equal (abs-addrs x) (abs-addrs y)))
       :hints (("goal" :in-theory (enable abs-addrs absfat-subsetp))))

  (local
   (defrefinement bar-equiv foo-equiv
     :hints
     (("goal"
       :in-theory (e/d (absfat-subsetp-correctness-1 abs-fs-p
                                                     absfat-equiv)
                       (abs-addrs-when-m1-file-alist-p abs-addrs-when-absfat-equiv))
       :use
       (abs-addrs-when-m1-file-alist-p
        (:instance
         abs-addrs-when-m1-file-alist-p (x y))
        abs-addrs-when-absfat-equiv))))))

(defthm absfat-place-file-correctness-lemma-7
  (implies (and (abs-fs-p dir)
                (not (member-equal (car (last pathname))
                                   (names-at dir nil))))
           (not (consp (assoc-equal (car (last pathname))
                                    dir))))
  :hints (("goal" :in-theory (enable names-at))))

;; I'm not even sure what the definition of abs-place-file above should be. But
;; I'm pretty sure it should support a theorem like the following.
;;
;; In the hypotheses here, there has to be a stipulation that not only is dir
;; complete, but also that it's the only one which has any names at that
;; particular relpath, i.e. (butlast 1 pathname). It's going to be a natural
;; outcome of partial-collapse, but it may have to be codified somehow.
(thm
 (implies
  (and
   ;; guard of hifat-place-file.
   (m1-file-alist-p fs)
   (hifat-no-dups-p fs)
   (fat32-filename-list-p pathname)
   (m1-regular-file-p file)
   (abs-fs-p dir)
   (abs-complete dir)
   (pathname-clear (butlast 1 pathname) frame)
   (atom (names-at root (butlast 1 pathname)))
   (abs-fs-p root)
   (not (zp x))
   (atom (assoc-equal 0 frame))
   (frame-p frame)
   (not (consp (assoc-equal x frame)))
   (no-duplicatesp-equal (strip-cars frame))
   (subsetp-equal
    (abs-addrs root)
    (frame-addrs-root
     (cons (cons x
                 (frame-val nil
                            (put-assoc-equal (car (last pathname))
                                             file dir)
                            src))
           frame)))
   (mv-nth 1 (collapse (frame-with-root
                        root
                        (cons
                         (cons
                          x
                          (frame-val
                           (butlast 1 pathname)
                           dir
                           src))
                         frame))))
   (absfat-equiv (mv-nth 0 (collapse (frame-with-root
                                      root
                                      (cons
                                       (cons
                                        x
                                        (frame-val
                                         (butlast 1 pathname)
                                         dir
                                         src))
                                       frame))))
                 fs)
   (abs-separate (frame-with-root
                  root
                  (cons
                   (cons
                    x
                    (frame-val
                     (butlast 1 pathname)
                     dir
                     src))
                   frame)))
   (not (member-equal (car (last pathname)) (names-at dir nil)))
   (consp pathname))
  (b*
      ((dir (put-assoc-equal (car (last pathname)) file dir))
       (frame (frame-with-root
               root
               (cons
                (cons
                 x
                 (frame-val
                  (butlast 1 pathname)
                  dir
                  src))
                frame)))
       ((mv fs error-code) (hifat-place-file fs pathname file)))
    (and
     (equal error-code 0)
     (mv-nth 1 (collapse frame))
     (absfat-equiv (mv-nth 0 (collapse frame))
                   fs)
     (abs-separate frame))))
 :hints
 (("goal"
   :do-not-induct t
   :in-theory
   (e/d
    (dist-names abs-separate hifat-place-file))))
 :otf-flg t)

(defthm
  frame-p-of-abs-place-file
  (implies (frame-p frame)
           (frame-p (mv-nth 0 (abs-place-file
                               frame
                               pathname
                               file))))
  :hints (("Goal" :in-theory (enable abs-place-file))))

(defund
  abs-remove-file (frame pathname)
  (declare
   (xargs :guard (and (frame-p frame)
                      (fat32-filename-list-p pathname))
          :guard-debug t
          :guard-hints (("Goal" :do-not-induct t) )
          :verify-guards nil))
  (b*
      (((when (atom frame))
        (mv frame *enoent*))
       (pathname (mbe :exec pathname
                      :logic (fat32-filename-list-fix pathname)))
       ((mv tail tail-error-code)
        (abs-remove-file (cdr frame) pathname))
       ((unless (and (equal tail-error-code *ENOENT*)
                     (prefixp (frame-val->path (cdar frame))
                              pathname)))
        (mv (list* (car frame) tail) tail-error-code))
       ;; Look up the parent directory - it has to be in one of the variables,
       ;; or else we must return ENOENT.
       ((mv & error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 (butlast 1 pathname))))
       ((when (or (equal error-code *enoent*)
                  (not (abs-complete (frame-val->dir (cdar frame))))))
        (mv (list* (car frame) tail) tail-error-code))
       ((mv head head-error-code)
        (hifat-remove-file (frame-val->dir (cdar frame)) pathname)))
    (mv
     (list* (cons (caar frame) (change-frame-val (cdar frame) :dir head))
            (cdr frame))
     head-error-code)))

(defund abs-mkdir
  (frame pathname)
  (b*
      ((frame (partial-collapse frame (butlast 1 pathname)))
       ;; After partial-collapse, either the parent directory is there in one
       ;; variable, or it isn't there at all.
       ((mv parent-dir error-code) (abs-find-file-helper (frame->root frame)
                                                         pathname))
       ((mv new-root &) (abs-remove-file (frame->root frame) pathname))
       ((unless (equal error-code 0))
        (mv frame -1 error-code))
       ((mv new-parent-dir error-code)
        (abs-place-file parent-dir pathname (make-abs-file :contents nil)))
       (frame (frame-with-root
               new-root
               (put-assoc-equal
                (find-new-index
                 ;; Using this, not (strip-cars (frame->frame frame)), to make
                 ;; sure we don't get a zero.
                 (strip-cars frame))
                new-parent-dir
                (frame->frame frame)))))
    (mv frame -1 error-code)))

(defthm abs-mkdir-correctness-lemma-1
  (implies (atom pathname)
           (equal (1st-complete-under-pathname frame pathname)
                  (1st-complete frame)))
  :hints (("goal" :in-theory (enable 1st-complete-under-pathname
                                     1st-complete prefixp))))

;; Move later.
(defthm true-listp-of-frame-with-root
  (equal (true-listp (frame-with-root root frame))
         (true-listp frame))
  :hints (("goal" :in-theory (enable frame-with-root))))
(defthm true-listp-of-put-assoc
  (implies (not (null name))
           (iff (true-listp (put-assoc-equal name val alist))
                (or (true-listp alist)
                    (atom (assoc-equal name alist))))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (mv-nth 1 (collapse frame))
                   (atom pathname)
                   (equal frame
                          (frame-with-root (frame->root frame)
                                           (frame->frame frame))))
              (equal (partial-collapse frame pathname)
                     (frame-with-root (mv-nth 0 (collapse frame))
                                      nil)))
     :hints (("goal" :in-theory (enable partial-collapse collapse collapse-this)
              :induct (collapse frame)
              :expand (partial-collapse frame pathname)))))

  (defthm
    abs-mkdir-correctness-lemma-2
    (implies
     (and (mv-nth 1
                  (collapse (frame-with-root root frame)))
          (atom pathname)
          (atom (assoc-equal 0 frame))
          (frame-p frame))
     (equal (partial-collapse (frame-with-root root frame)
                              pathname)
            (frame-with-root (mv-nth 0
                                     (collapse (frame-with-root root frame)))
                             nil)))
    :hints (("goal" :use (:instance lemma
                                    (frame (frame-with-root root frame)))))))

;; (thm
;;  (b*
;;      (((mv fs result) (collapse (frame-with-root root frame))))
;;    (implies
;;     (and
;;      result
;;      (atom (assoc-equal 0 frame))
;;      (frame-p frame))
;;     (and (mv-nth 1 (collapse (mv-nth 0 (abs-mkdir (frame-with-root root frame)
;;                                                   pathname))))
;;          (absfat-equiv (mv-nth 0 (collapse (mv-nth 0 (abs-mkdir
;;                                                       (frame-with-root root
;;                                                                        frame)
;;                                                       pathname))))
;;                        (mv-nth 0 (hifat-mkdir fs pathname))))))
;;  :hints (("Goal" :in-theory (enable hifat-mkdir abs-mkdir collapse)
;;           :do-not-induct t)) :otf-flg t)
