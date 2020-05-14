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

(encapsulate
  ()

  (local
   (defun
       induction-scheme (dir frame x)
     (declare (xargs :verify-guards nil
                     :measure (len (frame->frame frame))))
     (cond
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not
         (zp
          (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal
           (frame-val->src
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (remove-assoc-equal
               (1st-complete (frame->frame frame))
               (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (equal x (1st-complete (frame->frame frame))))
       (induction-scheme
        (ctx-app
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (frame->frame frame))))
         dir (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        (frame-val->src
         (cdr (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not
         (zp
          (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal
           (frame-val->src
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (remove-assoc-equal
               (1st-complete (frame->frame frame))
               (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (equal x
               (frame-val->src
                (cdr
                 (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
       (induction-scheme
        (ctx-app
         dir
         (frame-val->dir
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        x))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not
         (zp
          (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal
           (frame-val->src
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (remove-assoc-equal
               (1st-complete (frame->frame frame))
               (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))))
       (induction-scheme
        dir
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        x))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (zp
         (frame-val->src
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (ctx-app-ok
         (frame->root frame)
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
       (induction-scheme
        dir
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        x))
      (t (mv dir frame x)))))

  ;; The reason why it won't be easy to prove this is because its analog,
  ;; collapse-congruence-2, relies on collapse-congruence-1 which involves
  ;; absfat-equiv on the roots of the two frames - a deep relation if one
  ;; thinks about it. Here, what would be required is some sort of property
  ;; saying the same abstract addresses are present at the same places. Best to
  ;; skip the proof for now and move on.
  (skip-proofs
   (defthm
     absfat-place-file-correctness-lemma-2
    (implies
     (and (consp (assoc-equal x (frame->frame frame)))
          (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
          (abs-complete dir)
          (abs-fs-p dir))
     (and
      (equal
       (mv-nth 1 (collapse (frame-with-root (frame->root frame)
                                            (put-assoc-equal
                                             x
                                             (change-frame-val
                                              (cdr (assoc-equal x (frame->frame
                                                                   frame)))
                                              :dir dir)
                                             (frame->frame frame)))))
       (mv-nth 1 (collapse frame)))
      (absfat-equiv
       (mv-nth 0 (collapse (frame-with-root (frame->root frame)
                                            (put-assoc-equal
                                             x
                                             (change-frame-val
                                              (cdr (assoc-equal x (frame->frame
                                                                   frame)))
                                              :dir dir)
                                             (frame->frame frame)))))
       (mv-nth 0 (hifat-place-file
                  (mv-nth 0 (collapse frame))
                  (frame-val->path
                   (cdr (assoc-equal x (frame->frame
                                        frame))))
                  (change-m1-file
                   (mv-nth 0
                           (hifat-find-file
                            (mv-nth 0 (collapse frame))
                            (frame-val->path
                             (cdr (assoc-equal x (frame->frame
                                                  frame))))))
                   :contents dir))))
      (equal
       (mv-nth 1 (hifat-place-file
                  (mv-nth 0 (collapse frame))
                  (frame-val->path
                   (cdr (assoc-equal x (frame->frame
                                        frame))))
                  dir))
       0)))
    :hints
    (("goal"
      :in-theory
      (e/d
       (collapse collapse-this)
       ((:definition remove-assoc-equal)
        (:rewrite remove-assoc-of-remove-assoc)
        (:rewrite abs-file-alist-p-when-m1-file-alist-p)
        (:rewrite
         absfat-equiv-implies-set-equiv-names-at-1-lemma-1)
        (:rewrite put-assoc-equal-without-change . 2)
        (:definition no-duplicatesp-equal)
        (:definition member-equal)
        (:rewrite nthcdr-when->=-n-len-l)
        (:definition remove-equal)
        (:rewrite remove-when-absent)
        (:rewrite 1st-complete-of-put-assoc-2)
        (:definition put-assoc-equal)
        (:rewrite no-duplicatesp-of-strip-cars-of-put-assoc)
        (:type-prescription
         abs-fs-fix-of-put-assoc-equal-lemma-3)))
      :induct (induction-scheme dir frame x)
      :expand
      ((collapse frame)
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          x
          (frame-val
           (frame-val->path
            (cdr (assoc-equal x (frame->frame frame))))
           dir
           (frame-val->src
            (cdr (assoc-equal x (frame->frame frame)))))
          (frame->frame frame))))
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete (frame->frame frame))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           dir 0)
          (frame->frame frame))))))))))

;; The folllowing is based on
;; hifat-find-file-correctness-3-lemma-7.
(skip-proofs
 (defthm
   hifat-place-file-correctness-4
   (implies
    (hifat-equiv m1-file-alist2 m1-file-alist1)
    (and
     (equal
      (mv-nth 1
              (hifat-place-file m1-file-alist2 pathname file))
      (mv-nth 1
              (hifat-place-file m1-file-alist1 pathname file)))
     (hifat-equiv
      (mv-nth 0
              (hifat-place-file m1-file-alist2 pathname file))
      (mv-nth 0
              (hifat-place-file m1-file-alist1 pathname file)))))
   :rule-classes
   ((:congruence
     :corollary
     (implies
      (hifat-equiv m1-file-alist2 m1-file-alist1)
      (equal
       (mv-nth 1
               (hifat-place-file m1-file-alist2 pathname file))
       (mv-nth 1
               (hifat-place-file m1-file-alist1 pathname file)))))
    (:congruence
     :corollary
     (implies
      (hifat-equiv m1-file-alist2 m1-file-alist1)
      (hifat-equiv
       (mv-nth 0
               (hifat-place-file m1-file-alist2 pathname file))
       (mv-nth 0
               (hifat-place-file m1-file-alist1 pathname file))))))))

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

(thm
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
      (put-assoc-equal (car (last pathname))
                       file dir))))
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
   (not (member-equal (car (last pathname))
                      (names-at dir nil)))
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
 (("goal" :do-not-induct t
   :in-theory (e/d (hifat-equiv-when-absfat-equiv dist-names abs-separate)
                   (hifat-place-file-correctness-4))
   ;; This use hint is for debugging - we need to know the reason.
   :use
   (:instance
    hifat-place-file-correctness-4
    (m1-file-alist1
     (mv-nth
      0
      (collapse (frame-with-root root
                                 (cons (cons x (frame-val nil dir src))
                                       frame)))))
    (m1-file-alist2 fs)
    (pathname nil)
    (file (put-assoc-equal (car (last pathname))
                           file dir)))))
 :otf-flg t)

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
   ;; Guard of hifat-place-file.
   (and (m1-file-alist-p fs)
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
                frame))))
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
 (("GOal"
   :do-not-induct t
   :IN-THEORY
   (e/d
    (dist-names abs-separate)
    (ABSFAT-PLACE-FILE-CORRECTNESS-LEMMA-2
     ;; Enable this with care for this theorem. It makes a number of
     ;; absfat-equiv terms disappear and consequently a number of theorems stop
     ;; holding true...
     hifat-equiv-when-absfat-equiv))
   :USE
   (:INSTANCE
    ABSFAT-PLACE-FILE-CORRECTNESS-LEMMA-2
    (X X)
    (DIR (PUT-ASSOC-EQUAL (CAR (LAST PATHNAME))
                          FILE DIR))
    (FRAME (FRAME-WITH-ROOT ROOT
                            (CONS (CONS X (FRAME-VAL NIL DIR SRC))
                                  FRAME))))))
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
