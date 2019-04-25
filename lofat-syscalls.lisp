(in-package "ACL2")

;  lofat-syscalls.lisp                                 Mihir Mehta

; Syscalls for LoFAT. These syscalls usually return, among other things, a
; return value (corresponding to the C return value) and an errno.

(include-book "lofat")
(include-book "hifat-syscalls")

;; This needs some revision... obviously, we don't want to be staring into the
;; computation to get the root directory's directory entries here.
(defund lofat-open (pathname fat32-in-memory fd-table file-table)
  (declare (xargs :guard (and (lofat-fs-p fat32-in-memory)
                              (fat32-filename-list-p pathname)
                              (fd-table-p fd-table)
                              (file-table-p file-table))
                  :stobjs fat32-in-memory))
  (b*
      ((fd-table (fd-table-fix fd-table))
       (file-table (file-table-fix file-table))
       ((mv root-contents &)
        (get-clusterchain-contents
         fat32-in-memory
         (fat32-entry-mask (bpb_rootclus fat32-in-memory))
         2097152))
       ((mv & errno)
        (lofat-find-file-by-pathname
         fat32-in-memory
         (make-dir-ent-list
          (string=>nats
           root-contents))
         pathname))
       ((unless (equal errno 0))
        (mv fd-table file-table -1 errno))
       (file-table-index
        (find-new-index (strip-cars file-table)))
       (fd-table-index
        (find-new-index (strip-cars fd-table))))
    (mv
     (cons
      (cons fd-table-index file-table-index)
      fd-table)
     (cons
      (cons file-table-index (make-file-table-element :pos 0 :fid pathname))
      file-table)
     fd-table-index 0)))

(defthm
  lofat-open-refinement
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (equal (mv-nth 1 (lofat-to-hifat fat32-in-memory))
               0))
   (equal
    (lofat-open pathname
                fat32-in-memory fd-table file-table)
    (hifat-open pathname
                (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                fd-table file-table)))
  :hints
  (("goal"
    :in-theory
    (e/d (lofat-to-hifat lofat-open)
         ((:rewrite lofat-find-file-by-pathname-correctness-1)
          (:rewrite lofat-find-file-by-pathname-correctness-2)))
    :do-not-induct t
    :use
    ((:instance
      (:rewrite lofat-find-file-by-pathname-correctness-1)
      (pathname pathname)
      (dir-ent-list
       (make-dir-ent-list
        (string=>nats
         (mv-nth
          0
          (get-clusterchain-contents
           fat32-in-memory
           (fat32-entry-mask (bpb_rootclus fat32-in-memory))
           2097152)))))
      (fat32-in-memory fat32-in-memory)
      (entry-limit (max-entry-count fat32-in-memory)))
     (:instance
      (:rewrite lofat-find-file-by-pathname-correctness-2)
      (pathname pathname)
      (dir-ent-list
       (make-dir-ent-list
        (string=>nats
         (mv-nth
          0
          (get-clusterchain-contents
           fat32-in-memory
           (fat32-entry-mask (bpb_rootclus fat32-in-memory))
           2097152)))))
      (fat32-in-memory fat32-in-memory)
      (entry-limit (max-entry-count fat32-in-memory)))))))

;; This needs some revision... obviously, we don't want to be staring into the
;; computation to get the root directory's directory entries here.
(defund
  lofat-pread
  (fd count offset fat32-in-memory fd-table file-table)
  (declare (xargs :guard (and (natp fd)
                              (natp count)
                              (natp offset)
                              (fd-table-p fd-table)
                              (file-table-p file-table)
                              (lofat-fs-p fat32-in-memory))
                  :stobjs fat32-in-memory))
  (b*
      ((fd-table-entry (assoc-equal fd fd-table))
       ((unless (consp fd-table-entry))
        (mv "" -1 *ebadf*))
       (file-table-entry (assoc-equal (cdr fd-table-entry)
                                      file-table))
       ((unless (consp file-table-entry))
        (mv "" -1 *ebadf*))
       (pathname (file-table-element->fid (cdr file-table-entry)))
       ((mv root-contents &)
        (get-clusterchain-contents
         fat32-in-memory
         (fat32-entry-mask (bpb_rootclus fat32-in-memory))
         2097152))
       ((mv file error-code)
        (lofat-find-file-by-pathname
         fat32-in-memory
         (make-dir-ent-list
          (string=>nats
           root-contents))
         pathname))
       ((unless (and (equal error-code 0)
                     (lofat-regular-file-p file)))
        (mv "" -1 error-code))
       (file-contents (lofat-file->contents file))
       (new-offset (min (+ offset count)
                        (length file-contents)))
       (buf (subseq file-contents
                    (min offset
                         (length file-contents))
                    new-offset)))
    (mv buf (length buf) 0)))

(defthm
  lofat-pread-refinement
  (implies (equal (mv-nth 3 (lofat-to-hifat fat32-in-memory))
                  0)
           (equal (lofat-pread fd count offset
                               fat32-in-memory fd-table file-table)
                  (hifat-pread fd count offset
                               (mv-nth 3 (lofat-to-hifat fat32-in-memory))
                               fd-table file-table)))
  :hints (("goal" :in-theory (enable lofat-to-hifat lofat-pread))))

(defund lofat-lstat (fat32-in-memory pathname)
  (declare (xargs :guard (and (lofat-fs-p fat32-in-memory)
                              (fat32-filename-list-p pathname))
                  :stobjs fat32-in-memory))
  (b*
      (((mv root-contents &)
        (get-clusterchain-contents
         fat32-in-memory
         (fat32-entry-mask (bpb_rootclus fat32-in-memory))
         2097152))
       ((mv file errno)
        (lofat-find-file-by-pathname
         fat32-in-memory
         (make-dir-ent-list
          (string=>nats
           root-contents))
         pathname))
       ((when (not (equal errno 0)))
        (mv (make-struct-stat) -1 errno)))
    (mv
       (make-struct-stat
        :st_size (dir-ent-file-size
                  (lofat-file->dir-ent file)))
       0 0)))

(defthm lofat-lstat-refinement
  (implies
   (equal (mv-nth 3 (lofat-to-hifat fat32-in-memory))
          0)
   (equal
    (lofat-lstat fat32-in-memory pathname)
    (hifat-lstat (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                 pathname)))
  :hints (("goal" :in-theory (enable lofat-to-hifat lofat-lstat))))

(defthm
  find-file-by-pathname-correctness-3-lemma-1
  (implies
   (and (m1-file-alist-p m1-file-alist1)
        (hifat-subsetp m1-file-alist1 m1-file-alist2)
        (m1-regular-file-p (cdr (assoc-equal name m1-file-alist1))))
   (equal (m1-file->contents (cdr (assoc-equal name m1-file-alist2)))
          (m1-file->contents (cdr (assoc-equal name m1-file-alist1)))))
  :hints (("goal" :in-theory (enable m1-file-alist-p m1-file-no-dups-p))))

(defthm
  find-file-by-pathname-correctness-3
  (implies
   (and (m1-file-alist-p m1-file-alist1)
        (m1-file-alist-p m1-file-alist2)
        (hifat-subsetp m1-file-alist1 m1-file-alist2)
        (equal (mv-nth 1
                       (find-file-by-pathname m1-file-alist1 pathname))
               0))
   (equal (mv-nth 1
                  (find-file-by-pathname m1-file-alist2 pathname))
          0))
  :hints
  (("goal"
    :induct (mv (mv-nth 1
                        (find-file-by-pathname m1-file-alist1 pathname))
                (mv-nth 1
                        (find-file-by-pathname m1-file-alist2 pathname)))
    :in-theory (enable m1-file-alist-p))))

(defthmd
  find-file-by-pathname-correctness-4
  (implies
   (and (m1-file-alist-p m1-file-alist1)
        (m1-file-alist-p m1-file-alist2)
        (hifat-subsetp m1-file-alist1 m1-file-alist2))
   (mv-let
     (file error-code)
     (find-file-by-pathname m1-file-alist1 pathname)
     (declare (ignore error-code))
     (implies
      (m1-regular-file-p file)
      (equal
       (m1-file->contents
        (mv-nth
         0
         (find-file-by-pathname m1-file-alist2 pathname)))
       (m1-file->contents file)))))
  :hints
  (("goal"
    :induct
    (mv
     (mv-nth 1
             (find-file-by-pathname m1-file-alist1 pathname))
     (mv-nth 1
             (find-file-by-pathname m1-file-alist2 pathname)))
    :in-theory (enable m1-file-alist-p))))

;; The hifat-subsetp part of this alone can be proved with fewer hypotheses.
(defthm
  find-file-by-pathname-correctness-5
  (implies
   (and (m1-file-alist-p m1-file-alist1)
        (m1-file-alist-p m1-file-alist2)
        (hifat-subsetp m1-file-alist1 m1-file-alist2))
   (mv-let
     (file error-code)
     (find-file-by-pathname m1-file-alist1 pathname)
     (implies
      (and (equal error-code 0)
           (m1-directory-file-p file))
      (and
       (m1-directory-file-p
        (mv-nth 0
                (find-file-by-pathname m1-file-alist2 pathname)))
       (hifat-subsetp
        (m1-file->contents file)
        (m1-file->contents
         (mv-nth
          0
          (find-file-by-pathname m1-file-alist2 pathname))))))))
  :hints
  (("goal"
    :induct
    (mv
     (mv-nth 1
             (find-file-by-pathname m1-file-alist1 pathname))
     (mv-nth 1
             (find-file-by-pathname m1-file-alist2 pathname)))
    :in-theory (enable m1-file-alist-p))))

(defthm
  find-file-by-pathname-correctness-6
  (implies
   (and (m1-file-alist-p m1-file-alist2)
        (m1-file-no-dups-p m1-file-alist2)
        (hifat-equiv m1-file-alist2 m1-file-alist1))
   (mv-let
     (file error-code)
     (find-file-by-pathname m1-file-alist1 pathname)
     (declare (ignore error-code))
     (implies
      (m1-regular-file-p file)
      (equal (m1-file->contents
              (mv-nth 0
                      (find-file-by-pathname m1-file-alist2 pathname)))
             (m1-file->contents file)))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-file-alist-p hifat-equiv)
           :use (:rewrite find-file-by-pathname-correctness-4))))

(defthm
  find-file-by-pathname-correctness-7-lemma-1
  (implies
   (and (m1-file-alist-p fs)
        (m1-file-no-dups-p fs)
        (m1-directory-file-p (mv-nth 0 (find-file-by-pathname fs pathname))))
   (m1-file-no-dups-p
    (m1-file->contents (mv-nth 0
                               (find-file-by-pathname fs pathname)))))
  :hints (("goal" :in-theory (enable m1-file-no-dups-p m1-file-alist-p))))

(defthm
  find-file-by-pathname-correctness-7
  (implies
   (and (m1-file-alist-p m1-file-alist2)
        (m1-file-no-dups-p m1-file-alist2)
        (hifat-equiv m1-file-alist2 m1-file-alist1))
   (mv-let
     (file error-code)
     (find-file-by-pathname m1-file-alist1 pathname)
     (implies
      (and (equal error-code 0)
           (m1-directory-file-p file))
      (hifat-equiv
       (m1-file->contents file)
       (m1-file->contents
        (mv-nth 0
                (find-file-by-pathname m1-file-alist2 pathname)))))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-file-alist-p hifat-equiv))))

(defun lofat-unlink (fat32-in-memory pathname)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (lofat-fs-p fat32-in-memory)
                              (fat32-filename-list-p pathname))))
  (b*
      (((mv fs error-code) (lofat-to-hifat fat32-in-memory))
       ((unless (equal error-code 0)) (mv fat32-in-memory *eio*))
       ((mv fs & error-code) (hifat-unlink fs pathname))
       ((mv fat32-in-memory &) (hifat-to-lofat fat32-in-memory fs)))
    (mv fat32-in-memory error-code)))

(defun lofat-rmdir (fat32-in-memory pathname)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (lofat-fs-p fat32-in-memory)
                              (fat32-filename-list-p pathname))))
  (b*
      (((mv fs error-code) (lofat-to-hifat fat32-in-memory))
       ((unless (equal error-code 0)) (mv fat32-in-memory *eio*))
       ((mv fs & error-code) (hifat-rmdir fs pathname))
       ((mv fat32-in-memory &) (hifat-to-lofat fat32-in-memory fs)))
    (mv fat32-in-memory error-code)))
