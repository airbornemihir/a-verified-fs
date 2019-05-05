(in-package "ACL2")

;  hifat-entry-count.lisp                                 Mihir Mehta

; hifat-entry-count is related to the problem of transforming a potentially loopy
; FAT32 disk image into a tree in a bounded amount of time. Some lemmas for
; reasoning about it are placed here.

(include-book "hifat-equiv")

;; We're not counting this very directory, because the root does not have a
;; directory entry for itself.
;;
;; Before disabling, this rule used to cause 436909 frames and 8297 tries in
;; the main book; now those numbers are 4997 and 63 respectively.
(defund hifat-entry-count (fs)
  (declare (xargs :guard (m1-file-alist-p fs)))
  (if
      (atom fs)
      0
    (if (m1-directory-file-p (cdar fs))
        (+ 1
           (hifat-entry-count (m1-file->contents (cdar fs)))
           (hifat-entry-count (cdr fs)))
      (+ 1
         (hifat-entry-count (cdr fs))))))

;; This function is kinda weirdly named now that the when-hifat-no-dups-p
;; part has been shorn by remove-hyps...
(defthmd
  hifat-entry-count-when-hifat-no-dups-p
  (implies
   (consp (assoc-equal x m1-file-alist))
   (equal
    (hifat-entry-count m1-file-alist)
    (+ (hifat-entry-count (remove1-assoc x m1-file-alist))
       (if (m1-directory-file-p (cdr (assoc-equal x m1-file-alist)))
           (+ 1
              (hifat-entry-count
               (m1-file->contents (cdr (assoc-equal x m1-file-alist)))))
         1))))
  :hints (("goal" :in-theory (enable hifat-entry-count))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme
       (m1-file-alist1 m1-file-alist2)
     (declare
      (xargs
       :guard (and (m1-file-alist-p m1-file-alist1)
                   (m1-file-alist-p m1-file-alist2))
       :hints (("goal" :in-theory (enable m1-file->contents
                                          m1-directory-file-p)))))
     (b* (((when (atom m1-file-alist1)) t)
          ((when (or (atom (car m1-file-alist1))
                     (not (stringp (car (car m1-file-alist1))))))
           (and (member-equal (car m1-file-alist1)
                              m1-file-alist2)
                (induction-scheme (cdr m1-file-alist1)
                                  (remove1-assoc-equal
                                   (caar m1-file-alist1)
                                   m1-file-alist2))))
          (name (caar m1-file-alist1))
          (file1 (cdar m1-file-alist1))
          ((unless (consp (assoc-equal name m1-file-alist2)))
           nil)
          (file2 (cdr (assoc-equal name m1-file-alist2))))
       (if (not (m1-directory-file-p file1))
           (and (not (m1-directory-file-p file2))
                (induction-scheme (cdr m1-file-alist1)
                                  (remove1-assoc-equal
                                   name
                                   m1-file-alist2))
                (equal (m1-file->contents file1)
                       (m1-file->contents file2)))
         (and (m1-directory-file-p file2)
              (induction-scheme (cdr m1-file-alist1)
                                (remove1-assoc-equal
                                 name
                                 m1-file-alist2))
              (induction-scheme (m1-file->contents file1)
                                (m1-file->contents file2)))))))

  (local
   (defthm
     induction-scheme-correctness
     (implies (and (hifat-no-dups-p m1-file-alist1)
                   (m1-file-alist-p m1-file-alist1))
              (iff (induction-scheme m1-file-alist1 m1-file-alist2)
                   (hifat-subsetp m1-file-alist1 m1-file-alist2)))
     :hints (("goal" :induct (induction-scheme m1-file-alist1 m1-file-alist2)
              :in-theory (enable hifat-no-dups-p)))))

  (defthm
    hifat-entry-count-when-hifat-subsetp
    (implies (and (hifat-no-dups-p m1-file-alist1)
                  (m1-file-alist-p m1-file-alist1)
                  (hifat-subsetp m1-file-alist1 m1-file-alist2))
             (<= (hifat-entry-count m1-file-alist1)
                 (hifat-entry-count m1-file-alist2)))
    :rule-classes :linear
    :hints
    (("goal" :induct (induction-scheme m1-file-alist1 m1-file-alist2)
      :in-theory (enable hifat-no-dups-p hifat-entry-count))
     ("subgoal *1/7"
      :use (:instance (:rewrite hifat-entry-count-when-hifat-no-dups-p)
                      (m1-file-alist m1-file-alist2)
                      (x (car (car m1-file-alist1)))))
     ("subgoal *1/4"
      :use (:instance (:rewrite hifat-entry-count-when-hifat-no-dups-p)
                      (m1-file-alist m1-file-alist2)
                      (x (car (car m1-file-alist1))))))))

(defthm
  hifat-entry-count-when-hifat-equiv
  (implies (and (hifat-equiv m1-file-alist1 m1-file-alist2)
                (m1-file-alist-p m1-file-alist2)
                (hifat-no-dups-p m1-file-alist2))
           (equal (hifat-entry-count m1-file-alist1)
                  (hifat-entry-count m1-file-alist2)))
  :hints
  (("goal" :in-theory (e/d (hifat-equiv)
                           (hifat-entry-count-when-hifat-subsetp))
    :do-not-induct t
    :use ((:instance hifat-entry-count-when-hifat-subsetp
                     (m1-file-alist1 m1-file-alist2)
                     (m1-file-alist2 m1-file-alist1))
          hifat-entry-count-when-hifat-subsetp))))
