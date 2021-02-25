(in-package "ACL2")

;  lofat-pwrite.lisp                                   Mihir Mehta

(include-book "../lofat")
(include-book "../hifat-syscalls")

(local (in-theory (disable nth make-list-ac-removal last
                           make-list-ac)))

;; Move later.
(defthmd
  lofat-mkdir-refinement-lemma-12
  (true-equiv (true-fix x) x)
  :rule-classes :rewrite-quoted-constant)

(defund lofat-pwrite (fd buf offset fat32$c fd-table file-table)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (natp fd)
                              (stringp buf)
                              (natp offset)
                              (fd-table-p fd-table)
                              (file-table-p file-table))
                  :guard-debug t
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (enable len-of-insert-text)))))
  (b*
      ((fd-table-entry (assoc-equal fd fd-table))
       ((unless (consp fd-table-entry))
        (mv fat32$c -1 *ebadf*))
       (file-table-entry (assoc-equal (cdr fd-table-entry)
                                      file-table))
       ((unless (consp file-table-entry))
        (mv fat32$c -1 *ebadf*))
       (path (file-table-element->fid (cdr file-table-entry)))
       ((mv root-d-e-list &)
        (root-d-e-list fat32$c))
       ((mv file error-code)
        (lofat-find-file fat32$c root-d-e-list path))
       ((mv oldtext d-e)
        (if (and (equal error-code 0)
                 (lofat-regular-file-p file))
            (mv (coerce (lofat-file->contents file) 'list)
                (lofat-file->d-e file))
          (mv nil (d-e-fix nil))))
       ((unless (unsigned-byte-p 32 (+ offset (length buf))))
        (mv fat32$c -1 *enospc*))
       (file
        (make-lofat-file
         :d-e d-e
         :contents (coerce (insert-text oldtext offset buf)
                           'string)))
       ((mv fat32$c error-code)
        (lofat-place-file fat32$c (pseudo-root-d-e fat32$c) path file)))
    (mv fat32$c (if (equal error-code 0) 0 -1)
        error-code)))

(defthm integerp-of-lofat-pwrite
  (and
   (integerp (mv-nth 1 (lofat-pwrite fd buf offset fat32$c fd-table
                                     file-table)))
   (natp (mv-nth 2
                 (lofat-pwrite fd buf
                               offset fat32$c fd-table file-table))))
  :hints (("Goal" :in-theory (enable lofat-pwrite)) )
  :rule-classes
  ((:type-prescription
    :corollary
    (integerp (mv-nth 1 (lofat-pwrite fd buf offset fat32$c fd-table
                                      file-table))))
   (:type-prescription
    :corollary
    (natp (mv-nth 2
                  (lofat-pwrite fd buf
                                offset fat32$c fd-table file-table))))))

(defthm lofat-fs-p-of-lofat-pwrite
  (implies
   (lofat-fs-p fat32$c)
   (lofat-fs-p (mv-nth 0 (lofat-pwrite fd buf offset fat32$c fd-table
                                       file-table))))
  :hints (("Goal" :in-theory (enable lofat-pwrite)) ))

(defthm
  lofat-pwrite-refinement-lemma-9
  (implies (and (not (stringp buf))
                (< (+ offset (len buf)) 4294967296))
           (m1-file-contents-p (implode$inline (insert-text nil offset buf))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-pwrite m1-file-contents-p insert-text)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
          lofat-place-file))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file))))))

(defthm
  lofat-pwrite-refinement-lemma-17
  (implies
   (and (good-root-d-e-p (pseudo-root-d-e fat32$c)
                         fat32$c)
        (equal (mv-nth 1 (lofat-to-hifat fat32$c))
               0)
        (lofat-file-p file)
        (or (lofat-regular-file-p file)
            (equal (lofat-file->contents file) nil))
        (not (zp (mv-nth 1
                         (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                           path file)))))
   (equal (mv-nth 0
                  (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                    path file))
          fat32$c))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (lofat-to-hifat root-d-e-list)
                           (lofat-place-file-correctness-2))
           :use (:instance lofat-place-file-correctness-2
                           (root-d-e (pseudo-root-d-e fat32$c))
                           (entry-limit (max-entry-count fat32$c))))))

(defthm
  lofat-pwrite-refinement-lemma-20
  (implies (and (natp offset)
                (< (+ offset (len (explode buf)))
                   4294967296))
           (m1-file-contents-p (implode$inline (insert-text nil offset buf))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-pwrite m1-file-contents-p insert-text)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
          lofat-place-file))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file))))))

(defthm
  lofat-pwrite-refinement-lemma-19
  (implies
   (and
    (fat32-filename-list-p path)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not (equal (mv-nth 1
                        (lofat-find-file fat32$c
                                         (mv-nth 0 (root-d-e-list fat32$c))
                                         path))
                0)))
   (equal
    (mv-nth
     1
     (lofat-to-hifat
      (mv-nth 0
              (lofat-place-file
               fat32$c (pseudo-root-d-e fat32$c)
               path
               (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (implode (insert-text nil offset buf)))))))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (update-dir-contents-correctness-1)
                    ((:rewrite lofat-mkdir-refinement-lemma-10)
                     lofat-place-file))
    :expand (:free (fat32$c root-d-e file)
                   (lofat-place-file fat32$c root-d-e nil file))
    :use ((:instance
           (:rewrite lofat-mkdir-refinement-lemma-10)
           (file (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                             (implode (insert-text nil offset buf)))))))))

(defthm
  lofat-pwrite-refinement-lemma-21
  (implies (and (<= 0 offset)
                (< (+ offset (len (explode buf)))
                   4294967296))
           (lofat-file-contents-p (implode (insert-text nil offset buf))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-file-contents-p insert-text))))

(defthm lofat-pwrite-refinement-lemma-22
  (implies (and (<= 0 offset)
                (< (+ offset (len (explode buf)))
                   4294967296))
           (< (len (insert-text nil offset buf))
              4294967296))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (enable insert-text))))

(defthm
  lofat-pwrite-refinement-lemma-24
  (implies
   (and
    (fat32-filename-list-p path)
    (<= 0 offset)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not (equal (mv-nth 1
                        (lofat-find-file fat32$c
                                         (mv-nth 0 (root-d-e-list fat32$c))
                                         path))
                0))
    (not
     (equal
      (mv-nth 1
              (lofat-place-file
               fat32$c (pseudo-root-d-e fat32$c)
               path
               (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (implode (insert-text nil offset buf)))))
      28))
    (< (+ offset (len (explode buf)))
       4294967296))
   (hifat-equiv
    (mv-nth
     0
     (lofat-to-hifat
      (mv-nth 0
              (lofat-place-file
               fat32$c (pseudo-root-d-e fat32$c)
               path
               (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (implode (insert-text nil offset buf)))))))
    (mv-nth
     0
     (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                       path
                       (m1-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (implode (insert-text nil offset buf)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite lofat-mkdir-refinement-lemma-10)
                        (:rewrite lofat-mkdir-refinement-lemma-30))
    :use
    ((:instance (:rewrite lofat-mkdir-refinement-lemma-10)
                (file (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                  (implode (insert-text nil offset buf)))))
     (:instance
      (:rewrite lofat-mkdir-refinement-lemma-30)
      (file (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (implode (insert-text nil offset buf)))))))))

(defthm
  lofat-pwrite-refinement-lemma-25
  (implies
   (and
    (integerp offset)
    (<= 0 offset)
    (lofat-regular-file-p
     (mv-nth
      0
      (lofat-find-file fat32$c
                       (mv-nth 0 (root-d-e-list fat32$c))
                       (file-table-element->fid
                        (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                          file-table))))))
    (stringp buf)
    (< (+ offset (len (explode buf)))
       4294967296))
   (m1-file-contents-p
    (implode
     (insert-text
      (explode
       (lofat-file->contents
        (mv-nth 0
                (lofat-find-file
                 fat32$c
                 (mv-nth 0 (root-d-e-list fat32$c))
                 (file-table-element->fid
                  (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                    file-table)))))))
      offset buf))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-file-contents-p
                              len-of-insert-text))))

(defthm lofat-pwrite-refinement-lemma-27 (true-equiv (lofat-file->d-e x) t))

(defthm
  lofat-pwrite-refinement-lemma-44
  (implies
   (and
    (integerp offset)
    (<= 0 offset)
    (lofat-regular-file-p
     (mv-nth
      0
      (lofat-find-file fat32$c
                       (mv-nth 0 (root-d-e-list fat32$c))
                       (file-table-element->fid
                        (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                          file-table))))))
    (stringp buf)
    (< (+ offset (len (explode buf)))
       4294967296))
   (lofat-file-contents-p
    (implode
     (insert-text
      (explode
       (lofat-file->contents
        (mv-nth 0
                (lofat-find-file
                 fat32$c
                 (mv-nth 0 (root-d-e-list fat32$c))
                 (file-table-element->fid
                  (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                    file-table)))))))
      offset buf))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-file-contents-p
                              len-of-insert-text))))

(defthm
  lofat-pwrite-refinement-lemma-45
  (implies
   (and
    (integerp offset)
    (<= 0 offset)
    (lofat-regular-file-p
     (mv-nth
      0
      (lofat-find-file fat32$c
                       (mv-nth 0 (root-d-e-list fat32$c))
                       (file-table-element->fid
                        (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                          file-table))))))
    (stringp buf)
    (< (+ offset (len (explode buf)))
       4294967296))
   (<
    (len
     (insert-text
      (explode$inline
       (lofat-file->contents$inline
        (mv-nth 0
                (lofat-find-file
                 fat32$c
                 (mv-nth 0 (root-d-e-list fat32$c))
                 (file-table-element->fid$inline
                  (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                    file-table)))))))
      offset buf))
    4294967296))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-pwrite lofat-mkdir-refinement-lemma-12
                       len-of-insert-text)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
          lofat-place-file
          lofat-mkdir-refinement-lemma-15))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file)))))
  :rule-classes :linear)

(defthm
  lofat-pwrite-refinement-lemma-48
  (implies
   (and
    (<= 0 offset)
    (lofat-regular-file-p
     (mv-nth
      0
      (lofat-find-file fat32$c
                       (mv-nth 0 (root-d-e-list fat32$c))
                       path)))
    (not (stringp buf))
    (< (+ offset (len buf)) 4294967296))
   (m1-file-contents-p
    (implode$inline
     (insert-text
      (explode$inline
       (lofat-file->contents$inline
        (mv-nth 0
                (lofat-find-file
                 fat32$c
                 (mv-nth 0 (root-d-e-list fat32$c))
                 path))))
      offset buf))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (enable m1-file-contents-p insert-text))))

(defthm
  lofat-pwrite-refinement-lemma-49
  (implies
   (and (integerp offset)
        (<= 0 offset)
        (lofat-regular-file-p
         (mv-nth 0
                 (lofat-find-file fat32$c
                                  (mv-nth 0 (root-d-e-list fat32$c))
                                  path)))
        (not (stringp buf))
        (< (+ offset (len buf)) 4294967296))
   (lofat-file-contents-p
    (implode
     (insert-text
      (explode
       (lofat-file->contents
        (mv-nth 0
                (lofat-find-file fat32$c
                                 (mv-nth 0 (root-d-e-list fat32$c))
                                 path))))
      offset buf))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-file-contents-p insert-text))))

(defthm
  lofat-pwrite-refinement-lemma-50
  (implies
   (and (integerp offset)
        (<= 0 offset)
        (lofat-regular-file-p
         (mv-nth 0
                 (lofat-find-file fat32$c
                                  (mv-nth 0 (root-d-e-list fat32$c))
                                  path)))
        (not (stringp buf))
        (< (+ offset (len buf)) 4294967296))
   (<
    (len
     (insert-text
      (explode$inline
       (lofat-file->contents$inline
        (mv-nth 0
                (lofat-find-file fat32$c
                                 (mv-nth 0 (root-d-e-list fat32$c))
                                 path))))
      offset buf))
    4294967296))
  :hints (("goal" :do-not-induct t
           :in-theory (enable insert-text)))
  :rule-classes :linear)

(defthm
  lofat-pwrite-refinement-lemma-26
  (equal (lofat-place-file fat32$c root-d-e
                           path (lofat-file d-e1 contents))
         (lofat-place-file fat32$c root-d-e
                           path (lofat-file d-e2 contents)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-place-file lofat-place-file-helper
                       lofat-regular-file-p
                       lofat-directory-file-p
                       lofat-file-p lofat-file->contents
                       m1-file-hifat-file-alist-fix m1-file)
     (m1-file-hifat-file-alist-fix-normalisation
      abs-mkdir-correctness-lemma-36
      (:rewrite lofat-file-contents-fix-when-lofat-file-contents-p)
      (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-lemma-4)
      (:rewrite fat32-filename-p-correctness-1)
      (:rewrite lofat-file-contents-p-when-stringp)
      (:linear nth-when-d-e-p)
      (:linear len-of-explode-when-m1-file-contents-p-1)
      (:rewrite lofat-file-fix-when-lofat-file-p)
      (:rewrite lofat-file-contents-p-when-d-e-listp)
      (:rewrite nth-of-nats=>chars)
      (:rewrite m1-file-contents-p-when-stringp)
      (:type-prescription hifat-bounded-file-alist-p)
      (:rewrite stringp-when-nonempty-stringp)))))
  :rule-classes
  ((:congruence
    :corollary
    (implies (true-equiv d-e1 d-e2)
             (equal (lofat-place-file fat32$c root-d-e
                                      path (lofat-file d-e1 contents))
                    (lofat-place-file fat32$c root-d-e
                                      path (lofat-file d-e2 contents)))))))

(defthm
  lofat-pwrite-refinement
  (implies
   (and
    ;; This needs to go.
    (natp offset)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    ;; Let's discuss this hypothesis.
    ;;
    ;; This is something that we actually should
    ;; be able to derive from the structure of lofat-to-hifat-helper. That is,
    ;; we should be able to say that if we're able to do lofat-to-hifat-helper
    ;; with the max-entry-count parameter after the lofat-place-file operation,
    ;; then obviously we must have the capacity for that number of entries. And
    ;; if we don't have the capacity for that number of entries, then we must
    ;; be contradicting the hypothesis about the error code of lofat-place-file
    ;; being other than EIO. That is, this hypothesis should be implied by
    ;; that one, because in the case where that one holds, we must have gotten
    ;; away without an error while creating the new entry, and that means we
    ;; couldn't have exceeded the max entry count!
    ;;
    ;; That kind of reasoning, however, is exactly the kind of thing we gave up
    ;; on a while earlier. Now is not a great time to start either.
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not (equal (mv-nth 2 (lofat-pwrite fd buf offset fat32$c fd-table file-table)) *enospc*)))
   (and (equal (mv-nth 1
                       (lofat-to-hifat (mv-nth 0 (lofat-pwrite fd buf offset fat32$c fd-table file-table))))
               0)
        (hifat-equiv
         (mv-nth 0
                 (lofat-to-hifat (mv-nth 0 (lofat-pwrite fd buf offset fat32$c fd-table file-table))))
         (mv-nth 0
                 (hifat-pwrite fd buf offset (mv-nth 0 (lofat-to-hifat fat32$c)) fd-table file-table)))
        (equal (mv-nth 1 (lofat-pwrite fd buf offset fat32$c fd-table file-table))
               (mv-nth 1
                       (hifat-pwrite fd buf offset (mv-nth 0 (lofat-to-hifat fat32$c)) fd-table file-table)))
        (equal (mv-nth 2 (lofat-pwrite fd buf offset fat32$c fd-table file-table))
               (mv-nth 2
                       (hifat-pwrite fd buf offset (mv-nth 0 (lofat-to-hifat fat32$c)) fd-table file-table)))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-pwrite
          lofat-mkdir-refinement-lemma-12)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
          lofat-place-file
          lofat-mkdir-refinement-lemma-15))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file))))))
