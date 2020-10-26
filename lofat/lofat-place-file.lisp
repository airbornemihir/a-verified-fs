(in-package "ACL2")

(include-book "../utilities/flatten-equiv")
(include-book "../hifat-to-lofat-inversion")
(include-book "../lofat-to-string-inversion")

;  lofat-place-file.lisp                                Mihir Mehta

(encapsulate
  ()

  (local (include-book "../lofat"))

  (defund make-dir-ent-with-filename (filename)
    (declare
     (xargs
      :guard (and (stringp filename)
                  (equal (length filename) 11))))
    (dir-ent-set-filename (dir-ent-fix nil) filename))

  (defund lofat-file-contents-p (contents)
    (declare (xargs :guard t))
    (or (and (stringp contents)
             (unsigned-byte-p 32 (length contents)))
        (dir-ent-list-p contents)))

  (defund lofat-file-contents-fix (contents)
    (declare (xargs :guard t))
    (if (lofat-file-contents-p contents)
        contents
      ""))

  (fty::deffixtype lofat-file-contents
                   :pred lofat-file-contents-p
                   :fix lofat-file-contents-fix
                   :equiv lofat-file-contents-equiv
                   :define t)

  (fty::defprod
   lofat-file
   ((dir-ent dir-ent-p :default (dir-ent-fix nil))
    (contents lofat-file-contents-p :default (lofat-file-contents-fix nil))))

  (defund lofat-directory-file-p (file)
    (declare (xargs :guard t))
    (and (lofat-file-p file)
         (dir-ent-list-p (lofat-file->contents file))))

  (defund lofat-regular-file-p (file)
    (declare (xargs :guard t))
    (and (lofat-file-p file)
         (stringp (lofat-file->contents file))
         (unsigned-byte-p 32 (length (lofat-file->contents file)))))

  (defund clear-clusterchain
    (fat32-in-memory masked-current-cluster length)
    (declare
     (xargs :stobjs fat32-in-memory
            :guard (and (lofat-fs-p fat32-in-memory)
                        (fat32-masked-entry-p masked-current-cluster)
                        (natp length)
                        (>= masked-current-cluster
                            *ms-first-data-cluster*)
                        (< masked-current-cluster
                           (+ (count-of-clusters fat32-in-memory)
                              *ms-first-data-cluster*)))))
    (b*
        (((mv dir-clusterchain error-code)
          (get-clusterchain fat32-in-memory masked-current-cluster length))
         ((unless (equal error-code 0))
          (mv fat32-in-memory error-code))
         (fat32-in-memory
          (stobj-set-indices-in-fa-table
           fat32-in-memory dir-clusterchain
           (make-list (len dir-clusterchain)
                      :initial-element 0))))
      (mv fat32-in-memory 0)))

  (defun
      insert-dir-ent-helper
      (dir-contents ac parent-dir-ent current-dir-ent)
    (declare
     (xargs
      :guard (and (stringp dir-contents)
                  (dir-ent-list-p ac))
      :measure (length dir-contents)
      :guard-hints (("goal" :in-theory (enable dir-ent-p)))))
    (b*
        (((when (< (length dir-contents)
                   *ms-dir-ent-length*))
          (mv (revappend ac nil)
              parent-dir-ent current-dir-ent))
         (dir-ent
          (mbe
           :exec
           (string=>nats (subseq dir-contents 0 *ms-dir-ent-length*))
           :logic (dir-ent-fix
                   (chars=>nats (take *ms-dir-ent-length*
                                      (explode dir-contents))))))
         ((when (equal (char (dir-ent-filename dir-ent) 0)
                       (code-char 0)))
          (mv (revappend ac nil)
              parent-dir-ent current-dir-ent))
         ((when (equal (dir-ent-filename dir-ent)
                       *parent-dir-fat32-name*))
          (insert-dir-ent-helper
           (subseq dir-contents *ms-dir-ent-length* nil)
           ac dir-ent current-dir-ent))
         ((when (equal (dir-ent-filename dir-ent)
                       *current-dir-fat32-name*))
          (insert-dir-ent-helper
           (subseq dir-contents *ms-dir-ent-length* nil)
           ac parent-dir-ent dir-ent))
         ((when (useless-dir-ent-p dir-ent))
          (insert-dir-ent-helper
           (subseq dir-contents *ms-dir-ent-length* nil)
           ac parent-dir-ent current-dir-ent)))
      (insert-dir-ent-helper
       (subseq dir-contents *ms-dir-ent-length* nil)
       (list* dir-ent ac)
       parent-dir-ent current-dir-ent)))

  (defun
      place-dir-ent (dir-ent-list dir-ent)
    (declare (xargs :guard (and (dir-ent-p dir-ent)
                                (dir-ent-list-p dir-ent-list))))
    (b*
        ((dir-ent (mbe :exec dir-ent
                       :logic (dir-ent-fix dir-ent)))
         ((when (atom dir-ent-list))
          (list dir-ent))
         ((when (equal (dir-ent-filename dir-ent)
                       (dir-ent-filename (car dir-ent-list))))
          (list*
           dir-ent
           (mbe :exec (cdr dir-ent-list)
                :logic (dir-ent-list-fix (cdr dir-ent-list))))))
      (list* (mbe :logic (dir-ent-fix (car dir-ent-list))
                  :exec (car dir-ent-list))
             (place-dir-ent (cdr dir-ent-list)
                            dir-ent))))

  (defund
    insert-dir-ent (dir-contents dir-ent)
    (declare
     (xargs :guard (and (dir-ent-p dir-ent)
                        (unsigned-byte-listp 8 dir-contents))
            :guard-hints (("goal" :in-theory (enable dir-ent-p)))))
    (b*
        (((mv dir-ent-list parent-dir-ent current-dir-ent)
          (insert-dir-ent-helper (nats=>string dir-contents) nil nil nil)))
      (append
       (dir-ent-set-filename (dir-ent-fix current-dir-ent) *current-dir-fat32-name*)
       (dir-ent-set-filename (dir-ent-fix parent-dir-ent) *parent-dir-fat32-name*)
       (flatten (place-dir-ent dir-ent-list dir-ent)))))

  (defund
    update-dir-contents
    (fat32-in-memory first-cluster dir-contents)
    (declare
     (xargs
      :stobjs fat32-in-memory
      :guard (and (lofat-fs-p fat32-in-memory)
                  (fat32-masked-entry-p first-cluster)
                  (<= *ms-first-data-cluster* first-cluster)
                  (> (+ *ms-first-data-cluster*
                        (count-of-clusters fat32-in-memory))
                     first-cluster)
                  (stringp dir-contents))
      :guard-debug t
      :guard-hints
      (("goal"
        :expand (fat32-build-index-list
                 (effective-fat fat32-in-memory)
                 first-cluster
                 2097152 (cluster-size fat32-in-memory))
        :in-theory
        (disable unsigned-byte-p
                 bounded-nat-listp-correctness-1
                 (:linear non-negativity-of-car-of-last-when-nat-listp))
        :use
        ((:instance
          nat-listp-forward-to-integer-listp
          (x (mv-nth 0
                     (fat32-build-index-list
                      (effective-fat fat32-in-memory)
                      first-cluster *ms-max-dir-size*
                      (cluster-size fat32-in-memory)))))
         (:instance
          (:linear non-negativity-of-car-of-last-when-nat-listp)
          (l (mv-nth 0
                     (fat32-build-index-list
                      (effective-fat fat32-in-memory)
                      first-cluster *ms-max-dir-size*
                      (cluster-size fat32-in-memory))))))))))
    (b* (((mv clusterchain &)
          (get-clusterchain fat32-in-memory
                            first-cluster *ms-max-dir-size*))
         (last-value
          (fat32-entry-mask (fati (car (last clusterchain))
                                  fat32-in-memory)))
         ((mv fat32-in-memory error-code)
          (clear-clusterchain fat32-in-memory
                              first-cluster *ms-max-dir-size*))
         ((unless (equal error-code 0))
          (mv fat32-in-memory *eio*))
         (fat32-in-memory
          (update-fati first-cluster
                       (fat32-update-lower-28
                        (fati first-cluster fat32-in-memory)
                        *ms-end-of-clusterchain*)
                       fat32-in-memory))
         ((unless (> (length dir-contents) 0))
          (mv fat32-in-memory 0))
         ((mv fat32-in-memory & error-code &)
          (place-contents fat32-in-memory (dir-ent-fix nil)
                          dir-contents 0 first-cluster))
         ((when (equal error-code 0))
          (mv fat32-in-memory 0))
         ;; Reversing the effects of clear-clusterchain
         (fat32-in-memory (stobj-set-indices-in-fa-table
                           fat32-in-memory clusterchain
                           (append (cdr clusterchain)
                                   (list last-value)))))
      (mv fat32-in-memory error-code)))

  (defthm natp-of-update-dir-contents
    (natp (mv-nth 1
                  (update-dir-contents fat32-in-memory
                                       first-cluster dir-contents)))
    :rule-classes :type-prescription
    :hints (("goal" :in-theory (enable update-dir-contents))))

  (defund
    make-empty-subdir-contents
    (current-dir-first-cluster parent-dir-first-cluster)
    (declare (xargs :guard (and
                            (fat32-masked-entry-p current-dir-first-cluster)
                            (fat32-masked-entry-p parent-dir-first-cluster))))
    (nats=>string
     (append (dir-ent-set-first-cluster-file-size
              (dir-ent-set-filename (dir-ent-fix nil)
                                    *current-dir-fat32-name*)
              current-dir-first-cluster 0)
             (dir-ent-set-first-cluster-file-size
              (dir-ent-set-filename (dir-ent-fix nil)
                                    *parent-dir-fat32-name*)
              parent-dir-first-cluster 0))))

  ;; Nonrecursive part.
  (defund lofat-place-file-helper
    (fat32-in-memory root-dir-ent path file)
    (declare
     (xargs
      :guard (and (lofat-fs-p fat32-in-memory)
                  (dir-ent-p root-dir-ent)
                  (>= (dir-ent-first-cluster root-dir-ent) *ms-first-data-cluster*)
                  (< (dir-ent-first-cluster root-dir-ent)
                     (+ *ms-first-data-cluster*
                        (count-of-clusters fat32-in-memory)))
                  (fat32-filename-list-p path)
                  (lofat-file-p file)
                  (or (lofat-regular-file-p file)
                      (equal (lofat-file->contents file) nil)))
      :stobjs fat32-in-memory
      :verify-guards nil))
    (b* (((unless (consp path)) (mv fat32-in-memory *enoent*))
         ;; Design choice - calls which ask for the entire root directory to be affected will fail.
         (name (mbe :logic (fat32-filename-fix (car path)) :exec (car path)))
         ((mv dir-contents &) (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
         (dir-ent-list (make-dir-ent-list dir-contents))
         ((mv dir-ent error-code) (find-dir-ent dir-ent-list name))
         ;; If it's not there, it's a new file. In either case, though, we shouldn't give it the name
         ;; of the old file, that is, we shouldn't be inserting a directory entry with the name of
         ;; the old file. We may be moving a file and changing its name in the process.
         (dir-ent (if (equal error-code 0) dir-ent
                    (make-dir-ent-with-filename name)))
         (dir-ent (if (equal error-code 0) dir-ent
                    (dir-ent-install-directory-bit dir-ent (lofat-directory-file-p file))))
         ;; ENOTDIR - can't act on anything that supposedly exists inside a regular file.
         ((when (and (consp (cdr path)) (not (dir-ent-directory-p dir-ent))))
          (mv fat32-in-memory *enotdir*))
         (first-cluster (dir-ent-first-cluster dir-ent))
         ((when (and (or (< first-cluster 2)
                         (<= (+ 2 (count-of-clusters fat32-in-memory)) first-cluster))
                     (consp (cdr path))))
          (mv fat32-in-memory *eio*))
         ;; After these conditionals, the only remaining possibility is that (cdr path)
         ;; is an atom, which means we need to place a regular file or an empty directory, which
         ;; we have now ensured in the guard.
         (length (if (dir-ent-directory-p dir-ent) *ms-max-dir-size* (dir-ent-file-size dir-ent)))
         ;; Replacing a directory with a regular file is not permitted.
         ((when (or (and (dir-ent-directory-p dir-ent)
                         (lofat-regular-file-p file))
                    (and (not (dir-ent-directory-p dir-ent))
                         (lofat-directory-file-p file))))
          (mv fat32-in-memory *enoent*))
         ((mv fat32-in-memory &)
          (if (or (< first-cluster 2) (<= (+ 2 (count-of-clusters fat32-in-memory)) first-cluster))
              (mv fat32-in-memory 0) (clear-clusterchain fat32-in-memory first-cluster length)))
         ;; We're going to have to refer to two different values of file-length:
         ;; one which refers to how much space we need to allocate, which will be
         ;; non-zero for directories (remember, we're not adding any root
         ;; directories lol so we need to have dot and dotdot entries) and
         ;; another which refers to the filesize field in the directory entry,
         ;; which will be zero for directories.
         (file-length (if (lofat-regular-file-p file)
                          (length (lofat-file->contents file))
                        ;; 32 bytes for dot, 32 bytes for dotdot.
                        (+ *ms-dir-ent-length* *ms-dir-ent-length*)))
         ;; Note, this value of new-dir-contents only gets used when file-length
         ;; is zero - an empty regular file.
         (new-dir-contents
          (nats=>string (insert-dir-ent (string=>nats dir-contents)
                                        (dir-ent-set-first-cluster-file-size dir-ent 0 0))))
         ((when (and (zp file-length) (<= (length new-dir-contents) *ms-max-dir-size*)))
          (update-dir-contents fat32-in-memory (dir-ent-first-cluster root-dir-ent)
                               new-dir-contents))
         ((when (zp file-length)) (mv fat32-in-memory *enospc*))
         (indices (stobj-find-n-free-clusters fat32-in-memory 1))
         ((when (< (len indices) 1)) (mv fat32-in-memory *enospc*))
         (first-cluster (nth 0 indices))
         ;; Mark this cluster as used, without possibly interfering with any
         ;; existing clusterchains.
         (fat32-in-memory (update-fati first-cluster (fat32-update-lower-28
                                                      (fati first-cluster fat32-in-memory)
                                                      *ms-end-of-clusterchain*)
                                       fat32-in-memory))
         (contents (if (lofat-regular-file-p file) (lofat-file->contents file)
                     ;; Our guard ensures that the contents of this directory
                     ;; file are empty - so the only thing here is to add a dot
                     ;; entry and a dotdot entry.
                     (make-empty-subdir-contents first-cluster
                                                 (dir-ent-first-cluster root-dir-ent))))
         ;; OK, we've been done with the previous value of file-length for a
         ;; while. Now, we need a value that's going in the directory entry.
         (file-length (if (lofat-regular-file-p file) (length contents) 0))
         ((mv fat32-in-memory dir-ent error-code &)
          (place-contents fat32-in-memory dir-ent contents file-length first-cluster))
         ((unless (zp error-code)) (mv fat32-in-memory error-code))
         (new-dir-contents (nats=>string (insert-dir-ent (string=>nats dir-contents) dir-ent)))
         ((unless (<= (length new-dir-contents) *ms-max-dir-size*)) (mv fat32-in-memory *enospc*)))
      (update-dir-contents
       fat32-in-memory
       (dir-ent-first-cluster root-dir-ent)
       new-dir-contents)))

  (defund
      lofat-place-file-alt
      (fat32-in-memory root-dir-ent path file)
    (declare
     (xargs
      :guard (and (lofat-fs-p fat32-in-memory)
                  (dir-ent-p root-dir-ent)
                  (>= (dir-ent-first-cluster root-dir-ent) *ms-first-data-cluster*)
                  (< (dir-ent-first-cluster root-dir-ent)
                     (+ *ms-first-data-cluster*
                        (count-of-clusters fat32-in-memory)))
                  (fat32-filename-list-p path)
                  (lofat-file-p file)
                  (or (lofat-regular-file-p file)
                      (equal (lofat-file->contents file) nil)))
      :measure (acl2-count path)
      :stobjs fat32-in-memory
      :verify-guards nil))
    (b* (((unless (consp path))
          (lofat-place-file-helper
           fat32-in-memory root-dir-ent path file))
         ;; Design choice - calls which ask for the entire root directory to be affected will fail.
         (name (mbe :logic (fat32-filename-fix (car path)) :exec (car path)))
         ((mv dir-contents &) (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
         (dir-ent-list (make-dir-ent-list dir-contents))
         ((mv dir-ent error-code) (find-dir-ent dir-ent-list name))
         ;; If it's not there, it's a new file. In either case, though, we shouldn't give it the name
         ;; of the old file, that is, we shouldn't be inserting a directory entry with the name of
         ;; the old file. We may be moving a file and changing its name in the process.
         (dir-ent (if (equal error-code 0) dir-ent
                    (make-dir-ent-with-filename name)))
         (dir-ent (if (equal error-code 0) dir-ent
                    (dir-ent-install-directory-bit dir-ent (lofat-directory-file-p file))))
         ;; ENOTDIR - can't act on anything that supposedly exists inside a regular file.
         ((when (and (consp (cdr path)) (not (dir-ent-directory-p dir-ent))))
          (lofat-place-file-helper
           fat32-in-memory root-dir-ent path file))
         (first-cluster (dir-ent-first-cluster dir-ent))
         ((when (and (or (< first-cluster 2)
                         (<= (+ 2 (count-of-clusters fat32-in-memory)) first-cluster))
                     (consp (cdr path))))
          (lofat-place-file-helper
           fat32-in-memory root-dir-ent path file))
         ;; Recursion
         ((when (consp(cdr path)))
          (lofat-place-file-alt fat32-in-memory dir-ent (cdr path) file)))
      (lofat-place-file-helper
       fat32-in-memory root-dir-ent path file)))

  (local
   (defthm
     lofat-place-file-alt-correctness-1
     (equal
      (lofat-place-file-alt
       fat32-in-memory root-dir-ent path file)
      (lofat-place-file
       fat32-in-memory root-dir-ent path file))
     :hints
     (("Goal"
       :in-theory
       (enable lofat-place-file-alt lofat-place-file-helper)
       :induct
       (lofat-place-file
        fat32-in-memory root-dir-ent path file)))))

  (defund good-root-dir-ent-p (root-dir-ent fat32-in-memory)
    (declare (xargs :stobjs fat32-in-memory))
    (b*
        (((unless (and (lofat-fs-p fat32-in-memory)
                       (dir-ent-p root-dir-ent)
                       (dir-ent-directory-p root-dir-ent)
                       (<= *ms-first-data-cluster* (dir-ent-first-cluster root-dir-ent))
                       (< (dir-ent-first-cluster root-dir-ent)
                          (+ *ms-first-data-cluster* (count-of-clusters fat32-in-memory)))))
          nil)
         ((mv & error-code) (dir-ent-clusterchain-contents fat32-in-memory
                                                           root-dir-ent))
         ((mv clusterchain &)
          (dir-ent-clusterchain fat32-in-memory root-dir-ent)))
      (and (equal error-code 0)
           (no-duplicatesp-equal clusterchain))))

  (defthm
    lofat-find-file-correctness-1-lemma-5
    (implies
     (and (useful-dir-ent-list-p dir-ent-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper
                          fat32-in-memory
                          dir-ent-list entry-limit))
                 0))
     (equal
      (m1-directory-file-p
       (cdr
        (assoc-equal name
                     (mv-nth 0
                             (lofat-to-hifat-helper
                              fat32-in-memory
                              dir-ent-list entry-limit)))))
      (dir-ent-directory-p
       (mv-nth 0
               (find-dir-ent dir-ent-list name)))))
    :hints
    (("goal" :in-theory (enable lofat-to-hifat-helper
                                m1-directory-file-p))))

  (defthm
    lofat-remove-file-correctness-lemma-26
    (implies
     (and
      (good-root-dir-ent-p root-dir-ent fat32-in-memory)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         entry-limit))
       0)
      (dir-ent-directory-p
       (mv-nth
        0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         name))))
     (good-root-dir-ent-p
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        name))
      fat32-in-memory))
    :hints
    (("goal" :do-not-induct t
      :expand (lofat-remove-file fat32-in-memory root-dir-ent path)
      :in-theory (enable hifat-remove-file
                         (:rewrite lofat-to-hifat-inversion-lemma-4)
                         lofat-to-hifat-inversion-lemma-15
                         good-root-dir-ent-p))))

  (defthm
    lofat-find-file-correctness-1-lemma-6
    (implies
     (and (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list name)))
          (useful-dir-ent-list-p dir-ent-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit))
                 0))
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth 0 (find-dir-ent dir-ent-list name)))))
         entry-limit))
       0)
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents
                    fat32-in-memory
                    (mv-nth 0 (find-dir-ent dir-ent-list name)))))
          entry-limit)))
       entry-limit)))
    :hints
    (("goal"
      :induct (mv (mv-nth 3
                          (lofat-to-hifat-helper fat32-in-memory
                                                 dir-ent-list entry-limit))
                  (mv-nth 0 (find-dir-ent dir-ent-list name)))
      :in-theory
      (e/d (lofat-to-hifat-helper-correctness-4 lofat-to-hifat-helper)
           ((:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
            (:definition free-index-listp)
            (:rewrite nth-of-effective-fat)
            (:definition no-duplicatesp-equal)))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list name)))
            (useful-dir-ent-list-p dir-ent-list)
            (equal (mv-nth 3
                           (lofat-to-hifat-helper fat32-in-memory
                                                  dir-ent-list entry-limit))
                   0))
       (equal
        (mv-nth
         3
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents
                    fat32-in-memory
                    (mv-nth 0 (find-dir-ent dir-ent-list name)))))
          entry-limit))
        0)))
     (:linear
      :corollary
      (implies
       (and (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list name)))
            (useful-dir-ent-list-p dir-ent-list)
            (equal (mv-nth 3
                           (lofat-to-hifat-helper fat32-in-memory
                                                  dir-ent-list entry-limit))
                   0))
       (<
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32-in-memory
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents
                     fat32-in-memory
                     (mv-nth 0 (find-dir-ent dir-ent-list name)))))
           entry-limit)))
        entry-limit)))
     (:forward-chaining
      :corollary
      (implies
       (and (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list name)))
            (useful-dir-ent-list-p dir-ent-list)
            (equal (mv-nth 3
                           (lofat-to-hifat-helper fat32-in-memory
                                                  dir-ent-list entry-limit))
                   0))
       (equal
        (mv-nth
         3
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents
                    fat32-in-memory
                    (mv-nth 0 (find-dir-ent dir-ent-list name)))))
          entry-limit))
        0))
      :trigger-terms
      ((lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0 (find-dir-ent dir-ent-list name)))))
        entry-limit)))))

  (defthm
    lofat-place-file-correctness-lemma-61
    (implies
     (and (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit))
                 0)
          (useful-dir-ent-list-p dir-ent-list)
          ;; This hypothesis might be removable.
          (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list name))))
     (subsetp-equal
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0 (find-dir-ent dir-ent-list name)))))
        entry-limit))
      (mv-nth 2
              (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (find-dir-ent lofat-to-hifat-helper hifat-entry-count
                     lofat-to-hifat-helper-correctness-4)
       ((:rewrite
         dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-13
         . 1)
        (:rewrite nth-of-effective-fat)
        (:rewrite nth-of-nats=>chars)
        (:linear nth-when-dir-ent-p)
        (:rewrite lofat-place-file-correctness-1-lemma-13)
        (:rewrite lofat-place-file-correctness-1-lemma-14)
        (:rewrite nfix-when-zp)
        (:rewrite explode-of-dir-ent-filename)
        (:rewrite
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent-lemma-3)
        (:rewrite dir-ent-p-when-member-equal-of-dir-ent-list-p))))))

  (defthm
    lofat-to-hifat-helper-after-delete-and-clear-1-lemma-1
    (implies
     (and (useful-dir-ent-list-p dir-ent-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit))
                 0)
          (dir-ent-directory-p (mv-nth 0
                                       (find-dir-ent dir-ent-list filename))))
     (and
      (<= *ms-first-data-cluster*
          (dir-ent-first-cluster (mv-nth 0
                                         (find-dir-ent dir-ent-list filename))))
      (< (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
         (+ *ms-first-data-cluster*
            (count-of-clusters fat32-in-memory)))))
    :rule-classes :linear
    :hints (("goal" :in-theory (enable lofat-to-hifat-helper))))

  (defthm
    dir-ent-clusterchain-contents-of-lofat-place-file-alt-coincident-1
    (b*
        (((mv clusterchain-contents error-code)
          (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
         (new-dir-ent
          (if
           (< 0
              (len (explode (lofat-file->contents file))))
           (if
            (<=
             2
             (dir-ent-first-cluster
              (mv-nth
               0
               (find-dir-ent
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                (car path)))))
            (if
             (<
              (dir-ent-first-cluster
               (mv-nth
                0
                (find-dir-ent
                 (make-dir-ent-list
                  (mv-nth 0
                          (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                 (car path))))
              (+ 2 (count-of-clusters fat32-in-memory)))
             (dir-ent-set-first-cluster-file-size
              (mv-nth
               0
               (find-dir-ent
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                (car path)))
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32-in-memory)
                 (mv-nth
                  0
                  (dir-ent-clusterchain
                   fat32-in-memory
                   (mv-nth
                    0
                    (find-dir-ent
                     (make-dir-ent-list
                      (mv-nth
                       0
                       (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                     (car path)))))
                 (make-list-ac
                  (len
                   (mv-nth
                    0
                    (dir-ent-clusterchain
                     fat32-in-memory
                     (mv-nth
                      0
                      (find-dir-ent
                       (make-dir-ent-list
                        (mv-nth
                         0
                         (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                       (car path))))))
                  0 nil))
                1))
              (len (explode (lofat-file->contents file))))
             (dir-ent-set-first-cluster-file-size
              (mv-nth
               0
               (find-dir-ent
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                (car path)))
              (nth 0
                   (find-n-free-clusters (effective-fat fat32-in-memory)
                                         1))
              (len (explode (lofat-file->contents file)))))
            (if
             (equal
              (mv-nth
               1
               (find-dir-ent
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                (car path)))
              0)
             (dir-ent-set-first-cluster-file-size
              (mv-nth
               0
               (find-dir-ent
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                (car path)))
              (nth 0
                   (find-n-free-clusters (effective-fat fat32-in-memory)
                                         1))
              (len (explode (lofat-file->contents file))))
             (dir-ent-set-first-cluster-file-size
              (dir-ent-install-directory-bit
               (make-dir-ent-with-filename (car path))
               nil)
              (nth 0
                   (find-n-free-clusters (effective-fat fat32-in-memory)
                                         1))
              (len (explode (lofat-file->contents file))))))
           (if
            (equal
             (mv-nth
              1
              (find-dir-ent
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
               (car path)))
             0)
            (dir-ent-set-first-cluster-file-size
             (mv-nth
              0
              (find-dir-ent
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
               (car path)))
             0 0)
            (dir-ent-set-first-cluster-file-size
             (dir-ent-install-directory-bit (make-dir-ent-with-filename (car path))
                                            nil)
             0 0))))
         (new-contents
          (nats=>chars (insert-dir-ent (string=>nats clusterchain-contents)
                                       new-dir-ent))))
      (implies
       (and
        (lofat-fs-p fat32-in-memory)
        (dir-ent-p dir-ent)
        (dir-ent-directory-p dir-ent)
        (fat32-filename-list-p path)
        (equal error-code 0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper fat32-in-memory
                                        (make-dir-ent-list clusterchain-contents)
                                        entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory dir-ent))
         (mv-nth 2
                 (lofat-to-hifat-helper fat32-in-memory
                                        (make-dir-ent-list clusterchain-contents)
                                        entry-limit)))
        (not
         (<
          '2097152
          (binary-+
           '32
           (len
            (explode$inline
             (mv-nth
              '0
              (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))))))
        (equal (mv-nth 1
                       (lofat-place-file-alt fat32-in-memory dir-ent path file))
               0)
        (lofat-regular-file-p file))
       (equal
        (dir-ent-clusterchain-contents
         (mv-nth 0
                 (lofat-place-file-alt fat32-in-memory dir-ent path file))
         dir-ent)
        (if
         (atom (cdr path))
         (mv
          (implode
           (append
            new-contents
            (make-list-ac
             (- (* (cluster-size fat32-in-memory)
                   (len (make-clusters (implode new-contents)
                                       (cluster-size fat32-in-memory))))
                (len new-contents))
             (code-char 0)
             nil)))
          0)
         (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))))
    :instructions
    (:expand
     :expand
     :expand :expand :promote (:dive 1 1 2)
     (:rewrite lofat-place-file-alt-correctness-1)
     :top (:dive 1)
     (:claim
      (and (equal (mv-nth 1
                          (lofat-place-file fat32-in-memory dir-ent path file))
                  0))
      :hints :none)
     (:rewrite dir-ent-clusterchain-contents-of-lofat-place-file-coincident-1)
     :top
     :bash :bash))

  (defthm lofat-place-file-correctness-lemma-1
    (implies (good-root-dir-ent-p root-dir-ent fat32-in-memory)
             (and
              (dir-ent-p root-dir-ent)
              (dir-ent-directory-p root-dir-ent)
              (lofat-fs-p fat32-in-memory)
              (>= (dir-ent-first-cluster root-dir-ent) *ms-first-data-cluster*)
              (< (dir-ent-first-cluster root-dir-ent)
                 (binary-+ '2
                           (count-of-clusters fat32-in-memory)))))
    :hints (("goal" :do-not-induct t
             :in-theory (enable good-root-dir-ent-p)))
    :rule-classes :forward-chaining)

  (defthm
    lofat-place-file-correctness-lemma-5
    (implies
     (good-root-dir-ent-p root-dir-ent fat32-in-memory)
     (equal
      (mv-nth 1
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
      0))
    :hints (("goal" :do-not-induct t
             :in-theory (enable good-root-dir-ent-p))))

  (defthm
    len-of-insert-dir-ent
    (equal
     (len (insert-dir-ent dir-contents dir-ent))
     (* 32
        (+ 2
           (len (place-dir-ent (make-dir-ent-list (nats=>string dir-contents))
                               dir-ent)))))
    :hints (("goal" :in-theory (e/d (insert-dir-ent len-when-dir-ent-p)))))

  (defthm
    len-of-place-dir-ent
    (equal
     (len (place-dir-ent dir-ent-list dir-ent))
     (if (zp (mv-nth 1
                     (find-dir-ent dir-ent-list
                                   (dir-ent-filename dir-ent))))
         (len dir-ent-list)
       (+ 1 (len dir-ent-list))))))

;; Copied from natp-of-lofat-place-file.
(defthm natp-of-lofat-place-file-helper
  (natp (mv-nth 1
                (lofat-place-file-helper fat32-in-memory
                                      root-dir-ent path file)))
  :hints (("Goal" :in-theory (enable lofat-place-file-helper)))
  :rule-classes :type-prescription)
(defthm natp-of-lofat-place-file-alt
  (natp (mv-nth 1
                (lofat-place-file-alt fat32-in-memory
                                      root-dir-ent path file)))
  :hints (("Goal" :in-theory (enable lofat-place-file-alt)))
  :rule-classes :type-prescription)

(defthm
  lofat-place-file-alt-correctness-1-lemma-2
  (implies
   (atom path)
   (equal (lofat-place-file-helper fat32-in-memory root-dir-ent path file)
          (mv fat32-in-memory *enoent*)))
  :hints (("goal" :in-theory (enable lofat-place-file-helper))))

(encapsulate
  ()

  (local
   (defun-nx
     induction-scheme
     (entry-limit fat32-in-memory
                  file path root-dir-ent x)
     (cond
      ((and
        (consp path)
        (consp
         (assoc-equal
          (fat32-filename-fix (car path))
          (hifat-file-alist-fix
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32-in-memory
             (make-dir-ent-list
              (mv-nth 0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory root-dir-ent)))
             entry-limit)))))
        (m1-directory-file-p
         (cdr
          (assoc-equal
           (fat32-filename-fix (car path))
           (hifat-file-alist-fix
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32-in-memory
              (make-dir-ent-list
               (mv-nth 0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory root-dir-ent)))
              entry-limit)))))))
       (induction-scheme
        entry-limit
        fat32-in-memory file (cdr path)
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents
                    fat32-in-memory root-dir-ent)))
          (car path)))
        (append
         x
         (flatten
          (set-difference-equal
           (mv-nth 2
                   (lofat-to-hifat-helper
                    fat32-in-memory
                    (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory root-dir-ent)))
                    entry-limit))
           (mv-nth 2
                   (lofat-to-hifat-helper
                    fat32-in-memory
                    (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory (mv-nth
                                               0
                                               (find-dir-ent
                                                (make-dir-ent-list
                                                 (mv-nth 0
                                                         (dir-ent-clusterchain-contents
                                                          fat32-in-memory root-dir-ent)))
                                                (car path))))))
                    entry-limit)))))))
      (t (mv entry-limit fat32-in-memory
             file path root-dir-ent x)))))

  (defthm
    lofat-place-file-alt-correctness-1-lemma-1
    (implies
     (and
      (good-root-dir-ent-p root-dir-ent fat32-in-memory)
      (non-free-index-listp x (effective-fat fat32-in-memory))
      (fat32-filename-list-p path)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory root-dir-ent)))
         entry-limit))
       0)
      (not-intersectp-list
       (mv-nth 0
               (dir-ent-clusterchain fat32-in-memory root-dir-ent))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory root-dir-ent)))
         entry-limit)))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory root-dir-ent)))
         entry-limit)))
      (lofat-file-p file)
      (or
       (and
        (lofat-regular-file-p file)
        (<= (len (make-clusters (lofat-file->contents file)
                                (cluster-size fat32-in-memory)))
            (count-free-clusters (effective-fat fat32-in-memory))))
       (and
        (equal (lofat-file->contents file) nil)
        (<= 1
            (count-free-clusters (effective-fat fat32-in-memory)))))
      (zp (mv-nth 1
                  (lofat-place-file-alt fat32-in-memory
                                    root-dir-ent path file)))
      (integerp entry-limit)
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents
                    fat32-in-memory root-dir-ent)))
          entry-limit)))
       entry-limit)
      t)
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-place-file-alt fat32-in-memory root-dir-ent path file))
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents
            (mv-nth 0
                    (lofat-place-file-alt
                     fat32-in-memory root-dir-ent path file))
            root-dir-ent)))
         entry-limit))
       0)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-place-file-alt fat32-in-memory root-dir-ent path file))
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents
            (mv-nth 0
                    (lofat-place-file-alt
                     fat32-in-memory root-dir-ent path file))
            root-dir-ent)))
         entry-limit)))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-place-file-alt fat32-in-memory root-dir-ent path file))
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents
            (mv-nth 0
                    (lofat-place-file-alt
                     fat32-in-memory root-dir-ent path file))
            root-dir-ent)))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32-in-memory
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents
                     fat32-in-memory root-dir-ent)))
           entry-limit))
         path
         (m1-file dir-ent (lofat-file->contents file)))))))
   :hints
   (("goal"
     :induct
     (induction-scheme
      entry-limit fat32-in-memory file path root-dir-ent x)
     :in-theory (e/d (lofat-place-file-alt)
                     ())))))
