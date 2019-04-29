(in-package "ACL2")

;  hifat-to-lofat-inversion.lisp                        Mihir Mehta

; This is a proof of the invertibility of the hifat-to-lofat transformation as
; well as its inverse transformation lofat-to-hifat.

(include-book "generate-index-list")
(include-book "m1-entry-count")
(include-book "update-data-region")

;; These are some rules from other books which are either interacting badly
;; with the theory I've built up so far, or else causing a lot of unnecessary
;; frames and tries.
(local
 (in-theory (disable take-of-too-many make-list-ac-removal
                     revappend-removal str::hex-digit-listp-of-cons
                     loghead logtail)))

(local
 (in-theory (disable nth update-nth floor mod true-listp)))

(defund
  get-clusterchain
  (fat32-in-memory masked-current-cluster length)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :measure (nfix length)
    :guard (and (lofat-fs-p fat32-in-memory)
                (fat32-masked-entry-p masked-current-cluster)
                (natp length)
                (>= masked-current-cluster
                    *ms-first-data-cluster*)
                (< masked-current-cluster
                   (+ (count-of-clusters fat32-in-memory)
                      *ms-first-data-cluster*)))))
  (b*
      ((cluster-size (cluster-size fat32-in-memory))
       ((when
            (or (zp length) (zp cluster-size)))
        (mv nil (- *eio*)))
       (masked-next-cluster
        (fat32-entry-mask
         (if (mbt (< (nfix masked-current-cluster)
                     (nfix (+ (count-of-clusters fat32-in-memory)
                              *ms-first-data-cluster*))))
             (fati masked-current-cluster fat32-in-memory)
           nil)))
       ((when
            (< masked-next-cluster
               *ms-first-data-cluster*))
        (mv (list masked-current-cluster)
            (- *eio*)))
       ((when
            (or
             (fat32-is-eof masked-next-cluster)
             (>=
              masked-next-cluster
              (mbe
               :exec (+ (count-of-clusters fat32-in-memory)
                        *ms-first-data-cluster*)
               :logic (nfix (+ (count-of-clusters fat32-in-memory)
                               *ms-first-data-cluster*))))))
        (mv (list masked-current-cluster) 0))
       ((mv tail-index-list tail-error)
        (get-clusterchain fat32-in-memory masked-next-cluster
                          (nfix (- length cluster-size)))))
    (mv (list* masked-current-cluster tail-index-list)
        tail-error)))

(defund-nx
  effective-fat (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (lofat-fs-p fat32-in-memory)
          :guard-hints
          (("goal" :in-theory (enable fat32-in-memoryp)))))
  (take (+ (count-of-clusters fat32-in-memory)
           *ms-first-data-cluster*)
        (nth *fati* fat32-in-memory)))

(defthm len-of-effective-fat
  (equal (len (effective-fat fat32-in-memory))
         (nfix (+ (count-of-clusters fat32-in-memory)
                  *ms-first-data-cluster*)))
  :hints (("goal" :in-theory (enable effective-fat))))

(defthm
  fat32-entry-list-p-of-effective-fat
  (implies (and (fat32-in-memoryp fat32-in-memory)
                (<= (+ (count-of-clusters fat32-in-memory)
                       *ms-first-data-cluster*)
                    (fat-length fat32-in-memory)))
           (fat32-entry-list-p (effective-fat fat32-in-memory)))
  :hints
  (("goal" :in-theory (enable effective-fat
                              fat-length fat32-in-memoryp)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (lofat-fs-p fat32-in-memory)
             (fat32-entry-list-p (effective-fat fat32-in-memory))))))

(defthm
  nth-of-effective-fat
  (equal (nth n (effective-fat fat32-in-memory))
         (if (< (nfix n)
                (nfix (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*)))
             (fati n fat32-in-memory)
             nil))
  :hints (("goal" :in-theory (enable fati effective-fat nth))))

(defthm
  effective-fat-of-update-data-regioni
  (equal
   (effective-fat (update-data-regioni i v fat32-in-memory))
   (effective-fat fat32-in-memory))
  :hints (("goal" :in-theory (enable effective-fat))))

(defthm
  effective-fat-of-update-fati
  (equal (effective-fat (update-fati i v fat32-in-memory))
         (if (< (nfix i)
                (+ (count-of-clusters fat32-in-memory)
                   *ms-first-data-cluster*))
             (update-nth i v (effective-fat fat32-in-memory))
             (effective-fat fat32-in-memory)))
  :hints (("goal" :in-theory (enable effective-fat update-fati)
           :do-not-induct t)))

(encapsulate
  ()

  ;; Avoid a subinduction.
  (local
   (defthm
     get-clusterchain-alt-lemma-1
     (implies
      (and (not (zp length))
           (integerp (cluster-size fat32-in-memory))
           (< 0 (cluster-size fat32-in-memory))
           (integerp masked-current-cluster)
           (<= 0 masked-current-cluster)
           (<= (+ 2 (count-of-clusters fat32-in-memory))
               masked-current-cluster))
      (equal (fat32-build-index-list
              (take (+ 2 (count-of-clusters fat32-in-memory))
                    (nth *fati* fat32-in-memory))
              masked-current-cluster
              length (cluster-size fat32-in-memory))
             (mv (list masked-current-cluster)
                 (- *eio*))))))

  (defthm
    get-clusterchain-alt
    (equal (get-clusterchain fat32-in-memory
                             masked-current-cluster length)
           (fat32-build-index-list
            (effective-fat fat32-in-memory)
            masked-current-cluster
            length (cluster-size fat32-in-memory)))
    :rule-classes :definition
    :hints
    (("goal" :in-theory (enable get-clusterchain
                                fati fat-length effective-fat nth)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defun
      get-contents-from-clusterchain
      (fat32-in-memory clusterchain file-size)
    (declare
     (xargs
      :stobjs (fat32-in-memory)
      :guard
      (and
       (lofat-fs-p fat32-in-memory)
       (equal (data-region-length fat32-in-memory)
              (count-of-clusters fat32-in-memory))
       (fat32-masked-entry-list-p clusterchain)
       (natp file-size)
       (bounded-nat-listp clusterchain
                          (count-of-clusters fat32-in-memory))
       (lower-bounded-integer-listp
        clusterchain *ms-first-data-cluster*))))
    (if
        (atom clusterchain)
        ""
      (let*
          ((cluster-size (cluster-size fat32-in-memory))
           (masked-current-cluster (car clusterchain)))
        (concatenate
         'string
         (subseq
          (data-regioni
           (nfix (- masked-current-cluster *ms-first-data-cluster*))
           fat32-in-memory)
          0
          (min file-size cluster-size))
         (get-contents-from-clusterchain
          fat32-in-memory (cdr clusterchain)
          (nfix (- file-size cluster-size)))))))

  (defthm
    stringp-of-get-contents-from-clusterchain
    (stringp
     (get-contents-from-clusterchain
      fat32-in-memory clusterchain file-size))
    :rule-classes :type-prescription)

  (defund
    get-clusterchain-contents
    (fat32-in-memory masked-current-cluster length)
    (declare
     (xargs
      :stobjs fat32-in-memory
      :measure (nfix length)
      :guard (and (lofat-fs-p fat32-in-memory)
                  (equal (data-region-length fat32-in-memory)
                         (count-of-clusters fat32-in-memory))
                  (fat32-masked-entry-p masked-current-cluster)
                  (natp length)
                  (>= masked-current-cluster
                      *ms-first-data-cluster*)
                  (< masked-current-cluster
                     (+ (count-of-clusters fat32-in-memory)
                        *ms-first-data-cluster*)))
      :verify-guards nil))
    (b*
        ((cluster-size (cluster-size fat32-in-memory))
         ((unless (and (not (zp length))
                       (not (zp cluster-size))
                       (>= masked-current-cluster
                           *ms-first-data-cluster*)))
          (mv "" (- *eio*)))
         (current-cluster-contents
          (str-fix
           (data-regioni (- masked-current-cluster 2) fat32-in-memory)))
         (masked-next-cluster
          (fat32-entry-mask
           ;; This mbt (must be true) form was inserted in order to comport
           ;; with our current definition of effective-fat, which is implicitly
           ;; used in the rule get-clusterchain-contents-correctness-1.
           (if (mbt (< (nfix masked-current-cluster)
                       (nfix (+ (count-of-clusters fat32-in-memory)
                                *ms-first-data-cluster*))))
               (fati masked-current-cluster fat32-in-memory)
             nil)))
         ((unless (>= masked-next-cluster
                      *ms-first-data-cluster*))
          (mv (subseq current-cluster-contents 0 (min length cluster-size))
              (- *eio*)))
         ((unless (and (not (fat32-is-eof masked-next-cluster))
                       (< masked-next-cluster
                          (+ (count-of-clusters fat32-in-memory)
                             *ms-first-data-cluster*))))
          (mv (subseq current-cluster-contents 0 (min length cluster-size)) 0))
         ((mv tail-string tail-error)
          (get-clusterchain-contents
           fat32-in-memory masked-next-cluster
           (nfix (- length cluster-size))))
         ((unless (equal tail-error 0))
          (mv "" (- *eio*))))
      (mv (concatenate 'string
                       current-cluster-contents
                       tail-string)
          0)))

  (defthm
    integerp-of-get-clusterchain-contents
    (and
     (integerp (mv-nth 1
                       (get-clusterchain-contents
                        fat32-in-memory
                        masked-current-cluster length)))
     (>= 0
         (mv-nth 1
                 (get-clusterchain-contents
                  fat32-in-memory
                  masked-current-cluster length))))
    :rule-classes
    ((:type-prescription
      :corollary
      (integerp (mv-nth 1
                        (get-clusterchain-contents
                         fat32-in-memory
                         masked-current-cluster length))))
     (:linear :corollary
              (>= 0
                  (mv-nth 1
                          (get-clusterchain-contents
                           fat32-in-memory
                           masked-current-cluster length)))))
    :hints
    (("goal" :in-theory (enable get-clusterchain-contents)))))

(defthm
  stringp-of-get-clusterchain-contents
  (stringp
   (mv-nth
    0
    (get-clusterchain-contents fat32-in-memory
                               masked-current-cluster length)))
  :rule-classes :type-prescription
  :hints
  (("goal" :in-theory (enable get-clusterchain-contents))))

(verify-guards get-clusterchain-contents)


(defthm
  get-clusterchain-contents-correctness-2
  (implies
   (>= masked-current-cluster
       *ms-first-data-cluster*)
   (equal (mv-nth 1
                  (fat32-build-index-list
                   (effective-fat fat32-in-memory)
                   masked-current-cluster
                   length (cluster-size fat32-in-memory)))
          (mv-nth 1
                  (get-clusterchain-contents
                   fat32-in-memory
                   masked-current-cluster length))))
  :hints
  (("goal" :in-theory
    (e/d (fat-length fati effective-fat
                     nth get-clusterchain-contents)))))

(defthm
  get-contents-from-clusterchain-of-update-data-regioni
  (implies
   (and (integerp file-size)
        (lofat-fs-p fat32-in-memory)
        (equal (data-region-length fat32-in-memory)
               (count-of-clusters fat32-in-memory))
        (natp i)
        (not (member-equal (+ i *ms-first-data-cluster*)
                           clusterchain))
        (lower-bounded-integer-listp
         clusterchain *ms-first-data-cluster*))
   (equal
    (get-contents-from-clusterchain
     (update-data-regioni i v fat32-in-memory)
     clusterchain file-size)
    (get-contents-from-clusterchain fat32-in-memory
                                    clusterchain file-size))))

(defthm
  get-clusterchain-contents-correctness-1
  (implies
   (and
    (fat32-masked-entry-p masked-current-cluster)
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth
      1
      (get-clusterchain-contents fat32-in-memory
                                 masked-current-cluster length))
     0))
   (equal
    (get-contents-from-clusterchain
     fat32-in-memory
     (mv-nth 0
             (get-clusterchain fat32-in-memory
                               masked-current-cluster length))
     length)
    (mv-nth 0
            (get-clusterchain-contents
             fat32-in-memory
             masked-current-cluster length))))
  :hints
  (("goal" :in-theory (enable get-clusterchain-contents)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (fat32-masked-entry-p masked-current-cluster)
      (>= masked-current-cluster
          *ms-first-data-cluster*)
      (lofat-fs-p fat32-in-memory)
      (equal
       (mv-nth 1
               (fat32-build-index-list
                (effective-fat fat32-in-memory)
                masked-current-cluster
                length (cluster-size fat32-in-memory)))
       0))
     (equal
      (get-contents-from-clusterchain
       fat32-in-memory
       (mv-nth 0
               (fat32-build-index-list
                (effective-fat fat32-in-memory)
                masked-current-cluster
                length (cluster-size fat32-in-memory)))
       length)
      (mv-nth 0
              (get-clusterchain-contents
               fat32-in-memory
               masked-current-cluster length)))))))

(defthm
  get-clusterchain-contents-correctness-3
  (equal
   (mv
    (mv-nth
     0
     (get-clusterchain-contents fat32-in-memory
                                masked-current-cluster length))
    (mv-nth
     1
     (get-clusterchain-contents fat32-in-memory
                                masked-current-cluster length)))
   (get-clusterchain-contents fat32-in-memory
                              masked-current-cluster length))
  :hints (("Goal" :in-theory (enable get-clusterchain-contents)) ))

(defthm
  length-of-get-clusterchain-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (natp length))
   (<=
    (len (explode (mv-nth 0
                          (get-clusterchain-contents
                           fat32-in-memory
                           masked-current-cluster length))))
    length))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable get-clusterchain-contents)) ))

;; The following is not a theorem, because we took our error codes, more or
;; less, from fs/fat/cache.c, and there the length is not taken into account
;; while returning error codes (or not). Thus, it's possible to return an error
;; code of 0 without conforming to the length.
;; (defthm len-of-get-clusterchain-contents
;;   (b*
;;       (((mv contents error-code)
;;         (get-clusterchain-contents fat32-in-memory masked-current-cluster length)))
;;     (implies
;;      (equal error-code 0)
;;      (equal (length contents) length))))

;; Here's the idea: while transforming from M2 to M1,
;; - we are not going to to take directory entries which are deleted
;; - we are not going to take dot or dotdot entries
(defund
  useless-dir-ent-p (dir-ent)
  (declare
   (xargs
    :guard (dir-ent-p dir-ent)
    :guard-hints
    (("goal" :in-theory (e/d (dir-ent-p dir-ent-first-cluster)
                             (unsigned-byte-p))))))
  (or
   ;; the byte #xe5 marks deleted files, according to the spec
   (equal (nth 0 dir-ent) #xe5)
   (equal (dir-ent-filename dir-ent)
          *current-dir-fat32-name*)
   (equal (dir-ent-filename dir-ent)
          *parent-dir-fat32-name*)))

(defthm
  useless-dir-ent-p-of-dir-ent-install-directory-bit
  (implies
   (dir-ent-p dir-ent)
   (equal (useless-dir-ent-p
           (dir-ent-install-directory-bit dir-ent val))
          (useless-dir-ent-p dir-ent)))
  :hints
  (("goal"
    :in-theory (enable dir-ent-install-directory-bit
                       useless-dir-ent-p dir-ent-filename))))

(defthm
  useless-dir-ent-p-of-dir-ent-set-filename
  (implies (and (fat32-filename-p filename)
                (dir-ent-p dir-ent))
           (not (useless-dir-ent-p
                 (dir-ent-set-filename dir-ent filename))))
  :hints (("goal" :in-theory (enable useless-dir-ent-p))))

(defund
  make-dir-ent-list (dir-contents)
  (declare
   (xargs
    :guard (unsigned-byte-listp 8 dir-contents)
    :measure (len dir-contents)
    :guard-hints (("goal" :in-theory (enable dir-ent-p)))))
  (b* (((when (< (len dir-contents)
                 *ms-dir-ent-length*))
        nil)
       (dir-ent
        (mbe
         :exec (take *ms-dir-ent-length* dir-contents)
         :logic (dir-ent-fix (take *ms-dir-ent-length* dir-contents))))
       ;; From page 24 of the specification: "If DIR_Name[0] == 0x00, then the
       ;; directory entry is free (same as for 0xE5), and there are no
       ;; allocated directory entries after this one (all of the DIR_Name[0]
       ;; bytes in all of the entries after this one are also set to 0). The
       ;; special 0 value, rather than the 0xE5 value, indicates to FAT file
       ;; system driver code that the rest of the entries in this directory do
       ;; not need to be examined because they are all free."
       ((when (equal (nth 0 dir-ent) 0)) nil)
       ((when (useless-dir-ent-p dir-ent))
        (make-dir-ent-list
         (nthcdr *ms-dir-ent-length* dir-contents))))
    (list* dir-ent
           (make-dir-ent-list
            (nthcdr *ms-dir-ent-length* dir-contents)))))

(defund useful-dir-ent-list-p (dir-ent-list)
  (declare (xargs :guard t))
  (if (atom dir-ent-list)
      (equal dir-ent-list nil)
      (and (dir-ent-p (car dir-ent-list))
           (not (equal (nth 0 (car dir-ent-list)) 0))
           (not (useless-dir-ent-p (car dir-ent-list)))
           (useful-dir-ent-list-p (cdr dir-ent-list)))))

(defthm dir-ent-list-p-when-useful-dir-ent-list-p
  (implies (useful-dir-ent-list-p dir-ent-list)
           (dir-ent-list-p dir-ent-list))
  :hints
  (("Goal" :in-theory (enable useful-dir-ent-list-p))))

(defthm
  useful-dir-ent-list-p-of-make-dir-ent-list
  (useful-dir-ent-list-p (make-dir-ent-list dir-contents))
  :hints
  (("goal"
    :in-theory (enable make-dir-ent-list useful-dir-ent-list-p))))

(defthm
  useful-dir-ent-list-p-of-cdr
  (implies (useful-dir-ent-list-p dir-ent-list)
           (useful-dir-ent-list-p (cdr dir-ent-list)))
  :hints (("goal" :in-theory (enable useful-dir-ent-list-p))))

;; Here's the idea behind this recursion: A loop could occur on a badly formed
;; FAT32 volume which has a cycle in its directory structure (for instance, if
;; / and /tmp/ were to point to the same cluster as their initial cluster.)
;; This loop could be stopped most cleanly by maintaining a list of all
;; clusters which could be visited, and checking them off as we visit more
;; entries. Then, we would detect a second visit to the same cluster, and
;; terminate with an error condition. Only otherwise would we make a recursive
;; call, and our measure - the length of the list of unvisited clusters - would
;; decrease.

;; This would probably impose performance penalties, and so there's a better
;; way which does not (good!), and also does not cleanly detect cycles in the
;; directory structure (bad.) Still, it returns exactly the same result for
;; good FAT32 volumes, so it's acceptable. In this helper function, we set our
;; measure to be entry-limit, an upper bound on the number of entries we can
;; visit, and decrement every time we visit a new entry. In the main function,
;; we count the total number of visitable directory entries, by dividing the
;; entire length of the data region by *ms-dir-ent-length*, and set that as the
;; upper limit. This makes sure that we aren't disallowing any legitimate FAT32
;; volumes which just happen to be full of directories.

;; We're adding a return value for collecting all these clusterchains... again,
;; for proof purposes. We're also adding a return value, to signal an error
;; when we run out of entries.
(defund
  lofat-to-hifat-helper-exec
  (fat32-in-memory dir-ent-list entry-limit)
  (declare (xargs :measure (nfix entry-limit)
                  :guard (and (natp entry-limit)
                              (useful-dir-ent-list-p dir-ent-list)
                              (lofat-fs-p fat32-in-memory))
                  :verify-guards nil
                  :stobjs (fat32-in-memory)))
  (b*
      (;; entry-limit is the loop stopper, kind of - we know that in a
       ;; filesystem instance without any looping clusterchains (where, for
       ;; instance, 2 points to 3 and 3 points to 2), we can't have more
       ;; entries than the total number of entries possible if the data region
       ;; was fully packed with directory entries. So, we begin with that
       ;; number as the entry count, and keep decreasing in recursive
       ;; calls. This means we also decrease when we find an entry for a
       ;; deleted file, or a "." or ".."  entry, even though we won't include
       ;; these in the filesystem instance. The measure must strictly decrease.
       ;; If there isn't a full directory entry in dir-contents, we're done.
       ((when
            (atom dir-ent-list))
        (mv nil 0 nil 0))
       ((when (zp entry-limit))
        (mv nil 0 nil *EIO*))
       (dir-ent
        (car dir-ent-list))
       ;; Learn about the file we're looking at.
       (first-cluster (dir-ent-first-cluster dir-ent))
       (filename (dir-ent-filename dir-ent))
       (directory-p
        (dir-ent-directory-p dir-ent))
       ;; From page 36 of the specification: "Similarly, a FAT file system
       ;; driver must not allow a directory (a file that is actually a
       ;; container for other files) to be larger than 65,536 * 32 (2,097,152)
       ;; bytes." Note, this is the length value we'll use to traverse the
       ;; clusterchain, not the value we'll store in the directory entry -
       ;; that's 0, per the spec.
       (length (if directory-p
                   *ms-max-dir-size*
                 (dir-ent-file-size dir-ent)))
       ((mv contents error-code)
        (if
            ;; This clause is intended to make sure we don't try to explore the
            ;; contents of an empty file; that would cause a guard
            ;; violation. Unlike deleted file entries and dot or dotdot
            ;; entries, though, these will be present in the m1 instance.
            (or (< first-cluster
                   *ms-first-data-cluster*)
                (>=
                 first-cluster
                 (+ (count-of-clusters fat32-in-memory)
                    *ms-first-data-cluster*)))
            (mv "" 0)
            (get-clusterchain-contents fat32-in-memory
                                       first-cluster
                                       length)))
       ((mv clusterchain &)
        (if
            ;; This clause is intended to make sure we don't try to explore the
            ;; contents of an empty file; that would cause a guard
            ;; violation. Unlike deleted file entries and dot or dotdot
            ;; entries, though, these will be present in the m1 instance.
            (or (< first-cluster
                   *ms-first-data-cluster*)
                (>=
                 first-cluster
                 (+ (count-of-clusters fat32-in-memory)
                    *ms-first-data-cluster*)))
            (mv nil 0)
            (get-clusterchain fat32-in-memory
                              first-cluster
                              length)))
       ;; head-entry-count and head-clusterchain-list, here, do not include the
       ;; entry or clusterchain respectively for the head itself. Those will be
       ;; added at the end.
       ((mv head head-entry-count head-clusterchain-list head-error-code)
        (if directory-p
            (lofat-to-hifat-helper-exec
             fat32-in-memory
             (make-dir-ent-list (string=>nats contents))
             (- entry-limit 1))
          (mv contents 0 nil 0)))
       ;; get-clusterchain-contents returns either 0 or a negative error code,
       ;; which is not what we want...
       (error-code
        (if (equal error-code 0)
            head-error-code
          *EIO*))
       ;; we want entry-limit to serve both as a measure and an upper
       ;; bound on how many entries are found.
       (tail-entry-limit (nfix (- entry-limit
                                  (+ 1 (nfix head-entry-count)))))
       ((mv tail tail-entry-count tail-clusterchain-list tail-error-code)
        (lofat-to-hifat-helper-exec
         fat32-in-memory
         (cdr dir-ent-list)
         tail-entry-limit))
       (error-code (if (zp error-code) tail-error-code error-code)))
    ;; We add the file to this m1 instance.
    (mv (list* (cons filename
                     (make-m1-file :dir-ent dir-ent
                                   :contents head))
               tail)
        (+ 1 head-entry-count tail-entry-count)
        (append (list clusterchain) head-clusterchain-list
                tail-clusterchain-list)
        error-code)))

(defthm lofat-to-hifat-helper-exec-correctness-1-lemma-1
  (equal (rationalp (nth n (dir-ent-fix x)))
         (< (nfix n) *ms-dir-ent-length*)))

(defthm
  lofat-to-hifat-helper-exec-correctness-1
  (b* (((mv m1-file-alist entry-count
            clusterchain-list error-code)
        (lofat-to-hifat-helper-exec
         fat32-in-memory
         dir-ent-list entry-limit)))
    (and (natp entry-count)
         (<= entry-count (nfix entry-limit))
         (<= (len m1-file-alist)
             (len dir-ent-list))
         (alistp m1-file-alist)
         (true-list-listp clusterchain-list)
         (natp error-code)))
  :hints
  (("goal"
    :in-theory
    (e/d (fat32-filename-p lofat-to-hifat-helper-exec)
         (nth-of-string=>nats
          natp-of-cluster-size take-redefinition))
    :induct
    (lofat-to-hifat-helper-exec fat32-in-memory
                                     dir-ent-list entry-limit)))
  :rule-classes
  ((:type-prescription
    :corollary (b* (((mv & & & error-code)
                     (lofat-to-hifat-helper-exec
                      fat32-in-memory
                      dir-ent-list entry-limit)))
                 (natp error-code)))
   (:linear :corollary (b* (((mv m1-file-alist & & error-code)
                             (lofat-to-hifat-helper-exec
                              fat32-in-memory
                              dir-ent-list entry-limit)))
                         (and (<= 0 error-code)
                              (<= (len m1-file-alist)
                                  (len dir-ent-list)))))
   (:rewrite
    :corollary (b* (((mv & & clusterchain-list error-code)
                     (lofat-to-hifat-helper-exec
                      fat32-in-memory
                      dir-ent-list entry-limit)))
                 (and (integerp error-code)
                      (true-list-listp clusterchain-list))))
   (:type-prescription
    :corollary (b* (((mv m1-file-alist &)
                     (lofat-to-hifat-helper-exec
                      fat32-in-memory
                      dir-ent-list entry-limit)))
                 (true-listp m1-file-alist)))))

(defthm
  lofat-to-hifat-helper-exec-correctness-2-lemma-1
  (implies (and (dir-ent-p dir-ent)
                (< (nfix n) *ms-dir-ent-length*))
           (rationalp (nth n dir-ent)))
  :hints (("goal" :in-theory (enable dir-ent-p)))
  :rule-classes
  ((:rewrite
    :corollary (implies (and (dir-ent-p dir-ent)
                             (< (nfix n) *ms-dir-ent-length*))
                        (acl2-numberp (nth n dir-ent))))))

(defthm
  lofat-to-hifat-helper-exec-correctness-2
  (implies (useful-dir-ent-list-p dir-ent-list)
           (b* (((mv m1-file-alist & & &)
                 (lofat-to-hifat-helper-exec
                  fat32-in-memory
                  dir-ent-list entry-limit)))
             (m1-file-alist-p m1-file-alist)))
  :hints
  (("goal"
    :in-theory
    (e/d (fat32-filename-p useless-dir-ent-p
                           lofat-to-hifat-helper-exec
                           useful-dir-ent-list-p)
         (nth-of-string=>nats natp-of-cluster-size
                              take-redefinition))
    :induct (lofat-to-hifat-helper-exec
             fat32-in-memory
             dir-ent-list entry-limit))))

(defthm
  lofat-to-hifat-helper-exec-correctness-3
  (b* (((mv m1-file-alist entry-count & &)
        (lofat-to-hifat-helper-exec
         fat32-in-memory
         dir-ent-list entry-limit)))
    (equal entry-count
           (m1-entry-count m1-file-alist)))
  :hints
  (("goal" :in-theory (enable lofat-to-hifat-helper-exec m1-entry-count)))
  :rule-classes
  (:rewrite
   (:linear
    :corollary (b* (((mv m1-file-alist & & &)
                     (lofat-to-hifat-helper-exec
                      fat32-in-memory
                      dir-ent-list entry-limit)))
                 (<= (m1-entry-count m1-file-alist)
                     (nfix entry-limit)))
    :hints
    (("goal"
      :in-theory
      (disable lofat-to-hifat-helper-exec-correctness-1)
      :use lofat-to-hifat-helper-exec-correctness-1)))))

(defthmd
  lofat-to-hifat-helper-exec-correctness-4
  (implies
   (and (equal (mv-nth 3
                       (lofat-to-hifat-helper-exec
                        fat32-in-memory
                        dir-ent-list entry-limit1))
               0)
        (>= (nfix entry-limit2)
            (mv-nth 1
                    (lofat-to-hifat-helper-exec
                     fat32-in-memory
                     dir-ent-list entry-limit1))))
   (equal
    (lofat-to-hifat-helper-exec fat32-in-memory
                                     dir-ent-list entry-limit2)
    (lofat-to-hifat-helper-exec
     fat32-in-memory
     dir-ent-list entry-limit1)))
  :hints
  (("goal" :in-theory (enable lofat-to-hifat-helper-exec
                              m1-entry-count)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (equal (mv-nth 3
                         (lofat-to-hifat-helper-exec
                          fat32-in-memory
                          dir-ent-list entry-limit1))
                 0)
          (>= (nfix entry-limit2)
              (mv-nth 1
                      (lofat-to-hifat-helper-exec
                       fat32-in-memory
                       dir-ent-list entry-limit1)))
          (> entry-limit2 entry-limit1))
     (equal (lofat-to-hifat-helper-exec
             fat32-in-memory
             dir-ent-list entry-limit2)
            (lofat-to-hifat-helper-exec
             fat32-in-memory
             dir-ent-list entry-limit1))))))

(defthm true-listp-of-lofat-to-hifat-helper-exec
  (true-listp (mv-nth 2
                      (lofat-to-hifat-helper-exec
                       fat32-in-memory
                       dir-contents entry-limit))))

(verify-guards
  lofat-to-hifat-helper-exec
  :hints
  (("goal"
    :in-theory (disable (:e dir-ent-directory-p)
                        (:t dir-ent-directory-p)
                        (:definition fat32-build-index-list)))))

(defthm m1-bounded-file-alist-p-helper-of-lofat-to-hifat-helper-exec
  (m1-bounded-file-alist-p-helper
   (mv-nth 0 (lofat-to-hifat-helper-exec
              fat32-in-memory dir-ent-list entry-limit))
   (len dir-ent-list))
  :hints (("Goal" :in-theory (enable lofat-to-hifat-helper-exec)) ))

(defthm
  data-region-length-of-update-fati
  (equal (data-region-length (update-fati i v fat32-in-memory))
         (data-region-length fat32-in-memory))
  :hints
  (("goal" :in-theory (enable data-region-length update-fati))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm max-entry-count-guard-lemma-1
    (implies (and (not (zp j)) (integerp i) (> i j))
             (> (floor i j) 0))
    :rule-classes :linear))

(defund max-entry-count (fat32-in-memory)
  (declare
   (xargs :guard (lofat-fs-p fat32-in-memory)
          :stobjs fat32-in-memory))
  (mbe
   :exec
   (floor (* (data-region-length fat32-in-memory)
             (cluster-size fat32-in-memory))
          *ms-dir-ent-length*)
   :logic
   (nfix
    (floor (* (data-region-length fat32-in-memory)
              (cluster-size fat32-in-memory))
           *ms-dir-ent-length*))))

(defthm max-entry-count-of-update-fati
  (equal
   (max-entry-count (update-fati i v fat32-in-memory))
   (max-entry-count fat32-in-memory))
  :hints (("Goal" :in-theory (enable max-entry-count)) ))

(defund root-dir-ent-list (fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (lofat-fs-p fat32-in-memory)))
  (mv-let
    (root-dir-contents error-code)
    (get-clusterchain-contents
     fat32-in-memory
     (fat32-entry-mask (bpb_rootclus fat32-in-memory))
     *ms-max-dir-size*)
    (mv
     (make-dir-ent-list (string=>nats root-dir-contents))
     error-code)))

(defthm
  useful-dir-ent-list-p-of-root-dir-ent-list
  (useful-dir-ent-list-p
   (mv-nth 0 (root-dir-ent-list fat32-in-memory)))
  :hints (("goal" :in-theory (enable root-dir-ent-list))))

(defthm
  integerp-of-root-dir-ent-list
  (and
    (integerp (mv-nth 1 (root-dir-ent-list fat32-in-memory)))
    (>= 0 (mv-nth 1 (root-dir-ent-list fat32-in-memory))))
  :hints (("goal" :in-theory (enable root-dir-ent-list)))
  :rule-classes
  ((:type-prescription
    :corollary
    (integerp (mv-nth 1 (root-dir-ent-list fat32-in-memory))))
   (:linear
    :corollary
    (>= 0 (mv-nth 1 (root-dir-ent-list fat32-in-memory))))))

(defund
  lofat-to-hifat (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (lofat-fs-p fat32-in-memory)))
  (b*
      (((unless
         (mbt (>= (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                  *ms-first-data-cluster*)))
        (mv nil *eio*))
       ((mv root-dir-ent-list error-code)
        (root-dir-ent-list fat32-in-memory))
       ((unless (equal error-code 0))
        (mv nil (- error-code)))
       ((mv m1-file-alist & & error-code)
        (lofat-to-hifat-helper-exec
         fat32-in-memory root-dir-ent-list
         (max-entry-count fat32-in-memory))))
    (mv m1-file-alist error-code)))

(defthm
  lofat-to-hifat-correctness-1
  (and
   (m1-file-alist-p
    (mv-nth 0
            (lofat-to-hifat fat32-in-memory)))
   (natp (mv-nth 1
                 (lofat-to-hifat fat32-in-memory))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat)
     (m1-file-p
      (:rewrite get-clusterchain-contents-correctness-2)))
    :use
    (:instance
     (:rewrite get-clusterchain-contents-correctness-2)
     (length *ms-max-dir-size*)
     (masked-current-cluster
      (fat32-entry-mask (bpb_rootclus fat32-in-memory)))
     (fat32-in-memory fat32-in-memory))))
  :rule-classes
  ((:rewrite
    :corollary
    (and
     (m1-file-alist-p
      (mv-nth 0
              (lofat-to-hifat fat32-in-memory)))
     (integerp
      (mv-nth 1
              (lofat-to-hifat fat32-in-memory)))))
   (:linear
    :corollary
    (<= 0
        (mv-nth 1
                (lofat-to-hifat fat32-in-memory))))
   (:type-prescription
    :corollary
    (true-listp
     (mv-nth 0
             (lofat-to-hifat fat32-in-memory))))
   (:type-prescription
    :corollary
    (natp
     (mv-nth 1
             (lofat-to-hifat fat32-in-memory))))))

(defthm
  lofat-to-hifat-correctness-2
  (implies
   (equal (mv-nth 0
                  (get-clusterchain-contents
                   fat32-in-memory
                   (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                   *ms-max-dir-size*))
          "")
   (equal (mv-nth 0 (lofat-to-hifat fat32-in-memory))
          nil))
  :hints (("goal" :in-theory (enable lofat-to-hifat
                                     lofat-to-hifat-helper-exec
                                     root-dir-ent-list))))

(defthm
  m1-entry-count-of-lofat-to-hifat
  (implies
   (lofat-fs-p fat32-in-memory)
   (<= (m1-entry-count
        (mv-nth 0
                (lofat-to-hifat fat32-in-memory)))
       (max-entry-count fat32-in-memory)))
  :hints (("goal" :in-theory (enable lofat-to-hifat)))
  :rule-classes :linear)

(defund
  stobj-find-n-free-clusters-helper
  (fat32-in-memory n start)
  (declare
   (xargs
    :guard (and (lofat-fs-p fat32-in-memory)
                (natp n)
                (natp start))
    :stobjs fat32-in-memory
    :measure (nfix (- (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*)
                      start))))
  (if
   (or (zp n)
       (mbe :logic (zp (- (+ (count-of-clusters fat32-in-memory)
                             *ms-first-data-cluster*)
                          start))
            :exec (>= start
                      (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*))))
   nil
   (if
    (not (equal (fat32-entry-mask (fati start fat32-in-memory))
                0))
    (stobj-find-n-free-clusters-helper
     fat32-in-memory n (+ start 1))
    (cons
     (mbe :exec start :logic (nfix start))
     (stobj-find-n-free-clusters-helper fat32-in-memory (- n 1)
                                        (+ start 1))))))

(defthm
  nat-listp-of-stobj-find-n-free-clusters-helper
  (nat-listp
   (stobj-find-n-free-clusters-helper fat32-in-memory n start))
  :hints
  (("goal"
    :in-theory (enable stobj-find-n-free-clusters-helper)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (integer-listp (stobj-find-n-free-clusters-helper
                               fat32-in-memory n start)))))

(defthm
  stobj-find-n-free-clusters-helper-correctness-1
  (implies
   (and (natp start)
        (lofat-fs-p fat32-in-memory))
   (equal
    (stobj-find-n-free-clusters-helper fat32-in-memory n start)
    (find-n-free-clusters-helper
     (nthcdr start (effective-fat fat32-in-memory))
     n start)))
  :hints
  (("goal" :in-theory (enable stobj-find-n-free-clusters-helper
                              find-n-free-clusters-helper)
    :induct (stobj-find-n-free-clusters-helper
             fat32-in-memory n start))))

(defund
  stobj-find-n-free-clusters
  (fat32-in-memory n)
  (declare
   (xargs :guard (and (lofat-fs-p fat32-in-memory)
                      (natp n))
          :stobjs fat32-in-memory))
  (stobj-find-n-free-clusters-helper
   fat32-in-memory n *ms-first-data-cluster*))

(defthm
  nat-listp-of-stobj-find-n-free-clusters
  (nat-listp (stobj-find-n-free-clusters fat32-in-memory n))
  :hints
  (("goal" :in-theory (enable stobj-find-n-free-clusters)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (integer-listp (stobj-find-n-free-clusters-helper
                               fat32-in-memory n start)))))

(defthm
  stobj-find-n-free-clusters-correctness-1
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal (stobj-find-n-free-clusters fat32-in-memory n)
          (find-n-free-clusters (effective-fat fat32-in-memory)
                                n)))
  :hints (("goal" :in-theory (enable stobj-find-n-free-clusters
                                     find-n-free-clusters)))
  :rule-classes :definition)

(defthm
  stobj-set-indices-in-fa-table-guard-lemma-1
  (implies (fat32-in-memoryp fat32-in-memory)
           (fat32-entry-list-p (nth *fati* fat32-in-memory)))
  :hints (("Goal" :in-theory (enable fat32-in-memoryp))))

(defthm
  stobj-set-indices-in-fa-table-guard-lemma-2
  (implies
   (and (fat32-entry-p entry)
        (fat32-masked-entry-p masked-entry))
   (unsigned-byte-p 32
                    (fat32-update-lower-28 entry masked-entry)))
  :hints
  (("goal"
    :in-theory
    (e/d (fat32-entry-p)
         (fat32-update-lower-28-correctness-1 unsigned-byte-p))
    :use fat32-update-lower-28-correctness-1)))

(defund
  stobj-set-indices-in-fa-table
  (fat32-in-memory index-list value-list)
  (declare
   (xargs
    :measure (acl2-count index-list)
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (nat-listp index-list)
                (fat32-masked-entry-list-p value-list)
                (equal (len index-list)
                       (len value-list)))
    :guard-hints
    (("goal" :in-theory (disable unsigned-byte-p)))))
  (b*
      (((when (atom index-list))
        fat32-in-memory)
       (current-index (car index-list))
       ((unless (and (natp current-index)
                     (< current-index
                        (+ (count-of-clusters fat32-in-memory)
                           *ms-first-data-cluster*))
                     (mbt
                      (< current-index
                         (fat-length fat32-in-memory)))))
        fat32-in-memory)
       (fat32-in-memory
        (update-fati current-index
                     (fat32-update-lower-28
                      (fati current-index fat32-in-memory)
                      (car value-list))
                     fat32-in-memory)))
    (stobj-set-indices-in-fa-table
     fat32-in-memory (cdr index-list)
     (cdr value-list))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1-lemma-1
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal (update-nth *fati* (nth *fati* fat32-in-memory)
                      fat32-in-memory)
          fat32-in-memory))
  :hints (("Goal" :in-theory (enable fat32-in-memoryp))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1-lemma-2
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal
    (fat32-in-memoryp (update-nth *fati* val fat32-in-memory))
    (fat32-entry-list-p val)))
  :hints (("Goal" :in-theory (enable fat32-in-memoryp))))

(defthm
  count-of-clusters-of-stobj-set-indices-in-fa-table
  (equal
   (count-of-clusters (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (count-of-clusters fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1
  (implies
   (and (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list))
        (lofat-fs-p fat32-in-memory))
   (equal
    (effective-fat (stobj-set-indices-in-fa-table
                    fat32-in-memory index-list value-list))
    (set-indices-in-fa-table (effective-fat fat32-in-memory)
                             index-list value-list)))
  :hints
  (("goal"
    :in-theory
    (e/d (set-indices-in-fa-table
          stobj-set-indices-in-fa-table)))))

(defthm
  fati-of-stobj-set-indices-in-fa-table
  (implies
   (and (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list))
        (lofat-fs-p fat32-in-memory)
        (natp n)
        (nat-listp index-list)
        (not (member-equal n index-list)))
   (equal
    (nth n
         (effective-fat
          (stobj-set-indices-in-fa-table
           fat32-in-memory index-list value-list)))
    (nth n (effective-fat fat32-in-memory))))
  :hints (("goal" :in-theory (disable nth-of-effective-fat)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (fat32-masked-entry-list-p value-list)
          (equal (len index-list)
                 (len value-list))
          (lofat-fs-p fat32-in-memory)
          (natp n)
          (nat-listp index-list)
          (not (member-equal n index-list))
          (< n
             (+ (count-of-clusters fat32-in-memory)
                *ms-first-data-cluster*)))
     (equal (fati n
                  (stobj-set-indices-in-fa-table
                   fat32-in-memory index-list value-list))
            (fati n fat32-in-memory)))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (disable stobj-set-indices-in-fa-table-correctness-1))))))

(defthm
  lofat-fs-p-of-stobj-set-indices-in-fa-table
  (implies (and (lofat-fs-p fat32-in-memory)
                (fat32-masked-entry-list-p value-list)
                (equal (len index-list)
                       (len value-list)))
           (lofat-fs-p
            (stobj-set-indices-in-fa-table
             fat32-in-memory index-list value-list)))
  :hints
  (("goal" :in-theory
    (enable stobj-set-indices-in-fa-table))))

(defthm
  cluster-size-of-stobj-set-indices-in-fa-table
  (equal
   (cluster-size (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (cluster-size fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  data-region-length-of-stobj-set-indices-in-fa-table
  (equal
   (data-region-length (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (data-region-length fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  fat-length-of-stobj-set-indices-in-fa-table
  (equal
   (fat-length (stobj-set-indices-in-fa-table
                fat32-in-memory index-list value-list))
   (fat-length fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  bpb_rootclus-of-stobj-set-indices-in-fa-table
  (equal
   (bpb_rootclus (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (bpb_rootclus fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  data-regioni-of-stobj-set-indices-in-fa-table
  (equal (data-regioni i (stobj-set-indices-in-fa-table
                          fat32-in-memory index-list value-list))
         (data-regioni i fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  max-entry-count-of-stobj-set-indices-in-fa-table
  (equal
   (max-entry-count (stobj-set-indices-in-fa-table
                     fat32-in-memory index-list value-list))
   (max-entry-count fat32-in-memory))
  :hints (("goal" :in-theory (enable max-entry-count))))

(defun
    stobj-set-clusters
    (cluster-list index-list fat32-in-memory)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard
    (and (lofat-fs-p fat32-in-memory)
         (lower-bounded-integer-listp
          index-list *ms-first-data-cluster*)
         (cluster-listp cluster-list (cluster-size fat32-in-memory))
         (equal (len index-list)
                (len cluster-list)))))
  (b*
      (((unless (consp cluster-list))
        fat32-in-memory)
       (fat32-in-memory
        (stobj-set-clusters (cdr cluster-list)
                            (cdr index-list)
                            fat32-in-memory))
       ((unless (and (integerp (car index-list))
                     (>= (car index-list)
                         *ms-first-data-cluster*)
                     (< (car index-list)
                        (+ *ms-first-data-cluster*
                           (data-region-length fat32-in-memory)))))
        fat32-in-memory))
    (update-data-regioni (- (car index-list) *ms-first-data-cluster*)
                         (car cluster-list)
                         fat32-in-memory)))

(defthm
  cluster-size-of-stobj-set-clusters
  (equal
   (cluster-size
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (cluster-size fat32-in-memory)))

(defthm
  count-of-clusters-of-stobj-set-clusters
  (equal
   (count-of-clusters
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (count-of-clusters fat32-in-memory)))

(defthm
  data-region-length-of-stobj-set-clusters
  (equal
   (data-region-length
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (data-region-length fat32-in-memory)))

(defthm
  lofat-fs-p-of-stobj-set-clusters
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (lower-bounded-integer-listp
         index-list *ms-first-data-cluster*)
        (cluster-listp cluster-list (cluster-size fat32-in-memory))
        (equal (len cluster-list)
               (len index-list))
        (equal (data-region-length fat32-in-memory)
               (count-of-clusters fat32-in-memory)))
   (lofat-fs-p
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory)))
  :hints
  (("goal"
    :induct
    (stobj-set-clusters cluster-list index-list fat32-in-memory))))

(defthm
  fati-of-stobj-set-clusters
  (equal (fati i
               (stobj-set-clusters cluster-list
                                   index-list fat32-in-memory))
         (fati i fat32-in-memory)))

(defthm
  fat-length-of-stobj-set-clusters
  (equal
   (fat-length
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (fat-length fat32-in-memory)))

(defthm
  bpb_rootclus-of-stobj-set-clusters
  (equal
   (bpb_rootclus
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (bpb_rootclus fat32-in-memory)))

;; This function needs to return an mv containing the fat32-in-memory stobj,
;; the new directory entry, and an errno value (either 0 or ENOSPC).
;;
;; One idea we tried was setting first-cluster to *ms-end-of-clusterchain*
;; (basically, marking it used) inside the body of this function. This would
;; have made some proofs more modular... but it doesn't work, because when
;; we're placing the contents of a directory (inside hifat-to-lofat-helper), we
;; need to make a recursive call to get the contents of that directory in the
;; first place... and first-cluster must be marked used before that call is
;; made to ensure that cluster doesn't get used.
(defund
  place-contents
  (fat32-in-memory dir-ent
                   contents file-length first-cluster)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (dir-ent-p dir-ent)
                (unsigned-byte-p 32 file-length)
                (stringp contents)
                (fat32-masked-entry-p first-cluster)
                (>= first-cluster *ms-first-data-cluster*)
                (< first-cluster
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory))))
    :guard-hints
    (("goal" :in-theory (disable unsigned-byte-p)))))
  (b*
      ((dir-ent (dir-ent-fix dir-ent))
       (cluster-size (cluster-size fat32-in-memory))
       (clusters (make-clusters contents cluster-size)))
    (if
        (and
         (< (len clusters) 1)
         (mbt
          (and
           (fat32-masked-entry-p first-cluster)
           (< first-cluster
              (fat-length fat32-in-memory)))))
        (b*
            (;; There shouldn't be a memory leak - mark this as free.
             (fat32-in-memory
              (update-fati first-cluster
                           (fat32-update-lower-28
                            (fati first-cluster fat32-in-memory)
                            0)
                           fat32-in-memory))
             ;; From page 17 of the FAT specification: "Note that a zero-length
             ;; file [...] has a first cluster number of 0 placed in its
             ;; directory entry."
             (dir-ent (dir-ent-set-first-cluster-file-size
                       dir-ent 0 file-length)))
          (mv fat32-in-memory dir-ent 0 nil))
      (b*
          ((indices
            (list* first-cluster
                   (stobj-find-n-free-clusters
                    fat32-in-memory (- (len clusters) 1))))
           ((unless (equal (len indices) (len clusters)))
            (mv fat32-in-memory dir-ent *enospc* nil))
           (fat32-in-memory
            (stobj-set-clusters clusters indices fat32-in-memory))
           (fat32-in-memory
            (stobj-set-indices-in-fa-table
             fat32-in-memory indices
             (binary-append (cdr indices)
                            (list *ms-end-of-clusterchain*)))))
        (mv
         fat32-in-memory
         (dir-ent-set-first-cluster-file-size dir-ent (car indices)
                                              file-length)
         0 indices)))))

(defthm
  lofat-fs-p-of-place-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (stringp contents)
        (natp file-length)
        (integerp first-cluster)
        (>= first-cluster *ms-first-data-cluster*)
        (< first-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory))))
   (lofat-fs-p
    (mv-nth
     0
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster))))
  :hints
  (("goal" :in-theory
    (enable place-contents))))

(defthm
  cluster-size-of-place-contents
  (equal
   (cluster-size
    (mv-nth 0
            (place-contents fat32-in-memory
                            dir-ent contents file-length first-cluster)))
   (cluster-size fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  count-of-clusters-of-place-contents
  (equal
   (count-of-clusters
    (mv-nth 0
            (place-contents fat32-in-memory
                            dir-ent contents file-length first-cluster)))
   (count-of-clusters fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  data-region-length-of-place-contents
  (equal
   (data-region-length
    (mv-nth
     0
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster)))
   (data-region-length fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  bpb_rootclus-of-place-contents
  (equal
   (bpb_rootclus
    (mv-nth
     0
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster)))
   (bpb_rootclus fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  dir-ent-p-of-place-contents
  (dir-ent-p
   (mv-nth 1
           (place-contents fat32-in-memory
                           dir-ent contents file-length first-cluster)))
  :hints (("goal" :in-theory (enable place-contents)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (unsigned-byte-listp
     8
     (mv-nth 1
             (place-contents fat32-in-memory
                             dir-ent contents file-length first-cluster)))
    :hints (("goal" :in-theory (enable dir-ent-p))))
   (:rewrite
    :corollary
    (equal
     (len
      (mv-nth 1
              (place-contents fat32-in-memory
                              dir-ent contents file-length first-cluster)))
     *ms-dir-ent-length*)
    :hints (("goal" :in-theory (enable dir-ent-p))))
   (:rewrite
    :corollary
    (true-listp
     (mv-nth 1
             (place-contents fat32-in-memory
                             dir-ent contents file-length first-cluster)))
    :hints (("goal" :in-theory (enable dir-ent-p))))))

(defthm
  useless-dir-ent-p-of-dir-ent-set-first-cluster-file-size
  (implies
   (dir-ent-p dir-ent)
   (equal
    (useless-dir-ent-p (dir-ent-set-first-cluster-file-size
                        dir-ent first-cluster file-size))
    (useless-dir-ent-p dir-ent)))
  :hints
  (("goal"
    :in-theory
    (e/d (useless-dir-ent-p dir-ent-p dir-ent-filename
                            dir-ent-set-first-cluster-file-size)
         ((:rewrite logtail-loghead))))))

(defthm
  useless-dir-ent-p-of-place-contents
  (implies
   (dir-ent-p dir-ent)
   (equal
    (useless-dir-ent-p
     (mv-nth 1
             (place-contents fat32-in-memory
                             dir-ent contents file-length first-cluster)))
    (useless-dir-ent-p
     dir-ent)))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  fat-length-of-place-contents
  (equal
   (fat-length
    (mv-nth 0
            (place-contents fat32-in-memory
                            dir-ent contents file-length first-cluster)))
   (fat-length fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  natp-of-place-contents
  (natp
   (mv-nth 2
           (place-contents fat32-in-memory dir-ent
                           contents file-length first-cluster)))
  :hints (("goal" :in-theory (enable place-contents)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (integerp
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))))
   (:linear
    :corollary
    (<=
     0
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))))))

(defthm
  true-listp-of-place-contents
  (true-listp
   (mv-nth 3
           (place-contents fat32-in-memory dir-ent
                           contents file-length first-cluster)))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  fat32-masked-entry-list-p-of-place-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (fat32-masked-entry-p first-cluster))
   (fat32-masked-entry-list-p
    (mv-nth
     3
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster))))
  :hints
  (("goal"
    :in-theory
    (e/d (place-contents)
         ((:rewrite
           fat32-masked-entry-list-p-of-find-n-free-clusters
           . 1)))
    :use
    (:instance
     (:rewrite fat32-masked-entry-list-p-of-find-n-free-clusters
               . 1)
     (n
      (binary-+
       '-1
       (len (make-clusters contents
                           (cluster-size fat32-in-memory)))))
     (fa-table (effective-fat fat32-in-memory))))))

(defthm
  max-entry-count-of-place-contents
  (equal
   (max-entry-count
    (mv-nth
     0
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster)))
   (max-entry-count fat32-in-memory))
  :hints
  (("goal" :in-theory (enable max-entry-count place-contents))))

;; OK, this function needs to return a list of directory entries, so that when
;; it is called recursively to take care of all the entries in a subdirectory,
;; the caller gets the list of these entries and becomes able to concatenate
;; them all together, add entries in the front for "." and "..", and then treat
;; the result as the contents of a file. In this scenario, the
;; caller must allocate one cluster even before making the recursive call for
;; the subdirectory, because  the FAT spec says, on page 26, "One cluster is
;; allocated to the directory (unless it is the root directory on a FAT16/FAT12
;; volume), and you set DIR_FstClusLO and DIR_FstClusHI to that cluster number
;; and place an EOC mark in that cluster's entry in the FAT." Now, after the
;; recursive call returns a list of entries, the caller can create a "." entry
;; using the index of the cluster allocated for this subdirectory before this
;; call, and a ".." entry using its own first cluster. However, it cannot know
;; its own first cluster without having it passed from its parent, so this must
;; be an extra argument to the recursive call.
;; Purely for proof purposes, we're also going to have to return an extra
;; argument, namely, the list of indices we used. That will be (mv-nth 3 ...)
;; of the thing.
(defun
    hifat-to-lofat-helper
    (fat32-in-memory fs current-dir-first-cluster)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (m1-file-alist-p fs)
                (fat32-masked-entry-p current-dir-first-cluster))
    :hints (("goal" :in-theory (enable m1-file->contents
                                       m1-file-contents-fix)))
    :verify-guards nil))
  (b*
      (;; This is the base case; no directory entries are left. Return an error
       ;; code of 0 (that is, the (mv-nth 2 ...) of the return value).
       ((unless (consp fs))
        (mv fat32-in-memory nil 0 nil))
       ;; The induction case begins here. First, recursively take care of all
       ;; the directory entries after this one in the same directory.
       ((mv fat32-in-memory tail-list errno tail-index-list)
        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster))
       ;; If there was an error in the recursive call, terminate.
       ((unless (zp errno)) (mv fat32-in-memory tail-list errno tail-index-list))
       (head (car fs))
       ;; "." and ".." entries are not even allowed to be part of an
       ;; m1-file-alist, so perhaps we can use mbt to wipe out this clause...
       ((when (or (equal (car head) *current-dir-fat32-name*)
                  (equal (car head) *parent-dir-fat32-name*)))
        (mv fat32-in-memory tail-list errno tail-index-list))
       ;; Get the directory entry for the first file in this directory.
       (dir-ent (m1-file->dir-ent (cdr head)))
       ;; Search for one cluster - unless empty, the file will need at least
       ;; one.
       (indices
        (stobj-find-n-free-clusters
         fat32-in-memory 1))
       ;; This means we couldn't find even one free cluster, so we return a "no
       ;; space left" error.
       ((when (< (len indices) 1))
        (mv fat32-in-memory tail-list *enospc* tail-index-list))
       (first-cluster
        (nth 0 indices))
       ;; The mbt below says this branch will never be taken; but having this
       ;; allows us to prove a strong rule about fat-length.
       ((unless (mbt (< first-cluster (fat-length fat32-in-memory))))
        (mv fat32-in-memory tail-list *enospc* tail-index-list))
       ;; Mark this cluster as used, without possibly interfering with any
       ;; existing clusterchains.
       (fat32-in-memory
        (update-fati
         first-cluster
         (fat32-update-lower-28 (fati first-cluster fat32-in-memory)
                                *ms-end-of-clusterchain*)
         fat32-in-memory)))
    (if
        (m1-regular-file-p (cdr head))
        (b* ((contents (m1-file->contents (cdr head)))
             (file-length (length contents))
             ((mv fat32-in-memory dir-ent errno head-index-list)
              (place-contents fat32-in-memory
                              dir-ent contents file-length first-cluster))
             (dir-ent (dir-ent-set-filename dir-ent (car head)))
             (dir-ent
              (dir-ent-install-directory-bit
               dir-ent nil)))
          (mv fat32-in-memory
              (list* dir-ent tail-list)
              errno
              (append head-index-list tail-index-list)))
      (b* ((contents (m1-file->contents (cdr head)))
           (file-length 0)
           ((mv fat32-in-memory unflattened-contents errno head-index-list1)
            (hifat-to-lofat-helper
             fat32-in-memory contents first-cluster))
           ((unless (zp errno)) (mv fat32-in-memory tail-list errno tail-index-list))
           (contents
            (nats=>string
             (append
              (dir-ent-install-directory-bit
               (dir-ent-set-filename
                (dir-ent-set-first-cluster-file-size
                 dir-ent
                 first-cluster
                 0)
                *current-dir-fat32-name*)
               t)
              (dir-ent-install-directory-bit
               (dir-ent-set-filename
                (dir-ent-set-first-cluster-file-size
                 dir-ent
                 current-dir-first-cluster
                 0)
                *parent-dir-fat32-name*)
               t)
              (flatten unflattened-contents))))
           ((mv fat32-in-memory dir-ent errno head-index-list2)
            (place-contents fat32-in-memory
                            dir-ent contents file-length
                            first-cluster))
           (dir-ent (dir-ent-set-filename dir-ent (car head)))
           (dir-ent
            (dir-ent-install-directory-bit
             dir-ent t)))
        (mv fat32-in-memory
            (list* dir-ent tail-list)
            errno
            (append head-index-list1 head-index-list2 tail-index-list))))))

(defthm
  cluster-size-of-hifat-to-lofat-helper
  (equal
   (cluster-size (mv-nth 0
                         (hifat-to-lofat-helper
                          fat32-in-memory
                          fs current-dir-first-cluster)))
   (cluster-size fat32-in-memory)))

(defthm
  count-of-clusters-of-hifat-to-lofat-helper
  (equal
   (count-of-clusters
    (mv-nth 0
            (hifat-to-lofat-helper
             fat32-in-memory fs current-dir-first-cluster)))
   (count-of-clusters fat32-in-memory)))

(defthm natp-of-hifat-to-lofat-helper
  (natp (mv-nth 2
                (hifat-to-lofat-helper
                 fat32-in-memory
                 fs current-dir-first-cluster)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (integerp (mv-nth 2
                      (hifat-to-lofat-helper
                       fat32-in-memory
                       fs current-dir-first-cluster))))
   (:linear
    :corollary
    (<= 0
        (mv-nth 2
                (hifat-to-lofat-helper
                 fat32-in-memory
                 fs current-dir-first-cluster))))))

(defthm
  data-region-length-of-hifat-to-lofat-helper
  (equal
   (data-region-length
    (mv-nth 0
            (hifat-to-lofat-helper
             fat32-in-memory fs current-dir-first-cluster)))
   (data-region-length fat32-in-memory)))

(defthm
  bpb_rootclus-of-hifat-to-lofat-helper
  (equal
   (bpb_rootclus
    (mv-nth 0
            (hifat-to-lofat-helper
             fat32-in-memory fs current-dir-first-cluster)))
   (bpb_rootclus fat32-in-memory)))

(defthm
  fat-length-of-hifat-to-lofat-helper
  (equal
   (fat-length (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory fs first-cluster)))
   (fat-length fat32-in-memory))
  :hints (("goal" :in-theory (enable nth))))

(defthm
  lofat-fs-p-of-hifat-to-lofat-helper-lemma-1
  (implies
   (lofat-fs-p fat32-in-memory)
   (and
    (not (< (binary-+ '2
                      (count-of-clusters fat32-in-memory))
            '0))
    (not (< (binary-+ '2
                      (count-of-clusters fat32-in-memory))
            '2))
    (not
     (< (nfix (binary-+ '2
                        (count-of-clusters fat32-in-memory)))
        '2)))))

(defthm
  lofat-fs-p-of-hifat-to-lofat-helper
  (implies
   (lofat-fs-p fat32-in-memory)
   (lofat-fs-p
    (mv-nth 0
            (hifat-to-lofat-helper
             fat32-in-memory fs first-cluster))))
  :hints
  (("goal"
    :in-theory (disable stobj-set-indices-in-fa-table))))

(defthm
  dir-ent-list-p-of-hifat-to-lofat-helper
  (dir-ent-list-p
   (mv-nth 1
           (hifat-to-lofat-helper
            fat32-in-memory fs first-cluster))))

(defthm
  useful-dir-ent-list-p-of-hifat-to-lofat-helper
  (implies
   (m1-file-alist-p fs)
   (useful-dir-ent-list-p
    (mv-nth 1
            (hifat-to-lofat-helper
             fat32-in-memory fs first-cluster))))
  :hints
  (("goal"
    :in-theory
    (enable useful-dir-ent-list-p))))

(defthm
  unsigned-byte-listp-of-flatten-when-dir-ent-list-p
  (implies (dir-ent-list-p dir-ent-list)
           (unsigned-byte-listp 8 (flatten dir-ent-list)))
  :hints (("goal" :in-theory (enable flatten))))

(defthm
  len-of-flatten-when-dir-ent-list-p
  (implies (dir-ent-list-p dir-ent-list)
           (equal
            (len (flatten dir-ent-list))
            (* *ms-dir-ent-length* (len dir-ent-list))))
  :hints (("goal" :in-theory (enable flatten len-when-dir-ent-p))))

(defthmd
  hifat-to-lofat-helper-correctness-4
  (implies
   (and (m1-file-alist-p fs)
        (zp (mv-nth 2
                    (hifat-to-lofat-helper
                     fat32-in-memory fs first-cluster))))
   (equal (len (mv-nth 1
                       (hifat-to-lofat-helper
                        fat32-in-memory fs first-cluster)))
          (len fs)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (m1-file-alist-p fs)
          (zp (mv-nth 2
                      (hifat-to-lofat-helper
                       fat32-in-memory fs first-cluster))))
     (equal (consp (mv-nth 1
                         (hifat-to-lofat-helper
                          fat32-in-memory fs first-cluster)))
            (consp fs))))))

(defthm
  true-listp-of-hifat-to-lofat-helper
  (true-listp (mv-nth 3
                      (hifat-to-lofat-helper
                       fat32-in-memory
                       fs current-dir-first-cluster))))

(encapsulate
  ()

  (local
   (defthm
     hifat-to-lofat-helper-guard-lemma-1
     (implies (not (m1-regular-file-p file))
              (equal (m1-directory-file-p file)
                     (m1-file-p file)))
     :hints
     (("goal"
       :in-theory (enable m1-directory-file-p m1-file-p
                          m1-regular-file-p m1-file-contents-p
                          m1-file->contents)))))

  (local
   (defthm
     hifat-to-lofat-helper-guard-lemma-2
     (implies (unsigned-byte-listp 8 x)
              (true-listp x))))

  (defthm
    hifat-to-lofat-helper-guard-lemma-3
    (implies
     (lofat-fs-p fat32-in-memory)
     (not
      (<
       (nth
        '0
        (find-n-free-clusters
         (effective-fat (mv-nth '0
                                (hifat-to-lofat-helper
                                 fat32-in-memory (cdr fs)
                                 current-dir-first-cluster)))
         '1))
       '0)))
    :hints (("Goal" :in-theory (enable nth))))

  (verify-guards
    hifat-to-lofat-helper
    :hints
    (("goal"
      :in-theory
      (e/d
       (painful-debugging-lemma-9)
       (stobj-set-indices-in-fa-table))))))

(defthm
  max-entry-count-of-hifat-to-lofat-helper
  (equal
   (max-entry-count
    (mv-nth
     0
     (hifat-to-lofat-helper fat32-in-memory
                                      fs current-dir-first-cluster)))
   (max-entry-count fat32-in-memory)))

(defthmd
  hifat-to-lofat-guard-lemma-1
  (implies
   (lofat-fs-p fat32-in-memory)
   (iff
    (< (binary-+
        '1
        (fat32-entry-mask (bpb_rootclus fat32-in-memory)))
       (fat-entry-count fat32-in-memory))
    (or
     (not
      (equal (fat32-entry-mask (bpb_rootclus fat32-in-memory))
             (+ (count-of-clusters fat32-in-memory)
                1)))
     (not (equal (fat-entry-count fat32-in-memory)
                 (+ (count-of-clusters fat32-in-memory)
                    2))))))
  :hints
  (("goal" :in-theory
    (disable lofat-fs-p-correctness-1)
    :use lofat-fs-p-correctness-1)))

(defund
  hifat-to-lofat
  (fat32-in-memory fs)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (m1-file-alist-p fs))
    :guard-hints
    (("goal" :in-theory (e/d (hifat-to-lofat-guard-lemma-1)
                             (unsigned-byte-p))
      ;; This is the second time we've had to add a :cases hint, really. The
      ;; reason is the same: brr tells us that a case split which should be
      ;; happening is not happening automatically.
      :cases
      ((not (equal (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                   (binary-+ '1
                             (count-of-clusters fat32-in-memory))))
       (not (equal (fat-entry-count fat32-in-memory)
                   (binary-+ '2
                             (count-of-clusters fat32-in-memory)))))))))
  (b*
      ((rootclus (bpb_rootclus fat32-in-memory))
       (index-list-to-clear
        (generate-index-list *ms-first-data-cluster*
                             (count-of-clusters fat32-in-memory)))
       (fat32-in-memory (stobj-set-indices-in-fa-table
                         fat32-in-memory index-list-to-clear
                         (make-list (len index-list-to-clear)
                                    :initial-element 0)))
       (fat32-in-memory (update-fati (fat32-entry-mask rootclus)
                                     (fat32-update-lower-28
                                      (fati
                                       (fat32-entry-mask rootclus)
                                       fat32-in-memory)
                                      *ms-end-of-clusterchain*)
                                     fat32-in-memory))
       ((mv fat32-in-memory
            root-dir-ent-list errno &)
        (hifat-to-lofat-helper
         fat32-in-memory
         fs (fat32-entry-mask rootclus)))
       ((unless (zp errno))
        (mv fat32-in-memory errno))
       (contents
        (if
            (atom root-dir-ent-list)
            ;; Here's the reasoning: there has to be something in the root
            ;; directory, even if the root directory is empty (i.e. the
            ;; contents of the root directory are all zeros, occupying at least
            ;; one cluster.)
            (coerce (make-list (cluster-size fat32-in-memory)
                               :initial-element (code-char 0))
                    'string)
          (nats=>string (flatten root-dir-ent-list))))
       ((mv fat32-in-memory & error-code &)
        (place-contents fat32-in-memory (dir-ent-fix nil)
                        contents
                        0 (fat32-entry-mask rootclus))))
    (mv fat32-in-memory error-code)))

(defthm natp-of-hifat-to-lofat
  (natp (mv-nth 1
                (hifat-to-lofat
                 fat32-in-memory
                 fs)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (integerp (mv-nth 1
                      (hifat-to-lofat
                       fat32-in-memory
                       fs))))
   (:linear
    :corollary
    (<= 0
        (mv-nth 1
                (hifat-to-lofat
                 fat32-in-memory
                 fs)))))
  :hints (("Goal" :in-theory (enable hifat-to-lofat)) ))

(defthm
  lofat-fs-p-of-hifat-to-lofat
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs))
   (lofat-fs-p
    (mv-nth 0
            (hifat-to-lofat fat32-in-memory fs))))
  :hints
  (("goal"
    :in-theory (enable hifat-to-lofat
                       hifat-to-lofat-guard-lemma-1)
    :do-not-induct t
    :cases
    ((not
      (equal (fat32-entry-mask (bpb_rootclus fat32-in-memory))
             (binary-+ '1
                       (count-of-clusters fat32-in-memory))))
     (not
      (equal
       (fat-length fat32-in-memory)
       (binary-+ '2
                 (count-of-clusters fat32-in-memory))))))))

(defthm
  data-regioni-of-stobj-set-clusters
  (implies
   (and (natp i)
        (not (member-equal (+ i *ms-first-data-cluster*)
                           index-list)))
   (equal (data-regioni i
                        (stobj-set-clusters cluster-list
                                            index-list fat32-in-memory))
          (data-regioni i fat32-in-memory))))

(defthm
  get-clusterchain-contents-of-place-contents-disjoint
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (stringp contents)
    (integerp first-cluster)
    (<= 2 first-cluster)
    (fat32-masked-entry-p masked-current-cluster)
    (equal
     (mv-nth
      1
      (get-clusterchain-contents fat32-in-memory
                                 masked-current-cluster length))
     0)
    (not (member-equal
          first-cluster
          (mv-nth 0
                  (fat32-build-index-list
                   (effective-fat fat32-in-memory)
                   masked-current-cluster length
                   (cluster-size fat32-in-memory))))))
   (equal
    (get-clusterchain-contents
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     masked-current-cluster length)
    (get-clusterchain-contents fat32-in-memory
                               masked-current-cluster length)))
  :hints
  (("goal"
    :in-theory (e/d (place-contents intersectp-equal
                                    get-clusterchain-contents)
                    (intersectp-is-commutative)))))

(defthm
  effective-fat-of-stobj-set-clusters
  (equal (effective-fat
          (stobj-set-clusters cluster-list
                              index-list fat32-in-memory))
         (effective-fat fat32-in-memory)))

(defthm
  lofat-to-hifat-helper-exec-of-place-contents-lemma-1
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (<= 2 masked-current-cluster)
    (fat32-masked-entry-p masked-current-cluster)
    (integerp first-cluster)
    (>= first-cluster *ms-first-data-cluster*)
    (stringp contents)
    (not (member-equal
          first-cluster
          (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32-in-memory)
                                          masked-current-cluster
                                          length cluster-size))))
    (equal (mv-nth 1
                   (fat32-build-index-list (effective-fat fat32-in-memory)
                                           masked-current-cluster
                                           length cluster-size))
           0))
   (equal
    (fat32-build-index-list
     (effective-fat
      (mv-nth 0
              (place-contents fat32-in-memory dir-ent
                              contents file-length first-cluster)))
     masked-current-cluster
     length cluster-size)
    (fat32-build-index-list (effective-fat fat32-in-memory)
                            masked-current-cluster
                            length cluster-size)))
  :hints
  (("goal"
    :in-theory
    (e/d (place-contents)
         ((:rewrite fat32-masked-entry-list-p-of-find-n-free-clusters
                    . 1)
          (:rewrite intersectp-is-commutative)))
    :do-not-induct t
    :use
    ((:instance (:rewrite fat32-masked-entry-list-p-of-find-n-free-clusters
                          . 1)
                (n (+ -1
                      (len (make-clusters contents
                                          (cluster-size fat32-in-memory)))))
                (fa-table (effective-fat fat32-in-memory)))
     (:instance
      (:rewrite intersectp-is-commutative)
      (y
       (cons first-cluster
             (find-n-free-clusters
              (effective-fat fat32-in-memory)
              (+ -1
                 (len (make-clusters contents
                                     (cluster-size fat32-in-memory)))))))
      (x (mv-nth 0
                 (fat32-build-index-list (effective-fat fat32-in-memory)
                                         masked-current-cluster
                                         length cluster-size)))))
    :expand
    (intersectp-equal
     (cons first-cluster
           (find-n-free-clusters
            (effective-fat fat32-in-memory)
            (+ -1
               (len (make-clusters contents
                                   (cluster-size fat32-in-memory))))))
     (mv-nth 0
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     masked-current-cluster
                                     length cluster-size))))))

(defthm
  lofat-to-hifat-helper-exec-of-place-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (stringp contents)
        (integerp first-cluster)
        (>= first-cluster *ms-first-data-cluster*)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper-exec
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0)
        (not-intersectp-list
         (list first-cluster)
         (mv-nth 2
                 (lofat-to-hifat-helper-exec
                  fat32-in-memory
                  dir-ent-list entry-limit)))
        (dir-ent-list-p dir-ent-list))
   (equal
    (lofat-to-hifat-helper-exec
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     dir-ent-list entry-limit)
    (lofat-to-hifat-helper-exec fat32-in-memory
                                     dir-ent-list entry-limit)))
  :hints
  (("goal"
    :in-theory
    (e/d (lofat-to-hifat-helper-exec)
         (dir-ent-fix))
    :induct
    (lofat-to-hifat-helper-exec fat32-in-memory
                                     dir-ent-list entry-limit)
    :expand
    ((lofat-to-hifat-helper-exec
      (mv-nth
       0
       (place-contents fat32-in-memory dir-ent
                       contents file-length first-cluster))
      dir-ent-list entry-limit)
     (:free (y)
            (intersectp-equal (list first-cluster)
                              y))))))

(defthm
  get-clusterchain-contents-of-update-fati
  (implies
   (and
    (integerp masked-current-cluster)
    (not
     (member-equal
      i
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster length
                                      (cluster-size fat32-in-memory))))))
   (equal (get-clusterchain-contents (update-fati i v fat32-in-memory)
                                     masked-current-cluster length)
          (get-clusterchain-contents fat32-in-memory
                                     masked-current-cluster length)))
  :hints
  (("goal"
    :in-theory (enable get-clusterchain-contents)
    :induct (get-clusterchain-contents fat32-in-memory
                                       masked-current-cluster length)
    :expand ((get-clusterchain-contents (update-fati i v fat32-in-memory)
                                        masked-current-cluster length)))))

(defthm
  lofat-to-hifat-helper-exec-of-update-fati
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (dir-ent-list-p dir-ent-list)
        (< (nfix i)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (not-intersectp-list
         (list i)
         (mv-nth 2
                 (lofat-to-hifat-helper-exec
                  fat32-in-memory
                  dir-ent-list entry-limit)))
        (equal (mv-nth 3
                       (lofat-to-hifat-helper-exec
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0))
   (equal
    (lofat-to-hifat-helper-exec
     (update-fati i v fat32-in-memory)
     dir-ent-list entry-limit)
    (lofat-to-hifat-helper-exec fat32-in-memory
                                dir-ent-list entry-limit)))
  :hints
  (("goal"
    :induct
    (lofat-to-hifat-helper-exec fat32-in-memory
                                     dir-ent-list entry-limit)
    :expand ((lofat-to-hifat-helper-exec
              (update-fati i v fat32-in-memory)
              dir-ent-list entry-limit)
             (:free (x y)
                    (intersectp-equal (list x) y))
             (:free (y) (intersectp-equal nil y)))
    :in-theory
    (e/d
     (lofat-to-hifat-helper-exec)
     ((:rewrite natp-of-cluster-size . 1)
      (:definition fat32-build-index-list))))
   ;; This case split, below, is needed because :brr shows ACL2 hesitating
   ;; before a case split it needs to do...
   ("Subgoal *1/3" :cases ((natp i)))))

(encapsulate
  ()

  (local
   (defun induction-scheme
       (index-list text cluster-size length)
     (if (or (zp (length text))
             (zp cluster-size))
         (mv index-list length)
         (induction-scheme
          (cdr index-list)
          (subseq text (min cluster-size (length text))
                  nil)
          cluster-size
          (+ length (- cluster-size))))))

  (local
   (defthm
     get-contents-from-clusterchain-of-stobj-set-clusters-coincident-lemma-1
     (iff (equal (+ 1 (len x)) 1) (atom x))))

  (local
   (in-theory (enable make-clusters
                      nthcdr-when->=-n-len-l)))

  (defthm
    get-contents-from-clusterchain-of-stobj-set-clusters-coincident
    (implies
     (and
      (stringp text)
      (equal
       (len (make-clusters text (cluster-size fat32-in-memory)))
       (len index-list))
      (integerp length)
      (>= length (length text))
      (lower-bounded-integer-listp
       index-list *ms-first-data-cluster*)
      (bounded-nat-listp
       index-list
       (+ 2 (data-region-length fat32-in-memory)))
      (lofat-fs-p fat32-in-memory)
      (no-duplicatesp-equal index-list))
     (equal
      (get-contents-from-clusterchain
       (stobj-set-clusters
        (make-clusters text (cluster-size fat32-in-memory))
        index-list fat32-in-memory)
       index-list length)
      (implode
       (append
        (explode text)
        (make-list (- (min length
                           (* (len index-list)
                              (cluster-size fat32-in-memory)))
                      (length text))
                   :initial-element (code-char 0))))))
    :hints
    (("goal"
      :induct
      (induction-scheme index-list
                        text (cluster-size fat32-in-memory)
                        length)
      :expand
      ((:free (fat32-in-memory length)
              (get-contents-from-clusterchain
               fat32-in-memory index-list length))
       (make-clusters text (cluster-size fat32-in-memory))))
     ("subgoal *1/2"
      :in-theory
      (disable (:rewrite associativity-of-append))
      :use
      ((:instance
        (:rewrite associativity-of-append)
        (c (make-list-ac (+ (cluster-size fat32-in-memory)
                            (- (len (explode text)))
                            (* (cluster-size fat32-in-memory)
                               (len (cdr index-list))))
                         (code-char 0) nil))
        (b (nthcdr (cluster-size fat32-in-memory)
                   (explode text)))
        (a (take (cluster-size fat32-in-memory)
                 (explode text))))
       (:instance
        (:rewrite associativity-of-append)
        (c (make-list-ac (+ length (- (len (explode text))))
                         (code-char 0) nil))
        (b (nthcdr (cluster-size fat32-in-memory)
                   (explode text)))
        (a (take (cluster-size fat32-in-memory)
                 (explode text))))
       (:theorem (equal (+ (cluster-size fat32-in-memory)
                           (- (cluster-size fat32-in-memory))
                           (- (len (explode text))))
                        (- (len (explode text)))))))
     ("subgoal *1/1" :expand ((len (explode text))
                              (len index-list))))))

(defthm
  get-contents-from-clusterchain-of-stobj-set-indices-in-fa-table
  (equal
   (get-contents-from-clusterchain
    (stobj-set-indices-in-fa-table
     fat32-in-memory index-list value-list)
    clusterchain file-size)
   (get-contents-from-clusterchain fat32-in-memory
                                   clusterchain file-size)))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    get-clusterchain-contents-of-place-contents-coincident-lemma-1
    (implies (not (zp x))
             (<= (* x
                    (len (find-n-free-clusters fa-table n)))
                 (* x (nfix n))))
    :rule-classes :linear))

(defthm
  get-clusterchain-contents-of-place-contents-coincident
  (implies
   (and
    (equal
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     0)
    (not (zp (length contents)))
    (<= *ms-first-data-cluster* first-cluster)
    (stringp contents)
    (integerp length)
    (<= (length contents) length)
    (lofat-fs-p fat32-in-memory)
    (not
     (equal
      (fat32-entry-mask (fati first-cluster fat32-in-memory))
      0))
    (< first-cluster
       (+ 2 (count-of-clusters fat32-in-memory)))
    (fat32-masked-entry-p first-cluster))
   (equal
    (get-clusterchain-contents
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     first-cluster length)
    (mv
     (implode
      (append
       (explode contents)
       (make-list
        (+
         (min
          length
          (*
           (len (make-clusters contents
                               (cluster-size fat32-in-memory)))
           (cluster-size fat32-in-memory)))
         (- (length contents)))
        :initial-element (code-char 0))))
     0)))
  :hints
  (("goal" :in-theory (e/d (place-contents)
                           ((:rewrite
                             fat32-build-index-list-of-set-indices-in-fa-table)
                            (:rewrite get-clusterchain-contents-correctness-3)
                            (:rewrite get-clusterchain-contents-correctness-2)
                            (:rewrite get-clusterchain-contents-correctness-1)))
    :use
    ((:instance
      (:rewrite get-clusterchain-contents-correctness-1)
      (length length)
      (masked-current-cluster first-cluster)
      (fat32-in-memory
       (stobj-set-indices-in-fa-table
        (stobj-set-clusters
         (make-clusters contents (cluster-size fat32-in-memory))
         (cons
          first-cluster
          (find-n-free-clusters
           (effective-fat fat32-in-memory)
           (+
            -1
            (len
             (make-clusters contents
                            (cluster-size fat32-in-memory))))))
         fat32-in-memory)
        (cons
         first-cluster
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory))))))
        (append
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory)))))
         '(268435455)))))
     (:instance
      (:rewrite fat32-build-index-list-of-set-indices-in-fa-table)
      (cluster-size (cluster-size fat32-in-memory))
      (file-length length)
      (file-index-list
       (cons
        first-cluster
        (find-n-free-clusters
         (effective-fat fat32-in-memory)
         (+
          -1
          (len (make-clusters contents
                              (cluster-size fat32-in-memory)))))))
      (fa-table (effective-fat fat32-in-memory)))
     (:instance
      (:rewrite get-clusterchain-contents-correctness-3)
      (length length)
      (masked-current-cluster first-cluster)
      (fat32-in-memory
       (stobj-set-indices-in-fa-table
        (stobj-set-clusters
         (make-clusters contents (cluster-size fat32-in-memory))
         (cons
          first-cluster
          (find-n-free-clusters
           (effective-fat fat32-in-memory)
           (+
            -1
            (len
             (make-clusters contents
                            (cluster-size fat32-in-memory))))))
         fat32-in-memory)
        (cons
         first-cluster
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory))))))
        (append
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory)))))
         '(268435455)))))
     (:instance
      (:rewrite get-clusterchain-contents-correctness-2)
      (length length)
      (masked-current-cluster first-cluster)
      (fat32-in-memory
       (stobj-set-indices-in-fa-table
        (stobj-set-clusters
         (make-clusters contents (cluster-size fat32-in-memory))
         (cons
          first-cluster
          (find-n-free-clusters
           (effective-fat fat32-in-memory)
           (+
            -1
            (len
             (make-clusters contents
                            (cluster-size fat32-in-memory))))))
         fat32-in-memory)
        (cons
         first-cluster
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory))))))
        (append
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory)))))
         '(268435455)))))))))

(defthm
  fati-of-place-contents-disjoint
  (implies
   (and (natp x)
        (not (equal x first-cluster))
        (< x
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (integerp first-cluster)
        (>= first-cluster *ms-first-data-cluster*)
        (lofat-fs-p fat32-in-memory)
        (stringp contents)
        (not (equal (fat32-entry-mask (fati x fat32-in-memory))
                    0)))
   (equal
    (fati
     x
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster)))
    (fati x fat32-in-memory)))
  :hints
  (("goal" :in-theory (enable place-contents))))

(defthm
  fati-of-hifat-to-lofat-helper-disjoint-lemma-1
  (implies
   (and
    (equal
     (len
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory fs
                                                 current-dir-first-cluster)))
       1))
     1)
    (equal
     (fati
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory fs
                                                  current-dir-first-cluster)))
        1))
      (mv-nth 0
              (hifat-to-lofat-helper fat32-in-memory fs
                                               current-dir-first-cluster)))
     (fati
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory fs
                                                  current-dir-first-cluster)))
        1))
      fat32-in-memory))
    (lofat-fs-p fat32-in-memory))
   (equal
    (fat32-entry-mask
     (fati
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory fs
                                                  current-dir-first-cluster)))
        1))
      fat32-in-memory))
    0))
  :hints
  (("goal"
    :in-theory (disable nth
                        (:rewrite find-n-free-clusters-correctness-4))
    :use
    (:instance
     (:rewrite find-n-free-clusters-correctness-4)
     (n 1)
     (fa-table
      (effective-fat
       (mv-nth 0
               (hifat-to-lofat-helper fat32-in-memory fs
                                                current-dir-first-cluster))))
     (x
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory fs
                                                  current-dir-first-cluster)))
        1)))))))

(defthm
  fati-of-hifat-to-lofat-helper-disjoint-lemma-2
  (implies
   (and
    (equal
     (len
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory fs
                                                 current-dir-first-cluster)))
       1))
     1)
    (equal
     (fati
      x
      (mv-nth 0
              (hifat-to-lofat-helper fat32-in-memory fs
                                               current-dir-first-cluster)))
     (fati x fat32-in-memory))
    (lofat-fs-p fat32-in-memory)
    (not (equal (fat32-entry-mask (fati x fat32-in-memory))
                0)))
   (not
    (equal
     x
     (nth
      '0
      (find-n-free-clusters
       (effective-fat
        (mv-nth '0
                (hifat-to-lofat-helper fat32-in-memory fs
                                                 current-dir-first-cluster)))
       '1)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite make-clusters-correctness-1 . 1)))))

(defthm
  fati-of-hifat-to-lofat-helper-disjoint
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (integerp x)
        (>= x *ms-first-data-cluster*)
        (< x
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (not (equal (fat32-entry-mask (fati x fat32-in-memory))
                    0))
        (equal (mv-nth 2
                       (hifat-to-lofat-helper
                        fat32-in-memory
                        fs current-dir-first-cluster))
               0))
   (equal (fati x
                (mv-nth 0
                        (hifat-to-lofat-helper
                         fat32-in-memory
                         fs current-dir-first-cluster)))
          (fati x fat32-in-memory)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite make-clusters-correctness-1 . 1)))))

(defthm
  fat32-build-index-list-of-place-contents-coincident
  (implies
   (and
    (equal
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     0)
    (not (zp (length contents)))
    (<= *ms-first-data-cluster* first-cluster)
    (stringp contents)
    (integerp length)
    (<= (length contents) length)
    (lofat-fs-p fat32-in-memory)
    (not
     (equal
      (fat32-entry-mask (fati first-cluster fat32-in-memory))
      0))
    (< first-cluster
       (+ 2 (count-of-clusters fat32-in-memory)))
    (fat32-masked-entry-p first-cluster)
    (equal cluster-size
           (cluster-size fat32-in-memory)))
   (equal
    (fat32-build-index-list
     (effective-fat
      (mv-nth
       0
       (place-contents fat32-in-memory dir-ent
                       contents file-length first-cluster)))
     first-cluster length cluster-size)
    (mv
     (cons
      first-cluster
      (find-n-free-clusters
       (effective-fat fat32-in-memory)
       (+
        -1
        (len (make-clusters contents
                            (cluster-size fat32-in-memory))))))
     0)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (place-contents)
     ((:rewrite
       fat32-build-index-list-of-set-indices-in-fa-table)))
    :do-not-induct t
    :use
    ((:instance
      (:rewrite
       fat32-build-index-list-of-set-indices-in-fa-table)
      (cluster-size (cluster-size fat32-in-memory))
      (file-length length)
      (file-index-list
       (cons
        first-cluster
        (find-n-free-clusters
         (effective-fat fat32-in-memory)
         (+
          -1
          (len
           (make-clusters contents
                          (cluster-size fat32-in-memory)))))))
      (fa-table (effective-fat fat32-in-memory)))))))

(defthm place-contents-expansion-1
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (not (zp (cluster-size fat32-in-memory)))
        (dir-ent-p dir-ent)
        (fat32-masked-entry-p first-cluster)
        (< first-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory))))
   (equal
    (mv-nth 1
            (place-contents fat32-in-memory dir-ent
                            contents file-length first-cluster))
    (if
        (equal (length contents) 0)
        (dir-ent-set-first-cluster-file-size dir-ent 0 file-length)
      (if
          (equal
           (+
            1
            (len (stobj-find-n-free-clusters
                  fat32-in-memory
                  (+ -1
                     (len (make-clusters contents
                                         (cluster-size fat32-in-memory)))))))
           (len (make-clusters contents
                               (cluster-size fat32-in-memory))))
          (dir-ent-set-first-cluster-file-size dir-ent first-cluster file-length)
        dir-ent))))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm place-contents-expansion-2
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (not (zp (cluster-size fat32-in-memory)))
        (dir-ent-p dir-ent)
        (fat32-masked-entry-p first-cluster)
        (< first-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory))))
   (equal
    (mv-nth 2
            (place-contents fat32-in-memory dir-ent
                            contents file-length first-cluster))
    (if
        (equal (length contents) 0)
        0
      (if
          (equal
           (+
            1
            (len (stobj-find-n-free-clusters
                  fat32-in-memory
                  (+ -1
                     (len (make-clusters contents
                                         (cluster-size fat32-in-memory)))))))
           (len (make-clusters contents
                               (cluster-size fat32-in-memory))))
          0
        *enospc*))))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  make-dir-ent-list-of-append-1
  (implies
   (dir-ent-p dir-ent)
   (equal (make-dir-ent-list (append dir-ent dir-contents))
          (if (equal (nth 0 dir-ent) 0)
              nil
              (if (useless-dir-ent-p dir-ent)
                  (make-dir-ent-list dir-contents)
                  (cons dir-ent
                        (make-dir-ent-list dir-contents))))))
  :hints (("goal" :in-theory (enable make-dir-ent-list
                                     len-when-dir-ent-p))))

(defthm
  make-dir-ent-list-of-append-2
  (implies
   (and (dir-ent-list-p dir-ent-list)
        (unsigned-byte-listp 8 y)
        (or (< (len y) *ms-dir-ent-length*)
            (equal (nth 0 y) 0)))
   (equal (make-dir-ent-list (append (flatten dir-ent-list) y))
          (make-dir-ent-list (flatten dir-ent-list))))
  :hints
  (("goal" :in-theory (enable make-dir-ent-list flatten dir-ent-p)
    :induct (flatten dir-ent-list))))

(defthm
  make-dir-ent-list-of-make-list-ac-1
  (implies (not (zp n))
           (equal (make-dir-ent-list (make-list-ac n 0 ac))
                  nil))
  :hints
  (("goal"
    :in-theory (e/d (make-dir-ent-list) (make-list-ac))
    :expand ((make-dir-ent-list (make-list-ac n 0 ac))
             (dir-ent-fix (take *ms-dir-ent-length*
                                (make-list-ac n 0 ac)))))))

(defthm
  make-dir-ent-list-of-flatten-when-useful-dir-ent-listp
  (implies (useful-dir-ent-list-p dir-ent-list)
           (equal (make-dir-ent-list (flatten dir-ent-list))
                  dir-ent-list))
  :hints
  (("goal"
    :in-theory
    (enable useful-dir-ent-list-p make-dir-ent-list flatten))))

(defthm
  useless-dir-ent-p-of-dir-ent-set-filename-of-constant
  (implies
   (dir-ent-p dir-ent)
   (and
    (useless-dir-ent-p
     (dir-ent-set-filename dir-ent *parent-dir-fat32-name*))
    (useless-dir-ent-p
     (dir-ent-set-filename dir-ent *current-dir-fat32-name*))))
  :hints
  (("goal"
    :in-theory (enable useless-dir-ent-p
                       dir-ent-filename dir-ent-set-filename
                       dir-ent-fix dir-ent-p))))

(defun
    unmodifiable-listp (x fa-table)
  (if
      (atom x)
      (equal x nil)
    (and (integerp (car x))
         (<= *ms-first-data-cluster* (car x))
         (< (car x) (len fa-table))
         (not (equal (fat32-entry-mask (nth (car x) fa-table))
                     0))
         (unmodifiable-listp (cdr x)
                             fa-table))))

(defthm
  unmodifiable-listp-of-update-nth
  (implies
   (and (not (member-equal key x))
        (< key (len fa-table)))
   (equal (unmodifiable-listp x (update-nth key val fa-table))
          (unmodifiable-listp x fa-table))))

(defthm
  unmodifiable-listp-correctness-2
  (implies (and (unmodifiable-listp x fa-table)
                (equal (fat32-entry-mask (nth key fa-table))
                       0))
           (not (member-equal key x)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (unmodifiable-listp x fa-table)
          (equal (fat32-entry-mask (nth key fa-table))
                 0)
          (< key (len fa-table)))
     (unmodifiable-listp x (update-nth key val fa-table))))))

(defthm
  unmodifiable-listp-correctness-3
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (unmodifiable-listp x (effective-fat fat32-in-memory))
    (not (member-equal first-cluster x))
    (integerp first-cluster)
    (<= *ms-first-data-cluster* first-cluster)
    (stringp contents)
    (equal
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     0))
   (unmodifiable-listp
    x
    (effective-fat
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))))))

(defthm
  unmodifiable-listp-correctness-4-lemma-1
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (natp n1)
    (<
     (nfix n2)
     (len (find-n-free-clusters (effective-fat fat32-in-memory)
                                n1))))
   (equal
    (fat32-entry-mask
     (fati
      (nth n2
           (find-n-free-clusters (effective-fat fat32-in-memory)
                                 n1))
      fat32-in-memory))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable find-n-free-clusters-correctness-5
             (:linear find-n-free-clusters-correctness-7))
    :use
    ((:instance find-n-free-clusters-correctness-5
                (fa-table (effective-fat fat32-in-memory)))
     (:instance (:linear find-n-free-clusters-correctness-7)
                (n n1)
                (fa-table (effective-fat fat32-in-memory))
                (m n2))))))

(defthm
  unmodifiable-listp-correctness-4
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (equal (mv-nth 2
                       (hifat-to-lofat-helper
                        fat32-in-memory
                        fs current-dir-first-cluster))
               0)
        (unmodifiable-listp x (effective-fat fat32-in-memory)))
   (unmodifiable-listp
    x
    (effective-fat
     (mv-nth 0
             (hifat-to-lofat-helper
              fat32-in-memory
              fs current-dir-first-cluster))))))

(defthm
  unmodifiable-listp-correctness-5
  (implies
   (and (unmodifiable-listp x fa-table)
        (natp n)
        (fat32-entry-list-p fa-table))
   (not (intersectp-equal x (find-n-free-clusters fa-table n))))
  :hints (("goal" :in-theory (enable intersectp-equal))))

(defthm
  unmodifiable-listp-of-append
  (equal (unmodifiable-listp (append x y) fa-table)
         (and
          (unmodifiable-listp (true-list-fix x) fa-table)
          (unmodifiable-listp y fa-table))))

(defthm
  unmodifiable-listp-of-fat32-build-index-list
  (implies
   (and
    (equal
     (mv-nth
      1
      (fat32-build-index-list fa-table masked-current-cluster
                              length cluster-size))
     0)
    (integerp masked-current-cluster)
    (<= 2 masked-current-cluster)
    (< masked-current-cluster (len fa-table)))
   (unmodifiable-listp
    (mv-nth
     0
     (fat32-build-index-list fa-table masked-current-cluster
                             length cluster-size))
    fa-table)))

(defthm
  lofat-to-hifat-helper-exec-of-hifat-to-lofat-helper-disjoint-lemma-1
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (natp n)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper-exec
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0))
   (not-intersectp-list
    (find-n-free-clusters (effective-fat fat32-in-memory)
                          n)
    (mv-nth 2
            (lofat-to-hifat-helper-exec
             fat32-in-memory
             dir-ent-list entry-limit))))
  :hints
  (("goal"
    :in-theory
    (e/d (intersectp-equal lofat-to-hifat-helper-exec)
         ((:definition fat32-build-index-list)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (equal n 1)
      (equal
       (len
        (find-n-free-clusters (effective-fat fat32-in-memory)
                              n))
       1)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper-exec
                      fat32-in-memory
                      dir-ent-list entry-limit))
             0))
     (not-intersectp-list
      (cons
       (nth
        0
        (find-n-free-clusters (effective-fat fat32-in-memory)
                              n))
       nil)
      (mv-nth 2
              (lofat-to-hifat-helper-exec
               fat32-in-memory
               dir-ent-list entry-limit))))
    :hints
    (("goal"
      :expand
      ((len
        (find-n-free-clusters (effective-fat fat32-in-memory)
                              1))
       (len
        (cdr
         (find-n-free-clusters (effective-fat fat32-in-memory)
                               1))))
      :cases
      ((equal
        (list
         (car
          (find-n-free-clusters (effective-fat fat32-in-memory)
                                1)))
        (find-n-free-clusters (effective-fat fat32-in-memory)
                              1))))))))

(defthm
  lofat-to-hifat-helper-exec-of-hifat-to-lofat-helper-disjoint
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper-exec
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0)
        (dir-ent-list-p dir-ent-list))
   (equal
    (lofat-to-hifat-helper-exec
     (mv-nth 0
             (hifat-to-lofat-helper
              fat32-in-memory
              fs current-dir-first-cluster))
     dir-ent-list entry-limit)
    (lofat-to-hifat-helper-exec fat32-in-memory
                           dir-ent-list entry-limit))))

(defthm
  hifat-to-lofat-inversion-lemma-1
  (implies
   (and (equal (len (find-n-free-clusters fa-table 1))
               1)
        (not (intersectp-equal x (find-n-free-clusters fa-table 1)))
        (not (intersectp-equal x y)))
   (not (intersectp-equal x
                          (cons (nth 0 (find-n-free-clusters fa-table 1))
                                y))))
  :hints
  (("Goal" :in-theory (enable nth)
    :expand
    ((len (find-n-free-clusters fa-table 1))
     (len (cdr (find-n-free-clusters fa-table 1))))
    :cases
    ((equal (cons (nth 0 (find-n-free-clusters fa-table 1))
                  y)
            (append (find-n-free-clusters fa-table 1)
                    y))))))

;; At least once, accumulated-persistence has reported this rule as :useless,
;; but in fact it is needed to discharge a subgoal. There's no trivial way
;; around it.
(defthm
  hifat-to-lofat-inversion-lemma-2
  (implies (and (stringp (m1-file->contents file))
                (equal (len (explode (m1-file->contents file)))
                       0))
           (equal (m1-file->contents file) ""))
  :hints
  (("goal" :expand (len (explode (m1-file->contents file))))))

(defthm
  hifat-to-lofat-inversion-lemma-3
  (implies
   (not-intersectp-list
    (cons
     (nth
      0
      (find-n-free-clusters
       (effective-fat (mv-nth 0
                              (hifat-to-lofat-helper
                               fat32-in-memory (cdr fs)
                               current-dir-first-cluster)))
       1))
     x)
    (mv-nth
     2
     (lofat-to-hifat-helper-exec
      (mv-nth
       0
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper
                  fat32-in-memory (cdr fs)
                  current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth 0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory (cdr fs)
                        current-dir-first-cluster)))
              1))))
      (mv-nth
       1
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper
                  fat32-in-memory (cdr fs)
                  current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth 0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory (cdr fs)
                        current-dir-first-cluster)))
              1))))
      (+ -1 entry-limit))))
   (and
   (not-intersectp-list
    (list
     (nth
      0
      (find-n-free-clusters
       (effective-fat (mv-nth 0
                              (hifat-to-lofat-helper
                               fat32-in-memory (cdr fs)
                               current-dir-first-cluster)))
       1)))
    (mv-nth
     2
     (lofat-to-hifat-helper-exec
      (mv-nth
       0
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper
                  fat32-in-memory (cdr fs)
                  current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth 0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory (cdr fs)
                        current-dir-first-cluster)))
              1))))
      (mv-nth
       1
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper
                  fat32-in-memory (cdr fs)
                  current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth 0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory (cdr fs)
                        current-dir-first-cluster)))
              1))))
      (+ -1 entry-limit))))
   (not-intersectp-list
    x
    (mv-nth
     2
     (lofat-to-hifat-helper-exec
      (mv-nth
       0
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper
                  fat32-in-memory (cdr fs)
                  current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth 0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory (cdr fs)
                        current-dir-first-cluster)))
              1))))
      (mv-nth
       1
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper
                  fat32-in-memory (cdr fs)
                  current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth 0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory (cdr fs)
                        current-dir-first-cluster)))
              1))))
      (+ -1 entry-limit))))))
  :hints
  (("goal"
    :in-theory
    (disable (:rewrite not-intersectp-list-of-append-2))
    :use
    (:instance
     (:rewrite not-intersectp-list-of-append-2)
     (l
      (mv-nth
       2
       (lofat-to-hifat-helper-exec
        (mv-nth
         0
         (hifat-to-lofat-helper
          (update-fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth 0
                        (hifat-to-lofat-helper
                         fat32-in-memory (cdr fs)
                         current-dir-first-cluster)))
               1))
             (mv-nth 0
                     (hifat-to-lofat-helper
                      fat32-in-memory (cdr fs)
                      current-dir-first-cluster)))
            268435455)
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          (m1-file->contents (cdr (car fs)))
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper
                      fat32-in-memory (cdr fs)
                      current-dir-first-cluster)))
            1))))
        (mv-nth
         1
         (hifat-to-lofat-helper
          (update-fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth 0
                        (hifat-to-lofat-helper
                         fat32-in-memory (cdr fs)
                         current-dir-first-cluster)))
               1))
             (mv-nth 0
                     (hifat-to-lofat-helper
                      fat32-in-memory (cdr fs)
                      current-dir-first-cluster)))
            268435455)
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          (m1-file->contents (cdr (car fs)))
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper
                      fat32-in-memory (cdr fs)
                      current-dir-first-cluster)))
            1))))
        (+ -1 entry-limit))))
     (y x)
     (x
      (list
       (nth 0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))))))))

(encapsulate
  ()

  (local
   (defun-nx
     induction-scheme
     (fat32-in-memory fs
                      current-dir-first-cluster entry-limit x)
     (declare
      (xargs
       :stobjs fat32-in-memory
       :guard
       (and (lofat-fs-p fat32-in-memory)
            (m1-file-alist-p fs)
            (fat32-masked-entry-p current-dir-first-cluster))
       :hints (("goal" :in-theory (enable m1-file->contents
                                          m1-file-contents-fix)))
       :verify-guards nil))
     (b*
         (((unless (consp fs))
           (mv fat32-in-memory nil 0 nil))
          (head (car fs))
          ((mv fat32-in-memory
               tail-list errno tail-index-list)
           (induction-scheme
            fat32-in-memory (cdr fs)
            current-dir-first-cluster
            (-
             entry-limit
             (if
              (m1-regular-file-p (cdr head))
              1
              (+ 1
                 (m1-entry-count (m1-file->contents (cdr head))))))
            x))
          ((unless (zp errno))
           (mv fat32-in-memory
               tail-list errno tail-index-list))
          ((when (or (equal (car head)
                            *current-dir-fat32-name*)
                     (equal (car head)
                            *parent-dir-fat32-name*)))
           (mv fat32-in-memory
               tail-list errno tail-index-list))
          (dir-ent (m1-file->dir-ent (cdr head)))
          (indices (stobj-find-n-free-clusters fat32-in-memory 1))
          ((when (< (len indices) 1))
           (mv fat32-in-memory
               tail-list *enospc* tail-index-list))
          (first-cluster (nth 0 indices))
          ((unless (mbt (< first-cluster
                           (fat-length fat32-in-memory))))
           (mv fat32-in-memory
               tail-list *enospc* tail-index-list))
          (fat32-in-memory
           (update-fati first-cluster
                        (fat32-update-lower-28
                         (fati first-cluster fat32-in-memory)
                         *ms-end-of-clusterchain*)
                        fat32-in-memory)))
       (if
        (m1-regular-file-p (cdr head))
        (b*
            ((contents (m1-file->contents (cdr head)))
             (file-length (length contents))
             ((mv fat32-in-memory
                  dir-ent errno head-index-list)
              (place-contents fat32-in-memory dir-ent
                              contents file-length first-cluster))
             (dir-ent (dir-ent-set-filename dir-ent (car head)))
             (dir-ent (dir-ent-install-directory-bit dir-ent nil)))
          (mv fat32-in-memory
              (list* dir-ent tail-list)
              errno
              (append head-index-list tail-index-list)))
        (b*
            ((contents (m1-file->contents (cdr head)))
             (file-length 0)
             ((mv fat32-in-memory unflattened-contents
                  errno head-index-list1)
              (induction-scheme
               fat32-in-memory
               contents first-cluster (- entry-limit 1)
               (cons first-cluster x)))
             ((unless (zp errno))
              (mv fat32-in-memory
                  tail-list errno tail-index-list))
             (contents
              (nats=>string
               (append
                (dir-ent-install-directory-bit
                 (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                        dir-ent first-cluster 0)
                                       *current-dir-fat32-name*)
                 t)
                (dir-ent-install-directory-bit
                 (dir-ent-set-filename
                  (dir-ent-set-first-cluster-file-size
                   dir-ent current-dir-first-cluster 0)
                  *parent-dir-fat32-name*)
                 t)
                (flatten unflattened-contents))))
             ((mv fat32-in-memory
                  dir-ent errno head-index-list2)
              (place-contents fat32-in-memory dir-ent
                              contents file-length first-cluster))
             (dir-ent (dir-ent-set-filename dir-ent (car head)))
             (dir-ent (dir-ent-install-directory-bit dir-ent t)))
          (mv fat32-in-memory
              (list* dir-ent tail-list)
              errno
              (append head-index-list1
                      head-index-list2 tail-index-list)))))))

  (local
   (defthm
     induction-scheme-correctness
     (equal
      (induction-scheme fat32-in-memory fs
                        current-dir-first-cluster entry-limit x)
      (hifat-to-lofat-helper
       fat32-in-memory
       fs current-dir-first-cluster))))

  ;; We tried (in commit aaf008a0e4edf4343b3d33e23d4aeff897cb1138) removing the
  ;; three place-contents-expansion rules in favour of rules which do not
  ;; introduce case splits. This is not easily doable, because the case split
  ;; based on the emptiness of the file contents is necessary for Subgoal *1/3
  ;; of this induction. Either we'd have to do the case split in a different
  ;; rule, or else we'd have to introduce a hint for Subgoal *1/3 - neither
  ;; seems very much better than the status quo. Therefore, this will remain
  ;; the slowest proof because the case splitting is necessary.
  (defthm
    hifat-to-lofat-inversion-big-induction
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (m1-file-alist-p fs)
          (m1-bounded-file-alist-p fs)
          (m1-file-no-dups-p fs)
          (fat32-masked-entry-p current-dir-first-cluster)
          (<= *ms-first-data-cluster*
              current-dir-first-cluster)
          (< current-dir-first-cluster
             (+ *ms-first-data-cluster*
                (count-of-clusters fat32-in-memory)))
          (integerp entry-limit)
          (>= entry-limit (m1-entry-count fs))
          (unmodifiable-listp x (effective-fat fat32-in-memory)))
     (b*
         (((mv fat32-in-memory dir-ent-list error-code)
           (hifat-to-lofat-helper
            fat32-in-memory
            fs current-dir-first-cluster)))
       (implies
        (zp error-code)
        (and (equal (mv-nth 3
                            (lofat-to-hifat-helper-exec
                             fat32-in-memory
                             dir-ent-list entry-limit))
                    0)
             (not-intersectp-list
              x
              (mv-nth 2
                      (lofat-to-hifat-helper-exec
                       fat32-in-memory
                       dir-ent-list entry-limit)))
             (hifat-equiv (mv-nth 0
                                   (lofat-to-hifat-helper-exec
                                    fat32-in-memory
                                    dir-ent-list entry-limit))
                           fs)))))
    :hints
    (("goal"
      :induct
      (induction-scheme fat32-in-memory fs
                        current-dir-first-cluster entry-limit x)
      :in-theory
      (e/d
       (lofat-to-hifat-helper-exec
        hifat-to-lofat-helper-correctness-4
        m1-entry-count
        (:definition m1-file-no-dups-p))
       ((:rewrite make-clusters-correctness-1 . 1)
        (:rewrite nth-of-nats=>chars)
        (:rewrite dir-ent-p-when-member-equal-of-dir-ent-list-p)
        (:rewrite
         fati-of-hifat-to-lofat-helper-disjoint-lemma-2)
        (:definition induction-scheme)))
      :expand
      ((:free (y) (intersectp-equal nil y))
       (:free (x1 x2 y)
              (intersectp-equal (list x1)
                                (cons x2 y)))
       (:free (fat32-in-memory dir-ent dir-ent-list entry-limit)
              (lofat-to-hifat-helper-exec
               fat32-in-memory
               (cons dir-ent dir-ent-list)
               entry-limit)))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and (lofat-fs-p fat32-in-memory)
            (m1-file-alist-p fs)
            (m1-bounded-file-alist-p fs)
            (m1-file-no-dups-p fs)
            (fat32-masked-entry-p current-dir-first-cluster)
            (<= *ms-first-data-cluster*
                current-dir-first-cluster)
            (< current-dir-first-cluster
               (+ *ms-first-data-cluster*
                  (count-of-clusters fat32-in-memory)))
            (integerp entry-limit)
            (>= entry-limit (m1-entry-count fs))
            (unmodifiable-listp x (effective-fat fat32-in-memory)))
       (b*
           (((mv fat32-in-memory dir-ent-list error-code)
             (hifat-to-lofat-helper
              fat32-in-memory
              fs current-dir-first-cluster)))
         (implies
          (zp error-code)
          (not-intersectp-list
           x
           (mv-nth 2
                   (lofat-to-hifat-helper-exec
                    fat32-in-memory
                    dir-ent-list entry-limit))))))))))

(defthm
  hifat-to-lofat-inversion-big-induction-corollaries
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (m1-bounded-file-alist-p fs)
        (m1-file-no-dups-p fs)
        (fat32-masked-entry-p current-dir-first-cluster)
        (<= *ms-first-data-cluster*
            current-dir-first-cluster)
        (< current-dir-first-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (integerp entry-limit)
        (>= entry-limit (m1-entry-count fs)))
   (b*
       (((mv fat32-in-memory dir-ent-list error-code)
         (hifat-to-lofat-helper
          fat32-in-memory
          fs current-dir-first-cluster)))
     (implies
      (zp error-code)
      (and (equal (mv-nth 3
                          (lofat-to-hifat-helper-exec
                           fat32-in-memory
                           dir-ent-list entry-limit))
                  0)
           (hifat-equiv (mv-nth 0
                                 (lofat-to-hifat-helper-exec
                                  fat32-in-memory
                                  dir-ent-list entry-limit))
                         fs)))))
  :hints
  (("goal"
    :in-theory (disable hifat-to-lofat-inversion-big-induction)
    :use
    (:instance hifat-to-lofat-inversion-big-induction
               (x nil)))))

(defthmd hifat-to-lofat-inversion-lemma-10
  (implies
   (atom dir-ent-list)
   (equal
    (lofat-to-hifat-helper-exec fat32-in-memory
                                     dir-ent-list entry-limit)
    (mv nil 0 nil 0)))
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper-exec)) ))

(defthmd
  hifat-to-lofat-inversion-lemma-11
  (implies
   (lofat-fs-p fat32-in-memory)
   (and
    (< (fat32-entry-mask (bpb_rootclus fat32-in-memory))
       (binary-+ '2
                 (count-of-clusters fat32-in-memory)))
    (not
     (<
      (binary-+ '2
                (count-of-clusters fat32-in-memory))
      (binary-+
       '1
       (fat32-entry-mask (bpb_rootclus fat32-in-memory))))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    hifat-to-lofat-inversion-lemma-12
    (implies (lofat-fs-p fat32-in-memory)
             (>= *ms-max-dir-size*
                 (cluster-size fat32-in-memory)))
    :rule-classes :linear
    :hints
    (("goal" :in-theory
      (disable lofat-fs-p-correctness-1)
      :use lofat-fs-p-correctness-1)))

  (defthmd
    hifat-to-lofat-inversion-lemma-13
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (stringp text)
          (equal (length text)
                 (cluster-size fat32-in-memory)))
     (equal
      (len (make-clusters text (cluster-size fat32-in-memory)))
      1))
    :hints
    (("goal"
      :in-theory
      (disable lofat-fs-p-correctness-1)
      :use
      (lofat-fs-p-correctness-1
       (:instance
        len-of-make-clusters
        (cluster-size (cluster-size fat32-in-memory))))))))

(defthm
  hifat-to-lofat-inversion
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (m1-bounded-file-alist-p fs)
        (m1-file-no-dups-p fs)
        (<=
         (m1-entry-count fs)
         (max-entry-count fat32-in-memory)))
   (b*
       (((mv fat32-in-memory error-code)
         (hifat-to-lofat
          fat32-in-memory fs)))
     (implies
      (zp error-code)
      (and
       (equal
        (mv-nth 1
                (lofat-to-hifat
                 fat32-in-memory))
        0)
       (hifat-equiv
        (mv-nth 0
                (lofat-to-hifat
                 fat32-in-memory))
        fs)))))
  :hints
  (("goal"
    :in-theory (enable lofat-to-hifat
                       hifat-to-lofat
                       root-dir-ent-list
                       hifat-to-lofat-helper-correctness-4
                       hifat-to-lofat-inversion-lemma-10
                       hifat-to-lofat-inversion-lemma-11
                       hifat-to-lofat-inversion-lemma-13
                       painful-debugging-lemma-10
                       painful-debugging-lemma-11))))

(defund-nx
  lofat-equiv
  (fat32-in-memory1 fat32-in-memory2)
  (b* (((mv fs1 error-code1)
        (lofat-to-hifat fat32-in-memory1))
       (good1 (and (lofat-fs-p fat32-in-memory1)
                   (equal error-code1 0)))
       ((mv fs2 error-code2)
        (lofat-to-hifat fat32-in-memory2))
       (good2 (and (lofat-fs-p fat32-in-memory2)
                   (equal error-code2 0)))
       ((unless (and good1 good2))
        (and (not good1) (not good2))))
    (hifat-equiv fs1 fs2)))

(defequiv
  lofat-equiv
  :hints (("goal" :in-theory (enable lofat-equiv))))

(defthm
  lofat-to-hifat-inversion
  (implies
   (lofat-fs-p fat32-in-memory)
   (b*
       (((mv fs error-code)
         (lofat-to-hifat fat32-in-memory)))
     (implies
      (and
       (equal error-code 0)
       (m1-bounded-file-alist-p fs)
       (m1-file-no-dups-p fs)
       ;; This clause should always be true, but that's not yet proven. The
       ;; argument is: The only time we get an error out of
       ;; hifat-to-lofat-helper (and the wrapper) is when we run out
       ;; of space. We shouldn't be able to run out of space when we just
       ;; extracted an m1 instance from fat32-in-memory, and we didn't change
       ;; the size of fat32-in-memory at all. However, that's going to involve
       ;; reasoning about the number of clusters taken up by an m1 instance,
       ;; which is not really where it's at right now.
       (equal
        (mv-nth
         1
         (hifat-to-lofat
          fat32-in-memory
          fs))
        0))
      (lofat-equiv
       (mv-nth
        0
        (hifat-to-lofat
         fat32-in-memory
         fs))
       fat32-in-memory))))
  :hints (("Goal" :in-theory (enable lofat-equiv)) ))

;; This is a version of lofat-to-hifat-helper-exec intended for some proofs related
;; to syscalls. We'll probably keep lofat-to-hifat-helper-exec around at least for
;; the invertibility proof, since the list of clusterchains is useful for
;; proving non-interference... but one more version of lofat-to-hifat-helper-exec
;; would help with a more efficient execution where the list of clusterchains
;; is not computed at all.
(defun
  lofat-to-hifat-helper
  (fat32-in-memory dir-ent-list entry-limit)
  (declare
   (xargs :measure (nfix entry-limit)
          :guard (and (natp entry-limit)
                      (useful-dir-ent-list-p dir-ent-list)
                      (lofat-fs-p fat32-in-memory))
          :verify-guards nil
          :stobjs (fat32-in-memory)))
  (b*
      (((when (atom dir-ent-list)) (mv nil 0))
       ((when (zp entry-limit)) (mv nil *eio*))
       (dir-ent (car dir-ent-list))
       (first-cluster (dir-ent-first-cluster dir-ent))
       (filename (dir-ent-filename dir-ent))
       (directory-p (dir-ent-directory-p dir-ent))
       (length (if directory-p *ms-max-dir-size*
                   (dir-ent-file-size dir-ent)))
       ((mv contents error-code)
        (if (or (< first-cluster *ms-first-data-cluster*)
                (>= first-cluster
                    (+ (count-of-clusters fat32-in-memory)
                       *ms-first-data-cluster*)))
            (mv "" 0)
            (get-clusterchain-contents
             fat32-in-memory first-cluster length)))
       ((mv head head-error-code)
        (if directory-p
            (lofat-to-hifat-helper
             fat32-in-memory
             (make-dir-ent-list (string=>nats contents))
             (- entry-limit 1))
            (mv contents 0)))
       (head-entry-count (if directory-p (m1-entry-count head)
                             0))
       (error-code (if (equal error-code 0)
                       head-error-code *eio*))
       (tail-entry-limit (nfix (- entry-limit
                                  (+ 1 (nfix head-entry-count)))))
       ((mv tail tail-error-code)
        (lofat-to-hifat-helper
         fat32-in-memory (cdr dir-ent-list)
         tail-entry-limit))
       (error-code (if (zp error-code)
                       tail-error-code error-code)))
    (mv (list* (cons filename
                     (make-m1-file :dir-ent dir-ent
                                   :contents head))
               tail)
        error-code)))

(defthmd
  lofat-to-hifat-helper-correctness-1
  (equal
   (lofat-to-hifat-helper fat32-in-memory
                                dir-ent-list entry-limit)
   (mv
    (mv-nth 0
            (lofat-to-hifat-helper-exec fat32-in-memory
                                   dir-ent-list entry-limit))
    (mv-nth 3
            (lofat-to-hifat-helper-exec fat32-in-memory
                                   dir-ent-list entry-limit))))
  :hints
  (("goal"
    :in-theory (enable lofat-to-hifat-helper-exec)
    :induct (lofat-to-hifat-helper-exec fat32-in-memory
                                   dir-ent-list entry-limit)
    :expand
    (lofat-to-hifat-helper fat32-in-memory
                                 dir-ent-list entry-limit))))
