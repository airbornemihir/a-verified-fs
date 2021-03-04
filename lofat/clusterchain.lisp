(in-package "ACL2")

;  clusterchain.lisp                                    Mihir Mehta

(include-book "stobj-find-n-free-clusters")
(include-book "../hifat")

;; These are some rules from other books which are either interacting badly
;; with the theory I've built up so far, or else causing a lot of unnecessary
;; frames and tries.
(local
 (in-theory (disable take-of-too-many take-when-atom make-list-ac-removal
                     revappend-removal str::hex-digit-char-listp-of-cons
                     loghead logtail
                     (:rewrite member-of-nth-when-not-intersectp)
                     (:rewrite
                      integer-listp-of-cdr-when-integer-listp)
                     (:rewrite
                      acl2-number-listp-of-cdr-when-acl2-number-listp)
                     (:definition integer-listp)
                     (:rewrite
                      rationalp-of-car-when-rational-listp)
                     (:definition acl2-number-listp)
                     (:rewrite flatten-when-not-consp)
                     (:definition rational-listp)
                     (:rewrite subsetp-trans2)
                     (:rewrite subsetp-trans)
                     (:rewrite stringp-when-nonempty-stringp)
                     (:rewrite
                      rational-listp-of-cdr-when-rational-listp)
                     (:rewrite rational-listp-when-not-consp)
                     (:rewrite no-duplicatesp-of-member)
                     (:rewrite true-listp-when-string-list)
                     not-intersectp-list-when-subsetp-2)))

(local
 (in-theory (disable nth update-nth ceiling floor mod true-listp)))

(defund
  get-cc
  (fat32$c masked-current-cluster length)
  (declare
   (xargs
    :stobjs fat32$c
    :measure (nfix length)
    :guard (and (lofat-fs-p fat32$c)
                (fat32-masked-entry-p masked-current-cluster)
                (natp length)
                (>= masked-current-cluster
                    *ms-first-data-cluster*)
                (< masked-current-cluster
                   (+ (count-of-clusters fat32$c)
                      *ms-first-data-cluster*)))))
  (b*
      ((cluster-size (cluster-size fat32$c))
       ((when
            (or (zp length) (zp cluster-size)))
        (mv nil (- *eio*)))
       (masked-next-cluster
        (fat32-entry-mask
         (if (mbt (< (nfix masked-current-cluster)
                     (nfix (+ (count-of-clusters fat32$c)
                              *ms-first-data-cluster*))))
             (fati masked-current-cluster fat32$c)
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
               :exec (+ (count-of-clusters fat32$c)
                        *ms-first-data-cluster*)
               :logic (nfix (+ (count-of-clusters fat32$c)
                               *ms-first-data-cluster*))))))
        (mv (list masked-current-cluster) 0))
       ((mv tail-index-list tail-error)
        (get-cc fat32$c masked-next-cluster
                          (nfix (- length cluster-size)))))
    (mv (list* masked-current-cluster tail-index-list)
        tail-error)))

(defthm
  get-cc-alt
  (equal (get-cc fat32$c
                 masked-current-cluster length)
         (fat32-build-index-list (effective-fat fat32$c)
                                 masked-current-cluster
                                 length (cluster-size fat32$c)))
  :rule-classes :definition
  :hints (("goal" :in-theory (enable get-cc fat32-build-index-list
                                     fati fat-length effective-fat nth))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defun
      get-contents-from-cc
      (fat32$c cc file-size)
    (declare
     (xargs
      :stobjs (fat32$c)
      :guard
      (and
       (lofat-fs-p fat32$c)
       (equal (data-region-length fat32$c)
              (count-of-clusters fat32$c))
       (fat32-masked-entry-list-p cc)
       (natp file-size)
       ;; A bug was here for a long time - the bound was set to
       ;; (count-of-clusters fat32$c), giving away the last two
       ;; clusters.
       (bounded-nat-listp cc
                          (+ *ms-first-data-cluster*
                             (count-of-clusters fat32$c)))
       (lower-bounded-integer-listp
        cc *ms-first-data-cluster*))))
    (if
        (atom cc)
        ""
      (let*
          ((cluster-size (cluster-size fat32$c))
           (masked-current-cluster (car cc)))
        (concatenate
         'string
         (subseq
          (data-regioni
           (nfix (- masked-current-cluster *ms-first-data-cluster*))
           fat32$c)
          0
          (min file-size cluster-size))
         (get-contents-from-cc
          fat32$c (cdr cc)
          (nfix (- file-size cluster-size)))))))

  (defthm
    stringp-of-get-contents-from-cc
    (stringp
     (get-contents-from-cc
      fat32$c cc file-size))
    :rule-classes :type-prescription)

  (defund
    get-cc-contents
    (fat32$c masked-current-cluster length)
    (declare
     (xargs
      :stobjs fat32$c
      :measure (nfix length)
      :guard (and (lofat-fs-p fat32$c)
                  (fat32-masked-entry-p masked-current-cluster)
                  (natp length)
                  (>= masked-current-cluster
                      *ms-first-data-cluster*)
                  (< masked-current-cluster
                     (+ (count-of-clusters fat32$c)
                        *ms-first-data-cluster*)))
      :verify-guards nil))
    (b*
        ((cluster-size (cluster-size fat32$c))
         ((unless (and (not (zp length))
                       (not (zp cluster-size))
                       (>= masked-current-cluster
                           *ms-first-data-cluster*)))
          (mv "" (- *eio*)))
         (current-cluster-contents
          (str-fix
           (data-regioni (- masked-current-cluster 2) fat32$c)))
         (masked-next-cluster
          (fat32-entry-mask
           ;; This mbt (must be true) form was inserted in order to comport
           ;; with our current definition of effective-fat, which is implicitly
           ;; used in the rule get-cc-contents-correctness-1.
           (if (mbt (< (nfix masked-current-cluster)
                       (nfix (+ (count-of-clusters fat32$c)
                                *ms-first-data-cluster*))))
               (fati masked-current-cluster fat32$c)
             nil)))
         ((unless (>= masked-next-cluster
                      *ms-first-data-cluster*))
          (mv (subseq current-cluster-contents 0 (min length cluster-size))
              (- *eio*)))
         ((unless (and (not (fat32-is-eof masked-next-cluster))
                       (< masked-next-cluster
                          (+ (count-of-clusters fat32$c)
                             *ms-first-data-cluster*))))
          (mv (subseq current-cluster-contents 0 (min length cluster-size)) 0))
         ((mv tail-string tail-error)
          (get-cc-contents
           fat32$c masked-next-cluster
           (nfix (- length cluster-size))))
         ((unless (equal tail-error 0))
          (mv "" (- *eio*))))
      (mv (concatenate 'string
                       current-cluster-contents
                       tail-string)
          0)))

  (defthm
    integerp-of-get-cc-contents
    (and
     (integerp (mv-nth 1
                       (get-cc-contents
                        fat32$c
                        masked-current-cluster length)))
     (>= 0
         (mv-nth 1
                 (get-cc-contents
                  fat32$c
                  masked-current-cluster length))))
    :rule-classes
    :type-prescription
    :hints
    (("goal" :in-theory (enable get-cc-contents)))))

(defthm
  stringp-of-get-cc-contents
  (stringp
   (mv-nth
    0
    (get-cc-contents fat32$c
                               masked-current-cluster length)))
  :rule-classes :type-prescription
  :hints
  (("goal" :in-theory (enable get-cc-contents))))

(verify-guards get-cc-contents)

(defthm
  get-cc-contents-correctness-2
  (implies
   (>= masked-current-cluster
       *ms-first-data-cluster*)
   (equal
    (mv-nth 1
            (fat32-build-index-list (effective-fat fat32$c)
                                    masked-current-cluster
                                    length (cluster-size fat32$c)))
    (mv-nth 1
            (get-cc-contents fat32$c
                                       masked-current-cluster length))))
  :hints (("goal" :in-theory (enable fat-length fati
                                     effective-fat fat32-build-index-list
                                     nth get-cc-contents))))

(defthm
  get-contents-from-cc-of-update-data-regioni
  (implies
   (and (integerp file-size)
        (lofat-fs-p fat32$c)
        (equal (data-region-length fat32$c)
               (count-of-clusters fat32$c))
        (natp i)
        (not (member-equal (+ i *ms-first-data-cluster*)
                           cc))
        (lower-bounded-integer-listp
         cc *ms-first-data-cluster*))
   (equal
    (get-contents-from-cc
     (update-data-regioni i v fat32$c)
     cc file-size)
    (get-contents-from-cc fat32$c
                                    cc file-size))))

(defthm
  get-cc-contents-correctness-1
  (implies
   (and
    (fat32-masked-entry-p masked-current-cluster)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1
                   (get-cc-contents fat32$c
                                              masked-current-cluster length))
           0))
   (equal (get-contents-from-cc
           fat32$c
           (mv-nth 0
                   (get-cc fat32$c
                                     masked-current-cluster length))
           length)
          (mv-nth 0
                  (get-cc-contents fat32$c
                                             masked-current-cluster length))))
  :hints (("goal" :in-theory (enable get-cc-contents
                                     fat32-build-index-list)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (fat32-masked-entry-p masked-current-cluster)
      (>= masked-current-cluster
          *ms-first-data-cluster*)
      (lofat-fs-p fat32$c)
      (equal
       (mv-nth 1
               (fat32-build-index-list (effective-fat fat32$c)
                                       masked-current-cluster
                                       length (cluster-size fat32$c)))
       0))
     (equal
      (get-contents-from-cc
       fat32$c
       (mv-nth 0
               (fat32-build-index-list (effective-fat fat32$c)
                                       masked-current-cluster
                                       length (cluster-size fat32$c)))
       length)
      (mv-nth 0
              (get-cc-contents fat32$c
                                         masked-current-cluster length)))))))

(defthm
  get-cc-contents-correctness-3
  (equal
   (mv
    (mv-nth
     0
     (get-cc-contents fat32$c
                                masked-current-cluster length))
    (mv-nth
     1
     (get-cc-contents fat32$c
                                masked-current-cluster length)))
   (get-cc-contents fat32$c
                              masked-current-cluster length))
  :hints (("Goal" :in-theory (enable get-cc-contents)) ))

(defthm
  length-of-get-cc-contents
  t
  :rule-classes
  ((:linear
    :corollary
    (implies
     (and (lofat-fs-p fat32$c)
          (natp length))
     (<=
      (len (explode (mv-nth 0
                            (get-cc-contents
                             fat32$c
                             masked-current-cluster length))))
      length))
    :hints (("Goal" :in-theory (enable get-cc-contents)) ))
   (:linear
    :corollary
    (implies
     (equal (mv-nth 1
                    (get-cc-contents fat32$c
                                               masked-current-cluster length))
            0)
     (<
      0
      (len
       (explode
        (mv-nth 0
                (get-cc-contents fat32$c
                                           masked-current-cluster length))))))
    :hints (("goal" :in-theory (enable get-cc-contents))))))

(defthm
  get-cc-contents-of-update-fati
  (implies
   (and
    (integerp masked-current-cluster)
    (not
     (member-equal
      i
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32$c)
                                      masked-current-cluster length
                                      (cluster-size fat32$c))))))
   (equal (get-cc-contents (update-fati i v fat32$c)
                                     masked-current-cluster length)
          (get-cc-contents fat32$c
                                     masked-current-cluster length)))
  :hints
  (("goal"
    :in-theory (enable get-cc-contents
                       fat32-build-index-list)
    :induct (get-cc-contents fat32$c
                                       masked-current-cluster length)
    :expand ((get-cc-contents (update-fati i v fat32$c)
                                        masked-current-cluster length)))))

(defund
  d-e-cc
  (fat32$c d-e)
  (declare
   (xargs
    :stobjs fat32$c
    :guard (and (lofat-fs-p fat32$c)
                (d-e-p d-e)
                (<= *ms-first-data-cluster*
                    (d-e-first-cluster d-e))
                (< (d-e-first-cluster d-e)
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32$c))))))
  (if (d-e-directory-p d-e)
      (get-cc fat32$c
                        (d-e-first-cluster d-e)
                        *ms-max-dir-size*)
    (get-cc fat32$c
                      (d-e-first-cluster d-e)
                      (d-e-file-size d-e))))

(defthm
  true-listp-of-d-e-cc
  (true-listp
   (mv-nth
    0
    (d-e-cc fat32$c d-e)))
  :hints
  (("goal" :in-theory (enable d-e-cc)))
  :rule-classes (:rewrite :type-prescription))

(defthm fat32-masked-entry-list-p-of-d-e-cc
  (implies (d-e-p d-e)
           (fat32-masked-entry-list-p (mv-nth 0 (d-e-cc fat32$c d-e))))
  :hints (("goal" :in-theory (enable d-e-cc))))

(defthm
  d-e-cc-of-update-fati
  (implies
   (and (d-e-p d-e)
        (<= *ms-first-data-cluster* (d-e-first-cluster d-e))
        (not
         (member-equal i
                       (mv-nth 0
                               (d-e-cc fat32$c d-e)))))
   (equal (d-e-cc (update-fati i v fat32$c)
                                d-e)
          (d-e-cc fat32$c d-e)))
  :hints (("goal" :in-theory (enable d-e-cc))))

(defthm
  d-e-cc-under-iff
  (implies (lofat-fs-p fat32$c)
           (iff (mv-nth 0 (d-e-cc fat32$c d-e))
                (or (d-e-directory-p d-e)
                    (not (zp (d-e-file-size d-e))))))
  :hints
  (("goal" :in-theory (e/d (d-e-cc)
                           (consp-of-fat32-build-index-list))
    :use ((:instance consp-of-fat32-build-index-list
                     (cluster-size (cluster-size fat32$c))
                     (length 0)
                     (masked-current-cluster (d-e-first-cluster d-e))
                     (fa-table (effective-fat fat32$c)))
          (:instance consp-of-fat32-build-index-list
                     (cluster-size (cluster-size fat32$c))
                     (length 2097152)
                     (masked-current-cluster (d-e-first-cluster d-e))
                     (fa-table (effective-fat fat32$c)))
          (:instance consp-of-fat32-build-index-list
                     (cluster-size (cluster-size fat32$c))
                     (length (d-e-file-size d-e))
                     (masked-current-cluster (d-e-first-cluster d-e))
                     (fa-table (effective-fat fat32$c))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (implies (lofat-fs-p fat32$c)
                        (equal (consp (mv-nth 0 (d-e-cc fat32$c d-e)))
                               (or (d-e-directory-p d-e)
                                   (not (zp (d-e-file-size d-e))))))
    :hints (("goal" :in-theory (e/d nil (get-cc-alt)))))
   (:rewrite :corollary (implies (and (lofat-fs-p fat32$c)
                                      (zp (d-e-file-size d-e))
                                      (not (d-e-directory-p d-e)))
                                 (equal (mv-nth 0 (d-e-cc fat32$c d-e))
                                        nil)))))

(defthm integer-listp-of-d-e-cc
  (integer-listp (mv-nth 0 (d-e-cc fat32$c d-e)))
  :hints (("goal" :in-theory (enable d-e-cc))))

(defund
  d-e-cc-contents
  (fat32$c d-e)
  (declare
   (xargs
    :stobjs fat32$c
    :guard (and (lofat-fs-p fat32$c)
                (d-e-p d-e)
                (<= *ms-first-data-cluster*
                    (d-e-first-cluster d-e))
                (< (d-e-first-cluster d-e)
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32$c))))))
  (if (d-e-directory-p d-e)
      (get-cc-contents fat32$c
                                 (d-e-first-cluster d-e)
                                 *ms-max-dir-size*)
    (get-cc-contents fat32$c
                               (d-e-first-cluster d-e)
                               (d-e-file-size d-e))))

(defthm
  stringp-of-d-e-cc-contents
  (stringp
   (mv-nth
    0
    (d-e-cc-contents fat32$c d-e)))
  :rule-classes :type-prescription
  :hints
  (("goal" :in-theory (enable d-e-cc-contents))))

(defthm
  length-of-d-e-cc-contents
  t
  :rule-classes
  ((:linear
    :corollary
    (implies
     (and (lofat-fs-p fat32$c)
          (not (d-e-directory-p d-e)))
     (<= (len (explode (mv-nth 0
                               (d-e-cc-contents
                                fat32$c d-e))))
         (d-e-file-size d-e)))
    :hints
    (("goal"
      :in-theory (enable d-e-cc-contents))))
   (:linear
    :corollary
    (implies
     (and (lofat-fs-p fat32$c)
          (d-e-directory-p d-e))
     (<= (len (explode (mv-nth 0
                               (d-e-cc-contents
                                fat32$c d-e))))
         *ms-max-dir-size*))
    :hints
    (("goal"
      :in-theory (enable d-e-cc-contents))))
   (:linear
    :corollary
    (implies
     (equal
      (mv-nth 1
              (d-e-cc-contents
               fat32$c d-e))
      0)
     (< 0
        (len (explode (mv-nth 0
                              (d-e-cc-contents
                               fat32$c d-e))))))
    :hints
    (("goal"
      :in-theory (enable d-e-cc-contents))))))

;; After the fashion of get-cc-contents-correctness-2, we're going to
;; rewrite instances of (mv-nth 1 (d-e-cc ...))
;; We're adding a return value for collecting all these ccs, to help
;; us ensure the separation properties we want. We're also adding a return
;; value, to signal an error when we run out of entries.
(defthm
  d-e-cc-correctness-1
  (implies
   (<= *ms-first-data-cluster*
       (d-e-first-cluster d-e))
   (equal (mv-nth 1
                  (d-e-cc fat32$c d-e))
          (mv-nth 1
                  (d-e-cc-contents fat32$c d-e))))
  :hints (("goal" :in-theory (enable d-e-cc
                                     d-e-cc-contents))))

(defthm
  d-e-cc-contents-of-update-fati
  (implies
   (not
    (member-equal i
                  (mv-nth 0
                          (d-e-cc fat32$c d-e))))
   (equal (d-e-cc-contents (update-fati i v fat32$c)
                                         d-e)
          (d-e-cc-contents fat32$c d-e)))
  :hints (("goal" :in-theory (enable d-e-cc-contents
                                     d-e-cc))))

(defthm
  integerp-of-d-e-cc-contents
  (and
   (integerp (mv-nth 1
                     (d-e-cc-contents fat32$c d-e)))
   (>= 0
       (mv-nth 1
               (d-e-cc-contents fat32$c d-e))))
  :rule-classes :type-prescription
  :hints (("goal" :in-theory (enable d-e-cc-contents))))

;; Here's the idea: while transforming from M2 to M1,
;; - we are not going to to take directory entries which are deleted
;; - we are not going to take dot or dotdot entries
(defund
  useless-d-e-p (d-e)
  (declare
   (xargs
    :guard (d-e-p d-e)
    :guard-hints
    (("goal" :in-theory (e/d (d-e-p d-e-first-cluster)
                             (unsigned-byte-p))))))
  (or
   ;; the byte #xe5 marks deleted files, according to the spec
   (equal (char (d-e-filename d-e) 0) (code-char #xe5))
   (equal (d-e-filename d-e)
          *current-dir-fat32-name*)
   (equal (d-e-filename d-e)
          *parent-dir-fat32-name*)))

(defthm
  useless-d-e-p-of-d-e-install-directory-bit
  (implies
   (d-e-p d-e)
   (equal (useless-d-e-p
           (d-e-install-directory-bit d-e val))
          (useless-d-e-p d-e)))
  :hints
  (("goal"
    :in-theory (enable d-e-install-directory-bit
                       useless-d-e-p d-e-filename))))

(defthm
  useless-d-e-p-of-d-e-set-filename
  (implies (fat32-filename-p filename)
           (not (useless-d-e-p (d-e-set-filename d-e filename))))
  :hints (("goal" :in-theory (enable useless-d-e-p))))

(defund
  make-d-e-list (dir-contents)
  (declare
   (xargs
    :guard (stringp dir-contents)
    :measure (length dir-contents)
    :guard-hints (("goal" :in-theory (enable d-e-p)))))
  (b*
      (((when (< (length dir-contents)
                 *ms-d-e-length*))
        nil)
       (d-e
        (mbe
         :exec
         (string=>nats (subseq dir-contents 0 *ms-d-e-length*))
         :logic
         (d-e-fix
          (chars=>nats
           (take *ms-d-e-length* (explode dir-contents))))))
       ;; From page 24 of the specification: "If DIR_Name[0] == 0x00, then the
       ;; directory entry is free (same as for 0xE5), and there are no
       ;; allocated directory entries after this one (all of the DIR_Name[0]
       ;; bytes in all of the entries after this one are also set to 0). The
       ;; special 0 value, rather than the 0xE5 value, indicates to FAT file
       ;; system driver code that the rest of the entries in this directory do
       ;; not need to be examined because they are all free."
       ((when (equal (char (d-e-filename d-e) 0)
                     (code-char 0)))
        nil)
       ((when (useless-d-e-p d-e))
        (make-d-e-list
         (subseq dir-contents *ms-d-e-length* nil))))
    (list*
     d-e
     (make-d-e-list (subseq dir-contents
                                *ms-d-e-length* nil)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthmd
    len-of-make-d-e-list
    (<= (len (make-d-e-list dir-contents))
        (floor (len (explode dir-contents))
               *ms-d-e-length*))
    :rule-classes
    ((:linear :trigger-terms ((len (make-d-e-list dir-contents))
                              (floor (len (explode dir-contents))
                                     *ms-d-e-length*))))
    :hints (("goal" :in-theory (enable make-d-e-list)))))

(defund useful-d-e-list-p (d-e-list)
  (declare (xargs :guard t))
  (if (atom d-e-list)
      (equal d-e-list nil)
    (and (d-e-p (car d-e-list))
         (not (equal (char (d-e-filename
                            (car d-e-list))
                           0)
                     (code-char #x00)))
         (not (useless-d-e-p (car d-e-list)))
         (useful-d-e-list-p (cdr d-e-list)))))

(defthm d-e-list-p-when-useful-d-e-list-p
  (implies (useful-d-e-list-p d-e-list)
           (d-e-list-p d-e-list))
  :hints
  (("Goal" :in-theory (enable useful-d-e-list-p))))

(defthm
  useful-d-e-list-p-of-make-d-e-list
  (useful-d-e-list-p (make-d-e-list dir-contents))
  :hints
  (("goal"
    :in-theory (enable make-d-e-list useful-d-e-list-p))))

(defthm
  useful-d-e-list-p-of-cdr
  (implies (useful-d-e-list-p d-e-list)
           (useful-d-e-list-p (cdr d-e-list)))
  :hints (("goal" :in-theory (enable useful-d-e-list-p))))

(defthm
  useful-d-e-list-p-correctness-1
  (implies (and (useful-d-e-list-p d-e-list)
                (consp d-e-list))
           (fat32-filename-p (d-e-filename (car d-e-list))))
  :hints (("goal" :in-theory (enable useful-d-e-list-p useless-d-e-p
                                     fat32-filename-p d-e-filename))))
