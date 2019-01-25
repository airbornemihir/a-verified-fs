(in-package "ACL2")

;  file-system-m1.lisp                                 Mihir Mehta

; An abstract model used, for the time being, for doing file operations such as
; lstat on the filesystem.

(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/io/read-ints" :dir :system)
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "rtl/rel9/arithmetic/top" :dir :system))
(include-book "kestrel/utilities/strings" :dir :system)
(include-book "std/strings/case-conversion" :dir :system)

(include-book "insert-text")
(include-book "fat32")

;; Some code from Matt, illustrating a technique to get a definition without
;; all the accompanying events.
#!bitops
(encapsulate
  ()

  (local (include-book "centaur/bitops/extra-defs" :dir :system))

; Redundant; copied from the book above.
  (define install-bit ((n natp) (val bitp) (x integerp))
    :parents (bitops)
    :short "@(call install-bit) sets @('x[n] = val'), where @('x') is an integer,
@('n') is a bit position, and @('val') is a bit."

    (mbe :logic
         (b* ((x     (ifix x))
              (n     (nfix n))
              (val   (bfix val))
              (place (ash 1 n))
              (mask  (lognot place)))
           (logior (logand x mask)
                   (ash val n)))
         :exec
         (logior (logand x (lognot (ash 1 n)))
                 (ash val n)))
    ///

    (defthmd install-bit**
      (equal (install-bit n val x)
             (if (zp n)
                 (logcons val (logcdr x))
               (logcons (logcar x)
                        (install-bit (1- n) val (logcdr x)))))
      :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs)))
      :rule-classes
      ((:definition
        :clique (install-bit)
        :controller-alist ((install-bit t nil nil)))))

    (add-to-ruleset ihsext-redefs install-bit**)
    (add-to-ruleset ihsext-recursive-redefs install-bit**)

    (defthm natp-install-bit
      (implies (not (and (integerp x)
                         (< x 0)))
               (natp (install-bit n val x)))
      :rule-classes :type-prescription)

    (defcong nat-equiv equal (install-bit n val x) 1)
    (defcong bit-equiv equal (install-bit n val x) 2)
    (defcong int-equiv equal (install-bit n val x) 3)

    (defthmd logbitp-of-install-bit-split
      ;; Disabled by default since it can cause case splits.
      (equal (logbitp m (install-bit n val x))
             (if (= (nfix m) (nfix n))
                 (equal val 1)
               (logbitp m x)))
      :hints(("Goal" :in-theory (enable logbitp-of-ash-split))))

    (add-to-ruleset ihsext-advanced-thms logbitp-of-install-bit-split)
    (acl2::add-to-ruleset! logbitp-case-splits logbitp-of-install-bit-split)

    (local (in-theory (e/d (logbitp-of-install-bit-split)
                           (install-bit))))

    (defthm logbitp-of-install-bit-same
      (equal (logbitp m (install-bit m val x))
             (equal val 1)))

    (defthm logbitp-of-install-bit-diff
      (implies (not (equal (nfix m) (nfix n)))
               (equal (logbitp m (install-bit n val x))
                      (logbitp m x))))

    (local
     (defthm install-bit-induct
       t
       :rule-classes ((:induction
                       :pattern (install-bit pos v i)
                       :scheme (logbitp-ind pos i)))))

    (defthm install-bit-of-install-bit-same
      (equal (install-bit a v (install-bit a v2 x))
             (install-bit a v x))
      :hints(("Goal" :in-theory (enable install-bit**))))

    (defthm install-bit-of-install-bit-diff
      (implies (not (equal (nfix a) (nfix b)))
               (equal (install-bit a v (install-bit b v2 x))
                      (install-bit b v2 (install-bit a v x))))
      :hints(("Goal" :in-theory (enable install-bit**)))
      :rule-classes ((:rewrite :loop-stopper ((a b install-bit)))))

    (add-to-ruleset ihsext-basic-thms
                    '(logbitp-of-install-bit-same
                      logbitp-of-install-bit-diff
                      install-bit-of-install-bit-same
                      install-bit-of-install-bit-diff))

    (defthm install-bit-when-redundant
      (implies (equal (logbit n x) b)
               (equal (install-bit n b x)
                      (ifix x)))
      :hints(("Goal" :in-theory (enable install-bit**))))

    (defthm unsigned-byte-p-of-install-bit
      (implies (and (unsigned-byte-p n x)
                    (< (nfix i) n))
               (unsigned-byte-p n (install-bit i v x)))
      :hints(("Goal" :in-theory (e/d (install-bit** unsigned-byte-p**)
                                     (unsigned-byte-p))))))
  )

;; This was taken from rtl/rel9/arithmetic/top with thanks.
(defthm product-less-than-zero
  (implies (case-split (or (not (complex-rationalp x))
                           (not (complex-rationalp y))))
           (equal (< (* x y) 0)
                  (if (< x 0)
                      (< 0 y)
                      (if (equal 0 x)
                          nil
                          (if (not (acl2-numberp x))
                              nil (< y 0)))))))

(defthm
  down-alpha-p-of-upcase-char
  (not (str::down-alpha-p (str::upcase-char x)))
  :hints
  (("goal"
    :in-theory (enable str::upcase-char str::down-alpha-p))))

(defthm
  charlist-has-some-down-alpha-p-of-upcase-charlist
  (not (str::charlist-has-some-down-alpha-p
        (str::upcase-charlist x)))
  :hints
  (("goal"
    :in-theory (enable str::charlist-has-some-down-alpha-p
                       str::upcase-charlist))))

(defthmd integer-listp-when-unsigned-byte-listp
  (implies (not (integer-listp x))
           (not (unsigned-byte-listp n x))))

(defund dir-ent-p (x)
  (declare (xargs :guard t))
  (and (unsigned-byte-listp 8 x)
       (equal (len x) *ms-dir-ent-length*)))

(defthm dir-ent-p-correctness-1
  (implies (dir-ent-p x)
           (not (stringp x)))
  :hints (("goal" :in-theory (enable dir-ent-p)))
  :rule-classes :forward-chaining)

(defthm len-when-dir-ent-p
  (implies (dir-ent-p dir-ent)
           (equal (len dir-ent)
                  *ms-dir-ent-length*))
  :hints (("goal" :in-theory (enable dir-ent-p))))

(defthmd
  integer-listp-when-dir-ent-p
  (implies (dir-ent-p x)
           (integer-listp x))
  :hints
  (("goal" :in-theory
    (enable dir-ent-p
            integer-listp-when-unsigned-byte-listp))))

(defthm unsigned-byte-listp-when-dir-ent-p
  (implies (dir-ent-p dir-ent)
           (unsigned-byte-listp 8 dir-ent))
  :hints (("goal" :in-theory (enable dir-ent-p))))

(defthm dir-ent-p-of-update-nth
  (implies (dir-ent-p l)
           (equal (dir-ent-p (update-nth key val l))
                  (and (< (nfix key) *ms-dir-ent-length*)
                       (unsigned-byte-p 8 val))))
  :hints (("goal" :in-theory (enable dir-ent-p))))

(defthm dir-ent-p-of-append
  (equal (dir-ent-p (binary-append x y))
         (and (equal (+ (len x) (len y))
                     *ms-dir-ent-length*)
              (unsigned-byte-listp 8 y)
              (unsigned-byte-listp 8 (true-list-fix x))))
  :hints (("goal" :in-theory (enable dir-ent-p))))

(defthm
  nth-when-dir-ent-p
  (implies (dir-ent-p dir-ent)
           (equal (unsigned-byte-p 8 (nth n dir-ent))
                  (< (nfix n) *ms-dir-ent-length*)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (dir-ent-p dir-ent)
             (equal (integerp (nth n dir-ent))
                    (< (nfix n) *ms-dir-ent-length*)))
    :hints
    (("goal" :in-theory (enable integer-listp-when-dir-ent-p))))
   (:linear
    :corollary (implies (and (dir-ent-p dir-ent)
                             (< (nfix n) *ms-dir-ent-length*))
                        (and (<= 0 (nth n dir-ent))
                             (< (nth n dir-ent) (ash 1 8))))
    :hints
    (("goal"
      :in-theory
      (disable unsigned-byte-p-of-nth-when-unsigned-byte-listp
               nth))))))

(defun dir-ent-fix (x)
  (declare (xargs :guard t))
  (if
      (dir-ent-p x)
      x
    (make-list *ms-dir-ent-length* :initial-element 0)))

(defthm dir-ent-p-of-dir-ent-fix
  (dir-ent-p (dir-ent-fix x)))

(fty::deffixtype
 dir-ent
 :pred dir-ent-p
 :fix dir-ent-fix
 :equiv dir-ent-equiv
 :define t
 :forward t)

(fty::deflist dir-ent-list
      :elt-type dir-ent
      :true-listp t
    )

(defthm dir-ent-first-cluster-guard-lemma-1
  (implies (and (unsigned-byte-p 8 a3)
                (unsigned-byte-p 8 a2)
                (unsigned-byte-p 8 a1)
                (unsigned-byte-p 8 a0))
           (fat32-entry-p (combine32u a3 a2 a1 a0)))
  :hints (("goal" :in-theory (e/d (fat32-entry-p)
                                  (unsigned-byte-p)))))

(defund dir-ent-first-cluster (dir-ent)
  (declare
   (xargs :guard (dir-ent-p dir-ent)
          :guard-hints (("Goal" :in-theory (enable dir-ent-p)))))
  (fat32-entry-mask
   (combine32u (nth 21 dir-ent)
               (nth 20 dir-ent)
               (nth 27 dir-ent)
               (nth 26 dir-ent))))

(defthm fat32-masked-entry-p-of-dir-ent-first-cluster
  (implies
   (dir-ent-p dir-ent)
   (fat32-masked-entry-p (dir-ent-first-cluster dir-ent)))
  :hints (("goal" :in-theory (e/d (dir-ent-first-cluster dir-ent-p)))))

(defund dir-ent-file-size (dir-ent)
  (declare
   (xargs :guard (dir-ent-p dir-ent)
          :guard-hints (("Goal" :in-theory (enable dir-ent-p)))))
  (combine32u (nth 31 dir-ent)
              (nth 30 dir-ent)
              (nth 29 dir-ent)
              (nth 28 dir-ent)))

(defthm
  dir-ent-file-size-correctness-1
  (implies (dir-ent-p dir-ent)
           (and (<= 0 (dir-ent-file-size dir-ent))
                (< (dir-ent-file-size dir-ent)
                   (ash 1 32))))
  :rule-classes :linear
  :hints (("goal" :in-theory (e/d (dir-ent-file-size)
                                  (combine32u-unsigned-byte))
           :use (:instance combine32u-unsigned-byte
                           (a3 (nth 31 dir-ent))
                           (a2 (nth 30 dir-ent))
                           (a1 (nth 29 dir-ent))
                           (a0 (nth 28 dir-ent))))))

(defund
  dir-ent-set-first-cluster-file-size
  (dir-ent first-cluster file-size)
  (declare
   (xargs
    :guard (and (dir-ent-p dir-ent)
                (fat32-masked-entry-p first-cluster)
                (unsigned-byte-p 32 file-size))
    :guard-hints
    (("goal" :in-theory (enable dir-ent-p)))))
  (let*
   ((dir-ent (dir-ent-fix dir-ent))
    (old-first-cluster (combine32u (nth 21 dir-ent)
                                   (nth 20 dir-ent)
                                   (nth 27 dir-ent)
                                   (nth 26 dir-ent)))
    (new-first-cluster
     (mbe
      :logic
      (fat32-entry-fix
       (fat32-update-lower-28 old-first-cluster first-cluster))
      :exec
      (fat32-update-lower-28 old-first-cluster first-cluster)))
    (file-size (if (not (unsigned-byte-p 32 file-size))
                   0 file-size)))
   (append
    (subseq dir-ent 0 20)
    (list*
     (logtail 16 (loghead 24 new-first-cluster))
     (logtail 24 new-first-cluster)
     (append (subseq dir-ent 22 26)
             (list (loghead 8 new-first-cluster)
                   (logtail 8 (loghead 16 new-first-cluster))
                   (loghead 8 file-size)
                   (logtail 8 (loghead 16 file-size))
                   (logtail 16 (loghead 24 file-size))
                   (logtail 24 file-size)))))))

(defthm
  dir-ent-first-cluster-of-dir-ent-set-first-cluster-file-size
  (implies (and (dir-ent-p dir-ent)
                (fat32-masked-entry-p first-cluster)
                (natp file-size))
           (equal (dir-ent-first-cluster
                   (dir-ent-set-first-cluster-file-size
                    dir-ent first-cluster file-size))
                  first-cluster))
  :hints
  (("goal"
    :in-theory
    (e/d (dir-ent-set-first-cluster-file-size
          dir-ent-first-cluster dir-ent-p)
         (loghead logtail
                  fat32-update-lower-28-correctness-1))
    :use (:instance fat32-update-lower-28-correctness-1
                    (masked-entry first-cluster)
                    (entry (combine32u (nth 21 dir-ent)
                                       (nth 20 dir-ent)
                                       (nth 27 dir-ent)
                                       (nth 26 dir-ent)))))))

(defthm
  dir-ent-file-size-of-dir-ent-set-first-cluster-file-size
  (implies (and (dir-ent-p dir-ent)
                (unsigned-byte-p 32 file-size)
                (natp first-cluster))
           (equal (dir-ent-file-size
                   (dir-ent-set-first-cluster-file-size
                    dir-ent first-cluster file-size))
                  file-size))
  :hints
  (("goal" :in-theory (e/d (dir-ent-set-first-cluster-file-size dir-ent-file-size)
                           (loghead logtail)))))

(defthm
  dir-ent-p-of-dir-ent-set-first-cluster-file-size
  (implies
   (and (dir-ent-p dir-ent)
        (fat32-masked-entry-p first-cluster)
        (unsigned-byte-p 32 file-size))
   (and
    (unsigned-byte-listp 8
                         (dir-ent-set-first-cluster-file-size
                          dir-ent first-cluster file-size))
    (equal (len (dir-ent-set-first-cluster-file-size
                 dir-ent first-cluster file-size))
           *ms-dir-ent-length*)))
  :hints
  (("goal"
    :in-theory
    (e/d (dir-ent-p dir-ent-set-first-cluster-file-size
                    fat32-masked-entry-p fat32-entry-p)
         (fat32-update-lower-28-correctness-1))
    :use (:instance fat32-update-lower-28-correctness-1
                    (masked-entry first-cluster)
                    (entry (combine32u (nth 21 dir-ent)
                                       (nth 20 dir-ent)
                                       (nth 27 dir-ent)
                                       (nth 26 dir-ent))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (dir-ent-p dir-ent)
                  (fat32-masked-entry-p first-cluster)
                  (unsigned-byte-p 32 file-size))
             (dir-ent-p (dir-ent-set-first-cluster-file-size
                         dir-ent first-cluster file-size)))
    :hints (("goal" :in-theory (enable dir-ent-p))))))

(defund dir-ent-filename (dir-ent)
  (declare
   (xargs :guard (dir-ent-p dir-ent)
          :guard-hints (("Goal" :in-theory (enable dir-ent-p)))))
  (nats=>string (subseq dir-ent 0 11)))

(defthm
  dir-ent-filename-of-dir-ent-set-first-cluster-file-size
  (implies
   (dir-ent-p dir-ent)
   (equal
    (dir-ent-filename (dir-ent-set-first-cluster-file-size
                       dir-ent first-cluster file-size))
    (dir-ent-filename dir-ent)))
  :hints
  (("goal"
    :in-theory
    (e/d (dir-ent-set-first-cluster-file-size dir-ent-filename)
         (loghead logtail (:rewrite logtail-loghead))))))

(defund
  dir-ent-set-filename (dir-ent filename)
  (declare
   (xargs
    :guard (and (dir-ent-p dir-ent)
                (stringp filename)
                (equal (length filename) 11))
    :guard-hints (("goal" :in-theory (enable dir-ent-p)))))
  (mbe :exec (append (string=>nats filename)
                     (subseq dir-ent 11 *ms-dir-ent-length*))
       :logic
       (dir-ent-fix
        (append (string=>nats filename)
                (subseq dir-ent 11 *ms-dir-ent-length*)))))

(defthm
  dir-ent-p-of-dir-ent-set-filename
  (dir-ent-p (dir-ent-set-filename dir-ent filename))
  :hints (("goal" :in-theory (enable dir-ent-set-filename)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (unsigned-byte-listp
                8
                (dir-ent-set-filename dir-ent filename))
    :hints (("goal" :in-theory (enable dir-ent-p))))
   (:rewrite
    :corollary
    (true-listp (dir-ent-set-filename dir-ent filename))
    :hints (("goal" :in-theory (enable dir-ent-p))))))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (defthm dir-ent-p-of-set-first-cluster-file-size
    (dir-ent-p (dir-ent-set-first-cluster-file-size dir-ent first-cluster file-size))
    :hints (("goal" :in-theory (e/d (dir-ent-p
                                     dir-ent-set-first-cluster-file-size
                                     fat32-masked-entry-fix fat32-masked-entry-p)
                                    (loghead logtail))))))

;; per table on page 24 of the spec.
(defund
  dir-ent-directory-p (dir-ent)
  (declare
   (xargs
    :guard (dir-ent-p dir-ent)
    :guard-hints
    (("goal"
      :in-theory (enable integer-listp-when-dir-ent-p)))))
  (logbitp 4 (nth 11 dir-ent)))

(defund
  dir-ent-install-directory-bit
  (dir-ent val)
  (declare
   (xargs
    :guard (and (dir-ent-p dir-ent) (booleanp val))
    :guard-hints
    (("goal"
      :in-theory (enable integer-listp-when-dir-ent-p)))))
  (update-nth 11
              (install-bit 4 (if val 1 0)
                           (nth 11 dir-ent))
              dir-ent))

(defthm
  dir-ent-p-of-dir-ent-install-directory-bit
  (implies
   (dir-ent-p dir-ent)
   (dir-ent-p
    (dir-ent-install-directory-bit dir-ent val)))
  :hints
  (("goal"
    :in-theory
    (e/d (dir-ent-install-directory-bit dir-ent-p)))))

(defthm
  true-listp-of-dir-ent-install-directory-bit
  (implies
   (dir-ent-p dir-ent)
   (true-listp (dir-ent-install-directory-bit dir-ent val))))

(defthm
  dir-ent-install-directory-bit-correctness-1
  (equal (nth 0
              (dir-ent-install-directory-bit dir-ent val))
         (nth 0 dir-ent))
  :hints
  (("goal" :in-theory (enable dir-ent-install-directory-bit))))

(defthm
  dir-ent-directory-p-of-dir-ent-install-directory-bit
  (equal (dir-ent-directory-p
          (dir-ent-install-directory-bit dir-ent val))
         (if val t nil))
  :hints
  (("goal"
    :in-theory
    (e/d (dir-ent-install-directory-bit dir-ent-directory-p)
         (logbitp)))))

(defthm
  dir-ent-first-cluster-of-dir-ent-install-directory-bit
  (equal (dir-ent-first-cluster
          (dir-ent-install-directory-bit dir-ent val))
         (dir-ent-first-cluster dir-ent))
  :hints
  (("goal" :in-theory (enable dir-ent-first-cluster
                              dir-ent-install-directory-bit))))

(defthm
  dir-ent-file-size-of-dir-ent-install-directory-bit
  (equal (dir-ent-file-size
          (dir-ent-install-directory-bit dir-ent val))
         (dir-ent-file-size dir-ent))
  :hints
  (("goal" :in-theory (enable dir-ent-file-size
                              dir-ent-install-directory-bit))))

(defun fat32-filename-p (x)
  (declare (xargs :guard t))
  (and (stringp x)
       (equal (length x) 11)
       (not (equal (char x 0) (code-char #x00)))
       (not (equal (char x 0) (code-char #xe5)))
       (not (equal x *current-dir-fat32-name*))
       (not (equal x *parent-dir-fat32-name*))))

(defun
  fat32-filename-fix (x)
  (declare (xargs :guard (fat32-filename-p x)))
  (mbe
   :logic (if (fat32-filename-p x)
              x
              (coerce (make-list 11 :initial-element #\space)
                      'string))
   :exec x))

(defthm fat32-filename-p-of-fat32-filename-fix
  (fat32-filename-p (fat32-filename-fix x)))

(defthm fat32-filename-p-when-fat32-filename-p
  (implies (fat32-filename-p x)
           (equal (fat32-filename-fix x) x)))

(fty::deffixtype
 fat32-filename
 :pred fat32-filename-p
 :fix fat32-filename-fix
 :equiv fat32-filename-equiv
 :define t
 :forward t)

(make-event
 `(defthm
    fat32-filename-p-correctness-1
    (implies (fat32-filename-p x)
             (and (stringp x)
                  (equal (len (explode x)) 11)
                  (not (equal (nth 0 (explode x)) ,(code-char #x00)))
                  (not (equal (nth 0 (explode x)) ,(code-char #xe5)))
                  (not (equal x *current-dir-fat32-name*))
                  (not (equal x *parent-dir-fat32-name*))))))

(defthm dir-ent-set-filename-correctness-1
  (implies
   (and (fat32-filename-p filename)
        (dir-ent-p dir-ent))
   (and
    (not (equal (nth 0
                     (dir-ent-set-filename dir-ent filename))
                0))
    (not (equal (nth 0
                     (dir-ent-set-filename dir-ent filename))
                229))))
  :hints
  (("goal" :in-theory (e/d (dir-ent-set-filename dir-ent-p)
                           (nth)))))

(defthm
  dir-ent-directory-p-of-dir-ent-set-filename
  (implies (and (dir-ent-p dir-ent)
                (fat32-filename-p filename))
           (equal (dir-ent-directory-p
                   (dir-ent-set-filename dir-ent filename))
                  (dir-ent-directory-p dir-ent)))
  :hints (("goal" :in-theory (e/d (dir-ent-directory-p
                                   dir-ent-set-filename
                                   dir-ent-p)
                                  (logbitp)))))

(defthm
  dir-ent-first-cluster-of-dir-ent-set-filename
  (implies (and (dir-ent-p dir-ent)
                (stringp filename)
                (equal (length filename) 11))
           (equal (dir-ent-first-cluster
                   (dir-ent-set-filename dir-ent filename))
                  (dir-ent-first-cluster dir-ent)))
  :hints
  (("goal" :in-theory (enable dir-ent-first-cluster
                              dir-ent-set-filename dir-ent-p)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (dir-ent-p dir-ent)
          (fat32-filename-p filename))
     (equal (dir-ent-first-cluster
             (dir-ent-set-filename dir-ent filename))
            (dir-ent-first-cluster dir-ent)))
    :hints (("goal" :in-theory (enable fat32-filename-p))))))

(defthm
  dir-ent-filename-of-dir-ent-set-filename
  (implies
   (and (dir-ent-p dir-ent)
        (fat32-filename-p filename))
   (equal
    (dir-ent-filename (dir-ent-set-filename dir-ent filename))
    filename))
  :hints
  (("goal" :in-theory (enable dir-ent-filename
                              dir-ent-set-filename dir-ent-p))))

(defthm
  dir-ent-file-size-of-dir-ent-set-filename
  (implies
   (and (dir-ent-p dir-ent)
        (fat32-filename-p filename))
   (equal
    (dir-ent-file-size (dir-ent-set-filename dir-ent filename))
    (dir-ent-file-size dir-ent)))
  :hints (("goal" :in-theory (enable dir-ent-file-size
                                     dir-ent-set-filename))))

(defthm
  dir-ent-directory-p-of-dir-ent-set-first-cluster-file-size
  (implies
   (dir-ent-p dir-ent)
   (equal
    (dir-ent-directory-p (dir-ent-set-first-cluster-file-size
                          dir-ent first-cluster file-size))
    (dir-ent-directory-p dir-ent)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (dir-ent-directory-p dir-ent-set-first-cluster-file-size)
     (logbitp)))))

(fty::deflist fat32-filename-list
      :elt-type fat32-filename      ;; required, must have a known fixing function
      :true-listp t
    )

;; We need to write this whole thing out - based on an idea we got from an
;; event generated by fty::defalist - because the induction scheme has to be
;; created by us, without assistance from fty, just this once.
(defund
  m1-file-alist-p (x)
  (declare (xargs :guard t))
  (b* (((when (atom x)) (equal x nil))
       (head (car x))
       ((when (atom head)) nil)
       (file (cdr head))
       ((unless (and (alistp file)
                     (equal (strip-cars file)
                            '(dir-ent contents))))
        nil)
       (dir-ent (cdr (std::da-nth 0 (cdr head))))
       (contents (cdr (std::da-nth 1 (cdr head)))))
    (and (fat32-filename-p (car head))
         (dir-ent-p dir-ent)
         (or (and (stringp contents)
                  (unsigned-byte-p 32 (length contents)))
             (m1-file-alist-p contents))
         (m1-file-alist-p (cdr x)))))

(defund m1-file-contents-p (contents)
  (declare (xargs :guard t))
  (or (and (stringp contents)
           (unsigned-byte-p 32 (length contents)))
      (m1-file-alist-p contents)))

(defund m1-file-contents-fix (contents)
  (declare (xargs :guard t))
  (if (m1-file-contents-p contents)
      contents
    ""))

(defthm
  m1-file-contents-p-correctness-1
  (implies (m1-file-alist-p contents)
           (m1-file-contents-p contents))
  :hints (("goal" :in-theory (enable m1-file-contents-p))))

(defthm m1-file-contents-p-of-m1-file-contents-fix
  (m1-file-contents-p (m1-file-contents-fix x))
  :hints (("goal" :in-theory (enable m1-file-contents-fix))))

(defthm m1-file-contents-fix-when-m1-file-contents-p
  (implies (m1-file-contents-p x)
           (equal (m1-file-contents-fix x) x))
  :hints (("goal" :in-theory (enable m1-file-contents-fix))))

(defthm
  m1-file-contents-p-when-stringp
  (implies (stringp contents)
           (equal (m1-file-contents-p contents)
                  (unsigned-byte-p 32 (length contents))))
  :hints (("goal" :in-theory (enable m1-file-contents-p m1-file-alist-p))))

(defthm
  m1-file-alist-p-of-m1-file-contents-fix
  (equal (m1-file-alist-p (m1-file-contents-fix contents))
         (m1-file-alist-p contents))
  :hints (("goal" :in-theory (enable m1-file-contents-fix))))

(fty::deffixtype m1-file-contents
  :pred m1-file-contents-p
  :fix m1-file-contents-fix
  :equiv m1-file-contents-equiv
  :define t)

(fty::defprod
 m1-file
 ((dir-ent dir-ent-p :default (dir-ent-fix nil))
  (contents m1-file-contents-p :default (m1-file-contents-fix nil))))

(defthm
  acl2-count-of-m1-file->contents
  (implies (m1-file-p file)
           (< (acl2-count (m1-file->contents file))
              (acl2-count file)))
  :rule-classes :linear
  :hints
  (("goal" :in-theory (enable m1-file-p m1-file->contents))))

(defund m1-regular-file-p (file)
  (declare (xargs :guard t))
  (and (m1-file-p file)
       (stringp (m1-file->contents file))
       (unsigned-byte-p 32 (length (m1-file->contents file)))))

(defund m1-directory-file-p (file)
  (declare (xargs :guard t))
  (and (m1-file-p file)
       (m1-file-alist-p (m1-file->contents file))))

(encapsulate
  ()

  (local
   (defthm
     m1-regular-file-p-correctness-1-lemma-1
     (implies (stringp (m1-file->contents file))
              (not (m1-file-alist-p (m1-file->contents file))))
     :hints (("goal" :in-theory (enable m1-file-alist-p)))))

  (defthm
    m1-regular-file-p-correctness-1
    (implies (m1-regular-file-p file)
             (and (stringp (m1-file->contents file))
                  (not (m1-directory-file-p file))))
    :hints
    (("goal"
      :in-theory (enable m1-regular-file-p m1-directory-file-p)))
    :rule-classes
    ((:rewrite
      :corollary (implies (m1-regular-file-p file)
                          (stringp (m1-file->contents file))))
     (:rewrite
      :corollary (implies (m1-regular-file-p file)
                          (not (m1-directory-file-p file)))))))

(defthm m1-file-p-when-m1-regular-file-p
  (implies
   (m1-regular-file-p file)
   (m1-file-p file))
  :hints (("Goal" :in-theory (enable m1-regular-file-p))))

(defthm
  length-of-m1-file->contents
  (implies
   (m1-regular-file-p file)
   (unsigned-byte-p 32 (length (m1-file->contents file))))
  :hints (("goal" :in-theory (enable m1-regular-file-p)))
  :rule-classes
  ((:linear :corollary
            (implies (m1-regular-file-p file)
                     (< (len (explode (m1-file->contents file)))
                        (ash 1 32))))))

(defthm
  m1-directory-file-p-correctness-1
  (implies (m1-directory-file-p file)
           (and (m1-file-p file)
                (not (stringp (m1-file->contents file)))))
  :hints (("goal"
           :in-theory (enable m1-directory-file-p m1-file-alist-p
                              m1-regular-file-p))))

(defthm
  m1-file-alist-p-of-m1-file->contents
  (equal
   (m1-file-alist-p (m1-file->contents file))
   (m1-directory-file-p (m1-file-fix file)))
  :hints (("Goal" :in-theory (enable m1-file->contents m1-directory-file-p))))

(defthm
  m1-directory-file-p-of-m1-file
  (implies (m1-file-alist-p contents)
           (m1-directory-file-p (m1-file dir-ent contents)))
  :hints (("goal" :in-theory (enable m1-directory-file-p))))

(defthm
  m1-file-alist-p-of-revappend
  (equal (m1-file-alist-p (revappend x y))
         (and (m1-file-alist-p (list-fix x))
              (m1-file-alist-p y)))
  :hints
  (("goal"
    :use
    ((:functional-instance
      element-list-p-of-revappend
      (element-p (lambda (x)
                         (and (consp x)
                              (fat32-filename-p (car x))
                              (m1-file-p (cdr x)))))
      (non-element-p (lambda (x)
                             (not (and (consp x)
                                       (fat32-filename-p (car x))
                                       (m1-file-p (cdr x))))))
      (element-list-p (lambda (x) (m1-file-alist-p x)))
      (element-list-final-cdr-p not)))
    :in-theory (enable m1-file-alist-p
                       m1-file-p m1-file-contents-p)))
  :rule-classes ((:rewrite)))

(fty::defalist m1-file-alist
      :key-type fat32-filename
      :val-type m1-file
      :true-listp t)

(in-theory (disable fat32-filename-p fat32-filename-fix))

(defthm
  m1-file-alist-p-of-delete-assoc-equal
  (implies (m1-file-alist-p fs)
           (m1-file-alist-p (delete-assoc-equal key fs))))

(defun
  m1-bounded-file-alist-p-helper (x ac)
  (declare (xargs :guard (and (m1-file-alist-p x) (natp ac))
                  :measure (acl2-count x)))
  (and
   (not (zp ac))
   (or
    (atom x)
    (let
     ((head (car x)))
     (and
      (consp head)
      (let
       ((file (cdr head)))
       (if
        (m1-directory-file-p file)
        (and (m1-bounded-file-alist-p-helper (m1-file->contents file)
                                      *ms-max-dir-ent-count*)
             (m1-bounded-file-alist-p-helper (cdr x)
                                      (- ac 1)))
        (m1-bounded-file-alist-p-helper (cdr x)
                                 (- ac 1)))))))))

(defthmd len-when-m1-bounded-file-alist-p-helper
  (implies (m1-bounded-file-alist-p-helper x ac)
           (< (len x) (nfix ac)))
  :rule-classes :linear)

(defund
  m1-bounded-file-alist-p (x)
  (declare (xargs :guard (m1-file-alist-p x)))
  (m1-bounded-file-alist-p-helper x *ms-max-dir-ent-count*))

(defthm
  len-when-m1-bounded-file-alist-p
  (implies (m1-bounded-file-alist-p x)
           (< (len x) *ms-max-dir-ent-count*))
  :rule-classes
  (:linear
   (:linear
    :corollary (implies (m1-bounded-file-alist-p x)
                        (< (* *ms-dir-ent-length* (len x))
                           (* *ms-dir-ent-length*
                              *ms-max-dir-ent-count*))))
   (:linear
    :corollary (implies (and (m1-bounded-file-alist-p x) (consp x))
                        (< (* *ms-dir-ent-length* (len (cdr x)))
                           (-
                            (* *ms-dir-ent-length*
                               *ms-max-dir-ent-count*)
                            *ms-dir-ent-length*)))))
  :hints
  (("goal"
    :in-theory (enable m1-bounded-file-alist-p)
    :use (:instance len-when-m1-bounded-file-alist-p-helper
                    (ac *ms-max-dir-ent-count*)))))

(defthmd m1-bounded-file-alist-p-of-cdr-lemma-1
  (implies (and (m1-bounded-file-alist-p-helper x ac1)
                (< ac1 ac2)
                (not (zp ac2)))
           (m1-bounded-file-alist-p-helper x ac2)))

(defthm
  m1-bounded-file-alist-p-of-cdr-lemma-2
  (implies (and (m1-bounded-file-alist-p-helper x ac)
                (consp x))
           (m1-bounded-file-alist-p-helper (cdr x)
                                           ac))
  :hints
  (("goal" :induct (m1-bounded-file-alist-p-helper x ac))
   ("subgoal *1/3"
    :use (:instance m1-bounded-file-alist-p-of-cdr-lemma-1
                    (x (cdr x))
                    (ac1 (- ac 1))
                    (ac2 ac)))
   ("subgoal *1/1"
    :use (:instance m1-bounded-file-alist-p-of-cdr-lemma-1
                    (x (cdr x))
                    (ac1 (- ac 1))
                    (ac2 ac)))))

(defthm
  m1-bounded-file-alist-p-of-cdr
  (implies (and (m1-bounded-file-alist-p x) (consp x))
           (m1-bounded-file-alist-p (cdr x)) )
  :hints
  (("goal"
    :in-theory (enable m1-bounded-file-alist-p))))

(defthm
  m1-bounded-file-alist-p-of-cdar-lemma-1
  (implies (and (m1-file-p x)
                (not (m1-regular-file-p x)))
           (m1-directory-file-p x))
  :hints
  (("goal"
    :in-theory (enable m1-regular-file-p
                       m1-directory-file-p m1-file-p
                       m1-file-contents-p m1-file->contents))))

(defthm
  m1-bounded-file-alist-p-of-cdar
  (implies
   (and (m1-bounded-file-alist-p x)
        (consp x)
        (m1-directory-file-p (cdar x)))
   (m1-bounded-file-alist-p (m1-file->contents (cdar x))))
  :hints (("goal" :in-theory (enable m1-bounded-file-alist-p))))

(fty::defprod
 struct-stat
 ;; Currently, this is the only thing I can decipher.
 ((st_size natp :default 0)))

(fty::defprod
 struct-statfs
 ((f_type natp :default 0)
  (f_bsize natp :default 0)
  (f_blocks natp :default 0)
  (f_bfree natp :default 0)
  (f_bavail natp :default 0)
  (f_files natp :default 0)
  (f_ffree natp :default 0)
  (f_fsid natp :default 0)
  (f_namelen natp :default 72)))

;; This data structure may change later.
(fty::defprod
 file-table-element
 ((pos natp) ;; index within the file
  ;; mode ?
  (fid fat32-filename-list-p) ;; pathname of the file
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

(defun find-file-by-pathname (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (fat32-filename-list-p pathname))
                  :measure (acl2-count pathname)))
  (b* ((fs (m1-file-alist-fix fs))
       ((unless (consp pathname))
        (mv (make-m1-file) *enoent*))
       (name (fat32-filename-fix (car pathname)))
       (alist-elem (assoc-equal name fs))
       ((unless (consp alist-elem))
        (mv (make-m1-file) *enoent*))
       ((when (m1-directory-file-p (cdr alist-elem)))
        (if (atom (cdr pathname))
            (mv (cdr alist-elem) 0)
            (find-file-by-pathname
             (m1-file->contents (cdr alist-elem))
             (cdr pathname))))
       ((unless (atom (cdr pathname)))
        (mv (make-m1-file) *enotdir*)))
    (mv (cdr alist-elem) 0)))

(defthm
  find-file-by-pathname-correctness-1
  (mv-let (file error-code)
    (find-file-by-pathname fs pathname)
    (and (m1-file-p file)
         (integerp error-code)))
  :hints (("goal" :induct (find-file-by-pathname fs pathname))))

(defthm find-file-by-pathname-correctness-2
  (equal
    (find-file-by-pathname fs (fat32-filename-list-fix pathname))
    (find-file-by-pathname fs pathname)))

(defcong m1-file-alist-equiv equal (find-file-by-pathname fs pathname) 1)

(defcong fat32-filename-list-equiv equal (find-file-by-pathname fs pathname) 2
  :hints
  (("goal'"
    :in-theory (disable find-file-by-pathname-correctness-2)
    :use (find-file-by-pathname-correctness-2
          (:instance find-file-by-pathname-correctness-2
                     (pathname pathname-equiv))))))

(defthm
  m1-file-alist-p-of-put-assoc-equal
  (implies
   (m1-file-alist-p alist)
   (equal (m1-file-alist-p (put-assoc-equal name val alist))
          (and (fat32-filename-p name) (m1-file-p val)))))

;; This function should continue to take pathnames which refer to top-level
;; fs... but what happens when "." and ".." appear in a pathname? We'll have to
;; modify the code to deal with that.
(defun
    place-file-by-pathname
    (fs pathname file)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (fat32-filename-list-p pathname)
                              (m1-file-p file))
                  :measure (acl2-count pathname)
                  ;; temporary
                  :verify-guards nil))
  (b*
      ((fs (m1-file-alist-fix fs))
       (file (m1-file-fix file))
       ((unless (consp pathname))
        (mv fs *enoent*))
       (name (fat32-filename-fix (car pathname)))
       (alist-elem (assoc-equal name fs)))
    (if
        (consp alist-elem)
        (if
            (m1-directory-file-p (cdr alist-elem))
            (mv-let
              (new-contents error-code)
              (place-file-by-pathname
               (m1-file->contents (cdr alist-elem))
               (cdr pathname)
               file)
              (mv
               (put-assoc-equal
                name
                (make-m1-file
                 :dir-ent (m1-file->dir-ent (cdr alist-elem))
                 :contents new-contents)
                fs)
               error-code))
          (if (or
               (consp (cdr pathname))
               ;; this is the case where a regular file could get replaced by a
               ;; directory, which is a bad idea
               (m1-directory-file-p file))
              (mv fs *enotdir*)
            (mv (put-assoc-equal name file fs) 0)))
      (if (atom (cdr pathname))
          (mv (put-assoc-equal name file fs) 0)
        (mv fs *enotdir*)))))

(defthm
  place-file-by-pathname-correctness-1
  (mv-let (fs error-code)
    (place-file-by-pathname fs pathname file)
    (and (m1-file-alist-p fs)
         (integerp error-code)))
  :hints
  (("goal" :induct (place-file-by-pathname fs pathname file))))

(verify-guards place-file-by-pathname)

(defthm
  place-file-by-pathname-correctness-2
  (equal
   (place-file-by-pathname fs (fat32-filename-list-fix pathname)
                           file)
   (place-file-by-pathname fs pathname file)))

(defcong m1-file-alist-equiv equal
  (place-file-by-pathname fs pathname file) 1)

(defcong fat32-filename-list-equiv equal
  (place-file-by-pathname fs pathname file) 2
  :hints
  (("goal'"
    :in-theory (disable place-file-by-pathname-correctness-2)
    :use (place-file-by-pathname-correctness-2
          (:instance place-file-by-pathname-correctness-2
                     (pathname pathname-equiv))))))

(defcong m1-file-equiv equal
  (place-file-by-pathname fs pathname file) 3)

;; This function should continue to take pathnames which refer to top-level
;; fs... but what happens when "." and ".." appear in a pathname? We'll have to
;; modify the code to deal with that.
(defun
    remove-file-by-pathname
    (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (fat32-filename-list-p pathname))
                  :measure (acl2-count pathname)))
  (b*
      ((fs (m1-file-alist-fix fs))
       ((unless (consp pathname))
        (mv fs *enoent*))
       (name (fat32-filename-fix (car pathname)))
       (alist-elem (assoc-equal name fs)))
    (if
        (consp alist-elem)
        (if
            (m1-directory-file-p (cdr alist-elem))
            (mv-let
              (new-contents error-code)
              (remove-file-by-pathname
               (m1-file->contents (cdr alist-elem))
               (cdr pathname))
              (mv
               (put-assoc-equal
                name
                (make-m1-file
                 :dir-ent (m1-file->dir-ent (cdr alist-elem))
                 :contents new-contents)
                fs)
               error-code))
          (if (consp (cdr pathname))
              (mv fs *enotdir*)
            (mv (delete-assoc-equal name fs) 0)))
      ;; if it's not there, it can't be removed
      (mv fs *enoent*))))

(defthm
  remove-file-by-pathname-correctness-1
  (mv-let (fs error-code)
    (remove-file-by-pathname fs pathname)
    (and (m1-file-alist-p fs)
         (integerp error-code)))
  :hints
  (("goal" :induct (remove-file-by-pathname fs pathname))))

(defthm
  m1-read-after-write-lemma-1
  (implies
   (and (m1-file-alist-p alist)
        (fat32-filename-p name))
   (equal (m1-file-alist-fix (put-assoc-equal name val alist))
          (put-assoc-equal name (m1-file-fix val)
                           (m1-file-alist-fix alist))))
  :hints (("goal" :in-theory (enable m1-file-alist-fix))))

(defun fat32-filename-list-prefixp (x y)
  (declare (xargs :guard (and (fat32-filename-list-p x)
                              (fat32-filename-list-p y))))
  (if (consp x)
      (and (consp y)
           (fat32-filename-equiv (car x) (car y))
           (fat32-filename-list-prefixp (cdr x) (cdr y)))
    t))

(encapsulate
  ()

  (local
   (defun
       induction-scheme
       (pathname1 pathname2 fs)
     (declare (xargs :guard (and (fat32-filename-list-p pathname1)
                                 (fat32-filename-list-p pathname2)
                                 (m1-file-alist-p fs))))
     (if
         (or (atom pathname1) (atom pathname2))
         1
       (if
           (not (fat32-filename-equiv (car pathname2) (car pathname1)))
           2
         (let*
             ((fs (m1-file-alist-fix fs))
              (alist-elem (assoc-equal (fat32-filename-fix (car pathname1)) fs)))
           (if
               (atom alist-elem)
               3
             (if
                 (m1-directory-file-p (cdr alist-elem))
                 (induction-scheme (cdr pathname1)
                                   (cdr pathname2)
                                   (m1-file->contents (cdr alist-elem)))
               4)))))))

  (defthm
    m1-read-after-write
    (implies
     (m1-regular-file-p file2)
     (b*
         (((mv original-file original-error-code)
           (find-file-by-pathname fs pathname1))
          ((unless (and (equal original-error-code 0)
                        (m1-regular-file-p original-file)))
           t)
          ((mv new-fs new-error-code)
           (place-file-by-pathname fs pathname2 file2))
          ((unless (equal new-error-code 0)) t))
       (equal (find-file-by-pathname new-fs pathname1)
              (if (fat32-filename-list-equiv pathname1 pathname2)
                  (mv file2 0)
                  (find-file-by-pathname fs pathname1)))))
    :hints
    (("goal" :induct (induction-scheme pathname1 pathname2 fs)
      :in-theory (enable m1-regular-file-p
                         fat32-filename-list-fix))))

  (defthm
    m1-read-after-create
    (implies
     (and
      (m1-regular-file-p file2)
      ;; This is to avoid an odd situation where a query which would return
      ;; a "file not found" error earlier now returns "not a directory".
      (or (not (fat32-filename-list-prefixp pathname2 pathname1))
          (equal pathname2 pathname1)))
     (b* (((mv & original-error-code)
           (find-file-by-pathname fs pathname1))
          ((unless (not (equal original-error-code 0)))
           t)
          ((mv new-fs new-error-code)
           (place-file-by-pathname fs pathname2 file2))
          ((unless (equal new-error-code 0)) t))
       (equal (find-file-by-pathname new-fs pathname1)
              (if (fat32-filename-list-equiv pathname1 pathname2)
                  (mv file2 0)
                (find-file-by-pathname fs pathname1)))))
    :hints
    (("goal" :induct (induction-scheme pathname1 pathname2 fs)
      :in-theory (enable fat32-filename-list-fix
                         m1-regular-file-p)))))

(defun m1-lstat (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (fat32-filename-list-p pathname))))
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

(defthm
  find-new-index-helper-correctness-1-lemma-2
  (implies (integerp ac)
           (integerp (find-new-index-helper fd-list ac))))

(encapsulate
  ()

  (local (include-book "std/lists/remove" :dir :system))
  (local (include-book "std/lists/duplicity" :dir :system))

  (defthm
    find-new-index-helper-correctness-1
    (not (member-equal
          (find-new-index-helper fd-list ac)
          fd-list))))

(defund
  find-new-index (fd-list)
  (declare (xargs :guard (nat-listp fd-list)))
  (find-new-index-helper fd-list 0))

(defthm find-new-index-correctness-1-lemma-1
  (>= (find-new-index fd-list) 0)
  :hints (("Goal" :in-theory (enable find-new-index)))
  :rule-classes :linear)

(defthm
  find-new-index-correctness-1-lemma-2
  (integerp (find-new-index fd-list))
  :hints (("Goal" :in-theory (enable find-new-index))))

(defthm m1-open-guard-lemma-1
  (implies (fd-table-p fd-table)
           (alistp fd-table)))

(defun m1-open (pathname fs fd-table file-table)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (fat32-filename-list-p pathname)
                              (fd-table-p fd-table)
                              (file-table-p file-table))))
  (b*
      ((fd-table (fd-table-fix fd-table))
       (file-table (file-table-fix file-table))
       ((mv & errno)
        (find-file-by-pathname fs pathname))
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

(defthm m1-open-correctness-1
  (b*
      (((mv fd-table file-table & &) (m1-open pathname fs fd-table file-table)))
    (and
     (fd-table-p fd-table)
     (file-table-p file-table))))

(defthm
  m1-pread-guard-lemma-1
  (implies
   (and (file-table-p file-table)
        (consp (assoc-equal x file-table)))
   (file-table-element-p (cdr (assoc-equal x file-table)))))

;; Per the man page pread(2), this should not change the offset of the file
;; descriptor in the file table. Thus, there's no need for the file table to be
;; an argument.
(defun
  m1-pread
  (fd count offset fs fd-table file-table)
  (declare (xargs :guard (and (natp fd)
                              (natp count)
                              (natp offset)
                              (fd-table-p fd-table)
                              (file-table-p file-table)
                              (m1-file-alist-p fs))
                  :guard-debug t))
  (b*
      ((fd-table-entry (assoc-equal fd fd-table))
       ((unless (consp fd-table-entry))
        (mv "" -1 *ebadf*))
       (file-table-entry (assoc-equal (cdr fd-table-entry)
                                      file-table))
       ((unless (consp file-table-entry))
        (mv "" -1 *ebadf*))
       (pathname (file-table-element->fid (cdr file-table-entry)))
       ((mv file error-code)
        (find-file-by-pathname fs pathname))
       ((unless (and (equal error-code 0)
                     (m1-regular-file-p file)))
        (mv "" -1 error-code))
       (new-offset (min (+ offset count)
                        (length (m1-file->contents file))))
       (buf (subseq (m1-file->contents file)
                    (min offset
                         (length (m1-file->contents file)))
                    new-offset)))
    (mv buf (length buf) 0)))

(defthm
  m1-pread-correctness-1
  (mv-let (buf ret error-code)
    (m1-pread fd count offset fs fd-table file-table)
    (and (stringp buf)
         (integerp ret)
         (integerp error-code)
         (implies (>= ret 0)
                  (equal (length buf) ret)))))

(defun
  m1-pwrite
  (fd buf offset fs fd-table file-table)
  (declare (xargs :guard (and (natp fd)
                              (stringp buf)
                              (natp offset)
                              (fd-table-p fd-table)
                              (file-table-p file-table)
                              (m1-file-alist-p fs))
                  :guard-debug t
                  :guard-hints (("Goal" :in-theory (enable len-of-insert-text))
                                ("Subgoal 2'" :in-theory (disable
                                                          consp-assoc-equal)
                                 :use (:instance consp-assoc-equal
                                                 (name (CDR (CAR FD-TABLE)))
                                                 (l
                                                  FILE-TABLE))))))
  (b*
      ((fd-table-entry (assoc-equal fd fd-table))
       (fs (m1-file-alist-fix fs))
       ((unless (consp fd-table-entry))
        (mv fs -1 *ebadf*))
       (file-table-entry (assoc-equal (cdr fd-table-entry)
                                      file-table))
       ((unless (consp file-table-entry))
        (mv fs -1 *ebadf*))
       (pathname (file-table-element->fid (cdr file-table-entry)))
       ((mv file error-code)
        (find-file-by-pathname fs pathname))
       ((mv oldtext dir-ent)
        (if (and (equal error-code 0)
                 (m1-regular-file-p file))
            (mv (coerce (m1-file->contents file) 'list)
                (m1-file->dir-ent file))
            (mv nil (dir-ent-fix nil))))
       ((unless (unsigned-byte-p 32 (+ OFFSET (length BUF))))
        (mv fs -1 *enospc*))
       (file
        (make-m1-file
         :dir-ent dir-ent
         :contents (coerce (insert-text oldtext offset buf)
                           'string)))
       ((mv fs error-code)
        (place-file-by-pathname fs pathname file)))
    (mv fs (if (equal error-code 0) 0 -1)
        error-code)))

;; From the common man page basename(3)/dirname(3):
;; --
;; If  path  does  not contain a slash, dirname() returns the string "." while
;; basename() returns a copy of path.  If path is the string  "/",  then  both
;; dirname()  and basename() return the string "/".  If path is a NULL pointer
;; or points to an empty string, then both dirname() and basename() return the
;; string ".".
;; --
;; Of course, an empty list means something went wrong with the parsing code,
;; because even in the case of an empty path string, (list "") should be passed
;; to these functions. Still, we do the default thing, because neither of these
;; functions sets errno.

;; Also, an empty string right in the beginning indicates that the path began
;; with a "/". While not documented properly in the man page, for a path such
;; as "/home" or "/tmp", the dirname will be "/".
(defund
  m1-basename-dirname-helper (path)
  (declare (xargs :guard (string-listp path)
                  :guard-hints (("Goal" :in-theory (disable
                                                    make-list-ac-removal)))
                  :guard-debug t))
  (b*
      (((when (atom path))
        (mv *current-dir-fat32-name* (list *current-dir-fat32-name*)))
       (coerced-basename
        (if
            (or (atom (cdr path))
                (and (not (streqv (car path) ""))
                     (atom (cddr path))
                     (streqv (cadr path) "")))
            (coerce (str-fix (car path)) 'list)
          (coerce (str-fix (cadr path)) 'list)))
       (basename
        (coerce
         (append
          (take (min 11 (len coerced-basename)) coerced-basename)
          (make-list
           (nfix (- 11 (len coerced-basename)))
           :initial-element (code-char 0)))
         'string))
       ((when (or (atom (cdr path))
                  (and (not (streqv (car path) ""))
                       (atom (cddr path))
                       (streqv (cadr path) ""))))
        (mv
         basename
         (list *current-dir-fat32-name*)))
       ((when (atom (cddr path)))
        (mv basename
            (list (str-fix (car path))))))
    (mv-let (tail-basename tail-dirname)
      (m1-basename-dirname-helper (cdr path))
      (mv tail-basename
          (list* (str-fix (car path))
                 tail-dirname)))))

(defthm
  m1-basename-dirname-helper-correctness-1
  (mv-let (basename dirname)
    (m1-basename-dirname-helper path)
    (and (stringp basename)
         (equal (len (explode basename)) 11)
         (string-listp dirname)))
  :hints
  (("goal" :induct (m1-basename-dirname-helper path)
    :in-theory (enable m1-basename-dirname-helper)))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary
    (stringp (mv-nth 0 (m1-basename-dirname-helper path))))
   (:type-prescription
    :corollary
    (true-listp (mv-nth 1 (m1-basename-dirname-helper path))))))

(defun m1-basename (path)
  (declare (xargs :guard (string-listp path)))
  (mv-let (basename dirname)
    (m1-basename-dirname-helper path)
    (declare (ignore dirname))
    basename))

(defun m1-dirname (path)
  (declare (xargs :guard (string-listp path)))
  (mv-let (basename dirname)
    (m1-basename-dirname-helper path)
    (declare (ignore basename))
    dirname))

;; I'm leaving this guard unverified because that's not what I want to put my
;; time and energy into right now...
(defun
    m1-mkdir (fs pathname)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (fat32-filename-list-p pathname))
    :guard-hints
    (("goal"
      :in-theory
      (disable
       (:rewrite m1-basename-dirname-helper-correctness-1))
      :use
      (:instance
       (:rewrite m1-basename-dirname-helper-correctness-1)
       (path pathname))))
    :verify-guards nil))
  (b* ((dirname (m1-dirname pathname))
       ;; It's OK to strip out the leading "" when the pathname begins with /,
       ;; but what about when it doesn't and the pathname is relative to the
       ;; current working directory?
       (dirname (if (and (consp dirname)
                         (equal (car dirname) ""))
                    (cdr dirname)
                  dirname))
       ((mv parent-dir errno)
        (find-file-by-pathname fs dirname))
       ((unless (or (atom dirname)
                    (and (equal errno 0)
                         (m1-directory-file-p parent-dir))))
        (mv fs -1 *enoent*))
       ((mv & errno)
        (find-file-by-pathname fs pathname))
       ((unless (not (equal errno 0)))
        (mv fs -1 *eexist*))
       (basename (m1-basename pathname))
       ((unless (equal (length basename) 11))
        (mv fs -1 *enametoolong*))
       (dir-ent
        (update-nth 11 (ash 1 4)
                    (append (string=>nats basename)
                            (nthcdr 11 (dir-ent-fix nil)))))
       (file (make-m1-file :dir-ent dir-ent
                           :contents nil))
       (pathname (append dirname (list basename)))
       ((mv fs error-code)
        (place-file-by-pathname fs pathname file))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

;; I'm leaving this guard unverified because that's not what I want to put my
;; time and energy into right now...
(defun
    m1-mknod (fs pathname)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (string-listp pathname))
    :guard-hints
    (("goal"
      :in-theory
      (disable
       (:rewrite m1-basename-dirname-helper-correctness-1))
      :use
      (:instance
       (:rewrite m1-basename-dirname-helper-correctness-1)
       (path pathname))))
    :verify-guards nil))
  (b* ((dirname (m1-dirname pathname))
       ;; It's OK to strip out the leading "" when the pathname begins with /,
       ;; but what about when it doesn't and the pathname is relative to the
       ;; current working directory?
       (dirname (if (and (consp dirname)
                         (equal (car dirname) *empty-fat32-name*))
                    (cdr dirname)
                  dirname))
       ((mv parent-dir errno)
        (find-file-by-pathname fs dirname))
       ((unless (or (atom dirname)
                    (and (equal errno 0)
                         (m1-directory-file-p parent-dir))))
        (mv fs -1 *enoent*))
       ((mv & errno)
        (find-file-by-pathname fs pathname))
       ((unless (not (equal errno 0)))
        (mv fs -1 *eexist*))
       (basename (m1-basename pathname))
       ((unless (equal (length basename) 11))
        (mv fs -1 *enametoolong*))
       (dir-ent (append (string=>nats basename)
                        (nthcdr 11 (dir-ent-fix nil))))
       (file (make-m1-file :dir-ent dir-ent
                           :contents nil))
       (pathname (append dirname (list basename)))
       ((mv fs error-code)
        (place-file-by-pathname fs pathname file))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

(defthm
  m1-unlink-guard-lemma-1
  (implies (m1-file-p file)
           (and
            (true-listp (m1-file->dir-ent file))
            (equal (len (m1-file->dir-ent file)) *ms-dir-ent-length*)
            (unsigned-byte-listp 8 (m1-file->dir-ent file))))
  :hints
  (("goal" :in-theory (e/d (dir-ent-p)
                           (dir-ent-p-of-m1-file->dir-ent))
    :use (:instance dir-ent-p-of-m1-file->dir-ent
                    (x file)))))

;; I'm leaving this guard unverified because that's not what I want to put my
;; time and energy into right now...

;; The fat driver in Linux actually keeps the directory entries of files it is
;; deleting, while removing links to their contents. Thus, in the special case
;; where the last file is deleted from the root directory, the root directory
;; will still occupy one cluster, which in turn contains one entry which
;; points to the deleted file, with the filename's first character changed to
;; #xe5, which signifies a deleted file, its the file length changed to 0, and
;; the first cluster changed to 0. This may even hold for other directories
;; than root.
(defun
    m1-unlink (fs pathname)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (string-listp pathname))
    :guard-debug t
    :guard-hints
    (("goal"
      :in-theory
      (disable
       (:rewrite m1-basename-dirname-helper-correctness-1)
       return-type-of-string=>nats update-nth)
      :use
      ((:instance
        (:rewrite m1-basename-dirname-helper-correctness-1)
        (path pathname))
       (:instance return-type-of-string=>nats
                  (string
                   (mv-nth 0
                           (m1-basename-dirname-helper pathname)))))))
    :verify-guards nil))
  (b* ((dirname (m1-dirname pathname))
       ;; It's OK to strip out the leading "" when the pathname begins with /,
       ;; but what about when it doesn't and the pathname is relative to the
       ;; current working directory?
       (dirname (if (and (consp dirname)
                         (or
                          (equal (car dirname) *empty-fat32-name*)
                          (equal (car dirname) *current-dir-fat32-name*)))
                    (cdr dirname)
                  dirname))
       ;; ((mv parent-dir errno)
       ;;  (find-file-by-pathname fs dirname))
       ;; ((unless (or (atom dirname)
       ;;              (and (equal errno 0)
       ;;                   (m1-directory-file-p parent-dir))))
       ;;  (mv fs -1 *enoent*))
       ((mv file errno)
        (find-file-by-pathname fs pathname))
       ((unless (equal errno 0))
        (mv fs -1 *enoent*))
       (basename (m1-basename pathname))
       (pathname (append dirname (list basename)))
       ((mv fs error-code)
        (remove-file-by-pathname fs pathname))
       ((unless (equal error-code 0))
        (mv fs -1 error-code))
       ;; the byte #xe5 marks deleted files, according to the spec
       (coerced-basename-after-deletion (update-nth 0 #xe5
                                                    (string=>nats basename)))
       (dir-ent-after-deletion
        (append coerced-basename-after-deletion
                (nthcdr 11 (m1-file->dir-ent file))))
       ;; zeroing out the first cluster and file size
       (dir-ent-after-deletion
        (dir-ent-set-first-cluster-file-size
         dir-ent-after-deletion 0 0))
       (file-after-deletion
        (make-m1-file :dir-ent dir-ent-after-deletion
                      :contents nil))
       (pathname (append dirname (list (nats=>string
                                        coerced-basename-after-deletion))))
       ((mv fs error-code)
        (place-file-by-pathname fs pathname file-after-deletion))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

(defun
    name-to-fat32-name-helper
    (character-list n)
  (declare
   (xargs :guard (and (natp n)
                      (character-listp character-list))))
  (if (zp n)
      nil
    (if (atom character-list)
        (make-list n :initial-element #\space)
      (cons (str::upcase-char (car character-list))
            (name-to-fat32-name-helper (cdr character-list)
                                     (- n 1))))))

(defthm
  len-of-name-to-fat32-name-helper
  (equal (len (name-to-fat32-name-helper character-list n))
         (nfix n)))

;; (defthm name-to-fat32-name-helper-correctness-1
;;   (implies (member x (name-to-fat32-name-helper
;;                       character-list n))
;;            (or (equal x #\space) (str::up-alpha-p x))))

(defthm
  character-listp-of-name-to-fat32-name-helper
  (character-listp (name-to-fat32-name-helper character-list n))
  :hints (("goal" :in-theory (disable make-list-ac-removal))))

(defun
    name-to-fat32-name (character-list)
  (declare (xargs :guard (character-listp character-list)))
  (b*
      (((when (equal (coerce character-list 'string) *current-dir-name*))
        (coerce *current-dir-fat32-name* 'list))
       ((when (equal (coerce character-list 'string) *parent-dir-name*))
        (coerce *parent-dir-fat32-name* 'list))
       (dot-and-later-characters (member #\. character-list))
       (characters-before-dot
        (take (- (len character-list) (len dot-and-later-characters))
              character-list))
       (normalised-characters-before-dot
        (name-to-fat32-name-helper characters-before-dot 8))
       ((when (atom dot-and-later-characters))
        (append normalised-characters-before-dot
                (make-list 3 :initial-element #\space)))
       (characters-after-dot (cdr dot-and-later-characters))
       (second-dot-and-later-characters (member #\. characters-after-dot))
       (extension (take (- (len characters-after-dot)
                           (len second-dot-and-later-characters))
                        characters-after-dot))
       (normalised-extension
        (name-to-fat32-name-helper extension 3)))
    (append normalised-characters-before-dot normalised-extension)))

(assert-event
 (and
  (equal (name-to-fat32-name (coerce "6chars" 'list))
         (coerce "6CHARS     " 'list))
  (equal (name-to-fat32-name (coerce "6chars.h" 'list))
         (coerce "6CHARS  H  " 'list))
  (equal (name-to-fat32-name (coerce "6chars.txt" 'list))
         (coerce "6CHARS  TXT" 'list))
  (equal (name-to-fat32-name (coerce "6chars.6chars" 'list))
         (coerce "6CHARS  6CH" 'list))
  (equal (name-to-fat32-name (coerce "6chars.6ch" 'list))
         (coerce "6CHARS  6CH" 'list))
  (equal (name-to-fat32-name (coerce "11characters.6chars" 'list))
         (coerce "11CHARAC6CH" 'list))
  (equal (name-to-fat32-name (coerce "11characters.1.1.1" 'list))
         (coerce "11CHARAC1  " 'list))
  (equal (name-to-fat32-name (coerce "11characters.1.1" 'list))
         (coerce "11CHARAC1  " 'list))))

(defun
  fat32-name-to-name-helper
  (character-list n)
  (declare (xargs :guard (and (natp n)
                              (character-listp character-list)
                              (<= n (len character-list)))))
  (if (zp n)
      nil
      (if (equal (nth (- n 1) character-list)
                 #\space)
          (fat32-name-to-name-helper character-list (- n 1))
          (str::downcase-charlist (take n character-list)))))

(defthm
  character-listp-of-fat32-name-to-name-helper
  (character-listp
   (fat32-name-to-name-helper
    character-list n)))

(defun fat32-name-to-name (character-list)
  (declare (xargs :guard (and (character-listp character-list)
                              (equal (len character-list) 11))))
  (b*
      (((when (equal (coerce character-list 'string) *current-dir-fat32-name*))
        (coerce *current-dir-name* 'list))
       ((when (equal (coerce character-list 'string) *parent-dir-fat32-name*))
        (coerce *parent-dir-name* 'list))
       (characters-before-dot
        (fat32-name-to-name-helper (take 8 character-list) 8))
       (characters-after-dot
        (fat32-name-to-name-helper (subseq character-list 8 11) 3))
       ((when (atom characters-after-dot))
        characters-before-dot))
    (append characters-before-dot (list #\.) characters-after-dot)))

(assert-event
 (and
  (equal (fat32-name-to-name (coerce "6CHARS     " 'list))
         (coerce "6chars" 'list))
  (equal (fat32-name-to-name (coerce "6CHARS  H  " 'list))
         (coerce "6chars.h" 'list))
  (equal (fat32-name-to-name (coerce "6CHARS  TXT" 'list))
         (coerce "6chars.txt" 'list))
  (equal (fat32-name-to-name (coerce "6CHARS  6CH" 'list))
         (coerce "6chars.6ch" 'list))
  (equal (fat32-name-to-name (coerce "11CHARAC6CH" 'list))
         (coerce "11charac.6ch" 'list))
  (equal (fat32-name-to-name (coerce "11CHARAC1  " 'list))
         (coerce "11charac.1" 'list))))

(defun pathname-to-fat32-pathname (character-list)
  (declare (xargs :guard (character-listp character-list)))
  (b*
      ((slash-and-later-characters
        (member #\/ character-list))
       (characters-before-slash (take (- (len character-list)
                                         (len slash-and-later-characters))
                                      character-list))
       ((when (atom slash-and-later-characters))
        (list
         (coerce (name-to-fat32-name characters-before-slash) 'string))))
    (cons
     (coerce (name-to-fat32-name characters-before-slash) 'string)
     (pathname-to-fat32-pathname (cdr slash-and-later-characters)))))

(assert-event
 (and
  (equal (pathname-to-fat32-pathname (coerce "/bin/mkdir" 'list))
         (list "           " "BIN        " "MKDIR      "))
  (equal (pathname-to-fat32-pathname (coerce "books/build/cert.pl" 'list))
   (list "BOOKS      " "BUILD      " "CERT    PL "))))

(defun fat32-pathname-to-name (string-list)
  ;; (declare (xargs :guard (string-listp string-list)))
  (if (atom string-list)
      nil
    (append (fat32-name-to-name (coerce (car string-list) 'list))
            (if (atom (cdr string-list))
                nil
              (list* #\/
                     (fat32-pathname-to-name (cdr string-list)))))))

(assert-event
 (and
  (equal (coerce (fat32-pathname-to-name (list "BOOKS      " "BUILD      "
                                               "CERT    PL ")) 'string)
         "books/build/cert.pl")
  (equal (coerce (fat32-pathname-to-name (list "           " "BIN        "
                                               "MKDIR      ")) 'string)
         "/bin/mkdir")))

(defthm character-listp-of-fat32-pathname-to-name
  (character-listp (fat32-pathname-to-name string-list)))
