
;  file-system-3.lisp                                  Mihir Mehta

; Here we define the rudiments of a file system with length tracking.  We first
; start with a file-system recognizer, and then we define various file-system
; operations.

(include-book "misc/assert" :dir :system)

(defthm make-character-list-makes-character-list
  (character-listp (make-character-list x)))

(defthm len-of-binary-append
  (equal (len (binary-append x y)) (+ (len x) (len y))))

(defthm len-of-make-character-list
  (equal (len (make-character-list x)) (len x)))

(defthm len-of-revappend
  (equal (len (revappend x y)) (+ (len x) (len y))))

(defthm len-of-first-n-ac
  (implies (natp i) (equal (len (first-n-ac i l ac)) (+ i (len ac)))))

(defthm nthcdr-of-binary-append-1
  (implies (and (integerp n) (>= n (len x)))
           (equal (nthcdr n (binary-append x y))
                  (nthcdr (- n (len x)) y)))
  :hints (("Goal" :induct (nthcdr n x)) ))

(defthm first-n-ac-of-binary-append-1
  (implies (and (natp i) (<= i (len x)))
           (equal (first-n-ac i (binary-append x y) ac)
                  (first-n-ac i x ac))))

(defthm by-slice-you-mean-the-whole-cake
  (implies (true-listp l)
           (equal (first-n-ac (len l) l ac)
                  (revappend ac l)))
  :hints (("Goal" :induct (revappend l ac)) )
  :rule-classes ((:rewrite :corollary
                           (implies (and (true-listp l) (equal i (len l)))
                                    (equal (first-n-ac i l ac) (revappend ac l)))) ))

(defthm assoc-after-delete-assoc
  (implies (not (equal name1 name2))
           (equal (assoc-equal name1 (delete-assoc name2 alist))
                  (assoc-equal name1 alist))))

(defthmd revappend-is-append-of-rev
  (equal (revappend x (binary-append y z))
         (binary-append (revappend x y) z)))

(defthm binary-append-take-nthcdr
  (implies (and (natp i) (<= i (len l)))
           (equal (binary-append (first-n-ac i l ac) (nthcdr i l))
                  (revappend ac l)))
  :hints (("Goal" :induct (first-n-ac i l ac))
          ("Subgoal *1/1'''"
           :use (:instance revappend-is-append-of-rev
                           (x ac) (y nil) (z l)))))

(defthm make-character-list-of-character-list
  (implies (character-listp x)
           (equal (make-character-list x) x)))

(defthm character-listp-of-first-n-ac
  (implies (and (character-listp l)
                (character-listp acc)
                (<= n (len l)))
           (character-listp (first-n-ac n l acc))))

(defthm character-listp-nthcdr
  (implies (and (character-listp l))
           (character-listp (nthcdr n l))))

(defthm first-n-ac-of-binary-append
  (implies (and (natp i) (<= i (len x)))
           (equal (first-n-ac i (binary-append x y) ac)
                  (first-n-ac i x ac))))

(defthm take-of-take
  (implies (and (natp m) (integerp n) (<= m n) (<= n (len l)))
           (equal (take m (take n l)) (take m l)))
  :hints (("Goal" :in-theory (disable binary-append-take-nthcdr)
           :use (:instance binary-append-take-nthcdr (ac nil) (i n))) ))

(defthm make-character-list-of-binary-append
  (equal (make-character-list (binary-append x y))
         (binary-append (make-character-list x) (make-character-list y))))

(defconst *blocksize* 8)

(defthm len-of-nthcdr-1 (<= (len (nthcdr n l)) (len l)))

(defthm len-of-nthcdr-2 (implies (atom l) (atom (nthcdr n l))))

(defthm len-of-nthcdr-3
  (implies (and (consp l) (integerp n) (> n 0))
           (< (len (nthcdr n l)) (len l)))
  :instructions (:induct (:use (:instance len-of-nthcdr-2 (n (+ -1 n))
                                          (l (cdr l))))
                         :split (:dive 1 1)
                         :x :top (:dive 2)
                         :x
                         :top :bash
                         :bash :bash
                         :bash :bash))

(defun make-blocks (text)
  (declare (xargs :guard (character-listp text)
                  :measure (len text)))
  (if (atom text)
      nil
    (cons (make-character-list (take *blocksize* text))
          (make-blocks (nthcdr *blocksize* text)))))

(defun block-listp (block-list)
  (declare (xargs :guard t))
  (if (atom block-list)
      (eq block-list nil)
    (and (character-listp (car block-list))
         (equal (len (car block-list)) *blocksize*)
         (block-listp (cdr block-list)))))

(defun unmake-blocks (blocks n)
  (declare (xargs :guard (and (block-listp blocks)
                              (natp n)
                              (< (- (* (len blocks) *blocksize*) n) *blocksize*))))
  (if (atom blocks)
      nil
    (if (atom (cdr blocks))
        (take n (car blocks))
      (binary-append (car blocks)
                     (unmake-blocks (cdr blocks) (- n *blocksize*))))))

(defthm unmake-make-blocks-lemma-1
        (implies (natp n)
                 (iff (consp (nthcdr n l)) (> (len l) n)))
        :hints (("Goal" :induct (nthcdr n l))))
;; (defthm unmake-make-blocks-lemma-1
;;         (implies (and (consp (nthcdr n l)) (natp n))
;;                  (> (len l) n))
;;         :hints (("Goal" :induct (nthcdr n l))))

(defthm unmake-make-blocks-lemma-2
  (implies (and (natp n) (>= (len l) n))
           (equal (len (nthcdr n l)) (- (len l) n))))

(encapsulate ()
  (local (include-book "std/lists/repeat" :dir :system))

  (defthm unmake-make-blocks
    (implies (and (character-listp text))
             (equal (unmake-blocks (make-blocks text) (len text)) text))
    :hints (("Subgoal *1/3.2" :in-theory (disable unmake-make-blocks-lemma-1)
             :use (:instance unmake-make-blocks-lemma-1 (n *blocksize*) (l
                                                                         text)))
            ("Subgoal *1/3.1'"
             :in-theory (disable make-character-list-of-character-list
                                 take-of-too-many)
             :use ((:instance take-of-too-many (x text) (n *blocksize*))
                   (:instance unmake-make-blocks-lemma-1 (n *blocksize*) (l
                                                                          text))))))
  )

(defun bounded-nat-listp (l b)
  (if (atom b)
      (eq l nil)
    (and (natp (car l)) (< (car l) b) (bounded-nat-listp (cdr l) b))))

;; i could have made bounded-nat-listp a guard for this function. i chose not
;; to, because guard-checking later on would require me to look at the length
;; of the disk while deciding fs-p for an fs, which strikes me as a bit too
;; much for this model. as a consequence, i'm not going to heedlessly use nth -
;; instead, i'm going to leave out blocks that don't actually exist. thus,
;; we'll have only blocks and no nils.
(defun fetch-blocks-by-indices (block-list index-list)
  (declare (xargs :guard (and (block-listp block-list)
                              (nat-listp index-list))))
  (if (atom index-list)
      nil
    (if (>= (car index-list) (len block-list))
        (fetch-blocks-by-indices block-list (cdr index-list))
      (cons (nth (car index-list) block-list)
            (fetch-blocks-by-indices block-list (cdr index-list)))
      )))

(defthm fetch-blocks-by-indices-correctness-1
  (implies (and (block-listp block-list) (nat-listp index-list))
           (block-listp (fetch-blocks-by-indices block-list index-list))))

(defthm fetch-blocks-by-indices-correctness-2
  (implies (and (block-listp block-list)
                (bounded-nat-listp index-list (len block-list)))
           (equal (len (fetch-blocks-by-indices block-list index-list))
                  (len index-list))))

(defthm fetch-blocks-by-indices-correctness-3
  (implies (and (block-listp block-list) (nat-listp index-list))
           (<= (len (fetch-blocks-by-indices block-list index-list))
               (len index-list)))
  :rule-classes :linear)

(defun fs-p (fs)
  (declare (xargs :guard t))
  (if (atom fs)
      (null fs)
    (and (let ((directory-or-file-entry (car fs)))
           (if (atom directory-or-file-entry)
               nil
             (let ((name (car directory-or-file-entry))
                   (entry (cdr directory-or-file-entry)))
               (and (symbolp name)
                    (or (and (consp entry)
                             (nat-listp (car entry))
                             (natp (cdr entry))
                             (> (cdr entry)
                                (* *blocksize* (- (len (car entry)) 1))))
                        (fs-p entry))))))
         (fs-p (cdr fs)))))
;; this example - which evaluates to t - remains as a counterexample to an
;; erstwhile bug.
(defconst *test01* (fs-p '((a  "Mihir" . 5) (b "Warren" . 6) (c))))

(defthm alistp-fs-p
  (implies (fs-p fs)
           (alistp fs)))

(defthm fs-p-assoc
  (implies (and (fs-p fs)
                (consp (assoc-equal name fs))
                (consp (cddr (assoc-equal name fs))))
           (fs-p (cdr (assoc-equal name fs)))))

(assert!
 (fs-p '((a (1 2) . 10) (b (3 4) . 11) (c (a (5 6) . 12) (b (7 8) . 13)))))

(defthm stat-guard-lemma-1
  (implies (and (consp fs)
                (consp (assoc-equal name fs))
                (fs-p fs)
                (consp (cdr (assoc-equal name fs)))
                (nat-listp (cadr (assoc-equal name fs)))
                )
           (and (natp (cddr (assoc-equal name fs)))
                (> (cdr (cdr (assoc-equal name fs)))
                   (* *blocksize* (- (len (car (cdr (assoc-equal name fs)))) 1))))))

(defthm stat-guard-lemma-2
  (implies (and (consp fs) (fs-p fs)
                (consp (assoc-equal s fs))
                (not (and (consp (cdr (assoc-equal s fs)))
                          (nat-listp (cadr (assoc-equal s fs))))))
           (fs-p (cdr (assoc-equal s fs)))))

(defun stat (hns fs disk)
  (declare (xargs :guard-debug t
                  :guard (and (symbol-listp hns)
                              (fs-p fs)
                              (block-listp disk))
                  :guard-hints (("Subgoal 2.2'"
                                 :in-theory (disable stat-guard-lemma-1)
                                 :use (:instance stat-guard-lemma-1
                                                 (name (car hns)))))))
  (if (atom hns)
      fs
    (if (atom fs)
        nil
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            nil
          (let ((contents (cdr sd)))
            (if (and (consp contents) (nat-listp (car contents)))
                (and (null (cdr hns))
                     (unmake-blocks (fetch-blocks-by-indices disk (car contents))
                                    (cdr contents)))
              (stat (cdr hns) contents disk))))))))

;; (defthm stat-of-stat-lemma-1
;;   (implies (and (consp (assoc-equal (car outside) fs))
;;                 (not (nat-listp (cadr (assoc-equal (car outside) fs))))
;;                 (fs-p fs))
;;            (fs-p (cdr (assoc-equal (car outside) fs)))))

(defthm stat-of-stat
  (implies (and (symbol-listp inside)
                (symbol-listp outside)
                (stat outside fs)
                (fs-p fs))
           (equal (stat inside (stat outside fs))
                  (stat (append outside inside) fs)))
  :hints
  (("Goal"
    :induct (stat outside fs))))

(defun rdchs (hns fs start n)
  (declare (xargs :guard (and (symbol-listp hns)
                              (fs-p fs)
                              (natp start)
                              (natp n))))
  (let ((file (stat hns fs)))
    (if (not (stringp file))
        nil
      (let ((file-length (length file))
            (end (+ start n)))
        (if (< file-length end)
            nil
          (subseq file start (+ start n)))))))

; More for Mihir to do...

; Delete file
(defun unlink (hns fs)
  (declare (xargs :guard (and (symbol-listp hns)
                              (fs-p fs))))
  (if (atom hns)
      fs ;;error case, basically
    (if (atom (cdr hns))
        (delete-assoc (car hns) fs)
      (if (atom fs)
          nil
        (let ((sd (assoc (car hns) fs)))
          (if (atom sd)
              fs
            (let ((contents (cdr sd)))
              (if (stringp (car contents)) 
                  fs ;; we still have names but we're at a regular file - error
                (cons (cons (car sd)
                            (unlink (cdr hns) contents))
                      (delete-assoc (car hns) fs))))))))
    ))

;; putting these lemmas on the back burner because we would need to add uniquep
;; to our fs-p definition to make this work
;; (defthm unlink-works-lemma-1 (not (assoc-equal key (delete-assoc-equal key alist))))

;; (defthm unlink-works (implies (fs-p fs) (not (stat hns (unlink hns fs)))))

(defthm wrchs-guard-lemma-1
  (implies (and (stringp str))
           (character-listp (nthcdr n (coerce str 'list)))))

; Add wrchs...
(defun wrchs (hns fs start text)
  (declare (xargs :guard-debug t
                  :guard (and (symbol-listp hns)
                              (fs-p fs)
                              (natp start)
                              (stringp text))
                  :guard-hints
                  (("Subgoal 1.4" :use (:instance character-listp-coerce (str ()))) )))
  (if (atom hns)
      fs ;; error - showed up at fs with no name  - so leave fs unchanged
    (if (atom fs)
        nil ;; error, so leave fs unchanged
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            fs ;; file-not-found error, so leave fs unchanged
          (let ((contents (cdr sd)))
            (cons (cons (car sd)
                        (if (and (consp (cdr sd)) (stringp (cadr sd)))
                            (let ((file (cdr sd)))
                              (if (cdr hns)
                                  file ;; error, so leave fs unchanged
                                (let* (
                                       (end (+ start (length text)))
                                       (oldtext (coerce (car file) 'list))
                                       (newtext (append (make-character-list (take start oldtext))
                                                        (coerce text 'list)
                                                        (nthcdr end oldtext)))
                                       (newlength (len newtext)))
                                  (cons
                                   (coerce newtext 'string)
                                   newlength))))
                          (wrchs (cdr hns) contents start text)))
                  (delete-assoc (car hns) fs))
            ))))))

; Mihir, run some example and provide some ASSERT$ events.


(defthm wrchs-returns-fs-lemma-1
  (implies (and (consp (assoc-equal s fs))
                (fs-p fs))
           (symbolp (car (assoc-equal s fs)))))

(defthm wrchs-returns-fs-lemma-2
  (implies (fs-p fs)
           (fs-p (delete-assoc-equal s fs))))

(defthm wrchs-returns-fs
  (implies (and (fs-p fs))
           (fs-p (wrchs hns fs start text))))

(defthm unlink-returns-fs
  (implies (and (fs-p fs))
           (fs-p (unlink hns fs))))

(defthm read-after-write-1-lemma-1
  (implies (consp (assoc-equal name alist))
           (equal (car (assoc-equal name alist)) name)))

(defthm read-after-write-1-lemma-2
  (implies (and (fs-p fs) (stringp text) (stringp (stat hns fs)))
           (stringp (stat hns (wrchs hns fs start text)))))

(defthm read-after-write-1-lemma-3
  (implies (rdchs hns fs start n)
           (stringp (stat hns fs))))

(defthm read-after-write-1-lemma-4
  (implies (and (fs-p fs) (stringp text) (stringp (stat hns fs)))
           (equal (stat hns (wrchs hns fs start text))
                  (let* (
                         (end (+ start (length text)))
                         (oldtext (coerce (stat hns fs) 'list))
                         (newtext (append (make-character-list (take start oldtext))
                                          (coerce text 'list)
                                          (nthcdr end oldtext))))
                    (coerce newtext 'string)))))

(defthm read-after-write-1
  (implies (and (fs-p fs)
                (stringp text)
                (symbol-listp hns)
                (natp start)
                (equal n (length text))
                (stringp (stat hns fs)))
           (equal (rdchs hns (wrchs hns fs start text) start n) text)))

;; we want to prove
;; (implies (and (fs-p fs)
;;               (stringp text2)
;;               (symbol-listp hns1)
;;               (symbol-listp hns2)
;;               (not (equal hns1 hns2))
;;               (natp start2)
;;               (stringp (stat hns1 fs)))
;;          (equal (stat hns1 (wrchs hns2 fs start2 text2))
;;                 (stat hns1 fs)))
;; now, let's semi-formally write the cases we want.
;; case 1: (atom hns1) - this will violate the hypothesis
;; (stringp (stat hns1 fs))
;; case 2: (and (consp hns1) (atom fs)) - this will yield nil in both cases
;; case 3: (and (consp hns1) (consp fs) (atom (assoc (car hns1) fs))) - this
;; will yield nil in both cases (might need a lemma)
;; case 4: (and (consp hns1) (consp fs) (consp (assoc (car hns1) fs))
;;              (atom hns2)) - in this case
;; (wrchs hns2 fs start2 text2) will be the same as fs
;; case 5: (and (consp hns1) (consp fs) (consp (assoc (car hns1) fs))
;;              (consp hns2) (not (equal (car hns1) (car hns2)))) - in this
;; case, (assoc (car hns1) (wrchs hns2 fs start2 text2)) =
;; (assoc (car hns1) (delete-assoc (car hns2) fs)) =
;; (assoc (car hns1) fs) and from here on the terms will be equal
;; case 6: (and (consp hns1) (consp fs) (consp (assoc (car hns1) fs))
;;              (consp hns2) (equal (car hns1) (car hns2)) (atom (cdr hns1))) -
;; in this case (consp (cdr hns2)) is implicit because of
;; (not (equal hns1 hns2)) and (stringp (stat hns1 fs)) implies that
;; (wrchs hns2 fs start2 text2) = fs
;; case 7: (and (consp hns1) (consp fs) (consp (assoc (car hns1) fs))
;;              (consp hns2) (equal (car hns1) (car hns2)) (consp (cdr hns1))) -
;; (stat hns1 (wrchs hns2 fs start2 text2)) =
;; (stat hns1 (cons (cons (car hns1)
;;                        (wrchs (cdr hns2) (cdr (assoc (car hns1) fs)) start2 text2))
;;                  (delete-assoc (car hns1) fs)) =
;; (stat (cdr hns1) (wrchs (cdr hns2) (cdr (assoc (car hns1) fs)) start2 text2)) =
;; (stat (cdr hns1) (cdr (assoc (car hns1) fs))) = (induction hypothesis)
;; (stat hns1 fs)

(defthm read-after-write-2-lemma-1
  (implies (fs-p fs)
           (not (stringp (cdr (assoc-equal name fs))))))

(defthm read-after-write-2-lemma-2
  (implies (and (consp hns1)
                (consp fs)
                (consp (assoc-equal (car hns1) fs))
                (fs-p fs)
                (symbolp (car hns1))
                (not (cdr hns1))
                (stringp (stat hns1 fs)))
           (equal (stat hns1 fs) (cadr (assoc (car hns1) fs)))))

(encapsulate
  ()
  (local (defun induction-scheme (hns1 hns2 fs)
           (if (atom hns1)
               fs
             (if (atom fs)
                 nil
               (let ((sd (assoc (car hns2) fs)))
                 (if (atom sd)
                     fs
                   (if (atom hns2)
                       fs
                     (if (not (equal (car hns1) (car hns2)))
                         fs
                       (let ((contents (cdr sd)))
                         (if (atom (cdr hns1))
                             (cons (cons (car sd)
                                         contents)
                                   (delete-assoc (car hns2) fs))
                           (cons (cons (car sd)
                                       (induction-scheme (cdr hns1) (cdr hns2) contents))
                                 (delete-assoc (car hns2) fs)))
                         ))))
                 )))))

  (defthm read-after-write-2-lemma-3
    (implies (and (fs-p fs)
                  (stringp text2)
                  (symbol-listp hns1)
                  (symbol-listp hns2)
                  (not (equal hns1 hns2))
                  (natp start2)
                  (stringp (stat hns1 fs)))
             (equal (stat hns1 (wrchs hns2 fs start2 text2)) (stat hns1 fs)))
    :hints (("Goal"  :induct (induction-scheme hns1 hns2 fs))
            ("Subgoal *1/7.1''" :in-theory (disable alistp-fs-p)
             :use (:instance alistp-fs-p (fs (wrchs (cdr hns2)
                                                    (cdr (assoc-equal (car hns1) fs))
                                                    start2 text2))))))

  )

(defthm read-after-write-2
  (implies (and (fs-p fs)
                (stringp text2)
                (symbol-listp hns1)
                (symbol-listp hns2)
                (not (equal hns1 hns2))
                (natp start1)
                (natp start2)
                (natp n1)
                (stringp (stat hns1 fs)))
           (equal (rdchs hns1 (wrchs hns2 fs start2 text2) start1 n1)
                  (rdchs hns1 fs start1 n1))))

(defun fsck (fs)
  (declare (xargs :guard (fs-p fs)))
  (or (atom fs)
    (and (let ((directory-or-file-entry (car fs)))
           (let ((entry (cdr directory-or-file-entry)))
             (if (and (consp entry) (stringp (car entry)))
                 (equal (length (car entry)) (cdr entry))
               (fsck entry))))
         (fsck (cdr fs)))))

(defthm fsck-after-wrchs-lemma-1
  (implies (and (fs-p fs) (fsck fs))
           (fsck (delete-assoc-equal name fs))))

(defthm fsck-after-wrchs-lemma-2
  (implies (and (fs-p fs) (fsck fs))
           (fsck (cdr (assoc-equal (car hns) fs)))))

(defthm fsck-after-wrchs-lemma-3
  (implies (and (fs-p fs) (consp fs)) (not (stringp (car fs)))))

(defthm fsck-after-wrchs-lemma-4
  (implies (and (consp fs)
                (consp (assoc-equal name fs))
                (fs-p fs)
                (stringp text)
                (fsck fs)
                (consp (cdr (assoc-equal name fs)))
                (stringp (cadr (assoc-equal name fs))))
           (equal (len (coerce (cadr (assoc-equal name fs))
                               'list))
                  (cddr (assoc-equal name fs))))
)

(defthm fsck-after-wrchs
  (implies (and (fs-p fs) (stringp text) (fsck fs))
           (fsck (wrchs hns fs start text))))

(defthm fsck-after-unlink
  (implies (and (fs-p fs) (fsck fs))
           (fsck (unlink hns fs))))

; Find length of file
(defun wc-len (hns fs)
  (declare (xargs :guard (and (symbol-listp hns)
                              (fs-p fs))))
  (let ((file (stat hns fs)))
    (if (not (stringp file))
        nil
      (length file))))

; Prove (list-of-chars-to-string (string-to-chars str))
;       (string-to-chars (list-of-chars-to-string char-list))
; and then, you will be positioned to use either form.
#||From :doc STR::STD/STRINGS/COERCE
  Theorem: <coerce-inverse-1-better>

    (defthm coerce-inverse-1-better
            (equal (coerce (coerce x 'string) 'list)
                   (if (stringp x)
                       nil (make-character-list x))))

  Theorem: <coerce-inverse-2-better>

    (defthm coerce-inverse-2-better
            (equal (coerce (coerce x 'list) 'string)
                   (if (stringp x) x "")))
That takes care of that
||#
; Correspond (or not) with Linux system calls -- the low-level stuff...

; Add file -- or, if you will, create a file with some initial contents

; and so on...

(assign fs '((a "Mihir" . 5) (b "Warren" . 6) (c (a "Mehta" . 5) (b "Hunt" . 4))))

(assign h1 '(a))
(assign h2 '(a b))
(assign h3 '(c b))
(assign h4 '(c))

(stat (@ h1) (@ fs))
(stat (@ h2) (@ fs))
(stat (@ h3) (@ fs))
(stat (@ h4) (@ fs))

(wc-len (@ h1) (@ fs))
(wc-len (@ h2) (@ fs))
(wc-len (@ h3) (@ fs))
(wc-len (@ h4) (@ fs))

(wrchs (@ h1) (@ fs) 1 "athur")
(wrchs (@ h3) (@ fs) 1 "inojosa")
(wrchs (@ h3) (@ fs) 5 "Alvarez")
(wrchs (@ h2) (@ fs) 1 "athur") ;; buggy example

(unlink (@ h1) (@ fs))
(unlink (@ h2) (@ fs))
(unlink (@ h3) (@ fs))
(unlink (@ h4) (@ fs))
