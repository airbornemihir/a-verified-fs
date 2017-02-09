(in-package "ACL2")
;  file-system-1.lisp                                  Mihir Mehta

; Here we define the rudiments of a file system.  We first start with
; a file-system recognizer, and then we define various file-system
; operations.

(include-book "misc/assert" :dir :system)
(include-book "file-system-lemmas")

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
                    (or (stringp entry) (fs-p entry))))))
         (fs-p (cdr fs)))))
;; this example - which evaluates to t - remains as a counterexample to an
;; erstwhile bug.
(defconst *test01* (fs-p '((a . "Mihir") (b . "Warren") (c))))

(defthm alistp-fs-p
  (implies (fs-p fs)
           (alistp fs)))

(defthm fs-p-assoc
  (implies (and (fs-p fs)
                (consp (assoc-equal name fs))
                (consp (cdr (assoc-equal name fs))))
           (fs-p (cdr (assoc-equal name fs)))))

(assert!
 (fs-p '((a . "Mihir") (b . "Warren") (c (a . "Mehta") (b . "Hunt")))))

(defun stat (hns fs)
  (declare (xargs :guard (and (symbol-listp hns)
                              (fs-p fs))))
  (if (atom hns)
      fs
    (if (atom fs)
        nil
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            nil
          (let ((contents (cdr sd)))
            (if (atom contents)
                (and (null (cdr hns))
                     contents)
              (stat (cdr hns) contents))))))))

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
              (if (atom contents)
                  (and (null (cdr hns))
                       contents)
                (cons (cons (car sd) (unlink (cdr hns) contents)) (delete-assoc (car hns) fs))))))))
    ))

; Add wrchs...
; The problem with this definition of wrchs is that it deletes a directory if
; it's found where a text file is expected
(defun wrchs (hns fs start text)
  (declare (xargs :guard (and (symbol-listp hns)
                              (or (stringp fs) (fs-p fs))
                              (natp start)
                              (stringp text))))
  (if (atom hns)
      (let ((file fs))
        (if (not (stringp file))
            file ;; error, so leave fs unchanged
          (let (
                (end (+ start (length text))))
            (coerce
             (append (make-character-list (take start (coerce file 'list)))
                     (coerce text 'list)
                     (nthcdr end (coerce file 'list)))
             'string))))
    (if (atom fs)
        fs ;; error, so leave fs unchanged
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            fs ;; error, so leave fs unchanged
          (let ((contents (cdr sd)))
            (cons (cons (car sd) (wrchs (cdr hns) contents start text))
                  (delete-assoc (car hns) fs))
            ))))))

(defthm wrchs-returns-fs-lemma-1
  (implies (and (consp (assoc-equal s fs))
                (fs-p fs))
           (symbolp (car (assoc-equal s fs)))))

(defthm wrchs-returns-fs-lemma-2
  (implies (fs-p fs)
           (fs-p (delete-assoc-equal s fs))))

(defthm wrchs-returns-fs-lemma-3
  (implies (and (consp fs) (fs-p fs)
                (consp (assoc-equal s fs))
                (not (stringp (cdr (assoc-equal s fs)))))
           (fs-p (cdr (assoc-equal s fs)))))

(defthm wrchs-returns-fs
  (implies (and (symbol-listp hns) (fs-p fs))
           (fs-p (wrchs hns fs start text)))
  :hints (("Subgoal *1/6''" :use (:instance wrchs-returns-fs-lemma-3 (s (car hns)))) ))

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

(defthm read-after-write-1
  (implies (and (fs-p fs)
                (stringp text)
                (symbol-listp hns)
                (natp start)
                (equal n (length text))
                (stringp (stat hns fs)))
           (equal (rdchs hns (wrchs hns fs start text) start n) text)))

(defthm read-after-write-2-lemma-1
  (implies (fs-p fs)
           (not (stringp (assoc-equal name fs)))))

(defthm read-after-write-2-lemma-2
  (implies (and (consp hns1)
                (consp fs)
                (consp (assoc-equal (car hns1) fs))
                (fs-p fs)
                (symbolp (car hns1))
                (not (cdr hns1))
                (stringp (stat hns1 fs)))
           (equal (stat hns1 fs) (cdr (assoc (car hns1) fs)))))

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

;; (assign fs '((a . "Mihir") (b . "Warren") (c (a . "Mehta") (b . "Hunt"))))

;; (assign h1 '(a))
;; (assign h2 '(a b))
;; (assign h3 '(c b))
;; (assign h4 '(c))

;; (stat (@ h1) (@ fs))
;; (stat (@ h2) (@ fs))
;; (stat (@ h3) (@ fs))
;; (stat (@ h4) (@ fs))

;; (wc-len (@ h1) (@ fs))
;; (wc-len (@ h2) (@ fs))
;; (wc-len (@ h3) (@ fs))
;; (wc-len (@ h4) (@ fs))

;; (wrchs (@ h1) (@ fs) 1 "athur")
;; (wrchs (@ h3) (@ fs) 1 "inojosa")
;; (wrchs (@ h3) (@ fs) 5 "Alvarez")

;; (unlink (@ h1) (@ fs))
;; (unlink (@ h2) (@ fs))
;; (unlink (@ h3) (@ fs))
;; (unlink (@ h4) (@ fs))
