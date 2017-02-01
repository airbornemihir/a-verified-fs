
;  file-system-2.lisp                                  Mihir Mehta

; Here we define the rudiments of a file system with length tracking.  We first
; start with a file-system recognizer, and then we define various file-system
; operations.

(include-book "misc/assert" :dir :system)

(defthm make-character-list-makes-character-list
  (character-listp (make-character-list x)))

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
                    (or (and (consp entry) (stringp (car entry)) (natp (cdr entry)))
                        (fs-p entry))))))
         (fs-p (cdr fs)))))
;; this example - which evaluates to t - remains as a counterexample to an
;; erstwhile bug.
(defconst *test01* (fs-p '((a  "Mihir" . 5) (b "Warren" . 6) (c))))

(defthm alistp-fs-p
  (implies (fs-p fs)
           (alistp fs)))

;; (defthm fs-p-assoc
;;   (implies (and (fs-p fs)
;;                 (consp (assoc-equal name fs))
;;                 (consp (cdr (assoc-equal name fs))))
;;            (fs-p (cdr (assoc-equal name fs)))))

(defthm fs-p-assoc
  (implies (and (fs-p fs)
                (consp (assoc-equal name fs))
                (consp (cddr (assoc-equal name fs))))
           (fs-p (cdr (assoc-equal name fs)))))

(assert!
 (fs-p '((a "Mihir" . 5) (b "Warren" . 6) (c (a "Mehta" . 5) (b "Hunt" . 4)))))

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
            (if (stringp (car contents))
                (and (null (cdr hns))
                     (car contents))
              (stat (cdr hns) contents))))))))

(defthm stat-of-stat-lemma-1
  (implies (and (consp (assoc-equal (car outside) fs))
                (not (stringp (cadr (assoc-equal (car outside) fs))))
                (fs-p fs))
           (fs-p (cdr (assoc-equal (car outside) fs)))))

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
                  (and (null (cdr hns))
                       contents)  ;; We still need to remove the pair (delete-assoc (car hns) fs)
                ;; Mihir:  Consider this...
                (cons (cons (car sd)
                            (unlink (cdr hns) contents))
                      (delete-assoc (car hns) fs))))))))
    ))

(defthm wrchs-guard-lemma-1
  (implies (and (character-listp l)
                (character-listp acc)
                (<= n (len l)))
           (character-listp (first-n-ac n l acc))))

(defthm wrchs-guard-lemma-2
  (implies (and (character-listp l))
           (character-listp (nthcdr n l))))

(defthm wrchs-returns-fs-lemma-3
  (implies (and (consp fs) (fs-p fs)
                (consp (assoc-equal s fs))
                (not (stringp (cadr (assoc-equal s fs)))))
           (fs-p (cdr (assoc-equal s fs)))))

(defthm wrchs-guard-lemma-3
  (implies (and (stringp str))
           (character-listp (nthcdr n (coerce str 'list)))))

; Add wrchs...
<<<<<<< d06bad337ac6d10dbca02b470164d9587665bfa2
; The problem with this definition of wrchs is that it deletes a directory if
; it's found where a text file is expected
;; (defun wrchs (hns fs start text)
;;   (declare (xargs :guard-debug t
;;                   :guard (and (symbol-listp hns)
;;                               (or (stringp fs) (fs-p fs))
;;                               (natp start)
;;                               (stringp text))
;;                   :guard-hints
;;                   (("Subgoal 1.4" :use (:instance wrchs-returns-fs-lemma-3 (s (car hns)))) )))
;;   (if (atom hns)
;;       (let ((file fs))
;;         (if (not (and (consp file) (stringp (car file))))
;;             file ;; error, so leave fs unchanged
;;           (let* (
;;                  (end (+ start (length text)))
;;                  (oldtext (coerce (car file) 'list))
;;                  (newtext (append (make-character-list (take start oldtext))
;;                                   (coerce text 'list)
;;                                   (nthcdr end oldtext)))
;;                  (newlength (len newtext)))
;;             (cons
;;              (coerce newtext 'string)
;;              newlength))))
;;     (if (atom fs)
;;         nil
;;       (let ((sd (assoc (car hns) fs)))
;;         (if (or (atom sd) (and (consp (cdr sd)) (stringp (cadr sd))) )
;;             fs ;; error, so leave fs unchanged
;;           (let ((contents (cdr sd)))
;;             (cons (cons (car sd) (wrchs (cdr hns) contents start text))
;;                   (delete-assoc (car hns) fs))
;;             ))))))
=======
>>>>>>> Add definition of fsck
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
                              (if (not (and (consp file) (stringp (car file))))
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
  (implies (and (symbol-listp hns) (fs-p fs))
           (fs-p (wrchs hns fs start text)))
  )

(defun fsck (fs)
  (declare (xargs :guard (fs-p fs)))
  (or (atom fs)
    (and (let ((directory-or-file-entry (car fs)))
           (let ((entry (cdr directory-or-file-entry)))
             (if (and (consp entry) (stringp (car entry)))
                 (equal (len (car entry)) (cdr entry))
               (fs-p (cdr fs))))))))

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

(unlink (@ h1) (@ fs))
(unlink (@ h2) (@ fs))
(unlink (@ h3) (@ fs))
(unlink (@ h4) (@ fs))
