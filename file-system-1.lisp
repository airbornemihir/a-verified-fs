
;  file-system-1.lisp                                  Mihir Mehta

; Here we define the rudiments of a file system.  We first start with
; a file-system recognizer, and then we define various file-system
; operations.

(include-book "misc/assert" :dir :system)

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
                    (if (atom entry)
                        (stringp entry)
                      (fs-p entry))))))
         (fs-p (cdr fs)))))
;; this definition includes a stipulation that empty directories don't
;; exist. this is a possible definition of directories, but not a very good
;; one. see the example below - it will be nil.
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

(defthm wrchs-guard-lemma-1
  (implies (and (character-listp l) (character-listp acc) (<= n (len l)))
           (character-listp (first-n-ac n l acc))))

(defthm wrchs-guard-lemma-2
  (implies (and (character-listp l))
           (character-listp (nthcdr n l))))

; Add wrchs...
(defun wrchs (hns fs start text)
  (declare (xargs :guard (and (symbol-listp hns)
                              (fs-p fs)
                              (natp start)
                              (stringp text))))
  (let ((file (stat hns fs)))
    (if (not (stringp file))
        nil
      (let ((file-length (length file))
            (end (+ start (length text))))
        (if (< file-length end)
            nil
          (coerce
           (append (take start (coerce file 'list))
                   (coerce text 'list)
                   (nthcdr end (coerce file 'list)))
           'string))))))

; Find length of file

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

(assign fs '((a . "Mihir") (b . "Warren") (c (a . "Mehta") (b . "Hunt"))))

(assign h1 '(a))
(assign h2 '(a b))
(assign h3 '(c b))
(assign h4 '(c))

(stat (@ h1) (@ fs))
(stat (@ h2) (@ fs))
(stat (@ h3) (@ fs))
(stat (@ h4) (@ fs))

(unlink (@ h1) (@ fs))
(unlink (@ h2) (@ fs))
(unlink (@ h3) (@ fs))
(unlink (@ h4) (@ fs))
