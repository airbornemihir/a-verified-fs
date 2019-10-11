(in-package "ACL2")

(include-book "lofat")

;  abstract-separate.lisp                               Mihir Mehta

; This is a stobj model of the FAT32 filesystem.

(local
 (in-theory (disable take-of-too-many make-list-ac-removal
                     revappend-removal str::hex-digit-listp-of-cons
                     loghead logtail)))

(local
 (in-theory (disable nth update-nth floor mod true-listp take member-equal)))

(defund abstract-file-alist-p (x)
  (declare (xargs :guard t))
  (b* (((when (atom x)) (equal x nil))
       (head (car x)))
    ;; The presence of abstract variable makes this data structure not
    ;; strictly an alist - because they have no names and therefore they
    ;; don't need a cons pair with the car for the name.
    (and (or (natp head)
             (and (consp head)
                  (fat32-filename-p (car head))
                  (m1-file-p (cdr head))))
         (abstract-file-alist-p (cdr x)))))

(defthm
  abstract-file-alist-p-when-m1-file-alist-p
  (implies (m1-file-alist-p x)
           (abstract-file-alist-p x))
  :hints (("goal" :in-theory (enable abstract-file-alist-p))))

(defthm
  abstract-file-alist-p-correctness-1
  (implies (and (abstract-file-alist-p x)
                (alistp x))
           (m1-file-alist-p x))
  :hints (("goal" :in-theory (enable abstract-file-alist-p))))
