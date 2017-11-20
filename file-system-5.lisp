(in-package "ACL2")

;  file-system-5.lisp                                  Mihir Mehta

; Here we build on model 4 to add permissions to the file system. We'll go with
; something simple: let users be defined by integers, and not belong to groups
; at this point. Thus, only read and write permissions exist, and they are
; limited to being on/off for the creating user, and on/off for others.

; This will have to begin with defining an aggregate to hold the contents of a
; regular file. I'm not changing anything about directories at this point.

; begin encapsulate

(include-book "file-system-4")

(encapsulate
  ( ((l5-regular-file-entry-p *) => *)
    ((l5-make-regular-file * * * * * *) => *)
    ((l5-regular-file-contents *) => *)
    ((l5-regular-file-length *) => *)
    ((l5-regular-file-user-read *) => *)
    ((l5-regular-file-user-write *) => *)
    ((l5-regular-file-other-read *) => *)
    ((l5-regular-file-other-write *) => *))

  (local
   (defun l5-regular-file-entry-p (entry)
     (declare (xargs :guard t))
     (and (equal (len entry) 5)
          (nat-listp (car entry))
          (natp (cadr entry))
          (feasible-file-length-p (len (car entry)) (cadr entry))
          (booleanp (car (cddr entry)))
          (booleanp (cadr (cddr entry)))
          (booleanp (car (cddr (cddr entry))))
          (booleanp (cdr (cddr (cddr entry)))))))

  (local
   (defun l5-regular-file-contents (entry)
     (declare (xargs :guard (l5-regular-file-entry-p entry)))
     (car entry)))

  (local
   (defun l5-regular-file-length (entry)
     (declare (xargs :guard (l5-regular-file-entry-p entry)))
     (cadr entry)))

  (local
   (defun l5-regular-file-user-read (entry)
     (declare (xargs :guard (l5-regular-file-entry-p entry)))
     (car (cddr entry))))

  (local
   (defun l5-regular-file-user-write (entry)
     (declare (xargs :guard (l5-regular-file-entry-p entry)))
     (cadr (cddr entry))))

  (local
   (defun l5-regular-file-other-read (entry)
     (declare (xargs :guard (l5-regular-file-entry-p entry)))
     (car (cddr (cddr entry)))))

  (local
   (defun l5-regular-file-other-write (entry)
     (declare (xargs :guard (l5-regular-file-entry-p entry)))
     (cdr (cddr (cddr entry)))))

  (local
   (defun l5-make-regular-file
       (contents length user-read user-write other-read other-write)
     (declare (xargs :guard
                     (and (nat-listp contents)
                          (natp length)
                          (feasible-file-length-p (len contents)
                                                  length)
                          (booleanp user-read)
                          (booleanp user-write)
                          (booleanp other-read)
                          (booleanp other-write))))
     (cons contents
           (cons length
                 (cons user-read
                       (cons user-write
                             (cons other-read other-write)))))))

  (defthm l5-make-regular-file-correctness-1
    (implies (and (nat-listp contents)
                  (natp length)
                  (feasible-file-length-p (len contents)
                                          length)
                  (booleanp user-read)
                  (booleanp user-write)
                  (booleanp other-read)
                  (booleanp other-write))
             (l5-regular-file-entry-p
              (l5-make-regular-file
               contents length user-read user-write other-read other-write))))

  (defthm l5-regular-file-entry-p-correctness-1
    (implies (l5-regular-file-entry-p entry)
             (and (nat-listp (l5-regular-file-contents entry))
                  (natp (l5-regular-file-length entry))
                  (feasible-file-length-p (len (l5-regular-file-contents entry))
                                          (l5-regular-file-length entry))
                  (booleanp (l5-regular-file-user-read entry))
                  (booleanp (l5-regular-file-user-write entry))
                  (booleanp (l5-regular-file-other-read entry))
                  (booleanp (l5-regular-file-other-write entry)))))

  (defthm l5-regular-file-entry-p-correctness-2
    (booleanp (l5-regular-file-entry-p entry)))

; end encapsulate
  )
