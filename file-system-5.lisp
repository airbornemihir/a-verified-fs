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
  (local (include-book "std/util/defaggregate" :dir :system))

  (std::defaggregate
   regular-file
   (contents length user-read user-write other-read other-write)
   :tag :l5-regular-file)

  (local
   (defun l5-regular-file-entry-p (entry)
     (declare (xargs :guard t))
     (and (regular-file-p entry)
          (nat-listp (regular-file->contents entry))
          (natp (regular-file->length entry))
          (feasible-file-length-p (len (regular-file->contents entry)) (regular-file->length entry))
          (booleanp (regular-file->user-read entry))
          (booleanp (regular-file->user-write entry))
          (booleanp (regular-file->other-read entry))
          (booleanp (regular-file->other-write entry)))))

  (local
   (defun l5-regular-file-contents (entry)
     (declare (xargs :guard (l5-regular-file-entry-p entry)))
     (regular-file->contents entry)))

  (local
   (defun l5-regular-file-length (entry)
     (declare (xargs :guard (l5-regular-file-entry-p entry)))
     (regular-file->length entry)))

  (local
   (defun l5-regular-file-user-read (entry)
     (declare (xargs :guard (l5-regular-file-entry-p entry)))
     (regular-file->user-read entry)))

  (local
   (defun l5-regular-file-user-write (entry)
     (declare (xargs :guard (l5-regular-file-entry-p entry)))
     (regular-file->user-write entry)))

  (local
   (defun l5-regular-file-other-read (entry)
     (declare (xargs :guard (l5-regular-file-entry-p entry)))
     (regular-file->other-read entry)))

  (local
   (defun l5-regular-file-other-write (entry)
     (declare (xargs :guard (l5-regular-file-entry-p entry)))
     (regular-file->other-write entry)))

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
     (make-regular-file
      :contents contents
      :length length
      :user-read user-read
      :user-write user-write
      :other-read other-read
      :other-write other-write)))

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
