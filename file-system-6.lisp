(in-package "ACL2")

;  file-system-6.lisp                                  Mihir Mehta

; Here we build on model 4 to add a file allocation table. We follow exactly
; the allocation strategy laid out in model 4. To allow this to happen, we must
; set our cluster size to 1 sector, and our sector size to 8 bytes. This is
; based on every character in ACL2 being a byte.

(include-book "file-system-4")
(include-book "centaur/fty/top" :dir :system)

(defund fat32-entry-p (x)
  (declare (xargs :guard t))
  (Unsigned-byte-p 32 x))

;; 0 is chosen as the default value based on this comment from Microsoft's FAT
;; overview:
;; The only time that the high 4 bits of FAT32 FAT entries should ever be
;; changed is when the volume is formatted, at which time the whole 32-bit FAT
;; entry should be zeroed, including the high 4 bits.
(defund fat32-entry-fix (x)
  (declare (xargs :guard t))
  (if (fat32-entry-p x)
      x 0))

(in-theory (enable fat32-entry-p fat32-entry-fix))

(fty::deffixtype fat32-entry
                 :pred   fat32-entry-p
                 :fix    fat32-entry-fix
                 :equiv  fat32-entry-equiv
                 :define t
                 :forward t
                 )

(fty::deflist fat32-entry-list :elt-type fat32-entry-p :true-listp t)

(in-theory (disable fat32-entry-p fat32-entry-fix))

;; question: if fat entries are 28 bits long, then how is the maximum size
;; determined to be 4 GB?
(defund l6-regular-file-entry-p (entry)
  (declare (xargs :guard t))
  (and (consp entry)
       ;; fat entries are effectively 28 bits long
       (unsigned-byte-p 28 (car entry))
       (natp (cdr entry))
       (feasible-file-length-p (len (car entry)) (cdr entry))))

; This function defines a valid filesystem. It's an alist where all the cars
; are symbols and all the cdrs are either further filesystems or regular files.
(defun l6-fs-p (fs)
  (declare (xargs :guard t))
  (if (atom fs)
      (null fs)
    (and (let ((directory-or-file-entry (car fs)))
           (if (atom directory-or-file-entry)
               nil
             (let ((name (car directory-or-file-entry))
                   (entry (cdr directory-or-file-entry)))
               (and (symbolp name)
                    (or (l6-regular-file-entry-p entry)
                        (l6-fs-p entry))))))
         (l6-fs-p (cdr fs)))))

(defthm alistp-l6-fs-p
  (implies (l6-fs-p fs)
           (alistp fs)))

(defthm l6-fs-p-assoc
  (implies (and (l6-fs-p fs)
                (consp (assoc-equal name fs))
                (not (l6-regular-file-entry-p (cdr (assoc-equal name fs)))))
           (l6-fs-p (cdr (assoc-equal name fs)))))
