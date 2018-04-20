(in-package "ACL2")

;  fat32.lisp                                  Mihir Mehta

; Utilities for FAT32.

; The following is in fat32.acl2, but we include it here as well for
; when we are doing interactive development, in order to read gl:: symbols.
(include-book "centaur/gl/portcullis" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(local (include-book "file-system-lemmas"))

(defconst *expt-2-28* (expt 2 28))

;; from page 18 of the FAT specification
(defconst *ms-end-of-clusterchain* (- *expt-2-28* 1))

;; from page 14 of the FAT specification
(defconst *ms-first-data-cluster* 2)

;; from page 18 of the FAT specification
(defconst *ms-bad-cluster* 268435447)

;; from page 15 of the FAT specification
(defconst *ms-fat32-min-count-of-clusters* 65525)

;; from page 9 of the FAT specification
(defconst *ms-min-bytes-per-sector* 512)

;; inferred - there can be as few as one sectors in a cluster
(defconst *ms-min-data-region-size* (* *ms-min-bytes-per-sector*
                                       1
                                       *ms-fat32-min-count-of-clusters*))

;; from include/uapi/asm-generic/errno-base.h
(defconst *EIO* 5) ;; I/O error
(defconst *ENOSPC* 28) ;; No space left on device
(defconst *ENOENT* 2) ;; No such file or directory
(defconst *EEXIST* 17) ;; File exists

(defund fat32-entry-p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 32 x))

(defund fat32-masked-entry-p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 28 x))

;; 0 is chosen as the default value based on this comment from Microsoft's FAT
;; overview:
;; The only time that the high 4 bits of FAT32 FAT entries should ever be
;; changed is when the volume is formatted, at which time the whole 32-bit FAT
;; entry should be zeroed, including the high 4 bits.
(defund fat32-entry-fix (x)
  (declare (xargs :guard t))
  (if (fat32-entry-p x)
      x 0))

(defund fat32-masked-entry-fix (x)
  (declare (xargs :guard t))
  (if (fat32-masked-entry-p x)
      x 0))

(in-theory (enable fat32-entry-p fat32-entry-fix fat32-masked-entry-p fat32-masked-entry-fix))

(defthm fat32-masked-entry-p-correctness-1
  (implies (fat32-masked-entry-p x)
           (natp x))
  :rule-classes :forward-chaining)

;; Use a mask to take the low 28 bits.
(defund fat32-entry-mask (x)
  (declare (xargs :guard (fat32-entry-p x)))
  (logand x (- (ash 1 28) 1)))

(defthm
  fat32-entry-mask-correctness-1
  (fat32-masked-entry-p (fat32-entry-mask x))
  :hints (("goal" :in-theory (e/d (fat32-entry-mask fat32-masked-entry-p)
                                  (unsigned-byte-p logand-ash-lemma-1))
           :use (:instance logand-ash-lemma-1 (c 28)
                           (i x)))))

(fty::deffixtype fat32-entry
                 :pred   fat32-entry-p
                 :fix    fat32-entry-fix
                 :equiv  fat32-entry-equiv
                 :define t
                 :forward t
                 )

(fty::deffixtype fat32-masked-entry
                 :pred   fat32-masked-entry-p
                 :fix    fat32-masked-entry-fix
                 :equiv  fat32-masked-entry-equiv
                 :define t
                 :forward t
                 )

(fty::deflist fat32-entry-list :elt-type fat32-entry-p :true-listp t)

(fty::deflist fat32-masked-entry-list :elt-type fat32-masked-entry-p :true-listp t)

(defthm nat-listp-if-fat32-masked-entry-list-p
  (implies (fat32-masked-entry-list-p x)
           (nat-listp x))
  :rule-classes (:forward-chaining :rewrite))

(in-theory (disable fat32-entry-p fat32-entry-fix fat32-masked-entry-p fat32-masked-entry-fix))

(defthm member-of-fat32-entry-list
  (implies (and (member-equal x lst)
                (fat32-entry-list-p lst))
           (fat32-entry-p x)))

(defthm set-indices-in-fa-table-guard-lemma-1
  (implies (and (natp key)
                (< key (len l))
                (fat32-entry-list-p l)
                (fat32-entry-p val))
           (fat32-entry-list-p (update-nth key val l))))

(defthm set-indices-in-fa-table-guard-lemma-2
  (implies (fat32-entry-p x) (natp x))
  :hints (("goal" :in-theory (enable fat32-entry-p)))
  :rule-classes :forward-chaining)

(defthm set-indices-in-fa-table-guard-lemma-3
  (implies (and (fat32-entry-list-p l)
                (natp n)
                (< n (len l)))
           (fat32-entry-p (nth n l))))

(defund
  fat32-update-lower-28
  (entry masked-entry)
  (declare
   (xargs
    :guard-hints
    (("goal"
      :in-theory (enable fat32-entry-p fat32-masked-entry-p)))
    :guard (and (fat32-entry-p entry)
                (fat32-masked-entry-p masked-entry))))
  (logior (logand entry (- (ash 1 32) (ash 1 28)))
          masked-entry))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (defthm
    fat32-update-lower-28-correctness-1
    (implies
     (and (fat32-entry-p entry)
          (fat32-masked-entry-p masked-entry))
     (fat32-entry-p (fat32-update-lower-28 entry masked-entry)))
    :hints
    (("goal"
      :in-theory (e/d nil (unsigned-byte-p logand logior)
                      (fat32-entry-p fat32-masked-entry-p
                                     fat32-update-lower-28)))
     ("goal''" :in-theory (enable unsigned-byte-p)))))

; :Redef helps here for overcoming lemmas that are incompatible here (and
; finding all such lemmas in the process).
(encapsulate
  ()

  (local
   (include-book "centaur/gl/gl" :dir :system))

  (local
   (def-gl-thm fat32-update-lower-28-correctness-2
     :hyp (and (fat32-entry-p entry)
               (fat32-masked-entry-p masked-entry))
     :concl (equal (fat32-entry-mask (fat32-update-lower-28 entry
                                                            masked-entry))
                   masked-entry)
     :g-bindings (gl::auto-bindings (:nat entry 33) (:nat masked-entry 29))))

  (defthm
    fat32-update-lower-28-correctness-2
    (implies
     (and (fat32-entry-p entry)
          (fat32-masked-entry-p masked-entry))
     (equal
      (fat32-entry-mask (fat32-update-lower-28 entry masked-entry)) masked-entry))))