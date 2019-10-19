(in-package "ACL2")

(include-book "hifat")

;  abstract-separate.lisp                               Mihir Mehta

; This is a model of the FAT32 filesystem, related to HiFAT but with abstract
; variables.

(local
 (in-theory (disable take-of-too-many make-list-ac-removal
                     revappend-removal str::hex-digit-listp-of-cons
                     loghead logtail)))

(local
 (in-theory (disable nth update-nth floor mod true-listp take member-equal)))

;; This is explicitly a replacement for assoc-equal with a vacuous guard.
(defund abs-assoc (x alist)
  (declare (xargs :guard t))
  (cond ((atom alist) nil)
        ((and (atom (car alist)) (null x))
         (car alist))
        ((and (consp (car alist)) (equal x (car (car alist))))
         (car alist))
        (t (abs-assoc x (cdr alist)))))

(defthm abs-assoc-definition
  (equal (abs-assoc x alist)
         (assoc-equal x alist))
  :hints (("goal" :in-theory (enable abs-assoc)))
  :rule-classes :definition)

;; This is explicitly a replacement for put-assoc-equal with a vacuous guard.
(defund abs-put-assoc (name val alist)
  (declare (xargs :guard t))
  (cond ((atom alist) (list (cons name val)))
        ((and (atom (car alist)) (null name))
         (cons (cons name val) (cdr alist)))
        ((and (consp (car alist)) (equal name (caar alist)))
         (cons (cons name val) (cdr alist)))
        (t (cons (car alist)
                 (abs-put-assoc name val (cdr alist))))))

(defthm abs-put-assoc-definition
  (equal (abs-put-assoc name val alist)
         (put-assoc-equal name val alist))
  :hints (("goal" :in-theory (enable abs-put-assoc)))
  :rule-classes :definition)

;; This is explicitly a replacement for remove-assoc-equal with a vacuous guard.
(defund abs-remove-assoc (x alist)
  (declare (xargs :guard t))
  (cond ((atom alist) nil)
        ((and (atom (car alist)) (null x))
         (abs-remove-assoc x (cdr alist)))
        ((and (consp (car alist)) (equal x (car (car alist))))
         (abs-remove-assoc x (cdr alist)))
        (t (cons (car alist)
                 (abs-remove-assoc x (cdr alist))))))

(defthm abs-remove-assoc-definition
  (equal (abs-remove-assoc x alist)
         (remove-assoc-equal x alist))
  :hints (("goal" :in-theory (enable abs-remove-assoc)))
  :rule-classes :definition)

;; We need to write this whole thing out - the same way we did it for
;; m1-file-alist-p - because the induction scheme has to be created by us,
;; without assistance from fty, just this once.
(defund
  abs-file-alist-p (x)
  (declare (xargs :guard t))
  (b* (((when (atom x)) (equal x nil))
       (head (car x))
       ;; The presence of abstract variables makes this data structure not
       ;; strictly an alist - because they have no names and therefore they
       ;; don't need a cons pair with the car for the name.
       ((when (atom head))
        (and (natp head) (abs-file-alist-p (cdr x))))
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
             (abs-file-alist-p contents))
         (abs-file-alist-p (cdr x)))))

(defund abs-file-contents-p (contents)
  (declare (xargs :guard t))
  (or (and (stringp contents)
           (unsigned-byte-p 32 (length contents)))
      (abs-file-alist-p contents)))

(defund abs-file-contents-fix (contents)
  (declare (xargs :guard t))
  (if (abs-file-contents-p contents)
      contents
    ""))

(defthm
  abs-file-contents-p-correctness-1
  (implies (abs-file-alist-p contents)
           (abs-file-contents-p contents))
  :hints (("goal" :in-theory (enable abs-file-contents-p))))

(defthm abs-file-contents-p-of-abs-file-contents-fix
  (abs-file-contents-p (abs-file-contents-fix x))
  :hints (("goal" :in-theory (enable abs-file-contents-fix))))

(defthm abs-file-contents-fix-when-abs-file-contents-p
  (implies (abs-file-contents-p x)
           (equal (abs-file-contents-fix x) x))
  :hints (("goal" :in-theory (enable abs-file-contents-fix))))

(defthm
  abs-file-contents-p-when-stringp
  (implies (stringp contents)
           (equal (abs-file-contents-p contents)
                  (unsigned-byte-p 32 (length contents))))
  :hints (("goal" :in-theory (enable abs-file-contents-p abs-file-alist-p))))

(defthm
  abs-file-alist-p-of-abs-file-contents-fix
  (equal (abs-file-alist-p (abs-file-contents-fix contents))
         (abs-file-alist-p contents))
  :hints (("goal" :in-theory (enable abs-file-contents-fix))))

(fty::deffixtype abs-file-contents
                 :pred abs-file-contents-p
                 :fix abs-file-contents-fix
                 :equiv abs-file-contents-equiv
                 :define t)

(fty::defprod
 abs-file
 ((dir-ent dir-ent-p :default (dir-ent-fix nil))
  (contents abs-file-contents-p :default (abs-file-contents-fix nil))))

(defthm
  acl2-count-of-abs-file->contents
  t
  :rule-classes
  ((:linear
    :corollary
    (implies (abs-file-p file)
             (< (acl2-count (abs-file->contents file))
                (acl2-count file)))
    :hints
    (("goal" :in-theory (enable abs-file-p abs-file->contents))))
   (:linear
    :corollary
    (<= (acl2-count (abs-file->contents file))
        (acl2-count file))
    :hints
    (("goal"
      :in-theory
      (enable abs-file-p abs-file->contents abs-file-contents-fix))))))

(defund abs-directory-file-p (file)
  (declare (xargs :guard t))
  (and (abs-file-p file)
       (abs-file-alist-p (abs-file->contents file))))

(defthm
  abs-file-alist-p-when-m1-file-alist-p
  (implies (m1-file-alist-p x)
           (abs-file-alist-p x))
  :hints (("goal" :in-theory (enable abs-file-alist-p
                                     m1-file-alist-p))))

(defthm
  abs-file-contents-p-when-m1-file-contents-p
  (implies (m1-file-contents-p contents)
           (abs-file-contents-p contents))
  :hints (("goal" :in-theory (enable m1-file-contents-p
                                     abs-file-contents-p))))

(defthm
  abs-file-p-when-m1-regular-file-p
  (implies (m1-regular-file-p file)
           (abs-file-p file))
  :hints (("goal" :in-theory (enable m1-regular-file-p
                                     abs-file-p m1-file-p))))

;; Awful proof.
(defthm
  m1-regular-file-p-of-abs-file
  (equal
   (m1-regular-file-p (abs-file dir-ent contents))
   (and
    (stringp (abs-file-contents-fix contents))
    (unsigned-byte-p 32
                     (length (abs-file-contents-fix contents)))))
  :hints (("goal" :in-theory (enable m1-regular-file-p abs-file-contents-fix
                                     m1-file-p abs-file-contents-p abs-file
                                     m1-file->contents))))

(defthm
  abs-directory-file-p-correctness-1
  (implies (m1-directory-file-p file)
           (and (m1-file-p file)
                (not (stringp (m1-file->contents file)))))
  :hints (("goal"
           :in-theory (enable m1-directory-file-p m1-file-alist-p
                              m1-regular-file-p))))

(defthm
  abs-file-p-when-abs-directory-file-p
  (implies (abs-directory-file-p file)
           (abs-file-p file))
  :hints (("goal" :in-theory (enable abs-directory-file-p))))

(defthm
  abs-file-alist-p-of-abs-file->contents
  (equal (abs-file-alist-p (abs-file->contents file))
         (abs-directory-file-p (abs-file-fix file)))
  :hints (("goal" :in-theory (enable abs-file->contents
                                     abs-directory-file-p)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (abs-directory-file-p file)
             (abs-file-alist-p (abs-file->contents file))))))

(defthm
  abs-directory-file-p-of-abs-file
  (implies (abs-file-alist-p contents)
           (abs-directory-file-p (abs-file dir-ent contents)))
  :hints (("goal" :in-theory (enable abs-directory-file-p))))

;; top-complete is known to match up with alistp
(defund abs-complete (x)
  (declare (xargs :guard t))
  (or (atom x)
      (and (consp (car x))
           (or (not (abs-directory-file-p (cdar x)))
               (abs-complete (abs-file->contents (cdar x))))
           (abs-complete (cdr x)))))

(defthm
  abs-file-alist-p-correctness-1-lemma-1
  (implies (and (or (and (consp (car x))
                         (m1-file-alist-p (abs-file->contents (cdr (car x)))))
                    (not
                     (and (abs-file-alist-p (abs-file->contents (cdr (car x))))
                          (or (abs-directory-file-p (cdr (car x)))
                              (abs-complete (abs-file->contents (cdr (car x))))))))
                (abs-file-alist-p x))
           (m1-file-p (cdr (car x))))
  :hints
  (("goal" :expand ((m1-file-p (cdr (car x)))
                    (abs-file-alist-p x)
                    (m1-file-alist-p (abs-file->contents (cdr (car x))))
                    (abs-file->contents (cdr (car x)))
                    (abs-directory-file-p (cdr (car x)))
                    (abs-file-p (cdr (car x)))))))

(defthm
  abs-file-alist-p-correctness-1-lemma-2
  (implies (and (consp (car x))
                (m1-file-alist-p (abs-file->contents (cdr (car x))))
                (m1-file-alist-p (cdr x))
                (abs-file-alist-p x))
           (m1-file-alist-p x))
  :hints (("goal" :in-theory (disable (:rewrite m1-file-alist-p-of-cons))
           :use (:instance (:rewrite m1-file-alist-p-of-cons)
                           (x (cdr x))
                           (a (car x)))
           :expand (abs-file-alist-p x))))

(defthm
  abs-file-alist-p-correctness-1-lemma-3
  (implies (and (not (and (abs-file-alist-p (abs-file->contents (cdr (car x))))
                          (abs-complete (abs-file->contents (cdr (car x))))))
                (abs-file-alist-p x))
           (fat32-filename-p (car (car x))))
  :hints (("goal" :expand (abs-file-alist-p x))))

(defthm abs-file-alist-p-correctness-1-lemma-4
  (implies (stringp x)
           (not (abs-file-alist-p x)))
  :hints (("goal" :in-theory (enable abs-file-alist-p)))
  :rule-classes :type-prescription)

(defthm
  abs-file-alist-p-correctness-1-lemma-5
  (implies (and (not (and (abs-file-alist-p (abs-file->contents (cdr (car x))))
                          (or (abs-directory-file-p (cdr (car x)))
                              (abs-complete (abs-file->contents (cdr (car x)))))))
                (m1-file-alist-p (cdr x))
                (abs-file-alist-p x))
           (m1-file-alist-p x))
  :hints (("goal" :in-theory (disable (:rewrite m1-file-alist-p-of-cons))
           :use (:instance (:rewrite m1-file-alist-p-of-cons)
                           (x (cdr x))
                           (a (car x)))
           :expand (abs-file-alist-p x))))

;; This theorem states that an abstract filesystem tree without any body
;; addresses is just a HiFAT instance.
(defthm
  abs-file-alist-p-correctness-1
  (implies (and (abs-file-alist-p x)
                (abs-complete x))
           (m1-file-alist-p x))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-complete)
           :induct (abs-complete x))))

(defthm abs-file-alist-p-of-put-assoc-equal
  (implies (and (fat32-filename-p name)
                (abs-file-p val)
                (abs-file-alist-p alist))
           (abs-file-alist-p (put-assoc-equal name val alist)))
  :hints (("goal" :in-theory (enable abs-file-alist-p
                                     abs-file-p abs-file-contents-p))))

(defthm abs-file-alist-p-of-append
  (implies (and (abs-file-alist-p x)
                (abs-file-alist-p y))
           (abs-file-alist-p (append x y)))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defthm abs-file-alist-p-of-remove-equal
  (implies (abs-file-alist-p l)
           (abs-file-alist-p (remove-equal x l)))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defthm abs-file-alist-p-of-remove-assoc-equal
  (implies (abs-file-alist-p alist)
           (abs-file-alist-p (remove-assoc-equal x alist)))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defthm true-listp-when-abs-file-alist-p
  (implies (abs-file-alist-p fs)
           (true-listp fs))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defund
  abs-top-addrs (abs-file-alist)
  (declare
   (xargs :guard (abs-file-alist-p abs-file-alist)
          :guard-hints
          (("goal" :in-theory (enable abs-file-alist-p)))))
  (cond ((atom abs-file-alist) nil)
        ((natp (car abs-file-alist))
         (list* (car abs-file-alist)
                (abs-top-addrs (cdr abs-file-alist))))
        (t (abs-top-addrs (cdr abs-file-alist)))))

;; For this function, it might be worth investing in the abs-file-alist-fix
;; thing, but that function just generally seems like a placeholder fixer and
;; I'm not going there for now. The purpose of this function is to quickly
;; allow a given abstract variable to be found in the frame - just keep looking
;; at the (abs-addrs ...) of all the elements in the frame.
(defund
  abs-addrs (abs-file-alist)
  (declare
   (xargs :guard (abs-file-alist-p abs-file-alist)
          :guard-hints
          (("goal" :in-theory (enable abs-file-alist-p)))))
  (cond ((atom abs-file-alist) nil)
        ((atom (car abs-file-alist))
         (list* (mbe :logic (nfix (car abs-file-alist))
                     :exec (car abs-file-alist))
                (abs-addrs (cdr abs-file-alist))))
        ((abs-directory-file-p (cdar abs-file-alist))
         (append
          (abs-addrs (abs-file->contents (cdar abs-file-alist)))
          (abs-addrs (cdr abs-file-alist))))
        (t (abs-addrs (cdr abs-file-alist)))))

(defthm abs-complete-definition
  (equal (abs-complete x)
         (atom (abs-addrs x)))
  :rule-classes :definition
  :hints (("goal" :in-theory (enable abs-complete abs-addrs))))

;; Where are the numbers going to come from? It's not going to work, the idea
;; of letting variables be represented by their index in the list. Under such a
;; scheme, we'll never be able to rewrite an (append ...) term, since that
;; would immediately cause all the indices to become wrong. It's probably best
;; to use the function find-new-index for this purpose.
;;
;; In a certain theoretical sense, we don't actually need to store abstract heap
;; cells as pairs - keeping the address in the table along with the
;; substructure isn't actually necessary, because we can just look in the
;; larger structure for occurrences of the body address. However, this process
;; would be grossly inefficient because we would have to look everywhere in the
;; directory tree. I suspect that's why the idea of an abstract heap cell as a
;; pair arose in the first place.
;;
;; One more thing: I'm not returning an error code from this function at the
;; moment, because I can't fathom where such an error code would be useful. It
;; would only arise from a programming error on our part, where we tried to
;; context-apply a nonexistent variable - not from any real filesystem
;; error. In such a case, it's OK to keep the no-change loser behaviour, even
;; if we don't immediately formalise it.
;;
;; Another thing: this function only works if there are no body addresses in
;; the way down the path... otherwise, we'd have to look up those body
;; addresses and look inside them. In terms of recursion, we'd have to recur as
;; many times as body addresses occur along the path. Also, each time we were
;; looking for something and failed to find a directory entry at a certain
;; level - but found at least one body address - we'd have to iterate over all
;; body addresses at that level.
;;
;; <sigh>
(defund abs-context-apply
  (abs-file-alist1 abs-file-alist2 x x-path)
  (declare (xargs :guard
                  (and
                   (abs-file-alist-p abs-file-alist1)
                   (natp x)
                   (abs-file-alist-p abs-file-alist2)
                   (fat32-filename-list-p x-path))
                  :verify-guards nil))
  (b*
      (((when (and (consp x-path)
                   (consp (abs-assoc (car x-path) abs-file-alist1))
                   (abs-directory-file-p
                    (cdr (abs-assoc (car x-path) abs-file-alist1)))))
        (abs-put-assoc
         (car x-path)
         (abs-file
          (abs-file->dir-ent (cdr (abs-assoc (car x-path) abs-file-alist1)))
          (abs-context-apply
           (abs-file->contents (cdr (abs-assoc (car x-path) abs-file-alist1)))
           abs-file-alist2
           x
           (cdr x-path)))
         abs-file-alist1))
       ;; This is actually an error condition.
       ((when (consp x-path))
        abs-file-alist1)
       ((when (member x abs-file-alist1))
        (append (remove x abs-file-alist1) abs-file-alist2)))
    abs-file-alist1))

(defthm abs-file-alist-p-of-abs-context-apply-lemma-1
  (implies (and (abs-file-alist-p alist)
                (not (fat32-filename-p x)))
           (not (consp (assoc-equal x alist))))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defthm
  abs-file-alist-p-of-abs-context-apply-lemma-2
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal (car x-path)
                                                abs-file-alist1)))
        (abs-file-alist-p abs-file-alist1))
   (abs-file-alist-p
    (put-assoc-equal
     (car x-path)
     (abs-file (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                                    abs-file-alist1)))
               (abs-context-apply
                (abs-file->contents (cdr (assoc-equal (car x-path)
                                                      abs-file-alist1)))
                abs-file-alist2 x (cdr x-path)))
     abs-file-alist1)))
  :hints
  (("goal" :in-theory (disable abs-file-alist-p-of-abs-context-apply-lemma-1)
    :use (:instance abs-file-alist-p-of-abs-context-apply-lemma-1
                    (alist abs-file-alist1)
                    (x (car x-path))))))

(defthm abs-file-alist-p-of-abs-context-apply
  (implies
   (and
    (abs-file-alist-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist2))
   (abs-file-alist-p
    (abs-context-apply
     abs-file-alist1 abs-file-alist2 x x-path)))
  :hints
  (("Goal" :in-theory (enable abs-context-apply))))

(verify-guards abs-context-apply
  :guard-debug t
  :hints (("Goal" :in-theory (enable abs-file-alist-p)) ))

(defthm abs-addrs-of-append
  (equal (abs-addrs (append x y))
         (append (abs-addrs x) (abs-addrs y)))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm member-of-abs-addrs-when-natp
  (implies (and (natp x)
                (member-equal x abs-file-alist))
           (member-equal x (abs-addrs abs-file-alist)))
  :hints (("goal" :in-theory (enable abs-addrs abs-file-alist-p))))

(defund
  abs-no-dups-p (fs)
  (declare
   (xargs
    :guard (abs-file-alist-p fs)
    :guard-hints (("goal" :expand (abs-file-alist-p fs)))))
  (cond ((atom fs) t)
        ((not (abs-no-dups-p (cdr fs))) nil)
        ((not (and (consp (car fs))
                   (mbt (stringp (car (car fs))))))
         (not (member-equal (car fs) (cdr fs))))
        ((consp (abs-assoc (caar fs) (cdr fs)))
         nil)
        ((abs-directory-file-p (cdar fs))
         (abs-no-dups-p (abs-file->contents (cdar fs))))
        (t t)))

(defthm
  abs-no-dups-p-of-cdr-of-assoc
  (implies (and (abs-file-alist-p fs)
                (abs-no-dups-p fs)
                (abs-directory-file-p (cdr (assoc-equal name fs))))
           (abs-no-dups-p (abs-file->contents (cdr (assoc-equal name fs)))))
  :hints (("goal" :in-theory (enable abs-no-dups-p)
           :expand (abs-file-alist-p fs))))

(defthm abs-addrs-of-abs-context-apply-1-lemma-1
  (implies (and (member-equal x abs-file-alist1)
                (integerp x)
                (<= 0 x)
                (member-equal x (abs-addrs abs-file-alist2)))
           (intersectp-equal (abs-addrs abs-file-alist1)
                             (abs-addrs abs-file-alist2)))
  :hints (("goal" :use (:instance (:rewrite intersectp-member)
                                  (a x)
                                  (y (abs-addrs abs-file-alist2))
                                  (x (abs-addrs abs-file-alist1))))))

(defthm abs-addrs-of-abs-context-apply-1-lemma-2
  (subsetp-equal (abs-addrs (remove-equal x abs-file-alist))
                 (abs-addrs abs-file-alist))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-abs-context-apply-1-lemma-3
  (implies (and (member-equal x abs-file-alist1)
                (integerp x)
                (<= 0 x)
                (no-duplicatesp-equal (abs-addrs abs-file-alist1)))
           (not (member-equal x
                              (abs-addrs (remove-equal x abs-file-alist1)))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-abs-context-apply-1-lemma-4
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
        (no-duplicatesp-equal (abs-addrs abs-file-alist1)))
   (no-duplicatesp-equal
    (abs-addrs
     (abs-file->contents (cdr (assoc-equal name abs-file-alist1))))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-abs-context-apply-1-lemma-5
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
        (not (intersectp-equal (abs-addrs abs-file-alist1)
                               y)))
   (not
    (intersectp-equal
     (abs-addrs (abs-file->contents (cdr (assoc-equal name abs-file-alist1))))
     y)))
  :hints (("goal" :in-theory (e/d (abs-addrs intersectp-equal)
                                  (intersectp-is-commutative)))))

(defthm
  abs-addrs-of-abs-context-apply-1-lemma-6
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (member-equal
     x
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name abs-file-alist1))))))
   (member-equal x (abs-addrs abs-file-alist1)))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm abs-addrs-of-abs-context-apply-1-lemma-7
  (implies (and (natp x)
                (not (member-equal x (abs-addrs abs-file-alist1))))
           (equal (abs-context-apply abs-file-alist1
                                     abs-file-alist2 x x-path)
                  abs-file-alist1))
  :hints (("goal" :in-theory (enable abs-addrs abs-context-apply)
           :induct (abs-context-apply abs-file-alist1
                                      abs-file-alist2 x x-path)
           :do-not-induct t)))

(defthm
  abs-addrs-of-abs-context-apply-1-lemma-8
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name (cdr abs-file-alist1))))
    (member-equal
     x
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name (cdr abs-file-alist1))))))
    (member-equal
     x
     (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))))
   (intersectp-equal
    (abs-addrs (cdr abs-file-alist1))
    (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))))
  :hints
  (("goal"
    :use (:instance
          (:rewrite intersectp-member)
          (a x)
          (y (abs-addrs (abs-file->contents (cdr (car abs-file-alist1)))))
          (x (abs-addrs (cdr abs-file-alist1)))))))

(defthm
  abs-addrs-of-abs-context-apply-1-lemma-9
  (implies
   (not (member-equal x (abs-addrs abs-file-alist)))
   (not (member-equal x
                      (abs-addrs (remove-assoc-equal name abs-file-alist)))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-abs-context-apply-1-lemma-10
  (implies
   (and
    (member-equal
     x
     (abs-addrs (abs-file->contents (cdr (car abs-file-alist1)))))
    (member-equal x
                  (abs-addrs (remove-assoc-equal (car (car abs-file-alist1))
                                                 (cdr abs-file-alist1)))))
   (intersectp-equal
    (abs-addrs (cdr abs-file-alist1))
    (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))))
  :hints
  (("goal"
    :use (:instance
          (:rewrite intersectp-member)
          (a x)
          (y (abs-addrs (abs-file->contents (cdr (car abs-file-alist1)))))
          (x (abs-addrs (cdr abs-file-alist1)))))))

(defthm
  abs-addrs-of-abs-context-apply-1-lemma-11
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (member-equal
     x
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))))
    (no-duplicatesp-equal (abs-addrs abs-file-alist1)))
   (not (member-equal x
                      (abs-addrs (remove-assoc-equal name abs-file-alist1)))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-abs-context-apply-1-lemma-12
  (implies
   (and
    (not (member-equal x
                       (abs-addrs (remove-assoc-equal name abs-file-alist1))))
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (not (member-equal x (abs-addrs abs-file-alist2)))
    (abs-file-alist-p abs-file-alist2)
    (abs-file-alist-p abs-file-alist1)
    (abs-no-dups-p abs-file-alist1))
   (not
    (member-equal
     x
     (abs-addrs
      (put-assoc-equal
       name
       (abs-file (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
                 abs-file-alist2)
       abs-file-alist1)))))
  :hints
  (("goal"
    :in-theory (e/d ((:definition abs-addrs)
                     intersectp-equal abs-no-dups-p)
                    (intersectp-is-commutative))
    :expand ((abs-no-dups-p abs-file-alist1)
             (abs-file-alist-p abs-file-alist1))
    :induct
    (put-assoc-equal
     name
     (abs-file (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
               abs-file-alist2)
     abs-file-alist1))))

(defthm
  abs-addrs-of-abs-context-apply-1-lemma-13
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal (car x-path)
                                            abs-file-alist1)))
    (not
     (member-equal
      x
      (abs-addrs (abs-context-apply
                  (abs-file->contents (cdr (assoc-equal (car x-path)
                                                        abs-file-alist1)))
                  abs-file-alist2 x (cdr x-path)))))
    (integerp x)
    (<= 0 x)
    (no-duplicatesp-equal (abs-addrs abs-file-alist1))
    (not
     (equal
      (put-assoc-equal
       (car x-path)
       (abs-file (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                                      abs-file-alist1)))
                 (abs-context-apply
                  (abs-file->contents (cdr (assoc-equal (car x-path)
                                                        abs-file-alist1)))
                  abs-file-alist2 x (cdr x-path)))
       abs-file-alist1)
      abs-file-alist1))
    (abs-no-dups-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist2))
   (not
    (member-equal
     x
     (abs-addrs
      (put-assoc-equal
       (car x-path)
       (abs-file (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                                      abs-file-alist1)))
                 (abs-context-apply
                  (abs-file->contents (cdr (assoc-equal (car x-path)
                                                        abs-file-alist1)))
                  abs-file-alist2 x (cdr x-path)))
       abs-file-alist1)))))
  :hints
  (("goal"
    :in-theory (disable put-assoc-equal-without-change
                        (:rewrite abs-addrs-of-abs-context-apply-1-lemma-7)
                        (:rewrite abs-addrs-of-abs-context-apply-1-lemma-11))
    :use
    ((:instance
      put-assoc-equal-without-change
      (alist abs-file-alist1)
      (val
       (abs-file (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                                      abs-file-alist1)))
                 (abs-context-apply
                  (abs-file->contents (cdr (assoc-equal (car x-path)
                                                        abs-file-alist1)))
                  abs-file-alist2 x (cdr x-path))))
      (name (car x-path)))
     (:instance
      (:rewrite abs-addrs-of-abs-context-apply-1-lemma-7)
      (x-path (cdr x-path))
      (x x)
      (abs-file-alist2 abs-file-alist2)
      (abs-file-alist1
       (abs-file->contents (cdr (assoc-equal (car x-path)
                                             abs-file-alist1)))))
     (:instance (:rewrite abs-addrs-of-abs-context-apply-1-lemma-11)
                (abs-file-alist1 abs-file-alist1)
                (name (car x-path))
                (x x)))
    :do-not-induct t)))

;; There's a form of saying the same thing:
;; (implies (not (equal
;;                (abs-context-apply
;;                 abs-file-alist1 abs-file-alist2 x x-path)
;;                abs-file-alist1))
;;          (equal (abs-addrs
;;                  (abs-context-apply
;;                   abs-file-alist1 abs-file-alist2 x x-path))
;;                 (remove x (abs-addrs abs-file-alist1))))
;; that's very likely going to be tough to prove, so... let's leave it alone.
(defthm
  abs-addrs-of-abs-context-apply-1
  (implies
   (and (natp x)
        (no-duplicatesp-equal (abs-addrs abs-file-alist1))
        (not (equal (abs-context-apply abs-file-alist1
                                       abs-file-alist2 x x-path)
                    abs-file-alist1))
        (not (intersectp-equal (abs-addrs abs-file-alist1)
                               (abs-addrs abs-file-alist2)))
        (abs-no-dups-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2))
   (not
    (member-equal x
                  (abs-addrs (abs-context-apply abs-file-alist1
                                                abs-file-alist2 x x-path)))))
  :hints (("goal" :in-theory (enable abs-addrs abs-context-apply)
           :induct (abs-context-apply abs-file-alist1
                                      abs-file-alist2 x x-path))))

;; This just might be made obsolete soon...
(defthm
  abs-addrs-of-abs-context-apply-2-lemma-1
  (implies (not (intersectp-equal (abs-addrs abs-file-alist1)
                                  y))
           (not (intersectp-equal (abs-addrs (remove-equal x abs-file-alist1))
                                  y)))
  :hints (("goal" :in-theory (e/d (abs-addrs intersectp-equal)
                                  (intersectp-is-commutative)))))

(defthm
  abs-addrs-of-abs-context-apply-2-lemma-2
  (implies
   (no-duplicatesp-equal (abs-addrs abs-file-alist1))
   (no-duplicatesp-equal (abs-addrs (remove-equal x abs-file-alist1))))
  :hints
  (("goal"
    :in-theory (e/d (abs-addrs)
                    (intersectp-is-commutative))
    :expand
    ((:with intersectp-is-commutative
            (intersectp-equal
             (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
             (abs-addrs (remove-equal x (cdr abs-file-alist1)))))
     (:with intersectp-is-commutative
            (intersectp-equal
             (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
             (abs-addrs (cdr abs-file-alist1))))))))

(defthm
  abs-addrs-of-abs-context-apply-2-lemma-3
  (implies
   (and
    (abs-no-dups-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist2)
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (not
     (intersectp-equal (abs-addrs (remove-assoc-equal name abs-file-alist1))
                       y))
    (not (intersectp-equal (abs-addrs abs-file-alist2)
                           y)))
   (not
    (intersectp-equal
     (abs-addrs
      (put-assoc-equal
       name
       (abs-file (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
                 abs-file-alist2)
       abs-file-alist1))
     y)))
  :hints (("goal" :in-theory (e/d ((:definition abs-addrs)
                                   intersectp-equal abs-file-alist-p)
                                  (intersectp-is-commutative))
           :expand (abs-no-dups-p abs-file-alist1))))

(defthm
  abs-addrs-of-abs-context-apply-2-lemma-6
  (subsetp-equal (abs-addrs (remove-assoc-equal name abs-file-alist))
                 (abs-addrs abs-file-alist))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-abs-context-apply-2-lemma-4
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal (car x-path)
                                            abs-file-alist1)))
    (not
     (intersectp-equal
      (abs-addrs (abs-context-apply
                  (abs-file->contents (cdr (assoc-equal (car x-path)
                                                        abs-file-alist1)))
                  abs-file-alist2 x (cdr x-path)))
      y))
    (abs-file-alist-p abs-file-alist2)
    (not (intersectp-equal (abs-addrs abs-file-alist1)
                           y))
    (abs-file-alist-p abs-file-alist1)
    (abs-no-dups-p abs-file-alist1))
   (not
    (intersectp-equal
     (abs-addrs
      (put-assoc-equal
       (car x-path)
       (abs-file (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                                      abs-file-alist1)))
                 (abs-context-apply
                  (abs-file->contents (cdr (assoc-equal (car x-path)
                                                        abs-file-alist1)))
                  abs-file-alist2 x (cdr x-path)))
       abs-file-alist1))
     y)))
  :hints
  (("goal"
    :use (:instance (:rewrite intersect-with-subset)
                    (z y)
                    (y (abs-addrs abs-file-alist1))
                    (x (abs-addrs (remove-assoc-equal (car x-path)
                                                      abs-file-alist1)))))))

(defthm
  abs-addrs-of-abs-context-apply-2-lemma-7
  (implies
   (and (abs-file-alist-p abs-file-alist2)
        (not (intersectp-equal (abs-addrs abs-file-alist1)
                               y))
        (not (intersectp-equal (abs-addrs abs-file-alist2)
                               y))
        (abs-file-alist-p abs-file-alist1)
        (abs-no-dups-p abs-file-alist1))
   (not
    (intersectp-equal (abs-addrs (abs-context-apply abs-file-alist1
                                                    abs-file-alist2 x x-path))
                      y)))
  :hints (("goal" :in-theory (e/d ((:definition abs-addrs)
                                   abs-context-apply)
                                  (intersectp-is-commutative)))))

;; Move later
(defthm abs-addrs-of-abs-context-apply-2-lemma-9
  (implies (abs-no-dups-p abs-file-alist1)
           (abs-no-dups-p (cdr abs-file-alist1)))
  :hints (("goal" :in-theory (enable abs-no-dups-p))))
(defthm abs-addrs-of-abs-context-apply-2-lemma-10
  (implies (abs-file-alist-p abs-file-alist1)
           (abs-file-alist-p (cdr abs-file-alist1)))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defthm
  abs-addrs-of-abs-context-apply-2-lemma-11
  (implies
   (not (intersectp-equal
         (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
         (abs-addrs (cdr abs-file-alist1))))
   (not
    (intersectp-equal
     (abs-addrs (remove-assoc-equal name (cdr abs-file-alist1)))
     (abs-addrs (abs-file->contents$inline (cdr (car abs-file-alist1)))))))
  :hints
  (("goal"
    :use
    ((:instance
      (:rewrite intersect-with-subset)
      (z (abs-addrs (abs-file->contents (cdr (car abs-file-alist1)))))
      (x (abs-addrs (remove-assoc-equal name (cdr abs-file-alist1))))
      (y (abs-addrs (cdr abs-file-alist1))))))))

(defthm
  abs-addrs-of-abs-context-apply-2-lemma-8
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name (cdr abs-file-alist1))))
        (not (intersectp-equal
              (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
              (abs-addrs (cdr abs-file-alist1))))
        (not (intersectp-equal
              (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
              (abs-addrs abs-file-alist2)))
        (abs-no-dups-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2))
   (not
    (intersectp-equal
     (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
     (abs-addrs
      (put-assoc-equal
       name
       (abs-file
        (abs-file->dir-ent (cdr (assoc-equal name (cdr abs-file-alist1))))
        abs-file-alist2)
       (cdr abs-file-alist1))))))
  :hints
  (("goal"
    :in-theory (disable intersectp-is-commutative)
    :expand
    ((:with
      intersectp-is-commutative
      (intersectp-equal
       (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
       (abs-addrs
        (put-assoc-equal
         name
         (abs-file
          (abs-file->dir-ent (cdr (assoc-equal name (cdr abs-file-alist1))))
          abs-file-alist2)
         (cdr abs-file-alist1)))))
     (:with
      intersectp-is-commutative
      (intersectp-equal
       (abs-addrs abs-file-alist2)
       (abs-addrs
        (abs-file->contents$inline (cdr (car abs-file-alist1))))))))))

(defthm
  abs-addrs-of-abs-context-apply-2-lemma-12
  (implies
   (and (abs-directory-file-p (cdr (car abs-file-alist1)))
        (not (intersectp-equal
              (abs-addrs (remove-assoc-equal (car (car abs-file-alist1))
                                             (cdr abs-file-alist1)))
              (abs-addrs abs-file-alist2)))
        (abs-no-dups-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist1))
   (not (intersectp-equal (abs-addrs abs-file-alist2)
                          (abs-addrs (cdr abs-file-alist1)))))
  :hints (("goal" :expand ((abs-no-dups-p abs-file-alist1)
                           (abs-file-alist-p abs-file-alist1)))))

(defthm
  abs-addrs-of-abs-context-apply-2-lemma-5
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (no-duplicatesp-equal (abs-addrs abs-file-alist1))
    (not
     (intersectp-equal (abs-addrs (remove-assoc-equal name abs-file-alist1))
                       (abs-addrs abs-file-alist2)))
    (abs-no-dups-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist2)
    (no-duplicatesp-equal (abs-addrs abs-file-alist2)))
   (no-duplicatesp-equal
    (abs-addrs
     (put-assoc-equal
      name
      (abs-file (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
                abs-file-alist2)
      abs-file-alist1))))
  :hints (("goal" :in-theory (e/d ((:definition abs-addrs)
                                   intersectp-equal)
                                  (intersectp-is-commutative)))))
(defthm
  abs-addrs-of-abs-context-apply-2-lemma-13
  (implies
   (and
    (not
     (intersectp-equal
      (abs-addrs (remove-assoc-equal name (cdr abs-file-alist1)))
      (abs-addrs
       (abs-file->contents (cdr (assoc-equal name (cdr abs-file-alist1)))))))
    (abs-directory-file-p (cdr (assoc-equal name (cdr abs-file-alist1))))
    (not (member-equal (car abs-file-alist1)
                       (abs-addrs (cdr abs-file-alist1)))))
   (not
    (intersectp-equal
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name (cdr abs-file-alist1)))))
     (cons (car abs-file-alist1)
           (abs-addrs (remove-assoc-equal name (cdr abs-file-alist1)))))))
  :hints
  (("goal"
    :in-theory (e/d (intersectp-equal)
                    (intersectp-is-commutative))
    :expand
    (:with
     intersectp-is-commutative
     (intersectp-equal
      (abs-addrs
       (abs-file->contents (cdr (assoc-equal name (cdr abs-file-alist1)))))
      (cons (car abs-file-alist1)
            (abs-addrs (remove-assoc-equal name (cdr abs-file-alist1)))))))))

(defthm
  abs-addrs-of-abs-context-apply-2-lemma-14
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
        (no-duplicatesp-equal (abs-addrs abs-file-alist1))
        (abs-no-dups-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist1))
   (not
    (intersectp-equal
     (abs-addrs
      (abs-file->contents$inline (cdr (assoc-equal name abs-file-alist1))))
     (abs-addrs (remove-assoc-equal name abs-file-alist1)))))
  :hints (("goal" :in-theory (e/d (abs-addrs) nil)
           :expand ((abs-no-dups-p abs-file-alist1)
                    (abs-file-alist-p abs-file-alist1)))))

(defthm
  abs-addrs-of-abs-context-apply-2-lemma-15
  (implies
   (not (intersectp-equal (abs-addrs abs-file-alist1)
                          (abs-addrs abs-file-alist2)))
   (not
    (intersectp-equal (abs-addrs abs-file-alist2)
                      (abs-addrs (remove-assoc-equal name abs-file-alist1)))))
  :hints
  (("goal"
    :use (:instance (:rewrite intersect-with-subset)
                    (z (abs-addrs abs-file-alist2))
                    (x (abs-addrs (remove-assoc-equal name abs-file-alist1)))
                    (y (abs-addrs abs-file-alist1))))))

(defthm
  abs-addrs-of-abs-context-apply-2-lemma-16
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal (car x-path)
                                                abs-file-alist1)))
        (no-duplicatesp-equal (abs-addrs abs-file-alist1))
        (not (intersectp-equal (abs-addrs abs-file-alist1)
                               (abs-addrs abs-file-alist2)))
        (abs-no-dups-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2))
   (not
    (intersectp-equal
     (abs-addrs (remove-assoc-equal (car x-path)
                                    abs-file-alist1))
     (abs-addrs
      (abs-context-apply
       (abs-file->contents$inline (cdr (assoc-equal (car x-path)
                                                    abs-file-alist1)))
       abs-file-alist2 x (cdr x-path))))))
  :hints
  (("goal"
    :in-theory (disable intersectp-is-commutative)
    :do-not-induct t
    :expand
    (:with
     intersectp-is-commutative
     (intersectp-equal
      (abs-addrs (remove-assoc-equal (car x-path)
                                     abs-file-alist1))
      (abs-addrs
       (abs-context-apply
        (abs-file->contents$inline (cdr (assoc-equal (car x-path)
                                                     abs-file-alist1)))
        abs-file-alist2 x (cdr x-path))))))))

(defthm
  abs-addrs-of-abs-context-apply-2
  (implies (and (no-duplicatesp-equal (abs-addrs abs-file-alist1))
                (not (intersectp-equal (abs-addrs abs-file-alist1)
                                       (abs-addrs abs-file-alist2)))
                (abs-no-dups-p abs-file-alist1)
                (abs-file-alist-p abs-file-alist1)
                (abs-file-alist-p abs-file-alist2)
                (no-duplicatesp-equal (abs-addrs abs-file-alist2)))
           (no-duplicatesp-equal
            (abs-addrs (abs-context-apply abs-file-alist1
                                          abs-file-alist2 x x-path))))
  :hints (("goal" :in-theory (enable abs-addrs abs-context-apply)
           :induct (abs-context-apply abs-file-alist1
                                      abs-file-alist2 x x-path))))

(defund
  abs-file-alist-fix (x)
  (declare
   (xargs
    :guard (abs-file-alist-p x)
    :guard-hints (("goal" :expand (abs-file-alist-p x)
                   :in-theory (enable abs-file-p)))))
  (b* (((when (atom x)) nil)
       (head (car x))
       ((when (atom head))
        (cons (nfix head)
              (abs-file-alist-fix (cdr x)))))
    (cons (cons (fat32-filename-fix (car head))
                (abs-file-fix (cdr head)))
          (abs-file-alist-fix (cdr x)))))

(encapsulate
  () ;; start lemmas for abs-file-alist-fix-when-abs-file-alist-p

  (local
   (defthm abs-file-alist-fix-when-abs-file-alist-p-lemma-1
     (implies (and (alistp (cddr (car x)))
                   (equal (car (cadr (car x))) 'dir-ent)
                   (equal (strip-cars (cddr (car x)))
                          '(contents))
                   (dir-ent-p (cdr (cadr (car x))))
                   (stringp (cdr (caddr (car x))))
                   (< (len (explode (cdr (caddr (car x)))))
                      4294967296))
              (abs-file-p (cdr (car x))))
     :hints (("goal" :in-theory (enable abs-file-p)))))

  (local
   (defthm abs-file-alist-fix-when-abs-file-alist-p-lemma-2
     (implies (and (alistp (cddr (car x)))
                   (equal (car (cadr (car x))) 'dir-ent)
                   (equal (strip-cars (cddr (car x)))
                          '(contents))
                   (dir-ent-p (cdr (cadr (car x))))
                   (abs-file-alist-p (cdr (caddr (car x)))))
              (abs-file-p (cdr (car x))))
     :hints (("goal" :in-theory (enable abs-file-p)))))

  (defthm
    abs-file-alist-fix-when-abs-file-alist-p
    (implies (abs-file-alist-p x)
             (equal (abs-file-alist-fix x) x))
    :hints (("goal" :in-theory (enable abs-file-alist-fix abs-file-alist-p)))))

(defthm
  abs-file-alist-p-of-abs-file-alist-fix
  (abs-file-alist-p (abs-file-alist-fix x))
  :hints (("goal" :in-theory (enable abs-file-alist-fix abs-file-alist-p
                                     abs-file-fix abs-file-contents-fix
                                     abs-file-contents-p))))

(fty::deffixtype abs-file-alist
                 :pred abs-file-alist-p
                 :fix abs-file-alist-fix
                 :equiv abs-file-alist-equiv
                 :define t
                 :forward t)

;; Both these names, below, merit some thought later...
(fty::defprod frame-val
              ((path fat32-filename-list-p)
               (dir abs-file-alist-p)
               (src natp)))

(fty::defalist frame
               :key-type nat
               :val-type frame-val)

;; That this lemma is needed is a reminder to get some list macros around
;; abs-file-alist-p...
(defthm
  unlink-abs-alloc-helper-1-guard-lemma-1
  (implies
   (and (integerp index)
        (<= 0 index)
        (abs-directory-file-p (cdr (assoc-equal path1 fs))))
   (abs-file-contents-p
    (cons
     index
     (remove-assoc-equal (car path2)
                         (abs-file->contents (cdr (assoc-equal path1 fs)))))))
  :hints (("goal" :in-theory (enable abs-file-contents-p abs-file-alist-p)
           :do-not-induct t)))

;; It's going to be incredibly hard to implement the thing which this helper
;; function is a part of, because in general when we're looking up a file we'll
;; have to go down many, many rabbit holes. We might want to look up
;; /usr/bin/busybox in an instrumented filesystem where /usr has 4 abstract
;; addresses in it, and one of them has /usr/bin, and that one has 8 abstract
;; addresses in it, and finally it turns out none of the 8 has busybox in
;; it. We'd have to process abstract addresses through a queue into which we
;; keep adding them, accompanied by relative paths, as we find ourselves
;; stymied and over and over again while looking for a file. It pretty much
;; goes without saying that reasoning about abstract allocations and
;; deallocations would get very hard. It might be possible to reason about
;; single steps of allocation and deallocation - respectively taking a
;; substructure out of a directory we know to exist and putting it back where
;; we know no duplicates to exist - but it's still going to be hard.
;;
;; Return 4 values - the abs-file-alist, potentially changed; the list of
;; abstract addresses to look into, potentially empty; the substructure we
;; pulled out, potentially the default abs-file-alist; and the path from where
;; the substructure was pulled out, potentially empty.
(defund
  unlink-abs-alloc-helper-1 (fs path index)
  (declare (xargs :guard (and (abs-file-alist-p fs)
                              (fat32-filename-list-p path)
                              (natp index))
                  :measure (len path)
                  :guard-debug t))
  (b*
      (;; This is an error condition.
       ((when (atom path)) (mv fs nil nil *empty-fat32-name*))
       (head (mbe :exec (car path)
                  :logic (fat32-filename-fix (car path))))
       ((when (atom (abs-assoc head fs)))
        (mv fs (abs-top-addrs fs) nil head))
       ((when (atom (cdr path)))
        (mv (list* (mbe :exec index :logic (nfix index))
                   (abs-remove-assoc head fs))
            nil (list (abs-assoc head fs))
            head))
       ;; This is an error condition.
       ((unless (abs-directory-file-p (cdr (abs-assoc head fs))))
        (mv fs nil nil *empty-fat32-name*))
       ((mv insert addr-list sub-fs final-head)
        (unlink-abs-alloc-helper-1
         (abs-file->contents (cdr (abs-assoc head fs)))
         (cdr path)
         index)))
    (mv
     (abs-put-assoc
      head
      (abs-file (abs-file->dir-ent (cdr (abs-assoc head fs)))
                insert)
      fs)
     addr-list sub-fs final-head)))

(defthm
  unlink-abs-alloc-helper-1-correctness-1-lemma-1
  (implies
   (and (abs-file-alist-p abs-file-alist)
        (integerp index)
        (<= 0 index))
   (abs-file-alist-p (cons index
                           (remove-assoc-equal (fat32-filename-fix (car path))
                                               abs-file-alist))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-file-alist-p))))

(defthm
  unlink-abs-alloc-helper-1-correctness-1
  (implies (abs-file-alist-p abs-file-alist)
           (abs-file-alist-p
            (mv-nth 0
                    (unlink-abs-alloc-helper-1 abs-file-alist path index))))
  :hints (("goal" :in-theory (enable unlink-abs-alloc-helper-1))))

(assert-event
 (frame-p
  (list
   (cons
    0
    (frame-val
     nil
     (list
      (cons
       "INITRD  IMG"
       (abs-file (dir-ent-fix nil) ""))
      (cons
       "RUN        "
       (abs-file
        (dir-ent-fix nil)
        (list
         (cons
          "RSYSLOGDPID"
          (abs-file (dir-ent-fix nil) "")))))
      (cons
       "USR        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (dir-ent-fix nil) ()))
                  (cons
                   "LIB        "
                   (abs-file (dir-ent-fix nil) ()))
                  1))))
     0))
   (cons
    1
    (frame-val
     (list "USR        ")
     (list
      (cons
       "SHARE      "
       (abs-file (dir-ent-fix nil) ()))
      (cons
       "BIN        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "CAT        "
                   (abs-file (dir-ent-fix nil) ""))
                  2
                  (cons
                   "TAC        "
                   (abs-file (dir-ent-fix nil) ""))))))
     0))
   (cons
    2
    (frame-val
     (list "USR        " "BIN        ")
     (list
      (cons
       "COL        "
       (abs-file (dir-ent-fix nil) "")))
     1)))))

(assert-event
 (mv-let
   (fs addr-list sub-fs final-head)
   (unlink-abs-alloc-helper-1
    (list
     (cons
      "INITRD  IMG"
      (abs-file (dir-ent-fix nil) ""))
     (cons
      "RUN        "
      (abs-file
       (dir-ent-fix nil)
       (list
        (cons
         "RSYSLOGDPID"
         (abs-file (dir-ent-fix nil) "")))))
     (cons
      "USR        "
      (abs-file (dir-ent-fix nil)
                (list
                 (cons
                  "LOCAL      "
                  (abs-file (dir-ent-fix nil) ()))
                 (cons
                  "LIB        "
                  (abs-file (dir-ent-fix nil) ()))
                 1))))
    (list "INITRD  IMG")
    3)
   (and
    (equal
     fs
     (list
      3
      (cons
       "RUN        "
       (abs-file
        (dir-ent-fix nil)
        (list
         (cons
          "RSYSLOGDPID"
          (abs-file (dir-ent-fix nil) "")))))
      (cons
       "USR        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (dir-ent-fix nil) ()))
                  (cons
                   "LIB        "
                   (abs-file (dir-ent-fix nil) ()))
                  1)))))
    (equal
     addr-list
     nil)
    (equal
     sub-fs
     (list
      (cons
       "INITRD  IMG"
       (abs-file (dir-ent-fix nil) ""))))
    (equal
     final-head
     "INITRD  IMG"))))

(assert-event
 (mv-let
   (fs addr-list sub-fs final-head)
   (unlink-abs-alloc-helper-1
    (list
     (cons
      "INITRD  IMG"
      (abs-file (dir-ent-fix nil) ""))
     (cons
      "RUN        "
      (abs-file
       (dir-ent-fix nil)
       (list
        (cons
         "RSYSLOGDPID"
         (abs-file (dir-ent-fix nil) "")))))
     (cons
      "USR        "
      (abs-file (dir-ent-fix nil)
                (list
                 (cons
                  "LOCAL      "
                  (abs-file (dir-ent-fix nil) ()))
                 (cons
                  "LIB        "
                  (abs-file (dir-ent-fix nil) ()))
                 1))))
    (list "RUN        " "RSYSLOGDPID")
    3)
   (and
    (equal
     fs
     (list
      (cons
       "INITRD  IMG"
       (abs-file (dir-ent-fix nil) ""))
      (cons
       "RUN        "
       (abs-file
        (dir-ent-fix nil)
        (list
         3)))
      (cons
       "USR        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (dir-ent-fix nil) ()))
                  (cons
                   "LIB        "
                   (abs-file (dir-ent-fix nil) ()))
                  1)))))
    (equal
     addr-list
     nil)
    (equal
     sub-fs
     (list
      (cons
       "RSYSLOGDPID"
       (abs-file (dir-ent-fix nil) ""))))
    (equal
     final-head
     "RSYSLOGDPID"))))

(assert-event
 (mv-let
   (fs addr-list sub-fs final-head)
   (unlink-abs-alloc-helper-1
    (list
     (cons
      "INITRD  IMG"
      (abs-file (dir-ent-fix nil) ""))
     (cons
      "RUN        "
      (abs-file
       (dir-ent-fix nil)
       (list
        (cons
         "RSYSLOGDPID"
         (abs-file (dir-ent-fix nil) "")))))
     (cons
      "USR        "
      (abs-file (dir-ent-fix nil)
                (list
                 (cons
                  "LOCAL      "
                  (abs-file (dir-ent-fix nil) ()))
                 (cons
                  "LIB        "
                  (abs-file (dir-ent-fix nil) ()))
                 1))))
    (list "USR        " "BIN        " "COL        ")
    3)
   (and
    (equal
     fs
     (list
      (cons
       "INITRD  IMG"
       (abs-file (dir-ent-fix nil) ""))
      (cons
       "RUN        "
       (abs-file
        (dir-ent-fix nil)
        (list
         (cons
          "RSYSLOGDPID"
          (abs-file (dir-ent-fix nil) "")))))
      (cons
       "USR        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (dir-ent-fix nil) ()))
                  (cons
                   "LIB        "
                   (abs-file (dir-ent-fix nil) ()))
                  1)))))
    (equal
     addr-list
     (list 1))
    (equal
     sub-fs
     nil)
    (equal
     final-head
     "BIN        "))))

;; Let's simplify this. We will have some prefix reasoning - that's pretty much
;; unavoidable. Still, we aren't going to claim that we're starting from the
;; root directory (i.e. \mathcal{F}) and following the precise sequence of
;; paths which will lead us to the file we want at the path we want. That will
;; require a queue, which is messy... Instead, we're going to look through
;; all the elements in the frame until we have ruled out the existence of an
;; abstract variable which has this file in it.
(defund
  stat-abs-lookup (frame path)
  (declare (xargs :guard (and (frame-p frame)
                              (fat32-filename-list-p path))
                  :guard-debug t))
  (b*
      (((when (atom frame)) nil)
       (head-frame-val (cdr (car frame)))
       ((when
         (and
          (equal (frame-val->path head-frame-val)
                 (butlast path 1))
          (consp
           (abs-assoc (car (last path))
                      (frame-val->dir head-frame-val)))))
        t))
    (stat-abs-lookup (cdr frame) path)))

(assert-event
 (equal
  (stat-abs-lookup
   (list
    (cons
     0
     (frame-val
      nil
      (list
       (cons
        "INITRD  IMG"
        (abs-file (dir-ent-fix nil) ""))
       (cons
        "RUN        "
        (abs-file
         (dir-ent-fix nil)
         (list
          (cons
           "RSYSLOGDPID"
           (abs-file (dir-ent-fix nil) "")))))
       (cons
        "USR        "
        (abs-file (dir-ent-fix nil)
                  (list
                   (cons
                    "LOCAL      "
                    (abs-file (dir-ent-fix nil) ()))
                   (cons
                    "LIB        "
                    (abs-file (dir-ent-fix nil) ()))
                   1))))
      0))
    (cons
     1
     (frame-val
      (list "USR        ")
      (list
       (cons
        "SHARE      "
        (abs-file (dir-ent-fix nil) ()))
       (cons
        "BIN        "
        (abs-file (dir-ent-fix nil)
                  (list
                   (cons
                    "CAT        "
                    (abs-file (dir-ent-fix nil) ""))
                   2
                   (cons
                    "TAC        "
                    (abs-file (dir-ent-fix nil) ""))))))
      0))
    (cons
     2
     (frame-val
      (list "USR        " "BIN        ")
      (list
       (cons
        "COL        "
        (abs-file (dir-ent-fix nil) "")))
      1)))
   (list "INITRD  IMG"))
  t))

(assert-event
 (equal
  (stat-abs-lookup
   (list
    (cons
     0
     (frame-val
      nil
      (list
       (cons
        "INITRD  IMG"
        (abs-file (dir-ent-fix nil) ""))
       (cons
        "RUN        "
        (abs-file
         (dir-ent-fix nil)
         (list
          (cons
           "RSYSLOGDPID"
           (abs-file (dir-ent-fix nil) "")))))
       (cons
        "USR        "
        (abs-file (dir-ent-fix nil)
                  (list
                   (cons
                    "LOCAL      "
                    (abs-file (dir-ent-fix nil) ()))
                   (cons
                    "LIB        "
                    (abs-file (dir-ent-fix nil) ()))
                   1))))
      0))
    (cons
     1
     (frame-val
      (list "USR        ")
      (list
       (cons
        "SHARE      "
        (abs-file (dir-ent-fix nil) ()))
       (cons
        "BIN        "
        (abs-file (dir-ent-fix nil)
                  (list
                   (cons
                    "CAT        "
                    (abs-file (dir-ent-fix nil) ""))
                   2
                   (cons
                    "TAC        "
                    (abs-file (dir-ent-fix nil) ""))))))
      0))
    (cons
     2
     (frame-val
      (list "USR        " "BIN        ")
      (list
       (cons
        "COL        "
        (abs-file (dir-ent-fix nil) "")))
      1)))
   (list "USR        " "BIN        " "COL        "))
  t))

(assert-event
 (equal
  (stat-abs-lookup
   (list
    (cons
     0
     (frame-val
      nil
      (list
       (cons
        "INITRD  IMG"
        (abs-file (dir-ent-fix nil) ""))
       (cons
        "RUN        "
        (abs-file
         (dir-ent-fix nil)
         (list
          (cons
           "RSYSLOGDPID"
           (abs-file (dir-ent-fix nil) "")))))
       (cons
        "USR        "
        (abs-file (dir-ent-fix nil)
                  (list
                   (cons
                    "LOCAL      "
                    (abs-file (dir-ent-fix nil) ()))
                   (cons
                    "LIB        "
                    (abs-file (dir-ent-fix nil) ()))
                   1))))
      0))
    (cons
     1
     (frame-val
      (list "USR        ")
      (list
       (cons
        "SHARE      "
        (abs-file (dir-ent-fix nil) ()))
       (cons
        "BIN        "
        (abs-file (dir-ent-fix nil)
                  (list
                   (cons
                    "CAT        "
                    (abs-file (dir-ent-fix nil) ""))
                   2
                   (cons
                    "TAC        "
                    (abs-file (dir-ent-fix nil) ""))))))
      0))
    (cons
     2
     (frame-val
      (list "USR        " "BIN        ")
      (list
       (cons
        "COL        "
        (abs-file (dir-ent-fix nil) "")))
      1)))
   (list "USR        " "BIN        " "FIREFOX    "))
  nil))

;; We didn't include it in the guard, but... 0 should not be among the indices.
(defund abs-find-first-complete (frame)
  (declare (xargs :guard (frame-p frame)))
  (b* (((when (atom frame)) 0)
       (head-index (caar frame))
       (head-frame-val (cdar frame)))
    (if (abs-complete (frame-val->dir head-frame-val))
        (mbe :exec head-index :logic (nfix head-index))
        (abs-find-first-complete (cdr frame)))))

(defthm abs-find-first-complete-correctness-1
  (implies (not (zp (abs-find-first-complete frame)))
           (consp (assoc-equal (abs-find-first-complete frame)
                               frame)))
  :hints (("goal" :in-theory (enable abs-find-first-complete)))
  :rule-classes :type-prescription)

(defthm natp-of-abs-find-first-complete
  (natp (abs-find-first-complete frame))
  :hints (("goal" :in-theory (enable abs-find-first-complete)))
  :rule-classes :type-prescription)

(defthm frame-val-p-of-cdr-of-assoc-equal-when-frame-p
  (implies (frame-p x)
           (iff (frame-val-p (cdr (assoc-equal k x)))
                (or (consp (assoc-equal k x))
                    (frame-val-p nil))))
  :hints (("goal" :in-theory (enable frame-p))))

(defthm frame-p-of-put-assoc-equal
  (implies (frame-p alist)
           (equal (frame-p (put-assoc-equal name val alist))
                  (and (natp name) (frame-val-p val))))
  :hints (("goal" :in-theory (enable frame-p))))

(defthm frame-p-of-remove-assoc-equal
  (implies (frame-p alist)
           (frame-p (remove-assoc-equal x alist)))
  :hints (("goal" :in-theory (enable frame-p))))

(defund abs-collapse (root frame)
  (declare (xargs :guard (and (abs-file-alist-p root) (frame-p frame))
                  :guard-debug t :measure (len frame)))
  (b*
      (((when (atom frame)) (mv root t))
       (head-index (abs-find-first-complete frame))
       ((when (zp head-index)) (mv root nil))
       (head-frame-val (cdr (abs-assoc head-index frame)))
       (frame (abs-remove-assoc head-index frame))
       (src (frame-val->src head-frame-val)))
    (if
        (zp src)
        (b*
            ((root-after-context-apply
              (abs-context-apply
               root
               (frame-val->dir head-frame-val)
               head-index
               (frame-val->path head-frame-val)))
             ((when (equal root-after-context-apply root)) (mv root nil)))
          (abs-collapse root-after-context-apply frame))
      (b*
          ((path (frame-val->path head-frame-val))
           ((when (or (equal src head-index)
                      (atom (abs-assoc src frame))))
            (mv root nil))
           (src-path (frame-val->path (cdr (abs-assoc src frame))))
           ((when (not (prefixp src-path path)))
            (mv root nil))
           (src-dir (frame-val->dir (cdr (abs-assoc src frame))))
           (src-dir-after-context-apply
            (abs-context-apply
             src-dir
             (frame-val->dir head-frame-val)
             head-index
             (nthcdr (len src-path) path)))
           ((when (equal src-dir-after-context-apply src-dir)) (mv root nil))
           (frame (abs-put-assoc
                   src
                   (frame-val
                    (frame-val->path (cdr (abs-assoc src frame)))
                    src-dir-after-context-apply
                    (frame-val->src (cdr (abs-assoc src frame))))
                   frame)))
        (abs-collapse root frame)))))

(assert-event
 (b*
     (((mv root result)
       (abs-collapse
        (list
         (cons
          "INITRD  IMG"
          (abs-file (dir-ent-fix nil) ""))
         (cons
          "RUN        "
          (abs-file
           (dir-ent-fix nil)
           (list
            (cons
             "RSYSLOGDPID"
             (abs-file (dir-ent-fix nil) "")))))
         (cons
          "USR        "
          (abs-file (dir-ent-fix nil)
                    (list
                     (cons
                      "LOCAL      "
                      (abs-file (dir-ent-fix nil) ()))
                     (cons
                      "LIB        "
                      (abs-file (dir-ent-fix nil) ()))
                     1))))
        (list
         (cons
          1
          (frame-val
           (list "USR        ")
           (list
            (cons
             "SHARE      "
             (abs-file (dir-ent-fix nil) ()))
            (cons
             "BIN        "
             (abs-file (dir-ent-fix nil)
                       (list
                        (cons
                         "CAT        "
                         (abs-file (dir-ent-fix nil) ""))
                        2
                        (cons
                         "TAC        "
                         (abs-file (dir-ent-fix nil) ""))))))
           0))
         (cons
          2
          (frame-val
           (list "USR        " "BIN        ")
           (list
            (cons
             "COL        "
             (abs-file (dir-ent-fix nil) "")))
           1))))))
   (and
    (equal
     root
     (list
      (cons
       "INITRD  IMG"
       (abs-file (dir-ent-fix nil) ""))
      (cons
       "RUN        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "RSYSLOGDPID"
                   (abs-file (dir-ent-fix nil) "")))))
      (cons
       "USR        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (dir-ent-fix nil) nil))
                  (cons
                   "LIB        "
                   (abs-file (dir-ent-fix nil) nil))
                  (cons
                   "SHARE      "
                   (abs-file (dir-ent-fix nil) nil))
                  (cons
                   "BIN        "
                   (abs-file (dir-ent-fix nil)
                             (list
                              (cons
                               "CAT        "
                               (abs-file (dir-ent-fix nil) ""))
                              (cons
                               "TAC        "
                               (abs-file (dir-ent-fix nil) ""))
                              (cons
                               "COL        "
                               (abs-file (dir-ent-fix nil) ""))))))))))
    (equal result t))))

(assert-event
 (equal
  (abs-no-dups-p
   (list
    (cons
     "INITRD  IMG"
     (abs-file (dir-ent-fix nil) ""))
    (cons
     "RUN        "
     (abs-file
      (dir-ent-fix nil)
      (list
       (cons
        "RSYSLOGDPID"
        (abs-file (dir-ent-fix nil) "")))))
    (cons
     "USR        "
     (abs-file (dir-ent-fix nil)
               (list
                1
                (cons
                 "LIB        "
                 (abs-file (dir-ent-fix nil) ()))
                1)))))
  nil))

(assert-event
 (equal
  (abs-no-dups-p
   (list
    (cons
     "INITRD  IMG"
     (abs-file (dir-ent-fix nil) ""))
    (cons
     "RUN        "
     (abs-file
      (dir-ent-fix nil)
      (list
       (cons
        "RSYSLOGDPID"
        (abs-file (dir-ent-fix nil) "")))))
    (cons
     "USR        "
     (abs-file (dir-ent-fix nil)
               (list
                (cons
                 "LIB        "
                 (abs-file (dir-ent-fix nil) ()))
                1
                (cons
                 "LIB        "
                 (abs-file (dir-ent-fix nil) ())))))))
  nil))

(assert-event
 (equal
  (abs-no-dups-p
   (list
    (cons
     "INITRD  IMG"
     (abs-file (dir-ent-fix nil) ""))
    (cons
     "RUN        "
     (abs-file
      (dir-ent-fix nil)
      (list
       (cons
        "RSYSLOGDPID"
        (abs-file (dir-ent-fix nil) "")))))
    (cons
     "USR        "
     (abs-file (dir-ent-fix nil)
               (list
                (cons
                 "LIB        "
                 (abs-file (dir-ent-fix nil) ()))
                1)))))
  t))

(defthm
  abs-no-dups-p-when-m1-file-alist-p
  (implies (m1-file-alist-p fs)
           (equal (abs-no-dups-p fs)
                  (hifat-no-dups-p fs)))
  :hints (("goal" :induct (abs-no-dups-p fs)
           :in-theory (enable abs-no-dups-p abs-directory-file-p
                              m1-directory-file-p abs-file->contents
                              m1-file->contents abs-file-p)
           :expand ((hifat-no-dups-p fs)
                    (m1-file-alist-p fs)))))

(defund abs-top-names (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        ((atom (car x)) (abs-top-names (cdr x)))
        ((equal (caar x) nil) (abs-top-names (cdr x)))
        (t (cons (car (car x))
                 (abs-top-names (cdr x))))))

(defthm abs-top-names-definition
  (equal (abs-top-names x)
         (remove nil (strip-cars x)))
  :rule-classes :definition
  :hints (("goal" :in-theory (enable abs-top-names))))

(defund
  names-at-relpath (fs relpath)
  (declare (xargs :guard (and (abs-file-alist-p fs)
                              (fat32-filename-list-p relpath))
                  :guard-debug t))
  (b*
      (((when (atom relpath))
        (abs-top-names fs))
       (head (car relpath))
       ((unless
         (and (consp (abs-assoc head fs))
              (abs-directory-file-p (cdr (abs-assoc head fs)))))
        nil))
    (names-at-relpath
     (abs-file->contents (cdr (abs-assoc head fs)))
     (cdr relpath))))

(defund
  abs-separate (frame)
  (declare (xargs :guard (frame-p frame)))
  (or
   (atom frame)
   (and
    (abs-no-dups-p (frame-val->dir (cdar frame)))
    (no-duplicatesp-equal
     (names-at-relpath-across-frame (cdr frame) (frame-val->path (cdar frame))))
    (abs-separate (cdr frame)))))

;; This is a "false" frame because the src value given to the root is 0, same
;; as its abstract variable. This is one of a few compromises in elegance
;; required for distinguishing the root, which is necessary to properly define
;; the collapse relation.
(defund pseudo-frame (root frame)
  (declare (xargs :guard (and (abs-file-alist-p root)
                              (frame-p frame))))
  (list* (cons 0 (frame-val nil root 0))
         frame))

;; This is because of fixing.
(defthm frame-p-of-pseudo-frame
  (equal (frame-p (pseudo-frame root frame))
         (frame-p frame))
  :hints (("goal" :in-theory (enable pseudo-frame))))

(defthm abs-separate-correctness-1-lemma-1
  (implies (and (abs-file-alist-p root)
                (not (consp (abs-addrs root)))
                (abs-separate (pseudo-frame root frame)))
           (hifat-no-dups-p root))
  :hints (("goal" :in-theory (enable pseudo-frame abs-separate
                                     names-at-relpath-across-frame))))

;; Move later
(defthm strip-cars-of-remove-assoc
  (equal (strip-cars (remove-assoc-equal x alist))
         (remove-equal x (strip-cars alist))))
(defthm strip-cars-of-put-assoc
  (implies (consp (assoc-equal name alist))
           (equal (strip-cars (put-assoc-equal name val alist))
                  (strip-cars alist))))

(defthm
  abs-separate-correctness-1-lemma-2
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (abs-file-alist-p abs-file-alist2)
    (subsetp-equal
     (abs-addrs abs-file-alist2)
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name abs-file-alist1))))))
   (subsetp-equal
    (abs-addrs (put-assoc-equal name (abs-file dir-ent abs-file-alist2)
                                abs-file-alist1))
    (abs-addrs abs-file-alist1)))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-separate-correctness-1-lemma-3
  (implies
   (and (abs-file-alist-p abs-file-alist2)
        (atom (abs-addrs abs-file-alist2)))
   (subsetp-equal (abs-addrs (abs-context-apply abs-file-alist1
                                                abs-file-alist2 x x-path))
                  (abs-addrs abs-file-alist1)))
  :hints (("goal" :in-theory (enable abs-context-apply))))

;; Move later
(defthm member-of-strip-cars
  (implies (consp (assoc-equal x alist))
           (member-equal x (strip-cars alist))))

(defthm abs-separate-correctness-1-lemma-4
  (implies (and (frame-p frame)
                (not (zp (abs-find-first-complete frame)))
                (no-duplicatesp-equal (strip-cars frame)))
           (equal (abs-addrs (frame-val->dir (cdr (assoc-equal
                                                   (abs-find-first-complete frame) frame))))
                  nil))
  :hints (("Goal" :in-theory (enable abs-find-first-complete)) ))

(defthm
  abs-separate-correctness-1-lemma-5
  (implies (and (no-duplicatesp-equal (strip-cars frame))
                (frame-p frame))
           (subsetp-equal (abs-addrs (mv-nth 0 (abs-collapse root frame)))
                          (abs-addrs root)))
  :hints (("goal" :in-theory (enable abs-collapse))))

;; Move later
(defthm remove-when-absent
  (implies (not (member-equal x l))
           (equal (remove-equal x l)
                  (true-list-fix l))))

;; Move later
(defthmd intersectp-when-member
  (implies (member-equal x l)
           (iff (intersectp-equal l y)
                (or (intersectp-equal (remove-equal x l) y)
                    (member-equal x y))))
  :hints (("goal" :in-theory (e/d (intersectp-equal)
                                  (intersectp-is-commutative)))))

(defthm
  abs-separate-correctness-1-lemma-6
  (implies
   (and
    (< 0 (abs-find-first-complete frame))
    (not
     (equal
      (abs-context-apply
       root
       (frame-val->dir (cdr (assoc-equal (abs-find-first-complete frame)
                                         frame)))
       (abs-find-first-complete frame)
       (frame-val->path (cdr (assoc-equal (abs-find-first-complete frame)
                                          frame))))
      root))
    (abs-file-alist-p root)
    (abs-no-dups-p root)
    (frame-p frame)
    (no-duplicatesp-equal (abs-addrs root))
    (no-duplicatesp-equal (strip-cars frame)))
   (not
    (member-equal
     (abs-find-first-complete frame)
     (abs-addrs
      (mv-nth
       0
       (abs-collapse
        (abs-context-apply
         root
         (frame-val->dir (cdr (assoc-equal (abs-find-first-complete frame)
                                           frame)))
         (abs-find-first-complete frame)
         (frame-val->path (cdr (assoc-equal (abs-find-first-complete frame)
                                            frame))))
        (remove-assoc-equal (abs-find-first-complete frame)
                            frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (intersectp-equal)
                    (subsetp-member))
    :use
    (:instance
     (:rewrite subsetp-member . 4)
     (y
      (abs-addrs
       (abs-context-apply
        root
        (frame-val->dir (cdr (assoc-equal (abs-find-first-complete frame)
                                          frame)))
        (abs-find-first-complete frame)
        (frame-val->path (cdr (assoc-equal (abs-find-first-complete frame)
                                           frame))))))
     (x
      (abs-addrs
       (mv-nth
        0
        (abs-collapse
         (abs-context-apply
          root
          (frame-val->dir (cdr (assoc-equal (abs-find-first-complete frame)
                                            frame)))
          (abs-find-first-complete frame)
          (frame-val->path (cdr (assoc-equal (abs-find-first-complete frame)
                                             frame))))
         (remove-assoc-equal (abs-find-first-complete frame)
                             frame)))))
     (a (abs-find-first-complete frame))))))

(defthm
  abs-separate-correctness-1-lemma-7
  (implies
   (and
    (< 0 (abs-find-first-complete frame))
    (not
     (equal
      (abs-context-apply
       root
       (frame-val->dir (cdr (assoc-equal (abs-find-first-complete frame)
                                         frame)))
       (abs-find-first-complete frame)
       (frame-val->path (cdr (assoc-equal (abs-find-first-complete frame)
                                          frame))))
      root))
    (not
     (intersectp-equal
      (remove-equal (abs-find-first-complete frame)
                    (strip-cars frame))
      (abs-addrs
       (mv-nth
        0
        (abs-collapse
         (abs-context-apply
          root
          (frame-val->dir (cdr (assoc-equal (abs-find-first-complete frame)
                                            frame)))
          (abs-find-first-complete frame)
          (frame-val->path (cdr (assoc-equal (abs-find-first-complete frame)
                                             frame))))
         (remove-assoc-equal (abs-find-first-complete frame)
                             frame))))))
    (abs-file-alist-p root)
    (abs-no-dups-p root)
    (frame-p frame)
    (no-duplicatesp-equal (abs-addrs root))
    (no-duplicatesp-equal (strip-cars frame)))
   (not
    (intersectp-equal
     (strip-cars frame)
     (abs-addrs
      (mv-nth
       0
       (abs-collapse
        (abs-context-apply
         root
         (frame-val->dir (cdr (assoc-equal (abs-find-first-complete frame)
                                           frame)))
         (abs-find-first-complete frame)
         (frame-val->path (cdr (assoc-equal (abs-find-first-complete frame)
                                            frame))))
        (remove-assoc-equal (abs-find-first-complete frame)
                            frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance
     (:rewrite intersectp-when-member)
     (x (abs-find-first-complete frame))
     (y
      (abs-addrs
       (mv-nth
        0
        (abs-collapse
         (abs-context-apply
          root
          (frame-val->dir (cdr (assoc-equal (abs-find-first-complete frame)
                                            frame)))
          (abs-find-first-complete frame)
          (frame-val->path (cdr (assoc-equal (abs-find-first-complete frame)
                                             frame))))
         (remove-assoc-equal (abs-find-first-complete frame)
                             frame)))))
     (l (strip-cars frame))))))

;; This has a free variable... which merits examination later.
(defthm abs-separate-correctness-1-lemma-8
  (implies (and (abs-file-alist-p root)
                (abs-separate (pseudo-frame root frame)))
           (abs-no-dups-p root))
  :hints (("goal" :in-theory (enable abs-separate pseudo-frame))))

(thm
 (IMPLIES
  (AND
   (CONSP FRAME)
   (< 0 (ABS-FIND-FIRST-COMPLETE FRAME))
   (< 0
      (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                        FRAME))))
   (NOT
    (EQUAL (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                             FRAME)))
           (ABS-FIND-FIRST-COMPLETE FRAME)))
   (CONSP
    (ASSOC-EQUAL
     (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                       FRAME)))
     FRAME))
   (PREFIXP
    (FRAME-VAL->PATH
     (CDR
      (ASSOC-EQUAL
       (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                         FRAME)))
       FRAME)))
    (FRAME-VAL->PATH (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                       FRAME))))
   (NOT
    (EQUAL
     (ABS-CONTEXT-APPLY
      (FRAME-VAL->DIR
       (CDR
        (ASSOC-EQUAL
         (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                           FRAME)))
         FRAME)))
      (FRAME-VAL->DIR (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                        FRAME)))
      (ABS-FIND-FIRST-COMPLETE FRAME)
      (NTHCDR
       (LEN
        (FRAME-VAL->PATH
         (CDR
          (ASSOC-EQUAL
           (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                             FRAME)))
           FRAME))))
       (FRAME-VAL->PATH (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                          FRAME)))))
     (FRAME-VAL->DIR
      (CDR
       (ASSOC-EQUAL
        (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                          FRAME)))
        FRAME)))))
   (FRAME-P FRAME)
   (NO-DUPLICATESP-EQUAL (STRIP-CARS FRAME))
   (ABS-FILE-ALIST-P ROOT)
   (NO-DUPLICATESP-EQUAL (ABS-ADDRS ROOT))
   (SUBSETP-EQUAL (ABS-ADDRS ROOT)
                  (STRIP-CARS FRAME))
   (ABS-SEPARATE (PSEUDO-FRAME ROOT FRAME))
   (EQUAL
    (MV-NTH
     1
     (ABS-COLLAPSE
      ROOT
      (PUT-ASSOC-EQUAL
       (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                         FRAME)))
       (FRAME-VAL
        (FRAME-VAL->PATH
         (CDR
          (ASSOC-EQUAL
           (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                             FRAME)))
           FRAME)))
        (ABS-CONTEXT-APPLY
         (FRAME-VAL->DIR
          (CDR
           (ASSOC-EQUAL
            (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                              FRAME)))
            FRAME)))
         (FRAME-VAL->DIR (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                           FRAME)))
         (ABS-FIND-FIRST-COMPLETE FRAME)
         (NTHCDR
          (LEN
           (FRAME-VAL->PATH
            (CDR (ASSOC-EQUAL
                  (FRAME-VAL->SRC
                   (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                     FRAME)))
                  FRAME))))
          (FRAME-VAL->PATH (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                             FRAME)))))
        (FRAME-VAL->SRC
         (CDR
          (ASSOC-EQUAL
           (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                             FRAME)))
           FRAME))))
       (REMOVE-ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                           FRAME))))
    T))
  (ABS-SEPARATE
   (PSEUDO-FRAME
    ROOT
    (PUT-ASSOC-EQUAL
     (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                       FRAME)))
     (FRAME-VAL
      (FRAME-VAL->PATH
       (CDR
        (ASSOC-EQUAL
         (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                           FRAME)))
         FRAME)))
      (ABS-CONTEXT-APPLY
       (FRAME-VAL->DIR
        (CDR
         (ASSOC-EQUAL
          (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                            FRAME)))
          FRAME)))
       (FRAME-VAL->DIR (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                         FRAME)))
       (ABS-FIND-FIRST-COMPLETE FRAME)
       (NTHCDR
        (LEN
         (FRAME-VAL->PATH
          (CDR (ASSOC-EQUAL
                (FRAME-VAL->SRC
                 (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                   FRAME)))
                FRAME))))
        (FRAME-VAL->PATH (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                           FRAME)))))
      (FRAME-VAL->SRC
       (CDR
        (ASSOC-EQUAL
         (FRAME-VAL->SRC (CDR (ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                                           FRAME)))
         FRAME))))
     (REMOVE-ASSOC-EQUAL (ABS-FIND-FIRST-COMPLETE FRAME)
                         FRAME)))))
 :hints (("Goal" :in-theory (enable PSEUDO-FRAME abs-separate) :do-not-induct t) ))

(thm (implies (AND (ABS-FILE-ALIST-P ROOT)
                   (ABS-NO-DUPS-P ROOT)
                   (FRAME-P FRAME)
                   (equal (mv-nth 1 (ABS-COLLAPSE ROOT FRAME)  ) t)
                   (no-duplicatesp-equal (abs-addrs root))
                   (NO-DUPLICATESP-EQUAL (STRIP-CARS FRAME)))
              (not (intersectp-equal
                    (strip-cars frame)
                    (abs-addrs (mv-nth 0 (ABS-COLLAPSE ROOT FRAME)  )))))
     :hints (("Goal" :in-theory (enable ABS-COLLAPSE)
              :induct (ABS-COLLAPSE ROOT FRAME)
              :expand (:free (y) (intersectp-equal nil y))) ))

(defthm abs-separate-correctness-1
  (implies (and (frame-p frame)
                (no-duplicatesp-equal (strip-cars frame))
                (abs-file-alist-p root)
                ;; This next hypothesis is possibly a consequence of
                ;; (equal result t) below.
                (no-duplicatesp-equal (abs-addrs root))
                (subsetp (abs-addrs root) (strip-cars frame))
                (abs-separate (pseudo-frame root frame)))
           (mv-let
             (m1-file-alist result)
             (abs-collapse root frame)
             (implies (equal result t)
                      (and
                       (m1-file-alist-p m1-file-alist)
                       (hifat-no-dups-p m1-file-alist)))))
  :hints (("Goal" :in-theory (enable abs-collapse)
           :expand (:free (y) (intersectp-equal nil y))) ))
