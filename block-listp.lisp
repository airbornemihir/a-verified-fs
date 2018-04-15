(in-package "ACL2")

;  block-listp.lisp                                  Mihir Mehta

; Here we define the size of a block to be 8 characters, and define functions
; for making blocks from text and retrieving text from blocks, with proofs of
; their correctness and their one-way inverse relationship.

(include-book "file-system-lemmas")

;; I don't think blocks are 8 characters long in any system; I simply set this
;; in order to actually get fragmentation without having to make unreasonably
;; large examples.
(defconst *blocksize* 8)

;; This fragments a character-list into blocks that are *blocksize*-character
;; long. If the character-list is not exactly aligned to a block boundary, we
;; fill the space with null characters.
;; It will be used in wrchs.
(defund make-blocks (text)
  (declare (xargs :guard (character-listp text)
                  :measure (len text)))
  (if (atom text)
      nil
    (cons (make-character-list (take *blocksize* text))
          (make-blocks (nthcdr *blocksize* text)))))

(defthm
  make-blocks-correctness-5
  (iff (consp (make-blocks text))
       (consp text))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (iff (equal (len (make-blocks text)) 0)
                    (atom text))
    :hints (("goal''" :expand (len (make-blocks text))))))
  :hints (("goal" :in-theory (enable make-blocks))))

;; Characterisation of a disk, which is a list of blocks as described before.
(defun block-listp (block-list)
  (declare (xargs :guard t))
  (if (atom block-list)
      (eq block-list nil)
    (and (character-listp (car block-list))
         (equal (len (car block-list)) *blocksize*)
         (block-listp (cdr block-list)))))

;; Proving that we get a proper block-list out of make-blocks.
(defthm make-blocks-correctness-2
        (implies (character-listp text)
                 (block-listp (make-blocks text)))
        :hints (("Goal" :in-theory (enable make-blocks))))

;; Lemma
(defthm block-listp-correctness-1
  (implies (block-listp block-list)
           (true-listp block-list))
  :rule-classes (:forward-chaining))

;; Lemma
(defthm block-listp-correctness-2
  (implies (true-listp block-list1)
           (equal (block-listp (binary-append block-list1 block-list2))
                  (and (block-listp block-list1)
                       (block-listp block-list2)))))
