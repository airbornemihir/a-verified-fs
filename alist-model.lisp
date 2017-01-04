#||
This is a simple model of a unix-style filesystem, represented as a tree. A
file is constrained to be either a regular file (a character list with a
name, defined by the predicate am-reg-filep) or a directory file (a list of
files with a name, defined by the predicate am-dir-filep). This tree
representation is the model for implementations of the familiar unix FS
operations of creating, reading and writing files; however directory
creation and deletion of directories are left alone for now. With these, we
prove the two read-over-write properties, named am-read-what-was-written and
am-read-what-was-read here.

We plan to use these as the basis for more realistic models, starting by
relaxing the assumption that the contents of a file remain in one place, in
order to allow lengthy files to be split across blocks.
||#

(include-book "std/util/defconsts" :dir :system)
(include-book "std/util/bstar" :dir :system)

;; lemma for later theorems
(defthm len-of-revappend
  (equal (len (revappend x y))
         (+ (len x) (len y))))

;; lemma for later theorems
(defthm revappend-append
  (equal (append (revappend x y) z)
         (revappend x (append y z))))

;; lemma for later theorems
(defthmd revappend-replace
  (equal (revappend x y)
         (append (reverse x) y)))

;; lemma for later theorems
(defthm revappend-twice-reduces
  (equal (revappend (revappend x y) z)
         (revappend y (append x z))))

;; predicates defining two types of files
(defun am-reg-filep (x)
  (and (consp x)
       (character-listp (car x))
       (character-listp (cdr x))))
(mutual-recursion
 (defun am-dir-treep (x)
   (if (atom x)
       (equal x nil)
     (and (or (am-reg-filep (car x)) (am-dir-filep (car x)))
          (am-dir-treep (cdr x)))))
 (defun am-dir-filep (x)
   (and (consp x)
        (character-listp (car x))
        (am-dir-treep (cdr x))))
 )

;; predicate defining a file from either of the two types
(defun am-filep (x)
  (or (am-reg-filep x) (am-dir-filep x)))

(defthm am-dir-treep-correctness-1
  (implies (and (am-dir-treep t1) (am-dir-treep t2))
           (am-dir-treep (append t1 t2))))

(defthm am-dir-treep-correctness-2
  (implies (and (am-dir-treep x) (am-dir-treep y))
           (am-dir-treep (revappend x y))))

(defthm am-dir-treep-correctness-3
  (implies (and (am-dir-treep l) (am-dir-treep ac) (natp i) (<= i (len l)))
           (am-dir-treep (first-n-ac i l ac))))

(defthm am-dir-treep-correctness-4
  (implies (am-dir-treep l)
           (am-dir-treep (nthcdr n l))))

;; utility function for finding a file with the name fname in the directory
;; tree dirtree
(defun am-find-local-file-by-name (dir-tree fname index)
  (if (or
       ;; no more files to see
       (atom dir-tree)
       (not (am-filep (car dir-tree)))
       (not (natp index)))
      -1
    (if (equal fname (car (car dir-tree)))
        index
      (am-find-local-file-by-name (cdr dir-tree) fname (+ 1 index)))))

(defthm am-find-local-file-by-name-correctness-1
  (let ((index (am-find-local-file-by-name dir-tree fname index0)) )
    (implies (<= 0 index)
             (let ((indexfile (nth (- index index0) dir-tree)) )
               (and (am-filep indexfile) (equal (car indexfile) fname)))))
  )

(defthm am-find-local-file-by-name-correctness-2
  (implies (natp index)
           (< (am-find-local-file-by-name dir-tree fname index) (+ (len
                                                                    dir-tree) index))))

;; weaker version of the above theorem - unsuccessfully trying to make certain
;; arithmetic properties automatically provable
(defthm am-find-local-file-by-name-correctness-3
  (implies (natp index)
           (not (< (+ index (len dir-tree)) (am-find-local-file-by-name dir-tree fname index)))))

(defthm am-find-local-file-by-name-correctness-4
  (implies (and (<= 0 index)
                (<= 0 (am-find-local-file-by-name dir-tree fname index))
                (am-dir-treep dir-tree))
           (character-listp fname)))

(defthm am-find-local-file-by-name-correctness-5
  (let ((file-index (am-find-local-file-by-name dir-tree fname index)) )
    (implies (<= 0 file-index)
           (<= index file-index))))

(defthm am-find-local-file-by-name-correctness-6
  (let ((file-index (am-find-local-file-by-name dir-tree1 fname index)) )
    (implies
     (and (<= 0 index)
          (<= index file-index))
     (equal (am-find-local-file-by-name (binary-append dir-tree1 dir-tree2)
                                        fname index)
            file-index)))
  :instructions ((:induct (am-find-local-file-by-name dir-tree1 fname index))
                 (:use (:instance am-find-local-file-by-name-correctness-5
                                  (dir-tree (cdr dir-tree1))
                                  (index (+ 1 index))))
                 :split :bash :bash :bash
                 (:bash ("goal" :expand (append dir-tree1 dir-tree2)))
                 :bash))

(defthmd am-find-local-file-by-name-correctness-7
  (let ((file-index1 (am-find-local-file-by-name dir-tree fname index1))
        (file-index2 (am-find-local-file-by-name dir-tree fname index2)))
    (implies
     (and (natp index1) (natp index2)
          (<= 0 file-index1))
     (equal (- file-index2 index2)
            (- file-index1 index1))))
  :rule-classes
  ((:rewrite :corollary
              (let ((file-index1 (am-find-local-file-by-name dir-tree fname index1))
                    (file-index2 (am-find-local-file-by-name dir-tree fname index2)))
                (implies
                 (and (natp index1) (natp index2)
                      (<= 0 file-index1))
                 (equal file-index2
                        (+ file-index1 index2 (- index1))))))))

(defthm
  am-find-local-file-by-name-correctness-8
  (let
   ((file-index1 (am-find-local-file-by-name dir-tree1 fname index1))
    (file-index2 (am-find-local-file-by-name dir-tree2 fname index2)))
   (implies
    (and (am-dir-treep dir-tree1)
         (am-dir-treep dir-tree2)
         (natp index1)
         (natp index2)
         (< file-index1 0)
         (<= 0 file-index2))
    (equal (am-find-local-file-by-name (binary-append dir-tree1 dir-tree2)
                                       fname index2)
           (+ (len dir-tree1) file-index2))))
  :instructions
  (:split
   (:induct (and (append dir-tree1 dir-tree2)
                 (am-find-local-file-by-name dir-tree1 fname index1)
                 (am-find-local-file-by-name dir-tree2 fname index2)))
   :split
   :bash :bash :bash (:change-goal nil t)
   :split :bash :bash
   (:claim
    (equal (am-find-local-file-by-name (append (cdr dir-tree1) dir-tree2)
                                       fname (+ 1 index2))
           (+ 1
              (am-find-local-file-by-name (append (cdr dir-tree1) dir-tree2)
                                          fname index2)))
    :hints :none)
   (:change-goal nil t)
   (:dive 1)
   (:rewrite am-find-local-file-by-name-correctness-7
             ((index1 index2)))
   :top
   :bash :bash))

;; this is a recursive function for creating a file fname in the subdirectory dir
;; starting from directory cwd. the C prototype follows.
;; int cpmCreat(struct cpmInode *dir, const char *fname, struct cpmInode *ino, mode_t mode)
(defun am-cpmCreat (dir fname ino mode cwd)
  (declare (irrelevant ino mode))
  (if (not (am-dir-filep cwd))
      (mv -1 cwd)
    (if (atom dir)
        ;; already in the directory
        (if (>= (am-find-local-file-by-name (cdr cwd) fname 0) 0)
            ;; messed up! return -1
            (mv -1 cwd)
          ;; there's room for this file
          (mv 0 (cons (car cwd) (cons (cons fname nil) (cdr cwd)))))
      (let* ((index (am-find-local-file-by-name (cdr cwd) (car dir) 0))
             (indexdir (nth index (cdr cwd))))
        (if (or
             ;; nonexistent directory
             (< index 0)
             ;; invalid directory
             (not (am-dir-filep indexdir)))
            (mv -1 cwd)
          (mv-let (fd indexdir)
            (am-cpmCreat (cdr dir) fname ino mode indexdir)
            (if (< fd 0)
                (mv -1 cwd)
              (mv 0 (cons (car cwd)
                          (cons indexdir (append (take index (cdr cwd))
                                                 (Nthcdr (+ 1 index) (cdr cwd)))))))
            )))
      )))

(defthm am-cpmCreat-correctness-1
  (mv-let (fd cwd) (am-cpmCreat dir fname ino mode cwd0)
    (implies (< fd 0) (equal cwd cwd0))))

(defthm am-cpmcreat-preserves-am-dir-treep
  (implies (and (am-dir-filep cwd)
                (character-listp fname))
           (mv-let (fd cwd)
             (am-cpmcreat dir fname ino mode cwd)
             (and (integerp fd) (am-dir-filep cwd))))
  :hints (("goal" :induct (am-cpmcreat dir fname ino mode
                                       cwd)) ))

;; this predicate is used in theorem am-cpmCreat-correctness-2
(defun am-file-foundp (dir fname cwd)
  (and (am-dir-filep cwd)
       (if (atom dir)
           ;; file in the current directory
           (>= (am-find-local-file-by-name (cdr cwd) fname 0) 0)
         ;; file in a subdirectory 1 or more levels down
         (let* ((index (am-find-local-file-by-name (cdr cwd) (car dir) 0))
                (indexdir (nth index (cdr cwd))))
           (and (>= index 0)
                (am-dir-filep indexdir)
                (am-file-foundp (cdr dir) fname indexdir)))
         )))

(defthm am-cpmCreat-correctness-2
  (implies
   (character-listp fname)
   (mv-let (fd cwd) (am-cpmCreat dir fname ino mode cwd0)
     (implies (>= fd 0)
              (am-file-foundp dir fname cwd))))
  :instructions (
                 :split
                 (:induct (am-cpmcreat dir fname ino mode cwd0))
                 (:change-goal nil t)
                 :bash
                 :bash
                 :bash
                 :bash
                 :bash
                 :promote
                 (:demote 3 5)
                 (:dive 1)
                 :s
                 :top
                 :promote
                 (:claim
                  (equal (< (car (am-cpmcreat (cdr dir)
                                              fname ino mode
                                              (nth (am-find-local-file-by-name (cdr cwd0)
                                                                               (car dir)
                                                                               0)
                                                   (cdr cwd0))))
                            0)
                         nil))
                 (:dive 3 2)
                 :x
                 :up
                 :s
                 :up
                 :x
                 :split
                 :bash
                 :bash
                 :bash
                 :bash
                 (:change-goal nil t)
                 (:dive 3 2)
                 :s
                 :up
                 :top
                 (:demote 10)
                 :promote
                 (:use (:instance am-find-local-file-by-name-correctness-1
                                  (index0 0)
                                  (dir-tree (cdr cwd0))
                                  (fname (car dir))))
                 :promote
                 (:demote 1)
                 (:dive 1)
                 :expand
                 :s
                 :top
                 :promote
                 (:demote 10)
                 (:dive 1)
                 :s
                 (:dive 1)
                 (:dive 2 1 2)
                 :x
                 :up
                 :up
                 :up
                 :s
                 :up
                 :s
                 (:use (:instance am-find-local-file-by-name-correctness-1
                                  (index0 0)
                                  (dir-tree (cdr cwd0))
                                  (fname (car dir))))
                 :promote
                 (:demote 1)
                 (:dive 1)
                 :expand
                 :s
                 :top
                 :promote
                 (:demote 10)
                 (:dive 1)
                 (:dive 1 2 1 2)
                 :x
                 :up
                 :up
                 :up
                 :up
                 :s
                 :up
                 :s
                 (:use (:instance am-find-local-file-by-name-correctness-1
                                  (index0 0)
                                  (dir-tree (cdr cwd0))
                                  (fname (car dir))))
                 :promote
                 (:demote 1)
                 (:dive 1)
                 :expand
                 s
                 top
                 promote
                 (:demote 10)
                 (:dive 1)
                 (:dive 1 2 1 2)
                 x
                 top
                 bash))

(defthm am-cpmCreat-correctness-3
  (implies (and (character-listp fname) (am-file-foundp dir fname cwd0))
           (mv-let (fd cwd) (am-cpmCreat dir fname ino mode cwd0)
             (and (< fd 0) (equal cwd cwd0)))))

(defthm am-cpmCreat-fails-second-time
  (implies
   (and (am-dir-filep cwd)
        (character-listp fname))
   (let ((mv (am-cpmcreat dir fname ino mode cwd)))
     (let ((fd (mv-nth 0 mv)) (cwd (mv-nth 1 mv)))
       (implies (<= 0 fd)
                (let ((mv (am-cpmcreat dir fname ino mode cwd)))
                  (let ((fd (mv-nth 0 mv))
                        (cwd (hide (mv-nth 1 mv))))
                    (< fd 0)))))))
  :instructions (split
                 (:rewrite am-cpmcreat-correctness-3)
                 (:use (:instance am-cpmcreat-correctness-2 (cwd0 cwd)))
                 bash))

;; this function was created as an alternative to first-n-ac to preserve the
;; character-listp nature of the list, instead of inserting nil elements into
;; the list as first-n-ac is wont to do. it may be advantageous later to
;; re-write this function in the style of first-n
(defun
    first-n-characters-ac (i l ac)
  (declare (type (integer 0 *) i)
           (xargs :guard (and (true-listp l) (true-listp ac))))
  (cond ((zp i) (revappend ac nil))
        ((consp l) (first-n-characters-ac (1- i)
                                          (cdr l)
                                          (cons (car l) ac)))
        (t (first-n-characters-ac (1- i)
                       nil
                       (cons (code-char 0) ac)))))

(defthm first-n-characters-ac-count
  (implies (natp i)
           (equal (len (first-n-characters-ac i l ac))
                  (+ i (len ac))))
)

(defthm first-n-characters-ac-character-listp
  (implies (and (character-listp l) (character-listp ac))
           (character-listp (first-n-characters-ac i l ac))))

;; replacement of take that instead uses first-n-characters-ac
(defun take-characters (n l)
  (declare (xargs :guard (and (integerp n)
                              (not (< n 0))
                              (character-listp l))))
  (first-n-characters-ac n l nil))

;; this recursive function writes the character list contents into the file
;; fname in subdirectory dir starting from directory cwd, using the given
;; position as a starting point. the C prototype follows.
;; int cpmWrite(struct cpmFile *file, const char *buf, int count)
(defun am-cpmWrite (dir fname contents position cwd)
  (if (not (and (am-dir-filep cwd)
                (character-listp contents)
                (natp position)))
      (mv -1 cwd)
    (if (atom dir)
        ;; already in the directory
        (let* ((index (am-find-local-file-by-name (cdr cwd) fname 0))
               (indexfile (nth index (cdr cwd))))
          (if (or (< index 0)
                  (not (am-reg-filep indexfile)))
              ;; messed up! return -1
              (mv -1 cwd)
            ;; there's a file to put this in
            (mv 0 (cons (car cwd)
                        (cons (cons fname (binary-append (take-characters position (cdr indexfile))
                                                         (binary-append contents
                                                                        (nthcdr (+ position
                                                                                   (length
                                                                                    contents))
                                                                                (cdr indexfile)))))
                              (binary-append (take index (cdr cwd))
                                             (nthcdr (+ 1 index) (cdr cwd))))))))
      ;; outside the directory, so call recursively
      (let* ((index (am-find-local-file-by-name (cdr cwd) (car dir) 0))
             (indexdir (nth index (cdr cwd))))
        (if (or
             ;; nonexistent directory
             (< index 0)
             ;; invalid directory
             (not (am-dir-filep indexdir)))
            (mv -1 cwd)
          (mv-let (fd indexdir)
            (am-cpmWrite (cdr dir) fname contents position indexdir)
            (if (< fd 0)
                (mv -1 cwd)
              (mv 0 (cons (car cwd)
                          (cons indexdir (append (take index (cdr cwd))
                                                 (Nthcdr (+ 1 index) (cdr cwd)))))))
            ))))
    ))

(defconsts (& *am-cpmWrite-example-1*)
  (am-cpmWrite (list (coerce "tmp" 'list))
               (coerce "complaint" 'list)
               (coerce "delayed" 'list)
               0
               (cons nil (cons (cons (coerce "tmp" 'list)
                                     (cons (cons (coerce "complaint" 'list)
                                                 nil) nil)) nil))
               ))

(defthm am-cpmWrite-returns-file-lemma-1
  (implies (character-listp l)
           (character-listp (nthcdr n l))))

(defthm am-cpmWrite-returns-file
  (mv-let (fd cwd) (am-cpmWrite dir fname contents position cwd0)
    (implies (and (<= 0 fd) (am-dir-filep cwd0))
             (am-dir-filep cwd)))
  :instructions
  (:split
   (:induct (am-cpmwrite dir fname contents position cwd0))
   (:change-goal nil t)
   :bash :bash (:change-goal nil t)
   :bash :bash :split (:demote 6)
   (:dive 1)
   :x :top :promote (:dive 1 2)
   :x :top (:demote 1)
   (:dive 1)
   :x :top
   :promote :x :bash :split (:demote 6)
   (:dive 1)
   :x :top :promote (:dive 1 2)
   :x :top (:dive 1)
   :x :top
   (:claim (character-listp fname)
           :hints :none)
   (:change-goal nil t)
   (:rewrite am-find-local-file-by-name-correctness-4
             ((dir-tree (cdr cwd0)) (index 0)))
   :bash
   (:claim
    (character-listp
     (first-n-characters-ac position
                            (cdr (nth (am-find-local-file-by-name (cdr cwd0)
                                                                  fname 0)
                                      (cdr cwd0)))
                            nil))
    :hints :none)
   (:change-goal nil t)
   (:rewrite first-n-characters-ac-character-listp)
   :bash
   (:claim
    (character-listp (nthcdr (+ position (len contents))
                             (cdr (nth (am-find-local-file-by-name (cdr cwd0)
                                                                   fname 0)
                                       (cdr cwd0))))))
   :bash
   (:rewrite am-dir-treep-correctness-1)
   (:rewrite am-dir-treep-correctness-3)
   :bash
   (:use (:instance am-find-local-file-by-name-correctness-2
                    (index 0)
                    (dir-tree (cdr cwd0))))
   :bash
   (:rewrite am-dir-treep-correctness-4)
   :bash))

(defthm am-cpmWrite-preserves-names
  (mv-let (fd cwd) (am-cpmWrite dir fname contents position cwd0)
    (declare (ignore fd))
    (equal (car cwd) (car cwd0))))

;; (defthm am-cpmWrite-preserves-files
;;   (mv-let (fd cwd) (am-cpmWrite dir1 fname1 contents position cwd0)
;;     (declare (ignore fd))
;;     (implies (am-file-foundp dir2 fname2 cwd0)
;;              (am-file-foundp dir2 fname2 cwd))))

;; this recursive funcion reads the specified number of characters from the
;; specified position in the file fname in the subdirectory dir, starting from
;; directory cwd. the C prototype follows.
;; int cpmRead(struct cpmFile *file, char *buf, int count)
(defun am-cpmRead (dir fname length position cwd)
  (if (not (and (am-dir-filep cwd)
                (natp length)
                (natp position)))
      (mv -1 nil)
    (if (atom dir)
        ;; already in the directory
        (let* ((index (am-find-local-file-by-name (cdr cwd) fname 0))
               (indexfile (nth index (cdr cwd))))
          (if (or (< index 0)
                  (not (am-reg-filep indexfile)))
              ;; messed up! return -1
              (mv -1 nil)
            ;; there's a file to read this from
            (mv 0 (nthcdr position (take-characters (+ position length) (cdr indexfile))))))
      ;; outside the directory, so call recursively
      (let* ((index (am-find-local-file-by-name (cdr cwd) (car dir) 0))
             (indexdir (nth index (cdr cwd))))
        (if (or
             ;; nonexistent directory
             (< index 0)
             ;; invalid directory
             (not (am-dir-filep indexdir)))
            (mv -1 nil)
          (am-cpmRead (cdr dir) fname length position indexdir))))
    ))

(defconsts (& *am-cpmRead-example-1*)
  (am-cpmRead (cons (coerce "tmp" 'list) nil) (coerce "complaint" 'list) 7 0 *am-cpmWrite-example-1*))

(defthm am-cpmRead-correctness-1
  (implies
   (mv-let (fd contents) (am-cpmRead dir fname length position cwd)
     (declare (ignore contents))
     (>= fd 0))
   (am-file-foundp dir fname cwd)))

(defthm am-read-what-was-written-lemma-1
  (implies (and (character-listp l) (character-listp ac))
           (character-listp (first-n-characters-ac i l ac))))

(defthm am-read-what-was-written-lemma-2
  (implies (character-listp l)
           (character-listp (nthcdr n l))))

(defthm am-read-what-was-written-lemma-3
  (implies (and (natp len2)
                (equal (+ (len l1) len2) len3))
           (equal (first-n-characters-ac len3 (binary-append l1 l2) ac)
                  (first-n-characters-ac len2 l2 (revappend l1 ac))))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (and (equal len2 (- len3 (len l1)))
                                (natp len2)
                                (integerp len3))
                           (equal (first-n-characters-ac len3 (binary-append l1 l2) ac)
                                  (first-n-characters-ac len2 l2 (revappend l1 ac)))))))

(defthm am-read-what-was-written-lemma-4
  (implies (and (natp len2)
                (equal (+ (len l1) len2) len3))
           (equal (nthcdr len3 (binary-append l1 l2))
                  (nthcdr len2 l2)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (and (equal len2 (- len3 (len l1)))
                                (natp len2)
                                (integerp len3))
                           (equal (nthcdr len3 (binary-append l1 l2))
                                  (nthcdr len2 l2))))))

;; first read-on-write theorem - a read following a write at the same place
;; should return what was written.
(defthm am-read-what-was-written
  (implies (character-listp fname)
           (mv-let (fd1 cwd1) (am-cpmWrite dir fname contents0 position cwd0)
             (implies (>= fd1 0)
                      (mv-let (fd2 contents2) (am-cpmRead dir fname (len contents0) position cwd1)
                        (and (>= fd2 0)
                             (equal contents2 contents0))))))
  :instructions
  ((:induct (am-cpmwrite dir fname contents0 position cwd0))
   (:change-goal nil t)
   :bash :bash
   (:bash ("goal" :expand ((am-cpmwrite dir fname contents0 position cwd0))))
   (:dive 1 2)
   :top
   (:rewrite am-dir-treep-correctness-1)
   (:rewrite am-dir-treep-correctness-3)
   :bash
   (:use (:instance am-find-local-file-by-name-correctness-2
                    (index 0)
                    (dir-tree (cdr cwd0))))
   :bash
   (:rewrite am-dir-treep-correctness-4)
   :bash :bash :bash (:demote 1 4)
   (:dive 1)
   :s (:dive 1)
   :x :top :promote
   (:claim
    (am-dir-treep (append (first-n-ac (am-find-local-file-by-name (cdr cwd0)
                                                                  (car dir)
                                                                  0)
                                      (cdr cwd0)
                                      nil)
                          (nthcdr (am-find-local-file-by-name (cdr cwd0)
                                                              (car dir)
                                                              0)
                                  (cddr cwd0)))))
   :split :bash :bash :s (:dive 1 1 1 5 2)
   :x :top (:dive 1 1 1)
   :x :top
   (:use (:instance am-find-local-file-by-name-correctness-1
                    (dir-tree (cdr cwd0))
                    (fname (car dir))
                    (index0 0)))
   :bash
   (:use (:instance am-find-local-file-by-name-correctness-1
                    (dir-tree (cdr cwd0))
                    (fname (car dir))
                    (index0 0)))
   :bash))

;; second read-on-write theorem - a read following a write at a different place
;; should return what was present previously.
(defthm am-read-what-was-read
  (implies (and (character-listp fname)
                (not (and (equal dir1 dir2)
                          (equal fname1 fname2))))
           (b* (((mv & cwd1) (am-cpmWrite dir1 fname1 contents0 position1 cwd0))
                ((mv fd2 contents2) (am-cpmRead dir2 fname2 len2 position2 cwd1))
                ((mv fd3 contents3) (am-cpmRead dir2 fname2 len2 position2 cwd0)))
             (and (equal (>= fd2 0) (>= fd3 0))
                  (equal contents2 contents3))))
  :instructions
  ((:induct (am-cpmwrite dir1 fname1 contents0 position1 cwd0))
   (:change-goal nil t)
   :bash :bash (:change-goal nil t)
   :bash :bash (:change-goal (main . 4) t)
   (:demote 1 3)
   (:dive 1)
   :s-prop :top :pro
   (:claim
    (equal
     (am-cpmwrite dir1 fname1 contents0 position1 cwd0)
     (list
      0
      (list*
       (car cwd0)
       (cons
        fname1
        (append (first-n-characters-ac
                 position1
                 (cdr (nth (am-find-local-file-by-name (cdr cwd0)
                                                       fname1 0)
                           (cdr cwd0)))
                 nil)
                contents0
                (nthcdr (+ position1 (len contents0))
                        (cdr (nth (am-find-local-file-by-name (cdr cwd0)
                                                              fname1 0)
                                  (cdr cwd0))))))
       (append (first-n-ac (am-find-local-file-by-name (cdr cwd0)
                                                       fname1 0)
                           (cdr cwd0)
                           nil)
               (nthcdr (am-find-local-file-by-name (cdr cwd0)
                                                   fname1 0)
                       (cddr cwd0)))))))
   :expand :expand :expand
   :expand :expand :expand (:dive 1 1)
   :s (:dive 1 1 1 5)
   :x :top (:dive 1 2)
   :s :top (:dive 1 1 1 1 1 5 1 1 1)
   := :top (:dive 1 1 1 1 1 5 2 1)
   (:dive 1)
   := :top (:dive 2 1 2 5 2)
   := :up :s :top (:drop 9)
   (:dive 1 1 1 1 1 5)
   :s :top))
