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
;; to implement - cpmcreat cpmopen cpmread cpmwrite cpmclose

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

;; stupid theorem! weaker version of the above. a disaster!
(defthm am-find-local-file-by-name-correctness-3
  (implies (natp index)
           (not (< (+ index (len dir-tree)) (am-find-local-file-by-name dir-tree fname index)))))

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

;; int cpmWrite(struct cpmFile *file, const char *buf, int count)
(defun am-cpmWrite (dir fname contents position cwd)
  (if (or (not (am-dir-filep cwd))
          (character-listp contents)
          (natp position))
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
                        (cons (cons fname (append (take index (cdr indexfile))
                                                  (append contents
                                                          (nthcdr (+ position
                                                                     (length
                                                                      contents))
                                                                  (cdr indexfile)))))
                              (append (cdr cwd) (cdr cwd)))))))
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

;; int cpmRead(struct cpmFile *file, char *buf, int count)
(defun am-cpmRead (dir fname length position cwd)
  (if (or (not (am-dir-filep cwd))
          (natp length)
          (natp position))
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
            (mv 0 (nthcdr length (take (+ position length) (cdr indexfile))))))
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
