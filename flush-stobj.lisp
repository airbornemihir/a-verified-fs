(include-book "std/util/bstar" :dir :system)

(defconst *cluster-size* 1024)

(defconst *count-of-clusters* 70000)

(defconst *default-string* (coerce
                            (make-list *cluster-size* :initial-element #\0)
                            'string))

(make-event
 `(defstobj text-store

    (string-array :type (array string (*count-of-clusters*))
         :resizable t
         ;; per spec
         :initially ,*default-string*)

    (byte-array :type (array (unsigned-byte 8) (,(* *count-of-clusters* *cluster-size*)))
         :resizable t
         ;; per spec
         :initially 0)

    (character-array :type (array character (,(* *count-of-clusters* *cluster-size*)))
         :resizable t
         ;; per spec
         :initially #\0)))

(defthm
  byte-array-to-character-list-helper-guard-lemma-1
  (implies (byte-arrayp l)
           (iff (unsigned-byte-p 8 (nth n l))
                (< (nfix n) (len l))))
  :rule-classes
  ((:rewrite :corollary (implies (and (byte-arrayp l)
                                      (< (nfix n) (len l)))
                                 (integerp (nth n l))))
   (:linear :corollary (implies (and (byte-arrayp l)
                                     (< (nfix n) (len l)))
                                (and (<= 0 (nth n l))
                                     (< (nth n l) 256))))))

(defun
  byte-array-to-character-list-helper
  (text-store len ac)
  (declare
   (xargs :stobjs text-store
          :guard (and (text-storep text-store)
                      (natp len)
                      (<= len (byte-array-length text-store)))))
  (if (zp len)
      ac
      (byte-array-to-character-list-helper
       text-store (- len 1)
       (cons (code-char (byte-arrayi (- len 1) text-store))
             ac))))

(thm (equal (character-listp (byte-array-to-character-list-helper
                              text-store len ac))
            (character-listp ac)))

(b*
    ((character-list
      (time$
       (byte-array-to-character-list-helper
        text-store (byte-array-length text-store) nil)))
     (string
      (time$ (coerce character-list 'string)))
     ((mv channel state)
      (open-output-channel "test.txt" :character state))
     (state
      (time$ (princ$ string channel state)))
     (state
      (close-output-channel channel state)))
  state)

(defthm
  character-array-to-character-list-helper-guard-lemma-1
  (implies (character-arrayp l)
           (iff (characterp (nth n l))
                (< (nfix n) (len l))))
  :rule-classes
  ((:rewrite :corollary (implies (character-arrayp l)
                                 (equal (characterp (nth n l))
                                        (< (nfix n) (len l))))
             :hints (("goal" :do-not-induct t)))))

(defun
  character-array-to-character-list-helper
  (text-store len ac)
  (declare
   (xargs
    :stobjs text-store
    :guard (and (text-storep text-store)
                (natp len)
                (<= len
                    (character-array-length text-store)))))
  (if (zp len)
      ac
      (character-array-to-character-list-helper
       text-store (- len 1)
       (cons (character-arrayi (- len 1) text-store)
             ac))))

(thm (implies
      (and (text-storep text-store) (<= len (character-array-length text-store)))
      (equal (character-listp (character-array-to-character-list-helper
                               text-store len ac))
             (character-listp ac))))

(b*
    ((character-list
      (time$
       (character-array-to-character-list-helper
        text-store (byte-array-length text-store) nil)))
     (string
      (time$ (coerce character-list 'string)))
     ((mv channel state)
      (open-output-channel "test.txt" :character state))
     (state
      (time$ (princ$ string channel state)))
     (state
      (close-output-channel channel state)))
  state)
