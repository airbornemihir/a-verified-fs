(in-package "ACL2")

(include-book "hifat-to-lofat-inversion")

(defthm
  hifat-to-lofat-helper-correctness-5-lemma-5
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (equal (mv-nth 2
                       (hifat-to-lofat-helper fat32-in-memory
                                              fs current-dir-first-cluster))
               0))
   (equal
    (count-free-clusters
     (effective-fat
      (mv-nth 0
              (hifat-to-lofat-helper fat32-in-memory
                                     fs current-dir-first-cluster))))
    (- (count-free-clusters (effective-fat fat32-in-memory))
       (hifat-cluster-count fs (cluster-size fat32-in-memory)))))
  :hints
  (("goal"
    :in-theory (e/d (len-of-make-clusters hifat-cluster-count
                     painful-debugging-lemma-14)
                    (floor nth)))))

(encapsulate
  ()

  (local (in-theory (e/d
                     (hifat-cluster-count
                      count-free-clusters-of-effective-fat-of-place-contents-lemma-2
                      painful-debugging-lemma-12)
                     ((:rewrite
                       fati-of-hifat-to-lofat-helper-disjoint)
                      (:rewrite
                       fati-of-hifat-to-lofat-helper-disjoint-lemma-1)
                      (:definition update-nth) floor nth))))

  (defthm
    hifat-to-lofat-helper-correctness-5
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (m1-file-alist-p fs))
     (equal (mv-nth 2
                    (hifat-to-lofat-helper fat32-in-memory
                                           fs current-dir-first-cluster))
            (if (>= (count-free-clusters (effective-fat fat32-in-memory))
                    (hifat-cluster-count fs (cluster-size fat32-in-memory)))
                0 *enospc*)))
    :hints
    (("goal" :induct (hifat-to-lofat-helper fat32-in-memory
                                            fs current-dir-first-cluster)
      :expand ((make-clusters "" (cluster-size fat32-in-memory))
               (hifat-cluster-count fs (cluster-size fat32-in-memory))))
     ("subgoal *1/4" :in-theory (enable len-of-make-clusters)))))
