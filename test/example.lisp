(in-package "ACL2")

(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)

;; I started making this example, and then I realised the issue was about
;; resizability of arrays. I'm not going to develop this further.
(defstobj fat32-in-memory
    (array-8 :type (array (unsigned-byte 8) (3))
                ;; boilerplate
                :initially 0)
    (array-32 :type (array (unsigned-byte 32) (4))
         :resizable t
         ;; per spec
         :initially 0)

    (data-region :type (array (unsigned-byte 8) (*ms-min-data-region-size*))
         :resizable t
         ;; per spec
         :initially 0))
