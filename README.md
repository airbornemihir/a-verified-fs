# turbo-octo-sniffle
This repository contains a series of filesystem models of increasing
complexity.

More technical details can be found in the "papers" subdirectory,
where each of the models is described at length.

Model 5, in the file file-system-5.lisp, is the most
complex, and contains a model of a filesystem with read and write
permissions for each regular file in the filesystem, differentiated
for the owner of the file and all other users in the filesystem (as
yet, there are no groups or access control lists).

The key functions are l5-fs-p (this is a predicate that recognises a
well-formed filesystem), l5-rdchs (this reads a given
number of characters from a given file at a given point) and l5-wrchs
(this writes a given string to a given file at a given point.)

The two read-over-write theorems are proven; see theorems
l5-read-after-write-1 and l5-read-after-write-2. These proofs are
accomplished using equivalence proofs between reading and writing in
model 5 and model 4 respectively; see theorems l5-rdchs-correctness-1
and l5-wrchs-correctness-1 respectively.