This is the accompanying artefact submission for the paper titled
"Code Proofs with a Binary-Compatible Filesystem Model". These ACL2
books were certified with ACL2 version 8.2, the most recent release of
the theorem prover. Apart from certifiable books, there is a
co-simulation test suite in the test/ subdirectory; the GNU/Linux
programs mkfs.fat, diff, sudo, cp, mkdir, mv, rm, rmdir, stat,
truncate, unlink, and wc are required in order to run the tests, as is
the mtools suite of programs (version 4.0.18).

The FAT32 models HiFAT and LoFAT depend on a number of helper
functions and lemmas in other files; the cert.pl utility distributed
with ACL2 is useful in tracking and building these dependencies. The
shell command below certifies all the filesystem models, assuming
proper substitutions for ACL2_DIR (the directory containing ACL2) and
ACL2 (the ACL2 executable, likely to be $ACL2/saved_acl2) below.

$ ACL2_DIR/books/build/cert.pl --acl2 ACL2 file-system-*.lisp

This certification must be completed before attempting the co-simulation
tests, which are located in the test/ subdirectory. This subdirectory
has its own Makefile, which can be invoked as follows, again
substituting a proper value for ACL2.

$ cd test; sudo make ACL2=ACL2 test

This should run a number of tests built on LoFAT against the actual
programs from the Coreutils and the mtools. These include
co-simulation tests for the ls and rm programs detailed in the paper,
and the proofs mentioned in the paper can be found in the file
ls-rm-example.lisp. Another proof which displays the model's ablility
to reason about file contents can be found in the file
wc-truncate-example.lisp, which states that after truncation of a
given file to a given size, running wc -c on that same file will
return that same size.

sudo is required for mounting and unmounting the disk images involved
in these tests; thus, root privileges on the testing machine are
required. Installation note: these tests are known to work with an ACL2 built atop
Clozure Common Lisp (CCL). At least one other Common Lisp
implementation (SBCL) causes some tests to fail, on account of
inconsistent handling of command line arguments by
[oslib::argv](http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/?topic=OSLIB____ARGV). The
ACL2 installation page points to instructions for
[obtaining](http://www.cs.utexas.edu/users/moore/acl2/v8-1/HTML/installation/requirements.html#Obtaining-CCL)
and
[installing](http://www.cs.utexas.edu/users/moore/acl2/v8-1/HTML/installation/ccl.html)
CCL.