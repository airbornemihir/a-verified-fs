#!/bin/bash
# 64 MB was chosen because we're constrained to used a minimum sector
# size of 512 bytes and a minimum cluster count of 65525, so if we
# want to have more than one sector per cluster 64 MB is what we
# get. For safety, we're making it 73 MB to have a little room for the
# stuff outside the data region.
DISK=/tmp/disk1.raw
SIZE=73M
rm -f $DISK
qemu-img create -f raw $DISK $SIZE
(mkfs.fat -v -F 32 -s 1 $DISK) > ref-output.txt
$ACL2 < mkfs-replicant.lisp
diff -u -i ref-output.txt output.txt

qemu-img create -f raw $DISK $SIZE
(mkfs.fat -v -F 32 -s 2 $DISK) > ref-output.txt
$ACL2 < mkfs-replicant.lisp
diff -u -i ref-output.txt output.txt

rm -f $DISK
qemu-img create -f raw $DISK $SIZE
(mkfs.fat -v -F 32 -s 4 $DISK) > ref-output.txt
$ACL2 < mkfs-replicant.lisp
diff -u -i ref-output.txt output.txt
