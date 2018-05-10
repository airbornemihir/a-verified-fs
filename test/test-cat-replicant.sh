#!/bin/bash
# 64 MB was chosen because we're constrained to used a minimum sector
# size of 512 bytes and a minimum cluster count of 65525, so if we
# want to have more than one sector per cluster 64 MB is what we
# get. For safety, we're making it 73 MB to have a little room for the
# stuff outside the data region.
DISK=/tmp/disk1.raw
MOUNTPOINT=$HOME/mount1
FUSEPOINT=$HOME/mount2
SIZE=73M
BBFS=$HOME/src/fuse-tutorial-2018-02-04/src/bbfs
rm -f $DISK
rm -rf $MOUNTPOINT
rm -rf $FUSEPOINT
qemu-img create -f raw $DISK $SIZE
mkfs.fat -v -F 32 -s 1 $DISK
# make a mountpoint
mkdir -p $MOUNTPOINT
mkdir -p $FUSEPOINT
sudo mount -o loop,uid=$UID,gid=$GID -t msdos $DISK $MOUNTPOINT
$BBFS $MOUNTPOINT $FUSEPOINT
echo "four" > $FUSEPOINT/vmlinuz
cat $FUSEPOINT/vmlinuz > ref-output.txt
fusermount -u $FUSEPOINT
sudo umount $MOUNTPOINT
$ACL2 < cat-replicant.lisp
diff -u -i ref-output.txt output.txt
