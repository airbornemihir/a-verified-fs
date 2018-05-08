#!/bin/bash
DISK=/tmp/disk1.raw
MOUNTPOINT=/tmp/mount1
FUSEPOINT=/tmp/mount2
SIZE=73M
BBFS=$HOME/src/fuse-tutorial-2018-02-04/src/bbfs
# snippet from https://unix.stackexchange.com/a/438158/286440
UID=`id -u`
GID=`id -g`
OD_STEP="od -v -Ax --endian=little"
function mount_od_umount {
    sudo umount $MOUNTPOINT
    $OD_STEP -t x4 -j16384 -N32 $DISK
    sudo mount -o loop,uid=$UID,gid=$GID -t msdos $DISK $MOUNTPOINT
}
rm -f $DISK
rm -rf $MOUNTPOINT
rm -rf $FUSEPOINT
qemu-img create -f raw $DISK $SIZE
time mkfs.fat -v -F 32 $DISK
# make a mountpoint
mkdir -p $MOUNTPOINT
mkdir -p $FUSEPOINT
$OD_STEP -t x4 -j16384 -N32 $DISK
sudo mount -o loop,uid=$UID,gid=$GID -t msdos $DISK $MOUNTPOINT
$BBFS $MOUNTPOINT $FUSEPOINT
echo "four" > $FUSEPOINT/vmlinuz
# ls -lR $FUSEPOINT
stat $FUSEPOINT/vmlinuz
fusermount -u $FUSEPOINT
sudo umount $MOUNTPOINT
grep -o -e "^bb_[[:alnum:]]*" bbfs.log | sort | uniq > bbfs_operations.txt
# snippet from https://stackoverflow.com/a/1521498/6213541
while read p; do
  echo -n "$p: "; grep -c -e "^$p" bbfs.log
done < bbfs_operations.txt
grep -o -e "[[:alnum:]]*[[:space:]]\+returned" bbfs.log | sort | uniq
