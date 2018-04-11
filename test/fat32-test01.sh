#!/bin/bash
DISK=/tmp/disk1.raw
MOUNTPOINT=/tmp/mount1
SIZE=512M
OD_STEP="od -v -Ax --endian=little"
function mount_od_umount {
    sudo umount $MOUNTPOINT
    $OD_STEP -t x4 -j16384 -N32 $DISK
    sudo mount -o loop -t msdos $DISK $MOUNTPOINT
}
rm -f $DISK
rm -rf $MOUNTPOINT
# make a floppy!
qemu-img create -f raw $DISK $SIZE
time mkfs.fat -v -F 32 $DISK
echo "Octal representation of MSWIN4.1"
echo "MSWIN4.1" | $OD_STEP -t x1z
echo "What the FAT32 spec purports to be MSWIN4.1"
$OD_STEP -t x1z -j3 -N8 $DISK
echo "If 0x0200 is displayed below, there are 512 bytes in a sector."
$OD_STEP -t x2 -j11 -N2 $DISK
echo "If 0x08 is displayed below, there are 8 sectors (4 KB) in a cluster."
$OD_STEP -t x1 -j13 -N1 $DISK
echo "If 0x20 is displayed below, then the reserved area occupies 32 sectors (16 KB)."
$OD_STEP -t x2 -j14 -N2 $DISK
echo "The 1 byte number below is the number of file allocation tables."
$OD_STEP -t x1 -j16 -N1 $DISK
echo "The 4 byte hex number below is the size of one FAT32 table in sectors."
$OD_STEP -t x4 -j36 -N4 $DISK
echo "The 4 byte hex number below is the index of the root directory's first cluster."
$OD_STEP -t x4 -j44 -N4 $DISK
# make a mountpoint
mkdir -p $MOUNTPOINT
$OD_STEP -t x4 -j16384 -N32 $DISK
sudo mount -o loop -t msdos $DISK $MOUNTPOINT
sudo dd of=$MOUNTPOINT/vmlinuz if=/dev/zero bs=4 count=1
mount_od_umount
sudo mkdir -p $MOUNTPOINT/tmp/
mount_od_umount
sudo dd of=$MOUNTPOINT/tmp/ticket1.txt if=/dev/zero bs=4 count=1
mount_od_umount
sudo dd of=$MOUNTPOINT/tmp/ticket2.txt if=/dev/zero bs=4 count=1
ls -lR $MOUNTPOINT
sudo umount $MOUNTPOINT
$OD_STEP -t x4 -j16384 -N32 $DISK
rmdir $MOUNTPOINT
