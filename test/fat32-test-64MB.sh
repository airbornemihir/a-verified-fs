#!/bin/bash
# 64 MB was chosen because we're constrained to used a minimum sector
# size of 512 bytes and a minimum cluster count of 65525, so if we
# want to have more than one sector per cluster 64 MB is what we
# get. For safety, we're making it 73 MB to have a little room for the
# metadata.
DISK=/tmp/disk1.raw
MOUNTPOINT=/tmp/mount1
SIZE=73M
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
time mkfs.fat -v -F 32 -s 2 $DISK
echo "If 0x0200 is displayed below, there are 512 bytes in a sector."
$OD_STEP -t x2 -j11 -N2 $DISK
echo "If 0x02 is displayed below, there are 2 sectors (1 KB) in a cluster."
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
sudo dd of=$MOUNTPOINT/tmp/ticket2.txt if=/dev/zero bs=512 count=9
ls -lR $MOUNTPOINT
sudo umount $MOUNTPOINT
$OD_STEP -t x4 -j16384 -N32 $DISK
rmdir $MOUNTPOINT
# 0x20 reserved sectors + 0x244 sectors for FAT + 0x244 sectors for
# FAT = 0x4a8 sectors before data = 0x95000 bytes before data =
# 610304 bytes before data
echo "Directory entry for vmlinuz"
$OD_STEP -t x4 -j610304 -N32 $DISK
$OD_STEP -t x1z -j610304 -N11 $DISK
echo "Directory entry for tmp"
$OD_STEP -t x4 -j610336 -N32 $DISK
$OD_STEP -t x1z -j610336 -N11 $DISK
$OD_STEP -t x2 -j610356 -N8 $DISK
echo "Directory entry for tmp/."
$OD_STEP -t x4 -j612352 -N32 $DISK
$OD_STEP -t x1z -j612352 -N11 $DISK
$OD_STEP -t x2 -j612372 -N8 $DISK
echo "Directory entry for tmp/.."
$OD_STEP -t x4 -j612384 -N32 $DISK
$OD_STEP -t x1z -j612384 -N11 $DISK
$OD_STEP -t x2 -j612404 -N8 $DISK
echo "Directory entry for tmp/ticket1"
$OD_STEP -t x4 -j612416 -N32 $DISK
$OD_STEP -t x1z -j612416 -N11 $DISK
echo "Directory entry for tmp/ticket2"
$OD_STEP -t x4 -j612448 -N32 $DISK
$OD_STEP -t x1z -j612448 -N11 $DISK
