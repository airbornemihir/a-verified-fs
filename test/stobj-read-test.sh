#!/bin/bash
# 512 MB was chosen because that's when mkfs.fat chooses to increase
# the sectors-per-cluster value to 8, on its own accord, compared to
# the value of 1 which is used for 256 MB.
DISK=/tmp/disk1.raw
SIZE=512M
rm -f $DISK
# make a floppy!
touch $DISK
dd if=/dev/zero of=$DISK bs=512 count=1000000
