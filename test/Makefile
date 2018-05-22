test: test-cat-replicant-1 test-cat-replicant-2 test-cat-replicant-3 test-cat-replicant-4

.PHONY: clean-mountpoint clean-fusepoint test test-cat-replicant-1 \
test-cat-replicant-2 test-cat-replicant-3 test-cat-replicant-4 \
test-mkfs-replicant-1 test-mkfs-replicant-2 test-mkfs-replicant-3

DISK=disk1.raw
# 64 MB was chosen because we're constrained to used a minimum sector
# size of 512 bytes and a minimum cluster count of 65525, so if we
# want to have more than one sector per cluster 64 MB is what we
# get. For safety, we're making it 73 MB to have a little room for the
# stuff outside the data region.
SIZE=73M
MOUNTPOINT=mount1
FUSEPOINT=mount2
BBFS=$(HOME)/src/fuse-tutorial-2018-02-04/src/bbfs
UID=$(shell id -u)
GID=$(shell id -g)

clean-mountpoint:
	rm -rf $(MOUNTPOINT)

clean-fusepoint:
	rm -rf $(FUSEPOINT)

$(MOUNTPOINT):
	rm -rf $(MOUNTPOINT)
	mkdir -p $(MOUNTPOINT)

$(FUSEPOINT):
	rm -rf $(FUSEPOINT)
	mkdir -p $(FUSEPOINT)

test-cat-replicant-1: cat-ref-output-1.txt cat-output-1.txt
	diff -u -i cat-ref-output-1.txt cat-output-1.txt

test-cat-replicant-2: cat-ref-output-2.txt cat-output-2.txt
	diff -u -i cat-ref-output-2.txt cat-output-2.txt

test-cat-replicant-3: cat-ref-output-3.txt cat-output-3.txt
	diff -u -i cat-ref-output-3.txt cat-output-3.txt

test-cat-replicant-4: cat-ref-output-4.txt cat-output-4.txt
	diff -u -i cat-ref-output-4.txt cat-output-4.txt

test-mkfs-replicant-1: mkfs-ref-output-1.txt mkfs-output-1.txt
	diff -u -i mkfs-ref-output-1.txt mkfs-output-1.txt

test-mkfs-replicant-2: mkfs-ref-output-2.txt mkfs-output-2.txt
	diff -u -i mkfs-ref-output-2.txt mkfs-output-2.txt

test-mkfs-replicant-3: mkfs-ref-output-3.txt mkfs-output-3.txt
	diff -u -i mkfs-ref-output-3.txt mkfs-output-3.txt

cat-ref-output-1.txt cat-output-1.txt: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) 70000
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	echo "four" > $(FUSEPOINT)/vmlinuz
	cat $(FUSEPOINT)/vmlinuz > cat-ref-output-1.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CAT_OUTPUT="cat-output-1.txt" CAT_INPUT="VMLINUZ    " $(ACL2) < cat-replicant.lisp

cat-ref-output-2.txt cat-output-2.txt: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) 70000
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	cp input-1204-bytes.txt $(FUSEPOINT)/vmlinuz
	cat $(FUSEPOINT)/vmlinuz > cat-ref-output-2.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CAT_OUTPUT="cat-output-2.txt" CAT_INPUT="VMLINUZ    " $(ACL2) < cat-replicant.lisp

cat-ref-output-3.txt cat-output-3.txt: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) 70000
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	cp input-1204-bytes.txt $(FUSEPOINT)/vmlinuz
	cp input-4623-bytes.txt $(FUSEPOINT)/initrd.img
	cat $(FUSEPOINT)/initrd.img > cat-ref-output-3.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CAT_OUTPUT="cat-output-3.txt" CAT_INPUT="INITRD  IMG" $(ACL2) < cat-replicant.lisp

cat-ref-output-4.txt cat-output-4.txt: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) 70000
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	for i1 in $(shell seq 1 32); do \
		cp input-1204-bytes.txt $(FUSEPOINT)/initrd$$i1.img; \
	done
	cp input-4623-bytes.txt $(FUSEPOINT)/initrd.img
	cat $(FUSEPOINT)/initrd.img > cat-ref-output-4.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CAT_OUTPUT="cat-output-4.txt" CAT_INPUT="INITRD  IMG" $(ACL2) < cat-replicant.lisp

mkfs-ref-output-1.txt mkfs-output-1.txt: $(MOUNTPOINT) $(FUSEPOINT) mkfs-replicant.lisp
	rm -f $(DISK)
	qemu-img create -f raw $(DISK) $(SIZE)
	(mkfs.fat -v -F 32 -s 1 $(DISK)) > mkfs-ref-output-1.txt
	env DISK=$(DISK) MKFS_OUTPUT="mkfs-output-1.txt" $(ACL2) < mkfs-replicant.lisp

mkfs-ref-output-2.txt mkfs-output-2.txt: $(MOUNTPOINT) $(FUSEPOINT) mkfs-replicant.lisp
	rm -f $(DISK)
	qemu-img create -f raw $(DISK) $(SIZE)
	(mkfs.fat -v -F 32 -s 2 $(DISK)) > mkfs-ref-output-2.txt
	env DISK=$(DISK) MKFS_OUTPUT="mkfs-output-2.txt" $(ACL2) < mkfs-replicant.lisp

# this case does not actually produce a valid FAT32 filesystem, since
# there are fewer than 65525 clusters.
mkfs-ref-output-3.txt mkfs-output-3.txt: $(MOUNTPOINT) $(FUSEPOINT) mkfs-replicant.lisp
	rm -f $(DISK)
	qemu-img create -f raw $(DISK) $(SIZE)
	(mkfs.fat -v -F 32 -s 4 $(DISK)) > mkfs-ref-output-3.txt
	env DISK=$(DISK) MKFS_OUTPUT="mkfs-output-3.txt" $(ACL2) < mkfs-replicant.lisp
