test: test-cat-replicant-1 test-cat-replicant-2 test-cat-replicant-3 test-cat-replicant-4

.PHONY: rebuild-disk clean-mountpoint clean-fusepoint test test-cat-replicant-1 test-cat-replicant-2 test-cat-replicant-3 test-cat-replicant-4

DISK=disk1.raw
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

rebuild-disk:
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) 70000

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

cat-ref-output-1.txt cat-output-1.txt: rebuild-disk $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	echo "four" > $(FUSEPOINT)/vmlinuz
	cat $(FUSEPOINT)/vmlinuz > cat-ref-output-1.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CAT_OUTPUT="cat-output-1.txt" CAT_INPUT="VMLINUZ    " $(ACL2) < cat-replicant.lisp

cat-ref-output-2.txt cat-output-2.txt: rebuild-disk $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	cp input-1204-bytes.txt $(FUSEPOINT)/vmlinuz
	cat $(FUSEPOINT)/vmlinuz > cat-ref-output-2.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CAT_OUTPUT="cat-output-2.txt" CAT_INPUT="VMLINUZ    " $(ACL2) < cat-replicant.lisp

cat-ref-output-3.txt cat-output-3.txt: rebuild-disk $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	cp input-1204-bytes.txt $(FUSEPOINT)/vmlinuz
	cp input-4623-bytes.txt $(FUSEPOINT)/initrd.img
	cat $(FUSEPOINT)/initrd.img > cat-ref-output-3.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CAT_OUTPUT="cat-output-3.txt" CAT_INPUT="INITRD  IMG" $(ACL2) < cat-replicant.lisp

cat-ref-output-4.txt cat-output-4.txt: rebuild-disk $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
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
