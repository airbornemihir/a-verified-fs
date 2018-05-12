test: test-cat-replicant

.PHONY: clean-disk clean-mountpoint clean-fusepoint test test-cat-replicant

DISK=disk1.raw
SIZE=73M
MOUNTPOINT=mount1
FUSEPOINT=mount2
BBFS=$(HOME)/src/fuse-tutorial-2018-02-04/src/bbfs
UID=$(shell id -u)
GID=$(shell id -g)

clean-disk:
	rm $(DISK)

clean-mountpoint:
	rm -rf $(MOUNTPOINT)

clean-fusepoint:
	rm -rf $(FUSEPOINT)

$(DISK):
	rm -f $(DISK)
	qemu-img create -f raw $(DISK) $(SIZE)
	mkfs.fat -v -F 32 -s 2 $(DISK)

$(MOUNTPOINT):
	rm -rf $(MOUNTPOINT)
	mkdir -p $(MOUNTPOINT)

$(FUSEPOINT):
	rm -rf $(FUSEPOINT)
	mkdir -p $(FUSEPOINT)

test-cat-replicant: cat-ref-output.txt cat-output.txt
	diff -u -i cat-ref-output.txt cat-output.txt

cat-ref-output.txt cat-output.txt: $(DISK) $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	echo "four" > $(FUSEPOINT)/vmlinuz
	cat $(FUSEPOINT)/vmlinuz > cat-ref-output.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	$(ACL2) < cat-replicant.lisp
