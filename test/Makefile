test: test-cat-replicant

DISK=disk1.raw
SIZE=73M
MOUNTPOINT=mount1
FUSEPOINT=mount2
BBFS=$(HOME)/src/fuse-tutorial-2018-02-04/src/bbfs
UID=$(shell id -u)
GID=$(shell id -g)

clean-disk:
	rm -rf $(DISK)

clean-mountpoint:
	rm -rf $(MOUNTPOINT)

clean-fusepoint:
	rm -rf $(FUSEPOINT)

$(DISK): clean-disk
	qemu-img create -f raw $(DISK) $(SIZE)
	mkfs.fat -v -F 32 -s 2 $(DISK)

$(MOUNTPOINT): clean-mountpoint
	mkdir -p $(MOUNTPOINT)

$(FUSEPOINT): clean-fusepoint
	mkdir -p $(FUSEPOINT)

test-cat-replicant: ref-output.txt output.txt
	diff -u -i ref-output.txt output.txt

ref-output.txt output.txt: $(DISK) $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	echo "four" > $(FUSEPOINT)/vmlinuz
	cat $(FUSEPOINT)/vmlinuz > ref-output.txt
	$(ACL2) < cat-replicant.lisp
