test: test-cat-replicant-1 test-cat-replicant-2 test-cat-replicant-3 \
test-cat-replicant-4 test-mkfs-replicant-1 test-mkfs-replicant-2 \
test-mkfs-replicant-3 test-wc-replicant-1 test-wc-replicant-2 \
test-wc-replicant-3 test-stat-replicant-1 test-stat-replicant-2 \
test-rm-replicant-1 test-rm-replicant-2 mtools-test-cat-replicant-2

.PHONY: clean-mountpoint clean-fusepoint test test-cat-replicant-1 \
test-cat-replicant-2 test-cat-replicant-3 test-cat-replicant-4 \
test-mkfs-replicant-1 test-mkfs-replicant-2 test-mkfs-replicant-3 \
test-wc-replicant-1 test-wc-replicant-2 test-wc-replicant-3 \
test-stat-replicant-1 test-stat-replicant-2 test-rm-replicant-1 \
test-rm-replicant-2 mtools-test-cat-replicant-2

.PHONY: debug-create-dir-and-file debug-create-dir debug-do-nothing \
debug-create-dir-copy-file

DISK=disk1.raw
SIZE=70000
MOUNTPOINT=mount1
FUSEPOINT=mount2
BBFS=$(HOME)/src/bbfs/fuse-tutorial-2018-02-04/src/bbfs
UID=$(shell id -u)
GID=$(shell id -g)
MTOOLSRC=$(pwd)/.mtoolsrc

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

mtools-test-cat-replicant-2: mtools-cat-ref-output-2.txt mtools-cat-output-2.txt
	diff -u -i mtools-cat-ref-output-2.txt mtools-cat-output-2.txt

test-cat-replicant-5: cat-ref-output-5.txt cat-output-5.txt
	diff -u -i cat-ref-output-5.txt cat-output-5.txt

test-mkfs-replicant-1: mkfs-ref-output-1.txt mkfs-output-1.txt
	diff -u -i mkfs-ref-output-1.txt mkfs-output-1.txt

test-mkfs-replicant-2: mkfs-ref-output-2.txt mkfs-output-2.txt
	diff -u -i mkfs-ref-output-2.txt mkfs-output-2.txt

test-mkfs-replicant-3: mkfs-ref-output-3.txt mkfs-output-3.txt
	diff -u -i mkfs-ref-output-3.txt mkfs-output-3.txt

test-wc-replicant-1: wc-ref-output-1.txt wc-output-1.txt
	diff -u -i wc-ref-output-1.txt wc-output-1.txt

test-wc-replicant-2: wc-ref-output-2.txt wc-output-2.txt
	diff -u -i wc-ref-output-2.txt wc-output-2.txt

test-wc-replicant-3: wc-ref-output-3.txt wc-output-3.txt
	diff -u -i wc-ref-output-3.txt wc-output-3.txt

test-stat-replicant-1: stat-ref-output-1.txt stat-output-1.txt
	diff -u -i stat-ref-output-1.txt stat-output-1.txt

test-stat-replicant-2: stat-ref-output-2.txt stat-output-2.txt
	diff -u -i stat-ref-output-2.txt stat-output-2.txt

test-rm-replicant-1: rm-output-1.raw rm-ref-output-1.raw
	env DISK=$(DISK) REF_INPUT="rm-ref-output-1.raw" \
	INPUT="rm-output-1.raw" $(ACL2) -- < compare-disks.lisp

test-rm-replicant-2: rm-output-2.raw rm-ref-output-2.raw
	env DISK=$(DISK) REF_INPUT="rm-ref-output-2.raw" \
	INPUT="rm-output-2.raw" $(ACL2) -- < compare-disks.lisp

cat-ref-output-1.txt cat-output-1.txt: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	echo "four" > $(FUSEPOINT)/vmlinuz
	cat $(FUSEPOINT)/vmlinuz > cat-ref-output-1.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CAT_OUTPUT="cat-output-1.txt" \
	CAT_INPUT="VMLINUZ    " $(ACL2) < cat-replicant.lisp

cat-ref-output-2.txt cat-output-2.txt: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	cp input-1204-bytes.txt $(FUSEPOINT)/vmlinuz
	cat $(FUSEPOINT)/vmlinuz > cat-ref-output-2.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CAT_OUTPUT="cat-output-2.txt" \
	CAT_INPUT="VMLINUZ    " $(ACL2) < cat-replicant.lisp

cat-ref-output-3.txt cat-output-3.txt: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	cp input-1204-bytes.txt $(FUSEPOINT)/vmlinuz
	cp input-4623-bytes.txt $(FUSEPOINT)/initrd.img
	cat $(FUSEPOINT)/initrd.img > cat-ref-output-3.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CAT_OUTPUT="cat-output-3.txt" \
	CAT_INPUT="INITRD  IMG" $(ACL2) < cat-replicant.lisp

cat-ref-output-4.txt cat-output-4.txt: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
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
	env DISK=$(DISK) CAT_OUTPUT="cat-output-4.txt" \
	CAT_INPUT="INITRD  IMG" $(ACL2) < cat-replicant.lisp

mtools-cat-ref-output-2.txt mtools-cat-output-2.txt: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK) mtools-cat-ref-output-2.txt
	dd if=/dev/zero of=$(DISK) bs=4096 count=17920
	env MTOOLSRC=$(PWD)/.mtoolsrc mformat -T 140000 -h 64 -s 32 -S \
	2 -F -c 2 c:
	env MTOOLSRC=$(PWD)/.mtoolsrc mcopy input-1204-bytes.txt c:/vmlinuz
	env MTOOLSRC=$(PWD)/.mtoolsrc mcopy c:/vmlinuz mtools-cat-ref-output-2.txt
	env DISK=$(DISK) CAT_OUTPUT="mtools-cat-output-2.txt" \
	CAT_INPUT="VMLINUZ    " $(ACL2) < cat-replicant.lisp

cat-ref-output-5.txt cat-output-5.txt: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	cp input-1204-bytes.txt $(FUSEPOINT)/initrd.img
	sync $(FUSEPOINT)/initrd.img
	rm $(FUSEPOINT)/initrd.img
	for i1 in $(shell seq 1 32); do \
		cp input-1204-bytes.txt $(FUSEPOINT)/initrd$$i1.img; \
	done
	cp input-4623-bytes.txt $(FUSEPOINT)/initrd.img
	cat $(FUSEPOINT)/initrd.img > cat-ref-output-5.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CAT_OUTPUT="cat-output-5.txt" \
	CAT_INPUT="INITRD  IMG" $(ACL2) < cat-replicant.lisp

mkfs-ref-output-1.txt mkfs-output-1.txt: $(MOUNTPOINT) $(FUSEPOINT) \
mkfs.fat-3.0.28-replicant.lisp
	rm -f $(DISK)
	(mkfs.fat -C -v -F 32 -s 1 $(DISK) $(SIZE)) > mkfs-ref-output-1.txt
	env DISK=$(DISK) MKFS_OUTPUT="mkfs-output-1.txt" $(ACL2) < \
	mkfs.fat-3.0.28-replicant.lisp

mkfs-ref-output-2.txt mkfs-output-2.txt: $(MOUNTPOINT) $(FUSEPOINT) \
mkfs.fat-3.0.28-replicant.lisp
	rm -f $(DISK)
	(mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)) > mkfs-ref-output-2.txt
	env DISK=$(DISK) MKFS_OUTPUT="mkfs-output-2.txt" $(ACL2) < \
	mkfs.fat-3.0.28-replicant.lisp

# this case does not actually produce a valid FAT32 filesystem, since
# there are fewer than 65525 clusters.
mkfs-ref-output-3.txt mkfs-output-3.txt: $(MOUNTPOINT) $(FUSEPOINT) \
mkfs.fat-3.0.28-replicant.lisp
	rm -f $(DISK)
	(mkfs.fat -C -v -F 32 -s 4 $(DISK) $(SIZE)) > mkfs-ref-output-3.txt
	env DISK=$(DISK) MKFS_OUTPUT="mkfs-output-3.txt" $(ACL2) < \
	mkfs.fat-3.0.28-replicant.lisp

wc-ref-output-1.txt wc-output-1.txt: $(MOUNTPOINT) $(FUSEPOINT) wc-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	cp input-4623-bytes.txt $(FUSEPOINT)/initrd.img
	wc -c < $(FUSEPOINT)/initrd.img > wc-ref-output-1.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) WC_OUTPUT="wc-output-1.txt" \
	WC_INPUT="initrd.img" $(ACL2) -- -c < wc-replicant.lisp

wc-ref-output-2.txt wc-output-2.txt: $(MOUNTPOINT) $(FUSEPOINT) wc-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	cp input-4623-bytes.txt $(FUSEPOINT)/initrd.img
	wc -l < $(FUSEPOINT)/initrd.img > wc-ref-output-2.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) WC_OUTPUT="wc-output-2.txt" \
	WC_INPUT="initrd.img" $(ACL2) -- -l < wc-replicant.lisp

wc-ref-output-3.txt wc-output-3.txt: $(MOUNTPOINT) $(FUSEPOINT) wc-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	cp input-4623-bytes.txt $(FUSEPOINT)/initrd.img
	wc -w < $(FUSEPOINT)/initrd.img > wc-ref-output-3.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) WC_OUTPUT="wc-output-3.txt" \
	WC_INPUT="initrd.img" $(ACL2) -- -w < wc-replicant.lisp

stat-ref-output-1.txt stat-output-1.txt: $(MOUNTPOINT) $(FUSEPOINT) stat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	cp input-4623-bytes.txt $(FUSEPOINT)/initrd.img
	cd $(FUSEPOINT); stat -f initrd.img > ../stat-ref-output-1.txt; cd -
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) STAT_OUTPUT="stat-output-1.txt" \
	STAT_INPUT="initrd.img" $(ACL2) -- -f < stat-replicant.lisp

stat-ref-output-2.txt stat-output-2.txt: $(MOUNTPOINT) $(FUSEPOINT) stat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	for i1 in $(shell seq 1 32); do \
		cp input-1204-bytes.txt $(FUSEPOINT)/initrd$$i1.img; \
	done
	cp input-4623-bytes.txt $(FUSEPOINT)/initrd.img
	cd $(FUSEPOINT); stat -f initrd.img > ../stat-ref-output-2.txt; cd -
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) STAT_OUTPUT="stat-output-2.txt" \
	STAT_INPUT="initrd.img" $(ACL2) -- -f < stat-replicant.lisp

rm-ref-output-1.raw rm-output-1.raw: $(MOUNTPOINT) $(FUSEPOINT) rm-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	cp input-4623-bytes.txt $(FUSEPOINT)/initrd.img
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	cp $(DISK) rm-ref-output-1.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos rm-ref-output-1.raw $(MOUNTPOINT)
	rm $(MOUNTPOINT)/initrd.img
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) RM_OUTPUT="rm-output-1.raw" \
	RM_INPUT="initrd.img" $(ACL2) -- < rm-replicant.lisp

rm-ref-output-2.raw rm-output-2.raw: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	cp input-1204-bytes.txt $(FUSEPOINT)/initrd.img
	for i1 in $(shell seq 1 32); do \
		cp input-1204-bytes.txt $(FUSEPOINT)/initrd$$i1.img; \
	done
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	cp $(DISK) rm-ref-output-2.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos rm-ref-output-2.raw $(MOUNTPOINT)
	rm $(MOUNTPOINT)/initrd.img
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) RM_OUTPUT="rm-output-2.raw" \
	RM_INPUT="initrd.img" $(ACL2) -- < rm-replicant.lisp

debug-do-nothing: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	true

debug-create-dir: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	mkdir $(FUSEPOINT)/tmp
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	true

debug-create-dir-and-file: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	mkdir $(FUSEPOINT)/tmp
	touch $(FUSEPOINT)/tmp/ticket1.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	true

debug-create-dir-copy-file: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	mkdir $(FUSEPOINT)/tmp
	touch $(FUSEPOINT)/tmp/ticket1.txt
	cp $(FUSEPOINT)/tmp/ticket1.txt $(FUSEPOINT)/tmp/ticket2.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	true

debug-create-dir-and-file-rm: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	mkdir $(FUSEPOINT)/tmp
	touch $(FUSEPOINT)/tmp/ticket1.txt
	sync $(FUSEPOINT)/tmp/ticket1.txt
	rm $(FUSEPOINT)/tmp/ticket1.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	true

debug-create-dir-and-file-mv: $(MOUNTPOINT) $(FUSEPOINT) cat-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
	mkdir $(FUSEPOINT)/tmp
	touch $(FUSEPOINT)/tmp/ticket1.txt
	sync $(FUSEPOINT)/tmp/ticket1.txt
	mv $(FUSEPOINT)/tmp/ticket1.txt $(FUSEPOINT)/tmp/ticket2.txt
	sleep 1
	fusermount -u $(FUSEPOINT)
	sudo umount $(MOUNTPOINT)
	true
