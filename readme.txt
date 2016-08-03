Our model begins with a replica of the program mkfs.cpm - it's the
basis of everything afterwards. To model cpmcp and cpmfs, we'll need
the basic directory structure to be set up.

mkfs.cpm is fairly simple
- it starts by saving custom boot blocks if any, up to four
- then there's a component called cpmReadSuper
  which does some heavy lifting in setting up some data structures on
  the disk.
-- it starts by branching off into one of two functions,
   diskdefReadSuper and amsReadSuper, in order to read some basic info
   about what the disk should look like. I think we might want to go
   the way of hard-coding these things instead.
-- then it sets up a skew table.
-- then it initialises an allocation vector bitmap.
-- then, a directory buffer is allocated.
-- if a directory exists in the core, it is read, else it is created
-- additional superblock information - only if CPMFS_CPM3_OTHER
--- passwords
--- disc label
- then... we set bootTrackSize and write 0xe5 to bootTracks
- then we finish by writing these custom boot tracks that we saved
  previously...

Let's start by modelling the skew table and the allocation vector map.
