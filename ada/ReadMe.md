This is the Ada version.

Note that the queues are split in more files because the RX and TX functions need arrays of a generic argument, that requires a generic package, and GNAT requires 1 package per file.

Overall, this is a best-effort implementation in terms of code cleanliness, it was not written by Ada experts, far from it.
But it works!
