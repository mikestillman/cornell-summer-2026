12 June 2026
- Notes for additional tests to write
    - more tests with multiple asserts/ multiple calls to hilbert samuel in one test block
    - tests to make sure that failing cases / non-supported cases actuallyu throw an error

- (3) in `HilbertSamuel.m2` is to add a function to determine if a prime is primary in a local ring.
- Here is some more detail
    - Exercise: primary in a localisation if is primary and contained in prime that you're localising at
    -  Implementation for is Primary:
    - given an ideal in a local ring, 1) sub the ideal into the ambient ring 2) check if contained in prime being localised at 3) use the already implemented function isPrimary for non-local rings
