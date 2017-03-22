A mechancially verified drat-checker in Haskell.

Verification was done with Coq and the programm was then extracted from the proof.

## Building

    stack setup
    stack bulid
    stack exec -- drat-vc-exe FILE.CNF FILE.DRAT
