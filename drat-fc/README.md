A two watched literal implementation of DRAT checker in Haskell.

## Building and Running instructions

The project is using a cabal file. For building and running you can use
cabal or stack.

### Stack

    stack init
    stack build
    stack exec -- drat-checker data/manthey_single-ordered-initialized-w18-b7.cnf data/manthey_single-ordered-initialized-w18-b7.drup -H128m
