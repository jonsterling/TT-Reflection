# TT-Reflection

## Requirements

1.   [GHC](http://www.haskell.org/ghc/)
2.   [cabal-install](http://hackage.haskell.org/package/cabal-install)

See the [learnhaskell](https://github.com/bitemyapp/learnhaskell) for details on installing these.

## Building

```
$ cabal sandbox init
$ cabal install --only-dependencies
$ cabal configure
$ cabal build
```

## Running

```
$ cabal run -- check test.tt    # check a theory file
$ cabal run -- repl             # start the REPL
```
