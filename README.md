# TT-Reflection

## Requirements

1.   [GHC 7.8.2](http://www.haskell.org/ghc/)
2.   [cabal-install 1.20.0.x](http://hackage.haskell.org/package/cabal-install)

See the [learnhaskell](https://github.com/bitemyapp/learnhaskell) for details on installing these.

This may work with previous versions of GHC and cabal, but I have zero interest in making sure that it does.

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
