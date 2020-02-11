# mlish [![Build Status](https://travis-ci.org/stchang/mlish.svg?branch=master)](https://travis-ci.org/stchang/mlish)

An experimental, extensible language in the OCaml family.

Extensions are type-aware which means that "extensible" includes the
type system. In other words, new type system features may be
implemented and used as libraries, e.g.:
- [type classes](https://github.com/stchang/mlish/blob/master/mlish-test/tests/mlish/generic-with-adhoc-lib.mlish)
- [GADTs](https://github.com/stchang/mlish/blob/master/mlish-test/tests/mlish/mlish%2Bgadt-tests.rkt)

Plain extensions are straightforward as well, e.g., [monadic "do" notation](https://github.com/stchang/mlish/blob/2f9c90edbf51afbb51b7f9d7885631a8acd719aa/mlish-test/tests/mlish/result.mlish#L85-L102)

Implemented with [Turnstile+](https://github.com/stchang/macrotypes/) and [Racket](https://racket-lang.org/).
