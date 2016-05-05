Cha
===

[![Build Status][badge]][build]

Cha is two things:

- [MiniPRL][1] translated into Haskell

- With co-/inductive types smashed into it.

Unlike Danny Gratzer's original MiniPRL I've omitted support for
custom operators. I'll probably add that in at some later time.

The co-/inductive types includes sum types and generic programming,
inductive, and coinductive types over polynomial type operators
(i.e. those composed of type variables, sums, and products). These are
described in chapters 14-15 in [Bob Harper's][2] book Practical
Foundations for Programming Languages (draft of the 2nd edition). I've
included these as we've just covered them in [PLATYPUS][3] (a type
theory reading group in Sydney).

Running
=======

Cha can be built with `stack` and, probably, other tools but I only
use `stack`. To build and test cha, and to run a number of example
proofs through the refined, run the following command:

````
stack test --flag cha:coind
````

[1]: https://github.com/jozefg/miniprl
[2]: https://www.cs.cmu.edu/~rwh/
[3]: https://github.com/CommBank/PLATYPUS

[badge]: https://travis-ci.org/thsutton/cha.svg?branch=master
[build]: https://travis-ci.org/thsutton/cha
