# coqtbgen

A formally verified endgame tablebase generator.

* [Sample tablebase frontend](https://emarzion.github.io/coqtbgen/)
* [Blog post](https://emarzion.github.io/TB-Generator/)

## Build Instructions

```
opam install . --deps-only
dune build
```

To generate a `_CoqProject` for your editor:

```
./configure.sh
```
