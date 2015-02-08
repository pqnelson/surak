# Introduction

[Surak](http://en.memory-alpha.org/wiki/Surak) is a toy automated theorem prover, more for my learning how one works than actual use.

It's written in Haskell, and released under the MIT License.

# Versioning

For simplicity, the version number is going to be `x.y.z` where `x`
refers to the order of logic (0 for propositional logic, 1 for predicate
logic, 2 for second-order logic, etc.), `y` is the "major version", and
`z` is the "minor version".

# Run it

So, right now, the main function just executes a number of tests.
If you want to run it, simply open up a shell, and type in:

```bash
~/surak/$ cabal sandbox init
~/surak/$ cabal install --only-dependencies
~/surak/$ cabal build
~/surak/$ ./dist/build/surak/surak
```

Making this into a REPL, or even a batch-job, well, that's on my todo
list.
