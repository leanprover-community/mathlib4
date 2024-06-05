# mathlib4

![GitHub CI](https://github.com/leanprover-community/mathlib4/workflows/continuous%20integration/badge.svg?branch=master)
[![Bors enabled](https://bors.tech/images/badge_small.svg)](https://mathlib-bors-ca18eefec4cb.herokuapp.com/repositories/16)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://leanprover.zulipchat.com)

This is a complete port of [mathlib](https://github.com/leanprover-community/mathlib) to [Lean 4](https://leanprover.github.io/).
Development of mathlib now takes place in this repository.

[Mathlib](https://leanprover-community.github.io) is a user maintained library for the [Lean theorem prover](https://leanprover.github.io).
It contains both programming infrastructure and mathematics,
as well as tactics that use the former and allow to develop the latter.

## Installation

You can find detailed instructions to install Lean, mathlib, and supporting tools on [our website](https://leanprover-community.github.io/get_started.html).

## Using `mathlib4` as a dependency

Please refer to
[https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)

## Experimenting

Got everything installed? Why not start with the [tutorial project](https://leanprover-community.github.io/install/project.html)?

For more pointers, see [Learning Lean](https://leanprover-community.github.io/learn.html).

## Documentation

Besides the installation guides above and [Lean's general
documentation](https://leanprover.github.io/documentation/), the documentation
of mathlib consists of:

- [The mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/index.html): documentation [generated
  automatically](https://github.com/leanprover/doc-gen4) from the source `.lean` files.
- A description of [currently covered theories](https://leanprover-community.github.io/theories.html),
  as well as an [overview](https://leanprover-community.github.io/mathlib-overview.html) for mathematicians.
- Some [extra Lean documentation](https://leanprover-community.github.io/learn.html) not specific to mathlib (see "Miscellaneous topics")
- Documentation for people who would like to [contribute to mathlib](https://leanprover-community.github.io/contribute/index.html)

Much of the discussion surrounding mathlib occurs in a [Zulip chat
room](https://leanprover.zulipchat.com/), and you are welcome to join, or read
along without signing up.  Questions from users at all levels of expertise are
welcome!  We also provide an [archive of the public
discussions](https://leanprover-community.github.io/archive/), which is useful
for quick reference.

## Transitioning from Lean 3

For users familiar with Lean 3 who want to get up to speed in Lean 4 and migrate their existing
Lean 3 code we have:

- A [survival guide](https://github.com/leanprover-community/mathlib4/wiki/Lean-4-survival-guide-for-Lean-3-users)
  for Lean 3 users
- [Instructions to run `mathport`](https://github.com/leanprover-community/mathport#running-on-a-project-other-than-mathlib)
  on a project other than mathlib. `mathport` is the tool the community used to port the entirety
  of `mathlib` from Lean 3 to Lean 4.

## Contributing

The complete documentation for contributing to ``mathlib`` is located
[on the community guide contribute to mathlib](https://leanprover-community.github.io/contribute/index.html)

The process is different from other projects where one should not fork the repository.
Instead write permission for non-master branches should be requested on [Zulip](https://leanprover.zulipchat.com)
by introducing yourself, providing your GitHub handle and what contribution you are planning on doing.
You may want to subscribe to the `mathlib4` stream

* To obtain precompiled `olean` files, run `lake exe cache get`. (Skipping this step means the next step will be very slow.)
* To build `mathlib4` run `lake build`.
* To build and run all tests, run `make`.
* You can use `lake build Mathlib.Import.Path` to build a particular file, e.g. `lake build Mathlib.Algebra.Group.Defs`.
* If you added a new file, run the following command to update `Mathlib.lean`

  ```shell
  find Mathlib -name "*.lean" | env LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Mathlib.lean
  ```

### Guidelines

Mathlib has the following guidelines and conventions that must be followed

 - The [style guide](https://leanprover-community.github.io/contribute/style.html)
 - A guide on the [naming convention](https://leanprover-community.github.io/contribute/naming.html)
 - The [documentation style](https://leanprover-community.github.io/contribute/doc.html)

### Downloading cached build files

You can run `lake exe cache get` to download cached build files that are computed by `mathlib4`'s automated workflow.
If `tar` terminates with an error, it means that you might have ended up with corrupted files.
In this case, run `lake exe cache get!` to overwrite them (`get` won't try to download the same file again).

Call `lake exe cache` to see its help menu.

### Building HTML documentation

Building HTML documentation locally is straightforward, but it may take a while:

```shell
lake -Kdoc=on build Mathlib:docs
```

The HTML files can then be found in `build/doc`.

### Dependencies

If you are a mathlib contributor and want to update dependencies, use `lake update -Kdoc=on`.
This will update the `lake-manifest.json` file correctly.
You will need to make a PR after committing the changes to this file.

## Maintainers:

For a list containing more detailed information, see https://leanprover-community.github.io/teams/maintainers.html

* Anne Baanen (@Vierkantor): algebra, number theory, tactics
* Matthew Robert Ballard (@mattrobball): algebra, algebraic geometry, category theory, performance
* Reid Barton (@rwbarton): category theory, topology
* Riccardo Brasca (@riccardobrasca): algebra, number theory, algebraic geometry, category theory
* Kevin Buzzard (@kbuzzard): algebra, number theory, algebraic geometry, category theory
* Mario Carneiro (@digama0): lean formalization, tactics, type theory, proof engineering
* Bryan Gin-ge Chen (@bryangingechen): documentation, infrastructure
* Johan Commelin (@jcommelin): algebra, number theory, category theory, algebraic geometry
* Anatole Dedecker (@ADedecker): topology, functional analysis, calculus
* Rémy Degenne (@RemyDegenne): probability, measure theory, analysis
* Floris van Doorn (@fpvandoorn): measure theory, model theory, tactics
* Frédéric Dupuis (@dupuisf): linear algebra, functional analysis
* Gabriel Ebner (@gebner): tactics, infrastructure, core, formal languages
* Sébastien Gouëzel (@sgouezel): topology, calculus, geometry, analysis, measure theory
* Markus Himmel (@TwoFX): category theory
* Chris Hughes (@ChrisHughes24): algebra
* Yury G. Kudryashov (@urkud): analysis, topology, measure theory
* Robert Y. Lewis (@robertylewis): tactics, documentation
* Jireh Loreaux (@j-loreaux): analysis, topology, operator algebras
* Heather Macbeth (@hrmacbeth): geometry, analysis
* Patrick Massot (@patrickmassot): documentation, topology, geometry
* Bhavik Mehta (@b-mehta): category theory, combinatorics
* Kyle Miller (@kmill): combinatorics, tactics, metaprogramming
* Scott Morrison (@semorrison): category theory, tactics
* Oliver Nash (@ocfnash): algebra, geometry, topology
* Joël Riou (@joelriou): category theory, homology, algebraic geometry
* Adam Topaz (@adamtopaz): algebra, category theory, algebraic geometry
* Eric Wieser (@eric-wieser): algebra, infrastructure

## Emeritus maintainers:

* Jeremy Avigad (@avigad): analysis
* Johannes Hölzl (@johoelzl): measure theory, topology
* Simon Hudon (@cipher1024): tactics
