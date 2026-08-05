<<<<<<< HEAD
# mathlib4

![GitHub CI](https://github.com/leanprover-community/mathlib4/actions/workflows/build.yml/badge.svg?branch=master)
[![Bors enabled](https://raw.githubusercontent.com/bors-ng/bors-ng.github.io/refs/heads/master/images/badge_small.svg)](https://mathlib-bors-ca18eefec4cb.herokuapp.com/repositories/16)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://leanprover.zulipchat.com)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/leanprover-community/mathlib4)

[Mathlib](https://leanprover-community.github.io) is a user maintained library for the [Lean theorem prover](https://leanprover.github.io).
It contains both programming infrastructure and mathematics,
as well as tactics that use the former and allow to develop the latter.

## Installation

You can find detailed instructions to install Lean, mathlib, and supporting tools on [our website](https://leanprover-community.github.io/get_started.html).
Alternatively, click on one of the buttons below to open a GitHub Codespace or a Gitpod workspace containing the project.

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/leanprover-community/mathlib4)

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/leanprover-community/mathlib4)

## Using `mathlib4` as a dependency

Please refer to
[https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)

## Experimenting

Got everything installed? Why not start with the [tutorial project](https://leanprover-community.github.io/install/project.html)?

For more pointers, see [Learning Lean](https://leanprover-community.github.io/learn.html).

## Documentation

Besides the installation guides above and [Lean's general
documentation](https://docs.lean-lang.org/lean4/doc/), the documentation
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

## Contributing

The complete documentation for contributing to ``mathlib`` is located
[on the community guide contribute to mathlib](https://leanprover-community.github.io/contribute/index.html)

You may want to subscribe to the `mathlib4` channel on [Zulip](https://leanprover.zulipchat.com/) to introduce yourself and your plan to the community.
Often you can find community members willing to help you get started and advise you on the fit and
feasibility of your project.

* To obtain precompiled `olean` files, run `lake exe cache get`. (Skipping this step means the next step will be very slow.)
* To build `mathlib4` run `lake build`.
* To build and run all tests, run `lake test`.
* You can use `lake build Mathlib.Import.Path` to build a particular file, e.g. `lake build Mathlib.Algebra.Group.Defs`.
* If you added a new file, run the following command to update `Mathlib.lean`

  ```shell
  lake exe mk_all
  ```

### Guidelines

Mathlib has the following guidelines and conventions that must be followed

 - The [style guide](https://leanprover-community.github.io/contribute/style.html)
 - A guide on the [naming convention](https://leanprover-community.github.io/contribute/naming.html)
 - The [documentation style](https://leanprover-community.github.io/contribute/doc.html)

### Downloading cached build files

You can run `lake exe cache get` to download cached build files that are computed by `mathlib4`'s automated workflow.

If something goes mysteriously wrong,
you can try one of `lake clean` or `rm -rf .lake` before trying `lake exe cache get` again.
In some circumstances you might try `lake exe cache get!`
which re-downloads cached build files even if they are available locally.

Call `lake exe cache` to see its help menu.

### Building HTML documentation

The [mathlib4_docs repository](https://github.com/leanprover-community/mathlib4_docs)
is responsible for generating and publishing the
[mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/index.html).

That repo can be used to build the docs locally:
```shell
git clone https://github.com/leanprover-community/mathlib4_docs.git
cd mathlib4_docs
cp ../mathlib4/lean-toolchain .
lake exe cache get
lake build Mathlib:docs
```
The last step may take a while (>20 minutes).
The HTML files can then be found in `.lake/build/doc`.

## Transitioning from Lean 3

For users familiar with Lean 3 who want to get up to speed in Lean 4 and migrate their existing
Lean 3 code we have:

- A [survival guide](https://github.com/leanprover-community/mathlib4/wiki/Lean-4-survival-guide-for-Lean-3-users)
  for Lean 3 users
- [Instructions to run `mathport`](https://github.com/leanprover-community/mathport#running-on-a-project-other-than-mathlib)
  on a project other than mathlib. `mathport` is the tool the community used to port the entirety
  of `mathlib` from Lean 3 to Lean 4.

### Dependencies

If you are a mathlib contributor and want to update dependencies, use `lake update`,
or `lake update batteries aesop` (or similar) to update a subset of the dependencies.
This will update the `lake-manifest.json` file correctly.
You will need to make a PR after committing the changes to this file.

Please do not run `lake update -Kdoc=on` as previously advised, as the documentation related
dependencies should only be included when CI is building documentation.

## Maintainers:

For a list containing more detailed information, see https://leanprover-community.github.io/teams/maintainers.html

* Anne Baanen (@Vierkantor): algebra, number theory, tactics
* Matthew Robert Ballard (@mattrobball): algebra, algebraic geometry, category theory
* Riccardo Brasca (@riccardobrasca): algebra, number theory, algebraic geometry, category theory
* Kevin Buzzard (@kbuzzard): algebra, number theory, algebraic geometry, category theory
* Mario Carneiro (@digama0): lean formalization, tactics, type theory, proof engineering
* Bryan Gin-ge Chen (@bryangingechen): documentation, infrastructure
* Johan Commelin (@jcommelin): algebra, number theory, category theory, algebraic geometry
* Anatole Dedecker (@ADedecker): topology, functional analysis, calculus
* Rémy Degenne (@RemyDegenne): probability, measure theory, analysis
* Floris van Doorn (@fpvandoorn): measure theory, model theory, tactics
* Frédéric Dupuis (@dupuisf): linear algebra, functional analysis
* Sébastien Gouëzel (@sgouezel): topology, calculus, geometry, analysis, measure theory
* Markus Himmel (@TwoFX): category theory
* Yury G. Kudryashov (@urkud): analysis, topology, measure theory
* Robert Y. Lewis (@robertylewis): tactics, documentation
* Jireh Loreaux (@j-loreaux): analysis, topology, operator algebras
* Heather Macbeth (@hrmacbeth): geometry, analysis
* Patrick Massot (@patrickmassot): documentation, topology, geometry
* Bhavik Mehta (@b-mehta): category theory, combinatorics
* Kyle Miller (@kmill): combinatorics, tactics, metaprogramming
* Kim Morrison (@kim-em): category theory, tactics
* Oliver Nash (@ocfnash): algebra, geometry, topology
* Filippo A. E. Nuccio (@faenuccio): algebra, functional analysis, homology, number theory
* Joël Riou (@joelriou): category theory, homology, algebraic geometry
* Michael Rothgang (@grunweg): differential geometry, analysis, topology, linters
* Damiano Testa (@adomani): algebra, algebraic geometry, number theory, tactics, linters
* Adam Topaz (@adamtopaz): algebra, category theory, algebraic geometry
* Eric Wieser (@eric-wieser): algebra, infrastructure

## Past maintainers:

* Jeremy Avigad (@avigad): analysis
* Reid Barton (@rwbarton): category theory, topology
* Gabriel Ebner (@gebner): tactics, infrastructure, core, formal languages
* Johannes Hölzl (@johoelzl): measure theory, topology
* Simon Hudon (@cipher1024): tactics
* Chris Hughes (@ChrisHughes24): algebra
=======
# Euclid's Elements, Book I — Formalization in Lean 4

Machine-checked proofs of the first propositions of Euclid's *Elements* (c. 300 BCE)
that are **not** already in [mathlib4](https://github.com/leanprover-community/mathlib4).

## Author

**Warren Wong**

## What's here

| Prop | Content | In mathlib? | Status |
|------|---------|-------------|--------|
| I.1  | Equilateral triangle construction | ❌ No | ✅ Proven |
| I.2  | Copy a segment to a given point | ❌ No | ✅ Proven |
| I.3  | Cut a shorter segment from a longer | ❌ No | ✅ Proven |
| I.4  | SAS congruence | ✅ Yes | — (mathlib) |
| I.5  | Isosceles base angles equal | ✅ Yes | — (mathlib) |
| I.6  | Converse of I.5 | ✅ Yes | — (mathlib) |
| I.7  | Uniqueness of triangle (perp) | ❌ No | ✅ Proven |
| I.8  | SSS congruence | ✅ Yes | — (mathlib) |
| I.9  | Angle bisection (existence) | ❌ No | ✅ Proven |

**All proofs verified with `lake build` — ZERO `sorry`.**

## Theorem statements

```lean
-- I.1: On a given finite straight line, to construct an equilateral triangle.
Euclid.BookI.Prop1.equilateral_triangle_exists
  (A B : EuclideanSpace ℝ (Fin 2)) (h : A ≠ B)
  : ∃ C, dist A C = dist A B ∧ dist B C = dist A B

-- I.2: To place a straight line equal to a given straight line with one end at a given point.
Euclid.BookI.Prop2.segment_copy
  (A B C : EuclideanSpace ℝ (Fin 2)) : ∃ D, dist A D = dist B C

-- I.3: Given two unequal straight lines, to cut off from the greater a straight line equal to the less.
Euclid.BookI.Prop3.cut_segment
  (A B C D : EuclideanSpace ℝ (Fin 2)) (hAB : A ≠ B) (h : dist C D < dist A B)
  : ∃ E, Wbtw ℝ A E B ∧ dist A E = dist C D

-- I.7: On the same base and same side, two pairs of equal lines meet at the same point
--      (algebraic core: equidistant points are perpendicular to the base).
Euclid.BookI.Prop7.equidistant_implies_perp
  (A B C D : EuclideanSpace ℝ (Fin 2)) (hAC : dist A C = dist A D) (hBC : dist B C = dist B D)
  : inner ℝ (B - A) (C - D) = 0

-- I.9: To bisect a given rectilinear angle.
Euclid.BookI.Prop9.angle_bisector_exists
  (A B C : EuclideanSpace ℝ (Fin 2)) (hBA : A ≠ B) (hBC : C ≠ B)
  (hangle : inner ℝ (A - B) (C - B) ≠ -(‖A - B‖ * ‖C - B‖))
  : ∃ D, inner ℝ (A - B) (D - B) / (‖A - B‖ * ‖D - B‖) =
        inner ℝ (C - B) (D - B) / (‖C - B‖ * ‖D - B‖)
```

## How to build

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd ~/Projects/lean-geometry
lake build
```

Requires:
- [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) (toolchain pinned in `lean-toolchain`)
- [mathlib4](https://github.com/leanprover-community/mathlib4)
- (Optional) [Lean Copilot](https://github.com/lean-dojo/LeanCopilot) for AI-assisted proof search

## Why this matters

Euclid's *Elements* is the foundation of Western mathematics — 2,300 years of
continuous study. Modern formalization (in Coq, Isabelle, Mizar, Lean) has
touched Euclid indirectly through general geometry libraries, but a systematic,
construction-by-construction formalization of Book I in mathlib has been missing.
This project contributes the first five propositions as a coherent, verified block.

## Future work

- Extend to I.10–I.48 (remaining Book I propositions)
- Contribute to mathlib4 as `Geometry/Euclidean/Euclid/`
- Add the compass-and-straightedge construction lemmas as reusable tactics
>>>>>>> 7d142bde02 (Euclid Book I: five novel theorems (I.1, I.2, I.3, I.7, I.9))
