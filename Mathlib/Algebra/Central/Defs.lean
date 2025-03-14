/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Central Algebras

In this file we define the predicate `Algebra.IsCentral K D` where `K` is a commutative ring and `D`
is a (not necessarily commutative) `K`-algebra.

## Main definitions

- `Algebra.IsCentral K D` : `D` is a central algebra over `K` iff the center of `D` is exactly `K`.

## Implementation notes

We require the `K`-center of `D` to be smaller than or equal to the smallest subalgebra so that when
we prove something is central, we don't need to prove `⊥ ≤ center K D` even though this
direction is trivial.

### Central Simple Algebras

To define central simple algebras, we could do the following:
```lean
class Algebra.IsCentralSimple (K : Type u) [Field K] (D : Type v) [Ring D] [Algebra K D] where
  [is_central : IsCentral K D]
  [is_simple : IsSimpleRing D]
```
but an instance of `[Algebra.IsCentralSimple K D]` would not imply `[IsSimpleRing D]` because of
synthesization orders (`K` cannot be inferred). Thus, to obtain a central simple `K`-algebra `D`,
one should use `Algebra.IsCentral K D` and `IsSimpleRing D` separately.

Note that the predicate `Algebra.IsCentral K D` and `IsSimpleRing D` makes sense just for `K` a
`CommRing` but it doesn't give the right definition for central simple algebra; for a commutative
ring base, one should use the theory of Azumaya algebras. In fact ideals of `K` immediately give
rise to nontrivial quotients of `D` so there are no central simple algebras in this case according
to our definition, if `K` is not a field.
The theory of central simple algebras really is a theory over fields.

Thus to declare a central simple algebra, one should use the following:
```lean
variable (k D : Type*) [Field k] [Ring D] [Algebra k D]
variable [Algebra.IsCentral k D] [IsSimpleRing D]
variable [FiniteDimensional k D]
```
where `FiniteDimensional k D` is almost always assumed in most references, but some results do not
need this assumption.

## Tags
central algebra, center, simple ring, central simple algebra

-/

universe u v

/--
For a commutative ring `K` and a `K`-algebra `D`, we say that `D` is a central algebra over `K` if
the center of `D` is the image of `K` in `D`.
-/
class Algebra.IsCentral
    (K : Type u) [CommSemiring K] (D : Type v) [Semiring D] [Algebra K D] : Prop where
  out : Subalgebra.center K D ≤ ⊥
