/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Central Algebras

In this file we define the predicate `Algebra.IsCentral K D` where `K` is a commutative ring and `D`
is a (not necessarily commutative) `K`-algebra.

## Main definitions

- `Algebra.IsCentral K D` : `D` is a central algebra over `K` iff the center of `D` is exactly `K`.

## Implementation notes

We require the `K`-center of `D` to be smaller than or equal to the smallest subalgebra so that when
we prove something is central simple, there we don't need to prove `⊥ ≤ center K D` though this
direction is trivial.

-/

universe u v

/--
For a field `K` and a `K`-algebra `D`, we say that `D` is a central algebra over `K` if the center
of `D` is exactly `K` and that `D` is a simple ring.
-/
class Algebra.IsCentral
    (K : Type u) [CommSemiring K] (D : Type v) [Semiring D] [Algebra K D] : Prop where
  out : Subalgebra.center K D ≤ ⊥
