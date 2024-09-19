/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang, Kevin Buzzard
-/

import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Characteristic predicate for central simple algebras

In this file we define the predicate `IsCentralSimple K D` where `K` is a field
and `D` is a (noncommutative) `K`-algebra.

Note that the predicate makes sense just for `K` a `CommRing` but it doesn't give the
right definition; for a commutative ring base, one should use the theory of Azumaya algebras.
This adds an extra layer of complication which we don't need. In fact ideals of `K`
immediately give rise to nontrivial quotients of `D` so there are no central simple
algebras in this case according to our definition.

## Main definitions

- `Algebra.IsCentralSimple K D` : `D` is a central simple algebra over `K` iff the center of `D`
  is exactly `K` and `D` is a simple ring.

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
class Algebra.IsCentralSimple
    (K : Type u) [Field K] (D : Type v) [Ring D] [Algebra K D] : Prop where
  is_central : Subalgebra.center K D ≤ ⊥
  [is_simple : IsSimpleRing D]
