/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Order.Atoms

/-! # Simple rings

A ring `R` is **simple** if it has only two two-sided ideals, namely `⊥` and `⊤`.

## Main definitions

- `IsSimpleRing`: a predicate expressing that a ring is simple.

-/


/--
A ring `R` is **simple** if it has only two two-sided ideals, namely `⊥` and `⊤`.
-/
@[mk_iff] class IsSimpleRing (R : Type*) [NonUnitalNonAssocRing R] : Prop where
  simple : IsSimpleOrder (TwoSidedIdeal R)

attribute [instance] IsSimpleRing.simple
