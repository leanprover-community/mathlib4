/-
Copyright (c) 2024 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
import Mathlib.Order.CompleteLattice.SetLike

/-!
# Trees in the sense of descriptive set theory

This file defines trees of depth `ω` in the sense of descriptive set theory as sets of finite
sequences that are stable under taking prefixes.

## Main declarations

* `tree A`: a (possibly infinite) tree of depth at most `ω` with nodes in `A`
-/

namespace Descriptive

/-- A tree is a set of finite sequences, implemented as `List A`, that is stable under
  taking prefixes. For the definition we use the equivalent property `x ++ [a] ∈ T → x ∈ T`,
  which is more convenient to check. We define `tree A` as a complete sublattice of
  `Set (List A)`, which coerces to the type of trees on `A`. -/
def tree (A : Type*) : CompleteSublattice (Set (List A)) :=
  CompleteSublattice.mk' {T | ∀ ⦃x : List A⦄ ⦃a : A⦄, x ++ [a] ∈ T → x ∈ T}
    (by rintro S hS x a ⟨t, ht, hx⟩; use t, ht, hS ht hx)
    (by rintro S hS x a h T hT; exact hS hT <| h T hT)

@[simps!] instance (A : Type*) : SetLike (tree A) (List A) := SetLike.instSubtypeSet

end Descriptive
