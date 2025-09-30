/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.CategoryTheory.Category.Pointed.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Non-abelian group cohomology

Let `G` be a group acting on another (not necessarily abelian) group `A`, in this file we define
`H⁰(G, A)` and `H¹(G, A)`, and prove some basic properties about it.

## Main Results

## Reference

-/

universe u

namespace groupCohomology

namespace nonAbelian

section basic

abbrev NonAbelianRep (G : Type u) [Monoid G] := Action AddMonCat.{u} G

variable (G : Type u) [Monoid G]

instance : CoeSort (NonAbelianRep G) (Type u) := ⟨fun V ↦ V.V⟩

instance (A : NonAbelianRep G) : DistribMulAction G A := sorry

end basic

section H0

variable {G : Type u} [Monoid G] (A : NonAbelianRep G)

def H0 : AddSubmonoid A where
  carrier := setOf fun v => ∀ g : G, g • v = v
  add_mem' := sorry
  zero_mem' := sorry

end H0

end nonAbelian

end groupCohomology
