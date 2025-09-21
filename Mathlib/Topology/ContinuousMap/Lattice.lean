/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Nicolò Cavalleri
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Order.Group.Lattice
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Continuous maps as a lattice ordered group
-/


/-!
We now provide formulas for `f ⊓ g` and `f ⊔ g`, where `f g : C(α, β)`,
in terms of `ContinuousMap.abs`.
-/

namespace ContinuousMap

variable {α : Type*} [TopologicalSpace α]
variable {β : Type*} [TopologicalSpace β]

section Lattice

/-! `C(α, β)`is a lattice ordered group -/

@[to_additive]
instance [PartialOrder β] [CommMonoid β] [IsOrderedMonoid β] [ContinuousMul β] :
    IsOrderedMonoid C(α, β) where
  mul_le_mul_left _ _ hfg c x := mul_le_mul_left' (hfg x) (c x)

variable [Group β] [IsTopologicalGroup β] [Lattice β] [TopologicalLattice β]

@[to_additive (attr := simp, norm_cast)]
lemma coe_mabs (f : C(α, β)) : ⇑|f|ₘ = |⇑f|ₘ := rfl

@[to_additive (attr := simp)]
lemma mabs_apply (f : C(α, β)) (x : α) : |f|ₘ x = |f x|ₘ := rfl

end Lattice

end ContinuousMap
