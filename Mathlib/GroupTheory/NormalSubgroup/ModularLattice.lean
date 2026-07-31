/-
Copyright (c) 2026 Diwen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diwen Yu
-/
module

public import Mathlib.GroupTheory.NormalSubgroup.Basic
public import Mathlib.Order.ModularLattice

/-!
# Modular lattice of normal subgroups

This file proves the modular law for the complete lattice of normal subgroups of an arbitrary
group. This is the lattice-theoretic input for mathlib's abstract Jordan–Hölder construction.
-/

@[expose] public section

namespace NormalSubgroup

variable {G : Type*} [Group G]

/-- The normal subgroups of an arbitrary group form a modular lattice. -/
@[to_additive /-- The normal additive subgroups of an arbitrary additive group form a modular
lattice. -/]
instance : IsModularLattice (NormalSubgroup G) where
  sup_inf_le_assoc_of_le := by
    intro x y z h g hg
    change g ∈ (x.toSubgroup ⊔ y.toSubgroup) ⊓ z.toSubgroup at hg
    change g ∈ x.toSubgroup ⊔ (y.toSubgroup ⊓ z.toSubgroup)
    rw [← SetLike.mem_coe, Subgroup.normal_mul]
    rw [Subgroup.mul_inf_assoc _ _ _ h]
    change g ∈ (x.toSubgroup ⊔ y.toSubgroup) ∧ g ∈ z.toSubgroup at hg
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg
    exact hg

end NormalSubgroup
