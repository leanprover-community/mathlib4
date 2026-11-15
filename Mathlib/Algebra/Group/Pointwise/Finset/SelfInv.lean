/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.SelfInv

/-!
# Self-inverse finsets

This file specialises `IsSelfInv` to finsets equipped with the pointwise inversion.

See also `Algebra/Group/Pointwise/Set/SelfInv.lean` for the set version.

-/

@[expose] public section

open scoped Pointwise

/- Ensure that `@[to_additive]` uses the right namespace. -/
insert_to_additive_translation Finset.IsSelfInv Finset.IsSelfNeg

namespace Finset

variable {α : Type*} [DecidableEq α] [InvolutiveInv α] {s : Finset α}

@[to_additive (attr := simp)]
lemma isSelfInv_coe_iff : IsSelfInv (s : Set α) ↔ IsSelfInv s := by
  simp [isSelfInv_iff, Set.ext_iff, Finset.ext_iff]

@[to_additive]
alias ⟨IsSelfInv.of_coe_finset, IsSelfInv.coe_finset⟩ := isSelfInv_coe_iff

@[to_additive]
lemma isSelfInv_iff_forall_inv_mem : IsSelfInv s ↔ ∀ ⦃x⦄, x ∈ s → x⁻¹ ∈ s := by
  simp [← isSelfInv_coe_iff, Set.isSelfInv_iff_forall_inv_mem]

end Finset
