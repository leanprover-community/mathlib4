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

namespace Finset

variable {α : Type*} [DecidableEq α] [InvolutiveInv α] {s : Finset α}

@[to_additive (attr := simp)]
lemma isSelfInv_coe_iff : IsSelfInv (s : Set α) ↔ IsSelfInv s := by
  simp [isSelfInv_iff, Set.ext_iff, Finset.ext_iff]

@[to_additive]
lemma isSelfInv_iff_forall_inv_mem : IsSelfInv s ↔ ∀ ⦃x⦄, x ∈ s → x⁻¹ ∈ s := by
  simp only [← isSelfInv_coe_iff, _root_.isSelfInv_iff_forall_inv_mem, mem_coe]

end Finset
