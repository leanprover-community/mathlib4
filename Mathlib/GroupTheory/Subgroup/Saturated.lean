/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.GroupTheory.Subgroup.Basic

#align_import group_theory.subgroup.saturated from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Saturated subgroups

## Tags
subgroup, subgroups

-/


namespace Subgroup

variable {G : Type*} [Group G]

/-- A subgroup `H` of `G` is *saturated* if for all `n : ℕ` and `g : G` with `g^n ∈ H`
we have `n = 0` or `g ∈ H`. -/
@[to_additive
      "An additive subgroup `H` of `G` is *saturated* if for all `n : ℕ` and `g : G` with `n•g ∈ H`
      we have `n = 0` or `g ∈ H`."]
def Saturated (H : Subgroup G) : Prop :=
  ∀ ⦃n g⦄, g ^ n ∈ H → n = 0 ∨ g ∈ H
#align subgroup.saturated Subgroup.Saturated
#align add_subgroup.saturated AddSubgroup.Saturated

@[to_additive]
theorem saturated_iff_npow {H : Subgroup G} :
    Saturated H ↔ ∀ (n : ℕ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H :=
  Iff.rfl
#align subgroup.saturated_iff_npow Subgroup.saturated_iff_npow
#align add_subgroup.saturated_iff_nsmul AddSubgroup.saturated_iff_nsmul

@[to_additive]
theorem saturated_iff_zpow {H : Subgroup G} :
    Saturated H ↔ ∀ (n : ℤ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H := by
  constructor
  -- ⊢ Saturated H → ∀ (n : ℤ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H
  · intros hH n g hgn
    -- ⊢ n = 0 ∨ g ∈ H
    induction' n with n n
    -- ⊢ Int.ofNat n = 0 ∨ g ∈ H
    · simp only [Int.coe_nat_eq_zero, Int.ofNat_eq_coe, zpow_ofNat] at hgn ⊢
      -- ⊢ n = 0 ∨ g ∈ H
      exact hH hgn
      -- 🎉 no goals
    · suffices g ^ (n + 1) ∈ H by
        refine' (hH this).imp _ id
        simp only [IsEmpty.forall_iff, Nat.succ_ne_zero]
      simpa only [inv_mem_iff, zpow_negSucc] using hgn
      -- 🎉 no goals
  · intro h n g hgn
    -- ⊢ n = 0 ∨ g ∈ H
    specialize h n g
    -- ⊢ n = 0 ∨ g ∈ H
    simp only [Int.coe_nat_eq_zero, zpow_ofNat] at h
    -- ⊢ n = 0 ∨ g ∈ H
    apply h hgn
    -- 🎉 no goals
#align subgroup.saturated_iff_zpow Subgroup.saturated_iff_zpow
#align add_subgroup.saturated_iff_zsmul AddSubgroup.saturated_iff_zsmul

end Subgroup

namespace AddSubgroup

theorem ker_saturated {A₁ A₂ : Type*} [AddCommGroup A₁] [AddCommGroup A₂] [NoZeroSMulDivisors ℕ A₂]
    (f : A₁ →+ A₂) : f.ker.Saturated := by
  intro n g hg
  -- ⊢ n = 0 ∨ g ∈ AddMonoidHom.ker f
  simpa only [f.mem_ker, nsmul_eq_smul, f.map_nsmul, smul_eq_zero] using hg
  -- 🎉 no goals
#align add_subgroup.ker_saturated AddSubgroup.ker_saturated

end AddSubgroup
