/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.NoZeroSMulDivisors.Defs

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
/-- An additive subgroup `H` of `G` is *saturated* if for all `n : ℕ` and `g : G` with `n•g ∈ H` we
have `n = 0` or `g ∈ H`. -/]
def Saturated (H : Subgroup G) : Prop :=
  ∀ ⦃n g⦄, g ^ n ∈ H → n = 0 ∨ g ∈ H

@[to_additive]
theorem saturated_iff_npow {H : Subgroup G} :
    Saturated H ↔ ∀ (n : ℕ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H :=
  Iff.rfl

@[to_additive]
theorem saturated_iff_zpow {H : Subgroup G} :
    Saturated H ↔ ∀ (n : ℤ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H := by
  constructor
  · intro hH n g hgn
    cases n with
    | ofNat n =>
      simp only [Int.natCast_eq_zero, Int.ofNat_eq_coe, zpow_natCast] at hgn ⊢
      exact hH hgn
    | negSucc n =>
      suffices g ^ (n + 1) ∈ H by
        refine (hH this).imp ?_ id
        simp only [IsEmpty.forall_iff, Nat.succ_ne_zero]
      simpa only [inv_mem_iff, zpow_negSucc] using hgn
  · intro h n g hgn
    specialize h n g
    simp only [Int.natCast_eq_zero, zpow_natCast] at h
    apply h hgn

end Subgroup

namespace AddSubgroup

theorem ker_saturated {A₁ A₂ : Type*} [AddGroup A₁] [AddMonoid A₂] [NoZeroSMulDivisors ℕ A₂]
    (f : A₁ →+ A₂) : f.ker.Saturated := by
  intro n g hg
  simpa only [f.mem_ker, nsmul_eq_smul, f.map_nsmul, smul_eq_zero] using hg

end AddSubgroup
