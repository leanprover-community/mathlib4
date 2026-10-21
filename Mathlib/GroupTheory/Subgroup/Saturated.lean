/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Saturated subgroups

## Tags
subgroup, subgroups

-/

@[expose] public section


namespace Submonoid

variable {G : Type*} [Monoid G]

/-- A submonoid `H` of `G` is *saturated* if for all `n : ℕ` and `g : G` with `g^n ∈ H` we have
`n = 0` or `g ∈ H`. We use the name `PowSaturated` to distinguish from `Submonoid.MulSaturated`. -/
@[to_additive
/-- An additive submonoid `H` of `G` is *saturated* if for all `n : ℕ` and `g : G` with
`n•g ∈ H` we have `n = 0` or `g ∈ H`. We use the name `NSMulSaturated` to distinguish from
`Submonoid.MulSaturated`. -/]
def PowSaturated (H : Submonoid G) : Prop :=
  ∀ ⦃n g⦄, g ^ n ∈ H → n = 0 ∨ g ∈ H

@[to_additive]
theorem powSaturated_iff_npow {H : Submonoid G} :
    PowSaturated H ↔ ∀ (n : ℕ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H :=
  Iff.rfl

end Submonoid

namespace Subgroup

variable {G : Type*} [Group G]

@[to_additive]
theorem saturated_iff_zpow {H : Subgroup G} :
    H.PowSaturated ↔ ∀ (n : ℤ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H := by
  refine ⟨fun h n g hgn ↦ ?_, fun h n g hgn ↦ by simpa using h n g (by simpa using hgn)⟩
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simpa using h (by simpa using hgn)

end Subgroup

namespace AddSubmonoid

theorem ker_saturated {A₁ A₂ : Type*} [AddGroup A₁] [AddMonoid A₂] [IsAddTorsionFree A₂]
    (f : A₁ →+ A₂) : f.ker.NSMulSaturated := by simp [NSMulSaturated, or_comm]

end AddSubmonoid
