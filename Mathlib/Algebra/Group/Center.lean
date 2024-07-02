/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

#align_import group_theory.subsemigroup.center from "leanprover-community/mathlib"@"1ac8d4304efba9d03fa720d06516fac845aa5353"

/-!
# Centers of magmas and semigroups

## Main definitions

* `Set.center`: the center of a magma
* `Set.addCenter`: the center of an additive magma

See `Mathlib.GroupTheory.Subsemigroup.Center` for the definition of the center as a subsemigroup:
* `Subsemigroup.center`: the center of a semigroup
* `AddSubsemigroup.center`: the center of an additive semigroup

We provide `Submonoid.center`, `AddSubmonoid.center`, `Subgroup.center`, `AddSubgroup.center`,
`Subsemiring.center`, and `Subring.center` in other files.

-/

assert_not_exists Finset
assert_not_exists MonoidWithZero
assert_not_exists Subsemigroup

variable {M : Type*}

/-- Conditions for an element to be additively central -/
structure IsAddCentral [Add M] (z : M) : Prop where
  /-- addition commutes -/
  comm (a : M) : z + a = a + z
  /-- associative property for left addition -/
  left_assoc (b c : M) : z + (b + c) = (z + b) + c
  /-- middle associative addition property -/
  mid_assoc (a c : M) : (a + z) + c = a + (z + c)
  /-- associative property for right addition -/
  right_assoc (a b : M) : (a + b) + z = a + (b + z)

/-- Conditions for an element to be multiplicatively central -/
@[to_additive]
structure IsMulCentral [Mul M] (z : M) : Prop where
  /-- multiplication commutes -/
  comm (a : M) : z * a = a * z
  /-- associative property for left multiplication -/
  left_assoc (b c : M) : z * (b * c) = (z * b) * c
  /-- middle associative multiplication property -/
  mid_assoc (a c : M) : (a * z) * c = a * (z * c)
  /-- associative property for right multiplication -/
  right_assoc (a b : M) : (a * b) * z = a * (b * z)

attribute [mk_iff] IsMulCentral IsAddCentral
attribute [to_additive existing] isMulCentral_iff

namespace IsMulCentral

variable {a b c : M} [Mul M]

-- cf. `Commute.left_comm`
@[to_additive]
protected theorem left_comm (h : IsMulCentral a) (b c) : a * (b * c) = b * (a * c) := by
  simp only [h.comm, h.right_assoc]

-- cf. `Commute.right_comm`
@[to_additive]
protected theorem right_comm (h : IsMulCentral c) (a b) : a * b * c = a * c * b := by
  simp only [h.right_assoc, h.mid_assoc, h.comm]

end IsMulCentral

namespace Set

section Mul
variable (M) [Mul M]

/-- The center of a magma. -/
@[to_additive addCenter " The center of an additive magma. "]
def center : Set M :=
  { z | IsMulCentral z }
#align set.center Set.center
#align set.add_center Set.addCenter

-- Porting note: The `to_additive` version used to be `mem_addCenter` without the iff
@[to_additive mem_addCenter_iff]
theorem mem_center_iff {z : M} : z ∈ center M ↔ IsMulCentral z :=
  Iff.rfl
#align set.mem_center_iff Set.mem_center_iff
#align set.mem_add_center Set.mem_addCenter_iff

variable {M}

@[to_additive (attr := simp) add_mem_addCenter]
theorem mul_mem_center [Mul M] {z₁ z₂ : M} (hz₁ : z₁ ∈ Set.center M) (hz₂ : z₂ ∈ Set.center M) :
    z₁ * z₂ ∈ Set.center M where
  comm a := calc
    z₁ * z₂ * a = z₂ * z₁ * a := by rw [hz₁.comm]
    _ = z₂ * (z₁ * a) := by rw [hz₁.mid_assoc z₂]
    _ = (a * z₁) * z₂ := by rw [hz₁.comm, hz₂.comm]
    _ = a * (z₁ * z₂) := by rw [hz₂.right_assoc a z₁]
  left_assoc (b c : M) := calc
    z₁ * z₂ * (b * c) = z₁ * (z₂ * (b * c)) := by rw [hz₂.mid_assoc]
    _ = z₁ * ((z₂ * b) * c) := by rw [hz₂.left_assoc]
    _ = (z₁ * (z₂ * b)) * c := by rw [hz₁.left_assoc]
    _ = z₁ * z₂ * b * c := by rw [hz₂.mid_assoc]
  mid_assoc (a c : M) := calc
    a * (z₁ * z₂) * c = ((a * z₁) * z₂) * c := by rw [hz₁.mid_assoc]
    _ = (a * z₁) * (z₂ * c) := by rw [hz₂.mid_assoc]
    _ = a * (z₁ * (z₂ * c)) := by rw [hz₁.mid_assoc]
    _ = a * (z₁ * z₂ * c) := by rw [hz₂.mid_assoc]
  right_assoc (a b : M) := calc
    a * b * (z₁ * z₂) = ((a * b) * z₁) * z₂ := by rw [hz₂.right_assoc]
    _ = (a * (b * z₁)) * z₂ := by rw [hz₁.right_assoc]
    _ =  a * ((b * z₁) * z₂) := by rw [hz₂.right_assoc]
    _ = a * (b * (z₁ * z₂)) := by rw [hz₁.mid_assoc]
#align set.mul_mem_center Set.mul_mem_center
#align set.add_mem_add_center Set.add_mem_addCenter

end Mul

section Semigroup
variable [Semigroup M]

@[to_additive]
theorem _root_.Semigroup.mem_center_iff {z : M} :
    z ∈ Set.center M ↔ ∀ g, g * z = z * g := ⟨fun a g ↦ by rw [IsMulCentral.comm a g],
  fun h ↦ ⟨fun _ ↦ (Commute.eq (h _)).symm, fun _ _ ↦ (mul_assoc z _ _).symm,
  fun _ _ ↦ mul_assoc _ z _, fun _ _ ↦ mul_assoc _ _ z⟩ ⟩

variable (M)

-- TODO Add `instance : Decidable (IsMulCentral a)` for `instance decidableMemCenter [Mul M]`
instance decidableMemCenter [∀ a : M, Decidable <| ∀ b : M, b * a = a * b] :
    DecidablePred (· ∈ center M) := fun _ => decidable_of_iff' _ (Semigroup.mem_center_iff)
#align set.decidable_mem_center Set.decidableMemCenter

end Semigroup

section CommSemigroup
variable (M)

@[to_additive (attr := simp) addCenter_eq_univ]
theorem center_eq_univ [CommSemigroup M] : center M = univ :=
  (Subset.antisymm (subset_univ _)) fun _ _ => Semigroup.mem_center_iff.mpr (fun _ => mul_comm _ _)
#align set.center_eq_univ Set.center_eq_univ
#align set.add_center_eq_univ Set.addCenter_eq_univ

end CommSemigroup

variable (M)

@[to_additive (attr := simp) zero_mem_addCenter]
theorem one_mem_center [MulOneClass M] : (1 : M) ∈ Set.center M where
  comm _  := by rw [one_mul, mul_one]
  left_assoc _ _ := by rw [one_mul, one_mul]
  mid_assoc _ _ := by rw [mul_one, one_mul]
  right_assoc _ _ := by rw [mul_one, mul_one]
#align set.one_mem_center Set.one_mem_center
#align set.zero_mem_add_center Set.zero_mem_addCenter

variable {M}

@[to_additive (attr := simp) neg_mem_addCenter]
theorem inv_mem_center [DivisionMonoid M] {a : M} (ha : a ∈ Set.center M) : a⁻¹ ∈ Set.center M := by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← inv_inj, mul_inv_rev, inv_inv, ha.comm, mul_inv_rev, inv_inv]
#align set.inv_mem_center Set.inv_mem_centerₓ
#align set.neg_mem_add_center Set.neg_mem_addCenterₓ

@[to_additive subset_addCenter_add_units]
theorem subset_center_units [Monoid M] : ((↑) : Mˣ → M) ⁻¹' center M ⊆ Set.center Mˣ :=
  fun _ ha => by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← Units.eq_iff, Units.val_mul, Units.val_mul, ha.comm]
#align set.subset_center_units Set.subset_center_units
#align set.subset_add_center_add_units Set.subset_addCenter_add_units

@[simp]
theorem units_inv_mem_center [Monoid M] {a : Mˣ} (ha : ↑a ∈ Set.center M) :
    ↑a⁻¹ ∈ Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.units_inv_right <| ha ·)

@[simp]
theorem invOf_mem_center [Monoid M] {a : M} [Invertible a] (ha : a ∈ Set.center M) :
    ⅟a ∈ Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.invOf_right <| ha ·)

@[to_additive (attr := simp) sub_mem_addCenter]
theorem div_mem_center [DivisionMonoid M]
    {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a / b ∈ Set.center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center hb)
#align set.div_mem_center Set.div_mem_centerₓ
#align set.sub_mem_add_center Set.sub_mem_addCenterₓ

end Set
