/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Group.Submonoid.Pointwise

#align_import group_theory.submonoid.inverses from "leanprover-community/mathlib"@"59694bd07f0a39c5beccba34bd9f413a160782bf"

/-!

# Submonoid of inverses

Given a submonoid `N` of a monoid `M`, we define the submonoid `N.leftInv` as the submonoid of
left inverses of `N`. When `M` is commutative, we may define `fromCommLeftInv : N.leftInv →* N`
since the inverses are unique. When `N ≤ IsUnit.Submonoid M`, this is precisely
the pointwise inverse of `N`, and we may define `leftInvEquiv : S.leftInv ≃* S`.

For the pointwise inverse of submonoids of groups, please refer to
`Mathlib.GroupTheory.Submonoid.Pointwise`.

`N.leftInv` is distinct from `N.units`, which is the subgroup of `Mˣ` containing all units that are
in `N`. See the implementation notes of `Mathlib.GroupTheory.Submonoid.Units` for more details on
related constructions.

## TODO

Define the submonoid of right inverses and two-sided inverses.
See the comments of #10679 for a possible implementation.

-/


variable {M : Type*}

namespace Submonoid

@[to_additive]
noncomputable instance [Monoid M] : Group (IsUnit.submonoid M) :=
  { inferInstanceAs (Monoid (IsUnit.submonoid M)) with
    inv := fun x ↦ ⟨x.prop.unit⁻¹.val, x.prop.unit⁻¹.isUnit⟩
    mul_left_inv := fun x ↦
      Subtype.ext ((Units.val_mul x.prop.unit⁻¹ _).trans x.prop.unit.inv_val) }

@[to_additive]
noncomputable instance [CommMonoid M] : CommGroup (IsUnit.submonoid M) :=
  { inferInstanceAs (Group (IsUnit.submonoid M)) with
    mul_comm := fun a b ↦ by convert mul_comm a b }

@[to_additive]
theorem IsUnit.Submonoid.coe_inv [Monoid M] (x : IsUnit.submonoid M) :
    ↑x⁻¹ = (↑x.prop.unit⁻¹ : M) :=
  rfl
#align submonoid.is_unit.submonoid.coe_inv Submonoid.IsUnit.Submonoid.coe_inv
#align add_submonoid.is_unit.submonoid.coe_neg AddSubmonoid.IsUnit.Submonoid.coe_neg

section Monoid

variable [Monoid M] (S : Submonoid M)

/-- `S.leftInv` is the submonoid containing all the left inverses of `S`. -/
@[to_additive
      "`S.leftNeg` is the additive submonoid containing all the left additive inverses of `S`."]
def leftInv : Submonoid M where
  carrier := { x : M | ∃ y : S, x * y = 1 }
  one_mem' := ⟨1, mul_one 1⟩
  mul_mem' := fun {a} _b ⟨a', ha⟩ ⟨b', hb⟩ ↦
    ⟨b' * a', by simp only [coe_mul, ← mul_assoc, mul_assoc a, hb, mul_one, ha]⟩
#align submonoid.left_inv Submonoid.leftInv
#align add_submonoid.left_neg AddSubmonoid.leftNeg

@[to_additive]
theorem leftInv_leftInv_le : S.leftInv.leftInv ≤ S := by
  rintro x ⟨⟨y, z, h₁⟩, h₂ : x * y = 1⟩
  convert z.prop
  rw [← mul_one x, ← h₁, ← mul_assoc, h₂, one_mul]
#align submonoid.left_inv_left_inv_le Submonoid.leftInv_leftInv_le
#align add_submonoid.left_neg_left_neg_le AddSubmonoid.leftNeg_leftNeg_le

@[to_additive]
theorem unit_mem_leftInv (x : Mˣ) (hx : (x : M) ∈ S) : ((x⁻¹ : _) : M) ∈ S.leftInv :=
  ⟨⟨x, hx⟩, x.inv_val⟩
#align submonoid.unit_mem_left_inv Submonoid.unit_mem_leftInv
#align add_submonoid.add_unit_mem_left_neg AddSubmonoid.addUnit_mem_leftNeg

@[to_additive]
theorem leftInv_leftInv_eq (hS : S ≤ IsUnit.submonoid M) : S.leftInv.leftInv = S := by
  refine le_antisymm S.leftInv_leftInv_le ?_
  intro x hx
  have : x = ((hS hx).unit⁻¹⁻¹ : Mˣ) := by
    rw [inv_inv (hS hx).unit]
    rfl
  rw [this]
  exact S.leftInv.unit_mem_leftInv _ (S.unit_mem_leftInv _ hx)
#align submonoid.left_inv_left_inv_eq Submonoid.leftInv_leftInv_eq
#align add_submonoid.left_neg_left_neg_eq AddSubmonoid.leftNeg_leftNeg_eq

/-- The function from `S.leftInv` to `S` sending an element to its right inverse in `S`.
This is a `MonoidHom` when `M` is commutative. -/
@[to_additive
      "The function from `S.leftAdd` to `S` sending an element to its right additive
inverse in `S`. This is an `AddMonoidHom` when `M` is commutative."]
noncomputable def fromLeftInv : S.leftInv → S := fun x ↦ x.prop.choose
#align submonoid.from_left_inv Submonoid.fromLeftInv
#align add_submonoid.from_left_neg AddSubmonoid.fromLeftNeg

@[to_additive (attr := simp)]
theorem mul_fromLeftInv (x : S.leftInv) : (x : M) * S.fromLeftInv x = 1 :=
  x.prop.choose_spec
#align submonoid.mul_from_left_inv Submonoid.mul_fromLeftInv
#align add_submonoid.add_from_left_neg AddSubmonoid.add_fromLeftNeg

@[to_additive (attr := simp)]
theorem fromLeftInv_one : S.fromLeftInv 1 = 1 :=
  (one_mul _).symm.trans (Subtype.eq <| S.mul_fromLeftInv 1)
#align submonoid.from_left_inv_one Submonoid.fromLeftInv_one
#align add_submonoid.from_left_neg_zero AddSubmonoid.fromLeftNeg_zero

end Monoid

section CommMonoid

variable [CommMonoid M] (S : Submonoid M)

@[to_additive (attr := simp)]
theorem fromLeftInv_mul (x : S.leftInv) : (S.fromLeftInv x : M) * x = 1 := by
  rw [mul_comm, mul_fromLeftInv]
#align submonoid.from_left_inv_mul Submonoid.fromLeftInv_mul
#align add_submonoid.from_left_neg_add AddSubmonoid.fromLeftNeg_add

@[to_additive]
theorem leftInv_le_isUnit : S.leftInv ≤ IsUnit.submonoid M := fun x ⟨y, hx⟩ ↦
  ⟨⟨x, y, hx, mul_comm x y ▸ hx⟩, rfl⟩
#align submonoid.left_inv_le_is_unit Submonoid.leftInv_le_isUnit
#align add_submonoid.left_neg_le_is_add_unit AddSubmonoid.leftNeg_le_isAddUnit

@[to_additive]
theorem fromLeftInv_eq_iff (a : S.leftInv) (b : M) :
    (S.fromLeftInv a : M) = b ↔ (a : M) * b = 1 := by
  rw [← IsUnit.mul_right_inj (leftInv_le_isUnit _ a.prop), S.mul_fromLeftInv, eq_comm]
#align submonoid.from_left_inv_eq_iff Submonoid.fromLeftInv_eq_iff
#align add_submonoid.from_left_neg_eq_iff AddSubmonoid.fromLeftNeg_eq_iff

/-- The `MonoidHom` from `S.leftInv` to `S` sending an element to its right inverse in `S`. -/
@[to_additive (attr := simps)
    "The `AddMonoidHom` from `S.leftNeg` to `S` sending an element to its
    right additive inverse in `S`."]
noncomputable def fromCommLeftInv : S.leftInv →* S where
  toFun := S.fromLeftInv
  map_one' := S.fromLeftInv_one
  map_mul' x y :=
    Subtype.ext <| by
      rw [fromLeftInv_eq_iff, mul_comm x, Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc, ←
        mul_assoc (x : M), mul_fromLeftInv, one_mul, mul_fromLeftInv]
#align submonoid.from_comm_left_inv Submonoid.fromCommLeftInv
#align add_submonoid.from_comm_left_neg AddSubmonoid.fromCommLeftNeg

variable (hS : S ≤ IsUnit.submonoid M)

/-- The submonoid of pointwise inverse of `S` is `MulEquiv` to `S`. -/
@[to_additive (attr := simps apply) "The additive submonoid of pointwise additive inverse of `S` is
`AddEquiv` to `S`."]
noncomputable def leftInvEquiv : S.leftInv ≃* S :=
  { S.fromCommLeftInv with
    invFun := fun x ↦ by
      choose x' hx using hS x.prop
      exact ⟨x'.inv, x, hx ▸ x'.inv_val⟩
    left_inv := fun x ↦
      Subtype.eq <| by
        dsimp only; generalize_proofs h; rw [← h.choose.mul_left_inj]
        conv => rhs; rw [h.choose_spec]
        exact h.choose.inv_val.trans (S.mul_fromLeftInv x).symm
    right_inv := fun x ↦ by
      dsimp only [fromCommLeftInv]
      ext
      rw [fromLeftInv_eq_iff]
      convert (hS x.prop).choose.inv_val
      exact (hS x.prop).choose_spec.symm }
#align submonoid.left_inv_equiv Submonoid.leftInvEquiv
#align add_submonoid.left_neg_equiv AddSubmonoid.leftNegEquiv

@[to_additive (attr := simp)]
theorem fromLeftInv_leftInvEquiv_symm (x : S) : S.fromLeftInv ((S.leftInvEquiv hS).symm x) = x :=
  (S.leftInvEquiv hS).right_inv x
#align submonoid.from_left_inv_left_inv_equiv_symm Submonoid.fromLeftInv_leftInvEquiv_symm
#align add_submonoid.from_left_neg_left_neg_equiv_symm AddSubmonoid.fromLeftNeg_leftNegEquiv_symm

@[to_additive (attr := simp)]
theorem leftInvEquiv_symm_fromLeftInv (x : S.leftInv) :
    (S.leftInvEquiv hS).symm (S.fromLeftInv x) = x :=
  (S.leftInvEquiv hS).left_inv x
#align submonoid.left_inv_equiv_symm_from_left_inv Submonoid.leftInvEquiv_symm_fromLeftInv
#align add_submonoid.left_neg_equiv_symm_from_left_neg AddSubmonoid.leftNegEquiv_symm_fromLeftNeg

@[to_additive]
theorem leftInvEquiv_mul (x : S.leftInv) : (S.leftInvEquiv hS x : M) * x = 1 := by
  simpa only [leftInvEquiv_apply, fromCommLeftInv] using fromLeftInv_mul S x
#align submonoid.left_inv_equiv_mul Submonoid.leftInvEquiv_mul
#align add_submonoid.left_neg_equiv_add AddSubmonoid.leftNegEquiv_add

@[to_additive]
theorem mul_leftInvEquiv (x : S.leftInv) : (x : M) * S.leftInvEquiv hS x = 1 := by
  simp only [leftInvEquiv_apply, fromCommLeftInv, mul_fromLeftInv]
#align submonoid.mul_left_inv_equiv Submonoid.mul_leftInvEquiv
#align add_submonoid.add_left_neg_equiv AddSubmonoid.add_leftNegEquiv

@[to_additive (attr := simp)]
theorem leftInvEquiv_symm_mul (x : S) : ((S.leftInvEquiv hS).symm x : M) * x = 1 := by
  convert S.mul_leftInvEquiv hS ((S.leftInvEquiv hS).symm x)
  simp
#align submonoid.left_inv_equiv_symm_mul Submonoid.leftInvEquiv_symm_mul
#align add_submonoid.left_neg_equiv_symm_add AddSubmonoid.leftNegEquiv_symm_add

@[to_additive (attr := simp)]
theorem mul_leftInvEquiv_symm (x : S) : (x : M) * (S.leftInvEquiv hS).symm x = 1 := by
  convert S.leftInvEquiv_mul hS ((S.leftInvEquiv hS).symm x)
  simp
#align submonoid.mul_left_inv_equiv_symm Submonoid.mul_leftInvEquiv_symm
#align add_submonoid.add_left_neg_equiv_symm AddSubmonoid.add_leftNegEquiv_symm

end CommMonoid

section Group

variable [Group M] (S : Submonoid M)

open Pointwise

@[to_additive]
theorem leftInv_eq_inv : S.leftInv = S⁻¹ :=
  Submonoid.ext fun _ ↦
    ⟨fun h ↦ Submonoid.mem_inv.mpr ((inv_eq_of_mul_eq_one_right h.choose_spec).symm ▸
      h.choose.prop),
      fun h ↦ ⟨⟨_, h⟩, mul_right_inv _⟩⟩
#align submonoid.left_inv_eq_inv Submonoid.leftInv_eq_inv
#align add_submonoid.left_neg_eq_neg AddSubmonoid.leftNeg_eq_neg

@[to_additive (attr := simp)]
theorem fromLeftInv_eq_inv (x : S.leftInv) : (S.fromLeftInv x : M) = (x : M)⁻¹ := by
  rw [← mul_right_inj (x : M), mul_right_inv, mul_fromLeftInv]
#align submonoid.from_left_inv_eq_inv Submonoid.fromLeftInv_eq_inv
#align add_submonoid.from_left_neg_eq_neg AddSubmonoid.fromLeftNeg_eq_neg

end Group

section CommGroup

variable [CommGroup M] (S : Submonoid M) (hS : S ≤ IsUnit.submonoid M)

@[to_additive (attr := simp)]
theorem leftInvEquiv_symm_eq_inv (x : S) : ((S.leftInvEquiv hS).symm x : M) = (x : M)⁻¹ := by
  rw [← mul_right_inj (x : M), mul_right_inv, mul_leftInvEquiv_symm]
#align submonoid.left_inv_equiv_symm_eq_inv Submonoid.leftInvEquiv_symm_eq_inv
#align add_submonoid.left_neg_equiv_symm_eq_neg AddSubmonoid.leftNegEquiv_symm_eq_neg

end CommGroup

end Submonoid
