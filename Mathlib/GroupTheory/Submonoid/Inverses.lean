/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Group.Submonoid.Pointwise

/-!

# Submonoid of inverses

Given a submonoid `N` of a monoid `M`, we define the submonoid `N.leftInv` as the submonoid of
left inverses of `N`. When `M` is commutative, we may define `fromCommLeftInv : N.leftInv →* N`
since the inverses are unique. When `N ≤ IsUnit.Submonoid M`, this is precisely
the pointwise inverse of `N`, and we may define `leftInvEquiv : S.leftInv ≃* S`.

For the pointwise inverse of submonoids of groups, please refer to the file
`Mathlib/Algebra/Group/Submonoid/Pointwise.lean`.

`N.leftInv` is distinct from `N.units`, which is the subgroup of `Mˣ` containing all units that are
in `N`. See the implementation notes of `Mathlib/GroupTheory/Submonoid/Units.lean` for more details
on related constructions.

## TODO

Define the submonoid of right inverses and two-sided inverses.
See the comments of https://github.com/leanprover-community/mathlib4/pull/10679 for a possible
implementation.
-/


variable {M : Type*}

namespace Submonoid

@[to_additive]
noncomputable instance [Monoid M] : Group (IsUnit.submonoid M) :=
  { inferInstanceAs (Monoid (IsUnit.submonoid M)) with
    inv := fun x ↦ ⟨x.prop.unit⁻¹.val, x.prop.unit⁻¹.isUnit⟩
    inv_mul_cancel := fun x ↦
      Subtype.ext ((Units.val_mul x.prop.unit⁻¹ _).trans x.prop.unit.inv_val) }

@[to_additive]
noncomputable instance [CommMonoid M] : CommGroup (IsUnit.submonoid M) :=
  { inferInstanceAs (Group (IsUnit.submonoid M)) with
    mul_comm := fun a b ↦ by convert mul_comm a b }

@[to_additive]
theorem IsUnit.Submonoid.coe_inv [Monoid M] (x : IsUnit.submonoid M) :
    ↑x⁻¹ = (↑x.prop.unit⁻¹ : M) :=
  rfl

section Monoid

variable [Monoid M] (S : Submonoid M)

/-- `S.leftInv` is the submonoid containing all the left inverses of `S`. -/
@[to_additive
/-- `S.leftNeg` is the additive submonoid containing all the left additive inverses of `S`. -/]
def leftInv : Submonoid M where
  carrier := { x : M | ∃ y : S, x * y = 1 }
  one_mem' := ⟨1, mul_one 1⟩
  mul_mem' := fun {a} _b ⟨a', ha⟩ ⟨b', hb⟩ ↦
    ⟨b' * a', by simp only [coe_mul, ← mul_assoc, mul_assoc a, hb, mul_one, ha]⟩

@[to_additive]
theorem leftInv_leftInv_le : S.leftInv.leftInv ≤ S := by
  rintro x ⟨⟨y, z, h₁⟩, h₂ : x * y = 1⟩
  convert z.prop
  rw [← mul_one x, ← h₁, ← mul_assoc, h₂, one_mul]

@[to_additive]
theorem unit_mem_leftInv (x : Mˣ) (hx : (x : M) ∈ S) : ((x⁻¹ :) : M) ∈ S.leftInv :=
  ⟨⟨x, hx⟩, x.inv_val⟩

@[to_additive]
theorem leftInv_leftInv_eq (hS : S ≤ IsUnit.submonoid M) : S.leftInv.leftInv = S := by
  refine le_antisymm S.leftInv_leftInv_le ?_
  intro x hx
  have : x = ((hS hx).unit⁻¹⁻¹ : Mˣ) := by
    rw [inv_inv (hS hx).unit]
    rfl
  rw [this]
  exact S.leftInv.unit_mem_leftInv _ (S.unit_mem_leftInv _ hx)

/-- The function from `S.leftInv` to `S` sending an element to its right inverse in `S`.
This is a `MonoidHom` when `M` is commutative. -/
@[to_additive
/-- The function from `S.leftAdd` to `S` sending an element to its right additive
inverse in `S`. This is an `AddMonoidHom` when `M` is commutative. -/]
noncomputable def fromLeftInv : S.leftInv → S := fun x ↦ x.prop.choose

@[to_additive (attr := simp)]
theorem mul_fromLeftInv (x : S.leftInv) : (x : M) * S.fromLeftInv x = 1 :=
  x.prop.choose_spec

@[to_additive (attr := simp)]
theorem fromLeftInv_one : S.fromLeftInv 1 = 1 :=
  (one_mul _).symm.trans (Subtype.eq <| S.mul_fromLeftInv 1)

end Monoid

section CommMonoid

variable [CommMonoid M] (S : Submonoid M)

@[to_additive (attr := simp)]
theorem fromLeftInv_mul (x : S.leftInv) : (S.fromLeftInv x : M) * x = 1 := by
  rw [mul_comm, mul_fromLeftInv]

@[to_additive]
theorem leftInv_le_isUnit : S.leftInv ≤ IsUnit.submonoid M := fun x ⟨y, hx⟩ ↦
  ⟨⟨x, y, hx, mul_comm x y ▸ hx⟩, rfl⟩

@[to_additive]
theorem fromLeftInv_eq_iff (a : S.leftInv) (b : M) :
    (S.fromLeftInv a : M) = b ↔ (a : M) * b = 1 := by
  rw [← IsUnit.mul_right_inj (leftInv_le_isUnit _ a.prop), S.mul_fromLeftInv, eq_comm]

/-- The `MonoidHom` from `S.leftInv` to `S` sending an element to its right inverse in `S`. -/
@[to_additive (attr := simps) /-- The `AddMonoidHom` from `S.leftNeg` to `S` sending an element to
its right additive inverse in  `S`. -/]
noncomputable def fromCommLeftInv : S.leftInv →* S where
  toFun := S.fromLeftInv
  map_one' := S.fromLeftInv_one
  map_mul' x y :=
    Subtype.ext <| by
      rw [fromLeftInv_eq_iff, mul_comm x, Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc, ←
        mul_assoc (x : M), mul_fromLeftInv, one_mul, mul_fromLeftInv]

variable (hS : S ≤ IsUnit.submonoid M)

/-- The submonoid of pointwise inverse of `S` is `MulEquiv` to `S`. -/
@[to_additive (attr := simps apply) /-- The additive submonoid of pointwise additive inverse of `S`
is `AddEquiv` to `S`. -/]
noncomputable def leftInvEquiv : S.leftInv ≃* S :=
  { S.fromCommLeftInv with
    invFun := fun x ↦ ⟨↑(hS x.2).unit⁻¹, x, by simp⟩
    left_inv := by
      intro x
      ext
      simp [← Units.mul_eq_one_iff_inv_eq]
    right_inv := by
      rintro ⟨x, hx⟩
      ext
      simp [fromLeftInv_eq_iff] }

@[to_additive (attr := simp)]
theorem fromLeftInv_leftInvEquiv_symm (x : S) : S.fromLeftInv ((S.leftInvEquiv hS).symm x) = x :=
  (S.leftInvEquiv hS).right_inv x

@[to_additive (attr := simp)]
theorem leftInvEquiv_symm_fromLeftInv (x : S.leftInv) :
    (S.leftInvEquiv hS).symm (S.fromLeftInv x) = x :=
  (S.leftInvEquiv hS).left_inv x

@[to_additive]
theorem leftInvEquiv_mul (x : S.leftInv) : (S.leftInvEquiv hS x : M) * x = 1 := by
  simpa only [leftInvEquiv_apply, fromCommLeftInv] using fromLeftInv_mul S x

@[to_additive]
theorem mul_leftInvEquiv (x : S.leftInv) : (x : M) * S.leftInvEquiv hS x = 1 := by
  simp only [leftInvEquiv_apply, fromCommLeftInv, mul_fromLeftInv]

@[to_additive (attr := simp)]
theorem leftInvEquiv_symm_mul (x : S) : ((S.leftInvEquiv hS).symm x : M) * x = 1 := by
  convert S.mul_leftInvEquiv hS ((S.leftInvEquiv hS).symm x)
  simp

@[to_additive (attr := simp)]
theorem mul_leftInvEquiv_symm (x : S) : (x : M) * (S.leftInvEquiv hS).symm x = 1 := by
  convert S.leftInvEquiv_mul hS ((S.leftInvEquiv hS).symm x)
  simp

end CommMonoid

section Group

variable [Group M] (S : Submonoid M)

open Pointwise

@[to_additive]
theorem leftInv_eq_inv : S.leftInv = S⁻¹ :=
  Submonoid.ext fun _ ↦
    ⟨fun h ↦ Submonoid.mem_inv.mpr ((inv_eq_of_mul_eq_one_right h.choose_spec).symm ▸
      h.choose.prop),
      fun h ↦ ⟨⟨_, h⟩, mul_inv_cancel _⟩⟩

@[to_additive (attr := simp)]
theorem fromLeftInv_eq_inv (x : S.leftInv) : (S.fromLeftInv x : M) = (x : M)⁻¹ := by
  rw [← mul_right_inj (x : M), mul_inv_cancel, mul_fromLeftInv]

end Group

section CommGroup

variable [CommGroup M] (S : Submonoid M) (hS : S ≤ IsUnit.submonoid M)

@[to_additive (attr := simp)]
theorem leftInvEquiv_symm_eq_inv (x : S) : ((S.leftInvEquiv hS).symm x : M) = (x : M)⁻¹ := by
  rw [← mul_right_inj (x : M), mul_inv_cancel, mul_leftInvEquiv_symm]

end CommGroup

end Submonoid
