/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Group.Aut
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.GroupTheory.GroupAction.Units

#align_import group_theory.group_action.group from "leanprover-community/mathlib"@"3b52265189f3fb43aa631edffce5d060fafaf82f"

/-!
# Group actions applied to various types of group

This file contains lemmas about `SMul` on `GroupWithZero`, and `Group`.
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

section MulAction

/-- `Monoid.toMulAction` is faithful on nontrivial cancellative monoids with zero. -/
instance CancelMonoidWithZero.faithfulSMul [CancelMonoidWithZero α] [Nontrivial α] :
    FaithfulSMul α α :=
  ⟨fun h => mul_left_injective₀ one_ne_zero (h 1)⟩
#align cancel_monoid_with_zero.to_has_faithful_smul CancelMonoidWithZero.faithfulSMul

section Gwz

variable [GroupWithZero α] [MulAction α β] {a : α}

@[simp]
theorem inv_smul_smul₀ {c : α} (hc : c ≠ 0) (x : β) : c⁻¹ • c • x = x :=
  inv_smul_smul (Units.mk0 c hc) x
#align inv_smul_smul₀ inv_smul_smul₀

@[simp]
theorem smul_inv_smul₀ {c : α} (hc : c ≠ 0) (x : β) : c • c⁻¹ • x = x :=
  smul_inv_smul (Units.mk0 c hc) x
#align smul_inv_smul₀ smul_inv_smul₀

theorem inv_smul_eq_iff₀ {a : α} (ha : a ≠ 0) {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
  ⟨fun h => by rw [← h, smul_inv_smul₀ ha], fun h => by rw [h, inv_smul_smul₀ ha]⟩
#align inv_smul_eq_iff₀ inv_smul_eq_iff₀

theorem eq_inv_smul_iff₀ {a : α} (ha : a ≠ 0) {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
  (MulAction.toPerm (Units.mk0 a ha)).eq_symm_apply
#align eq_inv_smul_iff₀ eq_inv_smul_iff₀

@[simp]
theorem Commute.smul_right_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β}
    {c : α} (hc : c ≠ 0) : Commute a (c • b) ↔ Commute a b :=
  Commute.smul_right_iff (g := Units.mk0 c hc)
#align commute.smul_right_iff₀ Commute.smul_right_iff₀

@[simp]
theorem Commute.smul_left_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β} {c : α}
    (hc : c ≠ 0) : Commute (c • a) b ↔ Commute a b :=
  Commute.smul_left_iff (g := Units.mk0 c hc)
#align commute.smul_left_iff₀ Commute.smul_left_iff₀

/-- Right scalar multiplication as an order isomorphism. -/
@[simps] def Equiv.smulRight (ha : a ≠ 0) : β ≃ β where
  toFun b := a • b
  invFun b := a⁻¹ • b
  left_inv := inv_smul_smul₀ ha
  right_inv := smul_inv_smul₀ ha

protected theorem MulAction.bijective₀ (ha : a ≠ 0) : Function.Bijective (a • · : β → β) :=
  MulAction.bijective <| Units.mk0 a ha
#align mul_action.bijective₀ MulAction.bijective₀

protected theorem MulAction.injective₀ (ha : a ≠ 0) : Function.Injective (a • · : β → β) :=
  (MulAction.bijective₀ ha).injective
#align mul_action.injective₀ MulAction.injective₀

protected theorem MulAction.surjective₀ (ha : a ≠ 0) : Function.Surjective (a • · : β → β) :=
  (MulAction.bijective₀ ha).surjective
#align mul_action.surjective₀ MulAction.surjective₀

end Gwz

end MulAction

section DistribMulAction

section Group

variable [Group α] [AddMonoid β] [DistribMulAction α β]
variable (β)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPerm`. -/
@[simps (config := { simpRhs := true })]
def DistribMulAction.toAddEquiv (x : α) : β ≃+ β :=
  { DistribMulAction.toAddMonoidHom β x, MulAction.toPermHom α β x with }
#align distrib_mul_action.to_add_equiv DistribMulAction.toAddEquiv
#align distrib_mul_action.to_add_equiv_apply DistribMulAction.toAddEquiv_apply
#align distrib_mul_action.to_add_equiv_symm_apply DistribMulAction.toAddEquiv_symm_apply

variable (α)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`. -/
@[simps]
def DistribMulAction.toAddAut : α →* AddAut β where
  toFun := DistribMulAction.toAddEquiv β
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)
#align distrib_mul_action.to_add_aut DistribMulAction.toAddAut
#align distrib_mul_action.to_add_aut_apply DistribMulAction.toAddAut_apply

/-- Each non-zero element of a `GroupWithZero` defines an additive monoid isomorphism of an
`AddMonoid` on which it acts distributively.
This is a stronger version of `DistribMulAction.toAddMonoidHom`. -/
def DistribMulAction.toAddEquiv₀ {α : Type*} (β : Type*) [GroupWithZero α] [AddMonoid β]
    [DistribMulAction α β] (x : α) (hx : x ≠ 0) : β ≃+ β :=
  { DistribMulAction.toAddMonoidHom β x with
    invFun := fun b ↦ x⁻¹ • b
    left_inv := fun b ↦ inv_smul_smul₀ hx b
    right_inv := fun b ↦ smul_inv_smul₀ hx b }

variable {α β}

theorem smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← inv_smul_smul a x, h, smul_zero], fun h => h.symm ▸ smul_zero _⟩
#align smul_eq_zero_iff_eq smul_eq_zero_iff_eq

theorem smul_ne_zero_iff_ne (a : α) {x : β} : a • x ≠ 0 ↔ x ≠ 0 :=
  not_congr <| smul_eq_zero_iff_eq a
#align smul_ne_zero_iff_ne smul_ne_zero_iff_ne

end Group

end DistribMulAction

section MulDistribMulAction

variable [Group α] [Monoid β] [MulDistribMulAction α β]
variable (β)

/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPerm`. -/
@[simps (config := { simpRhs := true })]
def MulDistribMulAction.toMulEquiv (x : α) : β ≃* β :=
  { MulDistribMulAction.toMonoidHom β x, MulAction.toPermHom α β x with }
#align mul_distrib_mul_action.to_mul_equiv MulDistribMulAction.toMulEquiv
#align mul_distrib_mul_action.to_mul_equiv_symm_apply MulDistribMulAction.toMulEquiv_symm_apply
#align mul_distrib_mul_action.to_mul_equiv_apply MulDistribMulAction.toMulEquiv_apply

variable (α)

/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`. -/
@[simps]
def MulDistribMulAction.toMulAut : α →* MulAut β where
  toFun := MulDistribMulAction.toMulEquiv β
  map_one' := MulEquiv.ext (one_smul _)
  map_mul' _ _ := MulEquiv.ext (mul_smul _ _)
#align mul_distrib_mul_action.to_mul_aut MulDistribMulAction.toMulAut
#align mul_distrib_mul_action.to_mul_aut_apply MulDistribMulAction.toMulAut_apply

variable {α β}

end MulDistribMulAction

section Arrow

attribute [local instance] arrowAction

/-- When `B` is a monoid, `ArrowAction` is additionally a `MulDistribMulAction`. -/
def arrowMulDistribMulAction {G A B : Type*} [Group G] [MulAction G A] [Monoid B] :
    MulDistribMulAction G (A → B) where
  smul_one _ := rfl
  smul_mul _ _ _ := rfl
#align arrow_mul_distrib_mul_action arrowMulDistribMulAction

attribute [local instance] arrowMulDistribMulAction

/-- Given groups `G H` with `G` acting on `A`, `G` acts by
  multiplicative automorphisms on `A → H`. -/
@[simps!]
def mulAutArrow {G A H} [Group G] [MulAction G A] [Monoid H] : G →* MulAut (A → H) :=
  MulDistribMulAction.toMulAut _ _
#align mul_aut_arrow mulAutArrow
#align mul_aut_arrow_apply_apply mulAutArrow_apply_apply
#align mul_aut_arrow_apply_symm_apply mulAutArrow_apply_symm_apply

end Arrow

namespace IsUnit

section DistribMulAction

variable [Monoid α] [AddMonoid β] [DistribMulAction α β]

@[simp]
theorem smul_eq_zero {u : α} (hu : IsUnit u) {x : β} : u • x = 0 ↔ x = 0 :=
  (Exists.elim hu) fun u hu => hu ▸ show u • x = 0 ↔ x = 0 from smul_eq_zero_iff_eq u
#align is_unit.smul_eq_zero IsUnit.smul_eq_zero

end DistribMulAction

end IsUnit

section SMul

variable [Group α] [Monoid β]

theorem IsUnit.smul_sub_iff_sub_inv_smul [AddGroup β] [DistribMulAction α β] [IsScalarTower α β β]
    [SMulCommClass α β β] (r : α) (a : β) : IsUnit (r • (1 : β) - a) ↔ IsUnit (1 - r⁻¹ • a) := by
  rw [← isUnit_smul_iff r (1 - r⁻¹ • a), smul_sub, smul_inv_smul]
#align is_unit.smul_sub_iff_sub_inv_smul IsUnit.smul_sub_iff_sub_inv_smul

end SMul
