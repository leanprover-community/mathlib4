/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Aut
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.GroupWithZero.Units.Basic

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

section Gwz

variable [GroupWithZero α] [MulAction α β] {a : α}

@[simp]
theorem inv_smul_smul₀ {c : α} (hc : c ≠ 0) (x : β) : c⁻¹ • c • x = x :=
  inv_smul_smul (Units.mk0 c hc) x

@[simp]
theorem smul_inv_smul₀ {c : α} (hc : c ≠ 0) (x : β) : c • c⁻¹ • x = x :=
  smul_inv_smul (Units.mk0 c hc) x

theorem inv_smul_eq_iff₀ {a : α} (ha : a ≠ 0) {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
  ⟨fun h => by rw [← h, smul_inv_smul₀ ha], fun h => by rw [h, inv_smul_smul₀ ha]⟩

theorem eq_inv_smul_iff₀ {a : α} (ha : a ≠ 0) {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
  (MulAction.toPerm (Units.mk0 a ha)).eq_symm_apply

@[simp]
theorem Commute.smul_right_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β}
    {c : α} (hc : c ≠ 0) : Commute a (c • b) ↔ Commute a b :=
  Commute.smul_right_iff (g := Units.mk0 c hc)

@[simp]
theorem Commute.smul_left_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β} {c : α}
    (hc : c ≠ 0) : Commute (c • a) b ↔ Commute a b :=
  Commute.smul_left_iff (g := Units.mk0 c hc)

/-- Right scalar multiplication as an order isomorphism. -/
@[simps] def Equiv.smulRight (ha : a ≠ 0) : β ≃ β where
  toFun b := a • b
  invFun b := a⁻¹ • b
  left_inv := inv_smul_smul₀ ha
  right_inv := smul_inv_smul₀ ha

protected theorem MulAction.bijective₀ (ha : a ≠ 0) : Function.Bijective (a • · : β → β) :=
  MulAction.bijective <| Units.mk0 a ha

protected theorem MulAction.injective₀ (ha : a ≠ 0) : Function.Injective (a • · : β → β) :=
  (MulAction.bijective₀ ha).injective

protected theorem MulAction.surjective₀ (ha : a ≠ 0) : Function.Surjective (a • · : β → β) :=
  (MulAction.bijective₀ ha).surjective

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

variable (α)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`. -/
@[simps]
def DistribMulAction.toAddAut : α →* AddAut β where
  toFun := DistribMulAction.toAddEquiv β
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)

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

theorem smul_ne_zero_iff_ne (a : α) {x : β} : a • x ≠ 0 ↔ x ≠ 0 :=
  not_congr <| smul_eq_zero_iff_eq a

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

variable (α)

/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`. -/
@[simps]
def MulDistribMulAction.toMulAut : α →* MulAut β where
  toFun := MulDistribMulAction.toMulEquiv β
  map_one' := MulEquiv.ext (one_smul _)
  map_mul' _ _ := MulEquiv.ext (mul_smul _ _)

variable {α β}

end MulDistribMulAction

section Arrow

attribute [local instance] arrowAction

/-- When `B` is a monoid, `ArrowAction` is additionally a `MulDistribMulAction`. -/
def arrowMulDistribMulAction {G A B : Type*} [Group G] [MulAction G A] [Monoid B] :
    MulDistribMulAction G (A → B) where
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

attribute [local instance] arrowMulDistribMulAction

/-- Given groups `G H` with `G` acting on `A`, `G` acts by
  multiplicative automorphisms on `A → H`. -/
@[simps!]
def mulAutArrow {G A H} [Group G] [MulAction G A] [Monoid H] : G →* MulAut (A → H) :=
  MulDistribMulAction.toMulAut _ _

end Arrow

namespace IsUnit

section DistribMulAction

variable [Monoid α] [AddMonoid β] [DistribMulAction α β]

@[simp]
theorem smul_eq_zero {u : α} (hu : IsUnit u) {x : β} : u • x = 0 ↔ x = 0 :=
  (Exists.elim hu) fun u hu => hu ▸ show u • x = 0 ↔ x = 0 from smul_eq_zero_iff_eq u

end DistribMulAction

end IsUnit

section SMul

variable [Group α] [Monoid β]

theorem IsUnit.smul_sub_iff_sub_inv_smul [AddGroup β] [DistribMulAction α β] [IsScalarTower α β β]
    [SMulCommClass α β β] (r : α) (a : β) : IsUnit (r • (1 : β) - a) ↔ IsUnit (1 - r⁻¹ • a) := by
  rw [← isUnit_smul_iff r (1 - r⁻¹ • a), smul_sub, smul_inv_smul]

end SMul
