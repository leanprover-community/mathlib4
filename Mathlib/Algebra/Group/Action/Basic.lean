/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Group.Action.Units
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.GroupTheory.Perm.Basic

#align_import group_theory.group_action.group from "leanprover-community/mathlib"@"3b52265189f3fb43aa631edffce5d060fafaf82f"

/-!
# More lemmas about group actions

This file contains lemmas about group actions that require more imports than
`Algebra.Group.Action.Defs` offers.
-/

assert_not_exists MonoidWithZero

variable {α β γ : Type*}

section MulAction

section Group

variable [Group α] [MulAction α β]

@[to_additive (attr := simp)]
theorem inv_smul_smul (c : α) (x : β) : c⁻¹ • c • x = x := by rw [smul_smul, mul_left_inv, one_smul]
#align inv_smul_smul inv_smul_smul
#align neg_vadd_vadd neg_vadd_vadd

@[to_additive (attr := simp)]
theorem smul_inv_smul (c : α) (x : β) : c • c⁻¹ • x = x := by
  rw [smul_smul, mul_right_inv, one_smul]
#align smul_inv_smul smul_inv_smul
#align vadd_neg_vadd vadd_neg_vadd

/-- Given an action of a group `α` on `β`, each `g : α` defines a permutation of `β`. -/
@[to_additive (attr := simps)]
def MulAction.toPerm (a : α) : Equiv.Perm β :=
  ⟨fun x => a • x, fun x => a⁻¹ • x, inv_smul_smul a, smul_inv_smul a⟩
#align mul_action.to_perm MulAction.toPerm
#align add_action.to_perm AddAction.toPerm
#align add_action.to_perm_apply AddAction.toPerm_apply
#align mul_action.to_perm_apply MulAction.toPerm_apply
#align add_action.to_perm_symm_apply AddAction.toPerm_symm_apply
#align mul_action.to_perm_symm_apply MulAction.toPerm_symm_apply

/-- Given an action of an additive group `α` on `β`, each `g : α` defines a permutation of `β`. -/
add_decl_doc AddAction.toPerm

/-- `MulAction.toPerm` is injective on faithful actions. -/
@[to_additive "`AddAction.toPerm` is injective on faithful actions."]
theorem MulAction.toPerm_injective [FaithfulSMul α β] :
    Function.Injective (MulAction.toPerm : α → Equiv.Perm β) :=
  (show Function.Injective (Equiv.toFun ∘ MulAction.toPerm) from smul_left_injective').of_comp
#align mul_action.to_perm_injective MulAction.toPerm_injective
#align add_action.to_perm_injective AddAction.toPerm_injective

variable (α) (β)

/-- Given an action of a group `α` on a set `β`, each `g : α` defines a permutation of `β`. -/
@[simps]
def MulAction.toPermHom : α →* Equiv.Perm β where
  toFun := MulAction.toPerm
  map_one' := Equiv.ext <| one_smul α
  map_mul' u₁ u₂ := Equiv.ext <| mul_smul (u₁ : α) u₂
#align mul_action.to_perm_hom MulAction.toPermHom
#align mul_action.to_perm_hom_apply MulAction.toPermHom_apply

/-- Given an action of an additive group `α` on a set `β`, each `g : α` defines a permutation of
`β`. -/
@[simps!]
def AddAction.toPermHom (α : Type*) [AddGroup α] [AddAction α β] :
    α →+ Additive (Equiv.Perm β) :=
  MonoidHom.toAdditive'' <| MulAction.toPermHom (Multiplicative α) β
#align add_action.to_perm_hom AddAction.toPermHom

/-- The tautological action by `Equiv.Perm α` on `α`.

This generalizes `Function.End.applyMulAction`. -/
instance Equiv.Perm.applyMulAction (α : Type*) : MulAction (Equiv.Perm α) α where
  smul f a := f a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align equiv.perm.apply_mul_action Equiv.Perm.applyMulAction

@[simp]
protected theorem Equiv.Perm.smul_def {α : Type*} (f : Equiv.Perm α) (a : α) : f • a = f a :=
  rfl
#align equiv.perm.smul_def Equiv.Perm.smul_def

/-- `Equiv.Perm.applyMulAction` is faithful. -/
instance Equiv.Perm.applyFaithfulSMul (α : Type*) : FaithfulSMul (Equiv.Perm α) α :=
  ⟨Equiv.ext⟩
#align equiv.perm.apply_has_faithful_smul Equiv.Perm.applyFaithfulSMul

variable {α} {β}

@[to_additive]
theorem inv_smul_eq_iff {a : α} {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
  (MulAction.toPerm a).symm_apply_eq
#align inv_smul_eq_iff inv_smul_eq_iff
#align neg_vadd_eq_iff neg_vadd_eq_iff

@[to_additive]
theorem eq_inv_smul_iff {a : α} {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
  (MulAction.toPerm a).eq_symm_apply
#align eq_inv_smul_iff eq_inv_smul_iff
#align eq_neg_vadd_iff eq_neg_vadd_iff

theorem smul_inv [Group β] [SMulCommClass α β β] [IsScalarTower α β β] (c : α) (x : β) :
    (c • x)⁻¹ = c⁻¹ • x⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, smul_mul_smul, mul_right_inv, mul_right_inv, one_smul]
#align smul_inv smul_inv

theorem smul_zpow [Group β] [SMulCommClass α β β] [IsScalarTower α β β] (c : α) (x : β) (p : ℤ) :
    (c • x) ^ p = c ^ p • x ^ p := by
  cases p <;>
  simp [smul_pow, smul_inv]
#align smul_zpow smul_zpow

@[simp]
theorem Commute.smul_right_iff [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β}
    (r : α) : Commute a (r • b) ↔ Commute a b :=
  ⟨fun h => inv_smul_smul r b ▸ h.smul_right r⁻¹, fun h => h.smul_right r⟩
#align commute.smul_right_iff Commute.smul_right_iff

@[simp]
theorem Commute.smul_left_iff [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β}
    (r : α) : Commute (r • a) b ↔ Commute a b := by
  rw [Commute.symm_iff, Commute.smul_right_iff, Commute.symm_iff]
#align commute.smul_left_iff Commute.smul_left_iff

@[to_additive]
protected theorem MulAction.bijective (g : α) : Function.Bijective (g • · : β → β) :=
  (MulAction.toPerm g).bijective
#align mul_action.bijective MulAction.bijective
#align add_action.bijective AddAction.bijective

@[to_additive]
protected theorem MulAction.injective (g : α) : Function.Injective (g • · : β → β) :=
  (MulAction.bijective g).injective
#align mul_action.injective MulAction.injective
#align add_action.injective AddAction.injective

@[to_additive]
protected theorem MulAction.surjective (g : α) : Function.Surjective (g • · : β → β) :=
  (MulAction.bijective g).surjective
#align mul_action.surjective MulAction.surjective
#align add_action.surjective AddAction.surjective

@[to_additive]
theorem smul_left_cancel (g : α) {x y : β} (h : g • x = g • y) : x = y := MulAction.injective g h
#align smul_left_cancel smul_left_cancel
#align vadd_left_cancel vadd_left_cancel

@[to_additive (attr := simp)]
theorem smul_left_cancel_iff (g : α) {x y : β} : g • x = g • y ↔ x = y :=
  (MulAction.injective g).eq_iff
#align smul_left_cancel_iff smul_left_cancel_iff
#align vadd_left_cancel_iff vadd_left_cancel_iff

@[to_additive]
theorem smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g • x = y ↔ x = g⁻¹ • y :=
  (MulAction.toPerm g).apply_eq_iff_eq_symm_apply
#align smul_eq_iff_eq_inv_smul smul_eq_iff_eq_inv_smul
#align vadd_eq_iff_eq_neg_vadd vadd_eq_iff_eq_neg_vadd

end Group

section Monoid
variable [Monoid α] [MulAction α β] (c : α) (x y : β) [Invertible c]

@[simp] lemma invOf_smul_smul : ⅟c • c • x = x := inv_smul_smul (unitOfInvertible c) _
@[simp] lemma smul_invOf_smul : c • (⅟ c • x) = x := smul_inv_smul (unitOfInvertible c) _

variable {c x y}

lemma invOf_smul_eq_iff : ⅟c • x = y ↔ x = c • y := inv_smul_eq_iff (a := unitOfInvertible c)

theorem smul_eq_iff_eq_invOf_smul : c • x = y ↔ x = ⅟c • y :=
  smul_eq_iff_eq_inv_smul (g := unitOfInvertible c)

end Monoid
end MulAction

section Arrow

/-- If `G` acts on `A`, then it acts also on `A → B`, by `(g • F) a = F (g⁻¹ • a)`. -/
@[to_additive (attr := simps) arrowAddAction
      "If `G` acts on `A`, then it acts also on `A → B`, by `(g +ᵥ F) a = F (g⁻¹ +ᵥ a)`"]
def arrowAction {G A B : Type*} [DivisionMonoid G] [MulAction G A] : MulAction G (A → B) where
  smul g F a := F (g⁻¹ • a)
  one_smul := by
    intro f
    show (fun x => f ((1 : G)⁻¹ • x)) = f
    simp only [inv_one, one_smul]
  mul_smul := by
    intros x y f
    show (fun a => f ((x*y)⁻¹ • a)) = (fun a => f (y⁻¹ • x⁻¹ • a))
    simp only [mul_smul, mul_inv_rev]
#align arrow_action arrowAction
#align arrow_add_action arrowAddAction

end Arrow

namespace IsUnit
variable [Monoid α] [MulAction α β]

@[to_additive]
theorem smul_left_cancel {a : α} (ha : IsUnit a) {x y : β} : a • x = a • y ↔ x = y :=
  let ⟨u, hu⟩ := ha
  hu ▸ smul_left_cancel_iff u
#align is_unit.smul_left_cancel IsUnit.smul_left_cancel
#align is_add_unit.vadd_left_cancel IsAddUnit.vadd_left_cancel

end IsUnit

section SMul
variable [Group α] [Monoid β] [MulAction α β] [SMulCommClass α β β] [IsScalarTower α β β]

@[simp] lemma isUnit_smul_iff (g : α) (m : β) : IsUnit (g • m) ↔ IsUnit m :=
  ⟨fun h => inv_smul_smul g m ▸ h.smul g⁻¹, IsUnit.smul g⟩
#align is_unit_smul_iff isUnit_smul_iff

end SMul
