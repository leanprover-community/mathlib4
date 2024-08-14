/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Group.Action.Units
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# More lemmas about group actions

This file contains lemmas about group actions that require more imports than
`Mathlib.Algebra.Group.Action.Defs` offers.
-/

assert_not_exists MonoidWithZero

variable {α β γ : Type*}

section MulAction

section Group

variable [Group α] [MulAction α β]

/-- Given an action of a group `α` on `β`, each `g : α` defines a permutation of `β`. -/
@[to_additive (attr := simps)]
def MulAction.toPerm (a : α) : Equiv.Perm β :=
  ⟨fun x => a • x, fun x => a⁻¹ • x, inv_smul_smul a, smul_inv_smul a⟩

/-- Given an action of an additive group `α` on `β`, each `g : α` defines a permutation of `β`. -/
add_decl_doc AddAction.toPerm

/-- `MulAction.toPerm` is injective on faithful actions. -/
@[to_additive "`AddAction.toPerm` is injective on faithful actions."]
lemma MulAction.toPerm_injective [FaithfulSMul α β] :
    Function.Injective (MulAction.toPerm : α → Equiv.Perm β) :=
  (show Function.Injective (Equiv.toFun ∘ MulAction.toPerm) from smul_left_injective').of_comp

variable (α) (β)

/-- Given an action of a group `α` on a set `β`, each `g : α` defines a permutation of `β`. -/
@[simps]
def MulAction.toPermHom : α →* Equiv.Perm β where
  toFun := MulAction.toPerm
  map_one' := Equiv.ext <| one_smul α
  map_mul' u₁ u₂ := Equiv.ext <| mul_smul (u₁ : α) u₂

/-- Given an action of an additive group `α` on a set `β`, each `g : α` defines a permutation of
`β`. -/
@[simps!]
def AddAction.toPermHom (α : Type*) [AddGroup α] [AddAction α β] :
    α →+ Additive (Equiv.Perm β) :=
  MonoidHom.toAdditive'' <| MulAction.toPermHom (Multiplicative α) β

/-- The tautological action by `Equiv.Perm α` on `α`.

This generalizes `Function.End.applyMulAction`. -/
instance Equiv.Perm.applyMulAction (α : Type*) : MulAction (Equiv.Perm α) α where
  smul f a := f a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
protected lemma Equiv.Perm.smul_def {α : Type*} (f : Equiv.Perm α) (a : α) : f • a = f a :=
  rfl

/-- `Equiv.Perm.applyMulAction` is faithful. -/
instance Equiv.Perm.applyFaithfulSMul (α : Type*) : FaithfulSMul (Equiv.Perm α) α :=
  ⟨Equiv.ext⟩

variable {α} {β}

@[to_additive]
protected lemma MulAction.bijective (g : α) : Function.Bijective (g • · : β → β) :=
  (MulAction.toPerm g).bijective

@[to_additive]
protected lemma MulAction.injective (g : α) : Function.Injective (g • · : β → β) :=
  (MulAction.bijective g).injective

@[to_additive]
protected lemma MulAction.surjective (g : α) : Function.Surjective (g • · : β → β) :=
  (MulAction.bijective g).surjective

@[to_additive]
lemma smul_left_cancel (g : α) {x y : β} (h : g • x = g • y) : x = y := MulAction.injective g h

@[to_additive (attr := simp)]
lemma smul_left_cancel_iff (g : α) {x y : β} : g • x = g • y ↔ x = y :=
  (MulAction.injective g).eq_iff

@[to_additive]
lemma smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g • x = y ↔ x = g⁻¹ • y :=
  (MulAction.toPerm g).apply_eq_iff_eq_symm_apply

end Group

section Monoid
variable [Monoid α] [MulAction α β] (c : α) (x y : β) [Invertible c]

@[simp] lemma invOf_smul_smul : ⅟c • c • x = x := inv_smul_smul (unitOfInvertible c) _
@[simp] lemma smul_invOf_smul : c • (⅟ c • x) = x := smul_inv_smul (unitOfInvertible c) _

variable {c x y}

lemma invOf_smul_eq_iff : ⅟c • x = y ↔ x = c • y := inv_smul_eq_iff (g := unitOfInvertible c)

lemma smul_eq_iff_eq_invOf_smul : c • x = y ↔ x = ⅟c • y :=
  smul_eq_iff_eq_inv_smul (g := unitOfInvertible c)

end Monoid
end MulAction

section Arrow

/-- If `G` acts on `A`, then it acts also on `A → B`, by `(g • F) a = F (g⁻¹ • a)`. -/
@[to_additive (attr := simps) arrowAddAction
      "If `G` acts on `A`, then it acts also on `A → B`, by `(g +ᵥ F) a = F (g⁻¹ +ᵥ a)`"]
def arrowAction {G A B : Type*} [DivisionMonoid G] [MulAction G A] : MulAction G (A → B) where
  smul g F a := F (g⁻¹ • a)
  one_smul f := by
    show (fun x => f ((1 : G)⁻¹ • x)) = f
    simp only [inv_one, one_smul]
  mul_smul x y f := by
    show (fun a => f ((x*y)⁻¹ • a)) = (fun a => f (y⁻¹ • x⁻¹ • a))
    simp only [mul_smul, mul_inv_rev]

end Arrow

namespace IsUnit
variable [Monoid α] [MulAction α β]

@[to_additive]
lemma smul_left_cancel {a : α} (ha : IsUnit a) {x y : β} : a • x = a • y ↔ x = y :=
  let ⟨u, hu⟩ := ha
  hu ▸ smul_left_cancel_iff u

end IsUnit

section SMul
variable [Group α] [Monoid β] [MulAction α β] [SMulCommClass α β β] [IsScalarTower α β β]

@[simp] lemma isUnit_smul_iff (g : α) (m : β) : IsUnit (g • m) ↔ IsUnit m :=
  ⟨fun h => inv_smul_smul g m ▸ h.smul g⁻¹, IsUnit.smul g⟩

end SMul
