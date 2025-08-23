/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Group.Action.Units
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Logic.Embedding.Basic

/-!
# More lemmas about group actions

This file contains lemmas about group actions that require more imports than
`Mathlib/Algebra/Group/Action/Defs.lean` offers.
-/

assert_not_exists MonoidWithZero Equiv.Perm.permGroup

variable {G M A B α β : Type*}

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
@[to_additive /-- `AddAction.toPerm` is injective on faithful actions. -/]
lemma MulAction.toPerm_injective [FaithfulSMul α β] :
    Function.Injective (MulAction.toPerm : α → Equiv.Perm β) :=
  (show Function.Injective (Equiv.toFun ∘ MulAction.toPerm) from smul_left_injective').of_comp

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
@[simp] lemma smul_invOf_smul : c • (⅟c • x) = x := smul_inv_smul (unitOfInvertible c) _

variable {c x y}

lemma invOf_smul_eq_iff : ⅟c • x = y ↔ x = c • y := inv_smul_eq_iff (g := unitOfInvertible c)

lemma smul_eq_iff_eq_invOf_smul : c • x = y ↔ x = ⅟c • y :=
  smul_eq_iff_eq_inv_smul (g := unitOfInvertible c)

end Monoid
end MulAction

section Arrow
variable {G A B : Type*} [DivisionMonoid G] [MulAction G A]

/-- If `G` acts on `A`, then it acts also on `A → B`, by `(g • F) a = F (g⁻¹ • a)`. -/
@[to_additive (attr := simps) arrowAddAction
/-- If `G` acts on `A`, then it acts also on `A → B`, by `(g +ᵥ F) a = F (g⁻¹ +ᵥ a)` -/]
def arrowAction : MulAction G (A → B) where
  smul g F a := F (g⁻¹ • a)
  one_smul f := by
    change (fun x => f ((1 : G)⁻¹ • x)) = f
    simp only [inv_one, one_smul]
  mul_smul x y f := by
    change (fun a => f ((x*y)⁻¹ • a)) = (fun a => f (y⁻¹ • x⁻¹ • a))
    simp only [mul_smul, mul_inv_rev]

attribute [local instance] arrowAction

variable [Monoid M]

/-- When `M` is a monoid, `ArrowAction` is additionally a `MulDistribMulAction`. -/
def arrowMulDistribMulAction : MulDistribMulAction G (A → M) where
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

end Arrow

namespace IsUnit
variable [Monoid α] [MulAction α β]

@[to_additive]
theorem smul_bijective {m : α} (hm : IsUnit m) :
    Function.Bijective (fun (a : β) ↦ m • a) := by
  lift m to αˣ using hm
  exact MulAction.bijective m

@[deprecated (since := "2025-03-03")]
alias _root_.AddAction.vadd_bijective_of_is_addUnit := IsAddUnit.vadd_bijective

@[to_additive existing, deprecated (since := "2025-03-03")]
alias _root_.MulAction.smul_bijective_of_is_unit := IsUnit.smul_bijective

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

namespace MulAction
variable [Monoid M] [MulAction M α]

variable (M α) in
/-- Embedding of `α` into functions `M → α` induced by a multiplicative action of `M` on `α`. -/
@[to_additive
/-- Embedding of `α` into functions `M → α` induced by an additive action of `M` on `α`. -/]
def toFun : α ↪ M → α :=
  ⟨fun y x ↦ x • y, fun y₁ y₂ H ↦ one_smul M y₁ ▸ one_smul M y₂ ▸ by convert congr_fun H 1⟩

@[to_additive (attr := simp)]
lemma toFun_apply (x : M) (y : α) : MulAction.toFun M α y x = x • y := rfl

end MulAction

section MulDistribMulAction
variable [Monoid M] [Monoid A] [MulDistribMulAction M A]

/-- Pullback a multiplicative distributive multiplicative action along an injective monoid
homomorphism. -/
-- See note [reducible non-instances]
protected abbrev Function.Injective.mulDistribMulAction [Monoid B] [SMul M B] (f : B →* A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B where
  __ := hf.mulAction f smul
  smul_mul c x y := hf <| by simp only [smul, f.map_mul, smul_mul']
  smul_one c := hf <| by simp only [smul, f.map_one, smul_one]

/-- Pushforward a multiplicative distributive multiplicative action along a surjective monoid
homomorphism. -/
-- See note [reducible non-instances]
protected abbrev Function.Surjective.mulDistribMulAction [Monoid B] [SMul M B] (f : A →* B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B where
  __ := hf.mulAction f smul
  smul_mul c := by simp only [hf.forall, smul_mul', ← smul, ← f.map_mul, implies_true]
  smul_one c := by rw [← f.map_one, ← smul, smul_one]

variable (A) in
/-- Scalar multiplication by `r` as a `MonoidHom`. -/
@[simps] def MulDistribMulAction.toMonoidHom (r : M) : A →* A where
  toFun := (r • ·)
  map_one' := smul_one r
  map_mul' := smul_mul' r

@[simp] lemma smul_pow' (r : M) (x : A) (n : ℕ) : r • x ^ n = (r • x) ^ n :=
  (MulDistribMulAction.toMonoidHom _ _).map_pow _ _

variable (M A) in
/-- Each element of the monoid defines a monoid homomorphism. -/
@[simps]
def MulDistribMulAction.toMonoidEnd : M →* Monoid.End A where
  toFun := MulDistribMulAction.toMonoidHom A
  map_one' := MonoidHom.ext <| one_smul M
  map_mul' x y := MonoidHom.ext <| mul_smul x y

end MulDistribMulAction

section MulDistribMulAction
variable [Monoid M] [Group A] [MulDistribMulAction M A]

@[simp] lemma smul_inv' (r : M) (x : A) : r • x⁻¹ = (r • x)⁻¹ :=
  (MulDistribMulAction.toMonoidHom A r).map_inv x

lemma smul_div' (r : M) (x y : A) : r • (x / y) = r • x / r • y :=
  map_div (MulDistribMulAction.toMonoidHom A r) x y

end MulDistribMulAction
