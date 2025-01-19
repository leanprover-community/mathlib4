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

variable {G M N O α β : Type*}

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

/-- If `G` acts on `A`, then it acts also on `A → O`, by `(g • F) a = F (g⁻¹ • a)`. -/
@[to_additive (attr := simps) arrowAddAction
      "If `G` acts on `A`, then it acts also on `A → O`, by `(g +ᵥ F) a = F (g⁻¹ +ᵥ a)`"]
def arrowAction {G A O : Type*} [DivisionMonoid G] [MulAction G A] : MulAction G (A → O) where
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

section MulDistribMulAction
variable [Monoid M] [Monoid N] [Monoid O] [MulDistribMulAction M N] [MulDistribMulAction N O]

/-- Pullback a multiplicative distributive multiplicative action along an injective monoid
homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.mulDistribMulAction [SMul M O] (f : O →* N) (hf : Injective f)
  (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M O where
  __ := hf.mulAction f smul
  smul_mul c x y := hf <| by simp only [smul, f.map_mul, smul_mul']
  smul_one c := hf <| by simp only [smul, f.map_one, smul_one]

/-- Pushforward a multiplicative distributive multiplicative action along a surjective monoid
homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Surjective.mulDistribMulAction [SMul M O] (f : N →* O) (hf : Surjective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M O where
  __ := hf.mulAction f smul
  smul_mul c := by simp only [hf.forall, smul_mul', ← smul, ← f.map_mul, implies_true]
  smul_one c := by rw [← f.map_one, ← smul, smul_one]

variable (N) in
/-- Scalar multiplication by `r` as a `MonoidHom`. -/
def MulDistribMulAction.toMonoidHom (r : M) : N →* N where
  toFun := (r • ·)
  map_one' := smul_one r
  map_mul' := smul_mul' r

@[simp]
lemma MulDistribMulAction.toMonoidHom_apply (r : M) (x : N) : toMonoidHom N r x = r • x := rfl

@[simp] lemma smul_pow' (r : M) (x : N) (n : ℕ) : r • x ^ n = (r • x) ^ n :=
  (MulDistribMulAction.toMonoidHom ..).map_pow ..

end MulDistribMulAction

section MulDistribMulAction
variable [Monoid M] [Group G] [MulDistribMulAction M G]

@[simp]
lemma smul_inv' (r : M) (x : G) : r • x⁻¹ = (r • x)⁻¹ :=
  (MulDistribMulAction.toMonoidHom G r).map_inv x

lemma smul_div' (r : M) (x y : G) : r • (x / y) = r • x / r • y :=
  map_div (MulDistribMulAction.toMonoidHom G r) x y

end MulDistribMulAction

section MulDistribMulAction
variable [Group G] [Monoid M] [MulDistribMulAction G M]
variable (M)

/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPerm`. -/
@[simps (config := { simpRhs := true })]
def MulDistribMulAction.toMulEquiv (x : G) : M ≃* M :=
  { MulDistribMulAction.toMonoidHom M x, MulAction.toPermHom G M x with }

end MulDistribMulAction
