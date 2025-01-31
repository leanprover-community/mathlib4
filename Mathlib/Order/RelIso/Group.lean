/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Opposite
import Mathlib.Order.RelIso.Basic

/-!
# Relation isomorphisms form a group
-/


variable {α : Type*} {r : α → α → Prop}

namespace RelIso

instance : Group (r ≃r r) where
  one := RelIso.refl r
  mul f₁ f₂ := f₂.trans f₁
  inv := RelIso.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv_mul_cancel f := ext f.symm_apply_apply

@[simp]
theorem coe_one : ((1 : r ≃r r) : α → α) = id :=
  rfl

@[simp]
theorem coe_mul (e₁ e₂ : r ≃r r) : ((e₁ * e₂) : α → α) = e₁ ∘ e₂ :=
  rfl

theorem mul_apply (e₁ e₂ : r ≃r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl

@[simp]
theorem inv_apply_self (e : r ≃r r) (x) : e⁻¹ (e x) = x :=
  e.symm_apply_apply x

@[simp]
theorem apply_inv_self (e : r ≃r r) (x) : e (e⁻¹ x) = x :=
  e.apply_symm_apply x

/-- The tautological action by `r ≃r r` on `α`. -/
instance applyMulAction : MulAction (r ≃r r) α where
  smul := (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological action by `r ≃r r` on `α`. -/
instance applyOpMulAction : MulAction (r ≃r r)ᵐᵒᵖ α where
  smul e := e.unop.symm
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] lemma smul_def (f : r ≃r r) (a : α) : f • a = f a := rfl
@[simp] lemma op_smul_def (f : (r ≃r r)ᵐᵒᵖ) (a : α) : f • a = f.unop.symm a := rfl

instance apply_faithfulSMul : FaithfulSMul (r ≃r r) α where eq_of_smul_eq_smul h := RelIso.ext h

instance apply_op_faithfulSMul : FaithfulSMul (r ≃r r)ᵐᵒᵖ α where
  eq_of_smul_eq_smul h := MulOpposite.unop_injective <| symm_bijective.injective <| RelIso.ext h

end RelIso
