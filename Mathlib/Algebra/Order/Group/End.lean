/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.RelIso.Basic

/-!
# Relation isomorphisms form a group
-/

assert_not_exists MulAction MonoidWithZero

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

end RelIso
