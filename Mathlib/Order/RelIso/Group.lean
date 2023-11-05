/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.RelIso.Basic

#align_import order.rel_iso.group from "leanprover-community/mathlib"@"62a5626868683c104774de8d85b9855234ac807c"

/-!
# Relation isomorphisms form a group
-/


variable {α : Type*} {r : α → α → Prop}

namespace RelIso

instance : Group (r ≃r r) where
  one := RelIso.refl r
  mul f₁ f₂ := f₂.trans f₁
  inv := RelIso.symm
  mul_assoc f₁ f₂ f₃ := rfl
  one_mul f := ext fun _ => rfl
  mul_one f := ext fun _ => rfl
  mul_left_inv f := ext f.symm_apply_apply

@[simp]
theorem coe_one : ((1 : r ≃r r) : α → α) = id :=
  rfl
#align rel_iso.coe_one RelIso.coe_one

@[simp]
theorem coe_mul (e₁ e₂ : r ≃r r) : ((e₁ * e₂) : α → α) = e₁ ∘ e₂ :=
  rfl
#align rel_iso.coe_mul RelIso.coe_mul

theorem mul_apply (e₁ e₂ : r ≃r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl
#align rel_iso.mul_apply RelIso.mul_apply

@[simp]
theorem inv_apply_self (e : r ≃r r) (x) : e⁻¹ (e x) = x :=
  e.symm_apply_apply x
#align rel_iso.inv_apply_self RelIso.inv_apply_self

@[simp]
theorem apply_inv_self (e : r ≃r r) (x) : e (e⁻¹ x) = x :=
  e.apply_symm_apply x
#align rel_iso.apply_inv_self RelIso.apply_inv_self

end RelIso
