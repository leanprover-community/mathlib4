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

namespace RelHom

instance : Monoid (r →r r) where
  one := .id r
  mul := .comp
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

lemma one_def : (1 : r →r r) = .id r := rfl
lemma mul_def (f g : r →r r) : (f * g) = f.comp g := rfl

@[simp] lemma coe_one : ⇑(1 : r →r r) = id := rfl
@[simp] lemma coe_mul (f g : r →r r) : ⇑(f * g) = f ∘ g := rfl

lemma one_apply (a : α) : (1 : r →r r) a = a := rfl
lemma mul_apply (e₁ e₂ : r →r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

end RelHom

namespace RelEmbedding

instance : Monoid (r ↪r r) where
  one := .refl r
  mul f g := g.trans f
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

lemma one_def : (1 : r ↪r r) = .refl r := rfl
lemma mul_def (f g : r ↪r r) : (f * g) = g.trans f := rfl

@[simp] lemma coe_one : ⇑(1 : r ↪r r) = id := rfl
@[simp] lemma coe_mul (f g : r ↪r r) : ⇑(f * g) = f ∘ g := rfl

lemma one_apply (a : α) : (1 : r ↪r r) a = a := rfl
lemma mul_apply (e₁ e₂ : r ↪r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

end RelEmbedding

namespace RelIso

instance : Group (r ≃r r) where
  one := .refl r
  mul f₁ f₂ := f₂.trans f₁
  inv := .symm
  mul_assoc _ _ _ := rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv_mul_cancel f := ext f.symm_apply_apply

lemma one_def : (1 : r ≃r r) = .refl r := rfl
lemma mul_def (f g : r ≃r r) : (f * g) = g.trans f := rfl

@[simp] lemma coe_one : ((1 : r ≃r r) : α → α) = id := rfl
@[simp] lemma coe_mul (e₁ e₂ : r ≃r r) : ((e₁ * e₂) : α → α) = e₁ ∘ e₂ := rfl

lemma one_apply (x : α) : (1 : r ≃r r) x = x := rfl
lemma mul_apply (e₁ e₂ : r ≃r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

@[simp]
theorem inv_apply_self (e : r ≃r r) (x) : e⁻¹ (e x) = x :=
  e.symm_apply_apply x

@[simp]
theorem apply_inv_self (e : r ≃r r) (x) : e (e⁻¹ x) = x :=
  e.apply_symm_apply x

end RelIso
