/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.Hom.Basic
public import Mathlib.Data.FunLike.IsApply

/-! # Monoid structure on order homomorphisms -/

@[expose] public section

variable {α : Type*} [Preorder α]

namespace OrderHom

instance : Mul (α →o α) where mul f g := f.comp g
instance : One (α →o α) where one := .id
instance : IsMulApplyEqComp (α →o α) α where
  mul_apply_eq_comp _ _ _ := rfl
instance : IsOneApplyEqSelf (α →o α) α where
  one_apply_eq_self _ := rfl

lemma mul_eq_comp (f g : α →o α) : (f * g : α →o α) = f.comp g := rfl
lemma one_eq_id : (1 : α →o α) = .id := rfl

instance : Monoid (α →o α) where
  mul_assoc f g h := by simp [DFunLike.ext_iff]
  one_mul f := by simp [DFunLike.ext_iff]
  mul_one f := by simp [DFunLike.ext_iff]

end OrderHom

namespace OrderIso

variable {α : Type*} [Preorder α]

instance : Mul (α ≃o α) where mul f g := g.trans f
instance : One (α ≃o α) where one := refl α
instance : Inv (α ≃o α) where inv := symm
instance : IsMulApplyEqComp (α ≃o α) α where
  mul_apply_eq_comp _ _ _ := rfl
instance : IsOneApplyEqSelf (α ≃o α) α where
  one_apply_eq_self _ := rfl

@[simp] lemma inv_apply' (f : α ≃o α) (x : α) : f⁻¹ x = f.symm x := rfl

lemma mul_eq_trans (f g : α ≃o α) : (f * g : α ≃o α) = g.trans f := rfl
lemma one_eq_refl : (1 : α ≃o α) = refl α := rfl
lemma inv_eq_symm (f : α ≃o α) : f⁻¹ = f.symm := rfl

instance : Group (α ≃o α) where
  mul_assoc f g h := by simp [DFunLike.ext_iff]
  one_mul f := by simp [DFunLike.ext_iff]
  mul_one f := by simp [DFunLike.ext_iff]
  inv_mul_cancel f := by simp [DFunLike.ext_iff]

end OrderIso
