/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.Hom.Basic
public import Mathlib.Data.FunLike.IsApply

/-! # Monoid structure on order homomorphisms

The monoid/group structure on `RelHom`/`RelIso` can be found in
`Mathlib/Algebra/Order/Group/End.lean`. Since `OrderIso` is an abbreviation for `RelIso`, we don't
provide a `Group (α ≃o α)` instance below.
-/

@[expose] public section

variable {α : Type*}

namespace OrderHom

variable [Preorder α]

instance : Mul (α →o α) where mul f g := f.comp g
instance : One (α →o α) where one := .id
instance : IsMulApplyEqComp (α →o α) α where mul_apply_eq_comp _ _ _ := rfl
instance : IsOneApplyEqSelf (α →o α) α where one_apply_eq_self _ := rfl

lemma mul_eq_comp (f g : α →o α) : (f * g : α →o α) = f.comp g := rfl
lemma one_eq_id : (1 : α →o α) = .id := rfl

instance : Monoid (α →o α) where
  mul_assoc f g h := by simp [DFunLike.ext_iff]
  one_mul f := by simp [DFunLike.ext_iff]
  mul_one f := by simp [DFunLike.ext_iff]

end OrderHom
