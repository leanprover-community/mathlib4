/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Oplax
import Mathlib.CategoryTheory.EqToHom

/-!
# EqToHom lemmas for bicategories

This file contains basic eqToHom lemmas for bicategories.

-/

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

@[simp]
lemma OplaxFunctor.map₂_eqToHom (F : OplaxFunctor B C) {a b : B} {f g : a ⟶ b} (h : f = g) :
    F.map₂ (eqToHom h) = eqToHom (F.congr_map h) := by
  subst h; simp only [eqToHom_refl, OplaxFunctor.map₂_id]

end CategoryTheory
