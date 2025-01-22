/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The coproduct of a separating family of objects is separating

If a family of objects `S : ι → C` in a category with zero morphisms
is separating, then the coproduct of `S` is a separator in `C`.

-/

universe w v u

namespace CategoryTheory.IsSeparating

open Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {S : ι → C}

open Classical in
lemma isSeparator_of_isColimit_cofan
    (hS : IsSeparating (Set.range S)) {c : Cofan S} (hc : IsColimit c) :
    IsSeparator c.pt := by
  intro X Y f g h
  apply hS
  rintro _ ⟨i, rfl⟩ α
  let β : c.pt ⟶ X := Cofan.IsColimit.desc hc
      (fun j ↦ if hij : i = j then eqToHom (by rw [hij]) ≫ α else 0)
  have hβ : c.inj i ≫ β = α := by simp [β]
  simp only [← hβ, Category.assoc, h c.pt (by simp) β]

lemma isSeparator_coproduct (hS : IsSeparating (Set.range S)) [HasCoproduct S] :
    IsSeparator (∐ S) :=
  isSeparator_of_isColimit_cofan hS (colimit.isColimit _)

end CategoryTheory.IsSeparating
