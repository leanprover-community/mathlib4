/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The coproduct of a separating family of objects is separating

-/

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace IsSeparating

open Classical in
lemma isSeparator_of_isColimit_cofan
    {ι : Type w} {S : ι → C} (hS : IsSeparating (Set.range S))
    {c : Cofan S} (hc : IsColimit c) :
    IsSeparator c.pt := by
  intro X Y f g h
  refine hS _ _ ?_
  rintro _ ⟨i, rfl⟩ α
  let β : c.pt ⟶ X := Cofan.IsColimit.desc hc
      (fun j ↦ if hij : i = j then eqToHom (by rw [hij]) ≫ α else 0)
  have hβ : c.inj i ≫ β = α := by simp [β]
  simp only [← hβ, Category.assoc, h c.pt (by simp) β]

lemma isSeparator_coproduct
    {ι : Type w} {S : ι → C} (hS : IsSeparating (Set.range S)) [HasCoproduct S] :
    IsSeparator (∐ S) :=
  isSeparator_of_isColimit_cofan hS (colimit.isColimit _)

end IsSeparating

end CategoryTheory
