/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Grothendieck

/-!
# Finality of Projections in Comma Categories
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Functor

variable {A : Type (max u₂ u₃ v₁ v₂ v₃)} [Category.{max u₂ u₃ v₁ v₂ v₃} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable (L : A ⥤ T) (R : B ⥤ T)

example [R.Final] : (Comma.fst L R).Final := by
  rw  [Functor.final_iff_isIso_colimit_pre]
  intro G
  have hR : (Grothendieck.pre G R).Final :=
    sorry
  let i : colimit (Comma.fst L R ⋙ G) ≅ colimit G :=
    sorry
    ≪≫ (colimitIsoColimitGrothendieck L G).symm
  have hi : colimit.pre G (Comma.fst L R) = i.hom :=
    sorry
  rw [hi]
  exact Iso.isIso_hom i

example (X X' Y : B) (i : X ≅ Y) (f : X ⟶ Y) (h : f = i.hom) :
    IsIso f := by sorry

#check Functor.colimitIsoColimitGrothendieck

end CategoryTheory
