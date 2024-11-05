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

open Limits Functor CostructuredArrow

variable {A : Type v₁} [Category.{v₁} A]
variable {B : Type v₁} [Category.{v₁} B]
variable {T : Type v₁} [Category.{v₁} T]
variable (L : A ⥤ T) (R : B ⥤ T)

variable [HasColimitsOfShape (Comma L R) A]

example [R.Final] : (Comma.fst L R).Final := by
  rw  [Functor.final_iff_isIso_colimit_pre]
  intro G
  let R' := Grothendieck.pre (functor L) R
  have := Final.colimitIso (grothendieckPrecompFunctorEquivalence L R).functor
    (Comma.fst L R ⋙ G)
  let i : colimit G ≅ colimit (Comma.fst L R ⋙ G) :=
    colimitIsoColimitGrothendieck L G ≪≫
    (Final.colimitIso R' (grothendieckProj L ⋙ G)).symm ≪≫
    Final.colimitIso (grothendieckPrecompFunctorEquivalence L R).functor (Comma.fst L R ⋙ G)
  convert i.isIso_inv
  apply colimit.hom_ext
  rintro ⟨l, r, f⟩
  simp [i]
  sorry

end CategoryTheory
