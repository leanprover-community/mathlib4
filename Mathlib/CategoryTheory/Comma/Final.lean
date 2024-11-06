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

namespace Comma

open Limits Functor CostructuredArrow

variable {A : Type v₁} [Category.{v₁} A]
variable {B : Type v₁} [Category.{v₁} B]
variable {T : Type v₁} [Category.{v₁} T]
variable (L : A ⥤ T) (R : B ⥤ T)

lemma final_fst [R.Final] : (fst L R).Final := by
  rw  [Functor.final_iff_isIso_colimit_pre]
  intro G
  let i : colimit G ≅ colimit (fst L R ⋙ G) :=
    colimitIsoColimitGrothendieck L G ≪≫
    (Final.colimitIso (Grothendieck.pre (functor L) R) (grothendieckProj L ⋙ G)).symm ≪≫
    Final.colimitIso (grothendieckPrecompFunctorEquivalence L R).functor (fst L R ⋙ G)
  convert i.isIso_inv
  apply colimit.hom_ext
  intro ⟨l, r, f⟩
  simp [i]
  simp only [← Category.assoc, ← Iso.comp_inv_eq, Iso.eq_comp_inv]
  have : (L.lanUnit.app G).app l ≫ (L.lanObjObjIsoColimit G (L.obj l)).hom =
      colimit.ι (proj L (L.obj l) ⋙ G) (CostructuredArrow.mk (𝟙 _)) := by
    rw [← ι_lanObjObjIsoColimit_hom]
    simp
  simp [reassoc_of% this]
  rw [ι_colimitFiberwiseColimitIso_hom_assoc]
  simp
  sorry

end Comma

end CategoryTheory
