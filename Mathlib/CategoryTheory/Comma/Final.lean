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
  simp only [comp_obj, fst_obj, colimit.ι_pre, grothendieckPrecompFunctorEquivalence_functor,
    Iso.trans_inv, Iso.symm_inv, colimitIsoColimitGrothendieck_inv, Category.assoc, i]
  simp only [← Category.assoc, ← Iso.comp_inv_eq, Iso.eq_comp_inv]
  simp only [ι_colimitIsoOfIsLeftKanExtension_inv, comp_obj, Category.assoc,
    HasColimit.isoOfNatIso_ι_hom, fiberwiseColimit_obj, functor_obj, Cat.of_α,
    leftKanExtensionIsoFiberwiseColimit_hom_app,
    leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom_assoc,
    HasColimit.isoOfNatIso_ι_inv_assoc, proj_obj, mk_left, Grothendieck.ι_obj, grothendieckProj_obj,
    isoWhiskerRight_inv, whiskerRight_app, ιCompGrothendieckProj_inv_app, Functor.map_id,
    Category.id_comp]
  rw [ι_colimitFiberwiseColimitIso_hom_assoc]
  simp only [functor_obj, Cat.of_α, Grothendieck.ι_obj, comp_obj, grothendieckProj_obj, mk_left,
    Final.colimitIso, asIso_inv, asIso_hom]
  rw [← colimit.w (grothendieckProj L ⋙ G) (j' := (Grothendieck.pre _ R).obj ⟨r, .mk f⟩)
    ⟨f, (by { simp; exact 𝟙 _ })⟩]
  have : colimit.ι (Grothendieck.pre (functor L) R ⋙ grothendieckProj L ⋙ G) =
    colimit.ι (grothendieckPrecompFunctorToComma L R ⋙ fst L R ⋙ G) :=
    rfl
  simp [this, grothendieckPrecompFunctorToComma]

end Comma

end CategoryTheory
