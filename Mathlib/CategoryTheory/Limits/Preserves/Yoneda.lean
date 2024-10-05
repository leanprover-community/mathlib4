/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.FunctorToTypes

/-!
# Yoneda preserves certain colimits

Given a bifunctor `F : J ⥤ Cᵒᵖ ⥤ Type v`, we prove the isomorphism
`Hom(YX, colim_j F(j, -)) ≅ colim_j Hom(YX, F(j, -))`, where `Y` is the Yoneda embedding.

We state this in two ways. One is functorial in `X` and stated as a natural isomorphism of functors
`yoneda.op ⋙ yoneda.obj (colimit F) ≅ yoneda.op ⋙ colimit (F ⋙ yoneda)`, and the other is the
more traditional preservation statement `PreservesColimit F (coyoneda.obj (op (yoneda.obj X)))`.

The proof combines the Yoneda lemma with the fact that colimits in functor categories are computed
pointwise.

## See also

There is also a relative version of this statement where `F : J ⥤ Over A` for some presheaf
`A`, see `CategoryTheory.Comma.Presheaf`.

-/

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory

open CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C]

variable {J : Type v} [SmallCategory J] (F : J ⥤ Cᵒᵖ ⥤ Type v)

def myYonedaLemma' : yoneda.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj F ≅
    F.flip ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} := by
  refine Iso.trans (isoWhiskerRight largeCurriedYonedaLemma ((whiskeringLeft _ _ _).obj F)) ?_
  rfl

/-- Naturally in `X`, we have `Hom(YX, colim_i Fi) ≅ colim_i Hom(YX, Fi)`. -/
noncomputable def yonedaYonedaColimit₂ :
    yoneda.op ⋙ yoneda.obj (colimit F) ≅ yoneda.op ⋙ colimit (F ⋙ yoneda) := calc
  yoneda.op ⋙ yoneda.obj (colimit F)
    ≅ colimit F ⋙ uliftFunctor.{u} := yonedaOpCompYonedaObj (colimit F)
  _ ≅ F.flip ⋙ colim ⋙ uliftFunctor.{u} :=
        isoWhiskerRight (colimitIsoFlipCompColim F) uliftFunctor.{u}
  _ ≅ F.flip ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙ colim :=
        isoWhiskerLeft F.flip (preservesColimitNatIso uliftFunctor.{u})
  _ ≅ (yoneda.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj F) ⋙ colim :=
        isoWhiskerRight (myYonedaLemma' F).symm colim
  _ ≅ yoneda.op ⋙ colimit (F ⋙ yoneda) :=
        isoWhiskerLeft yoneda.op (colimitIsoFlipCompColim (F ⋙ yoneda)).symm

theorem qu {X : C} : ((yonedaYonedaColimit₂ F).app (op X)).inv =
    (colimitObjIsoColimitCompEvaluation _ _).hom
      ≫ (colimit.post F (coyoneda.obj (Opposite.op (yoneda.obj X)))) := by
  dsimp [yonedaYonedaColimit₂]
  simp only [Category.id_comp, Iso.cancel_iso_hom_left]
  apply colimit.hom_ext
  intro j
  ext η Y f
  simp only [Functor.comp_obj, coyoneda_obj_obj, ← comp_evaluation, whiskeringRight_obj_obj,
    Functor.op_obj, whiskeringLeft_obj_obj, evaluation_obj_obj, uliftFunctor_obj, op_unop,
    NatIso.ofComponents_inv_app, ι_colimMap_assoc, Equiv.toIso_inv,
    ι_preservesColimitsIso_inv_assoc, ← Functor.map_comp_assoc,
    colimitObjIsoColimitCompEvaluation_ι_inv, colimit.ι_post]
  simp [yonedaOpCompYonedaObj, map_yonedaEquiv, largeCurriedYonedaLemma,
    FunctorToTypes.colimit.map_ι_apply, ← comp_evaluation, myYonedaLemma', largeCurriedYonedaLemma]

noncomputable instance {X : C} : PreservesColimit F (coyoneda.obj (op (yoneda.obj X))) := by
  suffices IsIso (colimit.post F (coyoneda.obj (op (yoneda.obj X)))) from
    preservesColimitOfIsIsoPost _ _
  suffices colimit.post F (coyoneda.obj (op (yoneda.obj X))) =
      (colimitObjIsoColimitCompEvaluation _ _).inv ≫ ((yonedaYonedaColimit₂ F).app (op X)).inv from
    this ▸ inferInstance
  rw [qu, Iso.inv_hom_id_assoc]

end CategoryTheory
