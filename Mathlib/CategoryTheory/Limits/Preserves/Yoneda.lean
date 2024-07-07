/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory
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

-- coyoneda ⋙ (whiskeringLeft J (Cᵒᵖ ⥤ Type v) (Type (max u v))).obj F ≅ Functor.flip (F ⋙ yoneda)

-- @[simps! (config := { fullyApplied := false }) hom_app_app]
-- def blu₁ : (F ⋙ yoneda).flip ≅ yoneda.flip ⋙ (whiskeringLeft _ _ _).obj F :=
--   NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => Iso.refl _))

-- @[simps! (config := { fullyApplied := false }) hom_app_app]
-- def blu₂ : yoneda.flip ≅ (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v) :=
--   NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => Iso.refl _))

-- @[simp]
-- theorem flip_obj {X} : F.flip.obj X = F ⋙ (evaluation _ _).obj X := rfl

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
-- variable (F : )

-- @[simp]
-- theorem flip_comp_yoneda_obj {G} : (F ⋙ yoneda).flip.obj G = F ⋙ coyoneda.obj G := rfl

-- @[simp]
theorem flip_obj (F : C ⥤ D ⥤ E) {X} : F.flip.obj X = F ⋙ (evaluation _ _).obj X := rfl

-- @[simp]
-- theorem yoneda_comp_evaluation {X} :
--   yoneda ⋙ (evaluation (Cᵒᵖ ⥤ Type v₁)ᵒᵖ (Type (max u₁ v₁))).obj X = coyoneda.obj X := rfl

-- @[simp]
-- theorem yoneda_comp_evaluation_assoc {X} (F : D ⥤ _) :
  -- (F ⋙ yoneda) ⋙ (evaluation (Cᵒᵖ ⥤ Type v₁)ᵒᵖ (Type (max u₁ v₁))).obj X = F ⋙ coyoneda.obj X := rfl

end

-- Yoneda lemma for bifunctors
@[simps!? (config := { isSimp := false, fullyApplied := false }) hom_app_app]
def myYonedaLemma : F.flip ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ≅
    yoneda.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj F :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => by
    -- dsimp
    apply Equiv.toIso
    exact Equiv.trans Equiv.ulift (yonedaEquiv).symm
    ) (by
      intros j j' f
      ext x
      apply yonedaEquiv.injective
      simp [yonedaEquiv]
    )) (by
      intros X Y f
      ext j x
      apply yonedaEquiv.injective
      simp [yonedaEquiv])

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
  -- _ ≅ (F.flip ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙ colim) :=
  --       (Functor.associator _ _ _).symm

  _ ≅ (yoneda.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj F) ⋙ colim :=
        -- isoWhiskerRight (isoWhiskerRight largeCurriedYonedaLemma.symm ((whiskeringLeft _ _ _).obj _)) colim
        isoWhiskerRight (myYonedaLemma' F).symm colim

  -- _ ≅ yoneda.op ⋙ (coyoneda ⋙ (whiskeringLeft _ _ _).obj F) ⋙ colim :=
  --       Functor.associator _ _ _
  -- _ ≅ yoneda.op ⋙ (yoneda.flip ⋙ (whiskeringLeft _ _ _).obj F) ⋙ colim :=
  --       isoWhiskerLeft yoneda.op (isoWhiskerRight (isoWhiskerRight blu₂.symm _) colim)
  -- _ ≅ yoneda.op ⋙ (F ⋙ yoneda).flip ⋙ colim :=
  --       isoWhiskerLeft yoneda.op (isoWhiskerRight (blu₁ F).symm colim)
  _ ≅ yoneda.op ⋙ colimit (F ⋙ yoneda) :=
        isoWhiskerLeft yoneda.op (colimitIsoFlipCompColim (F ⋙ yoneda)).symm

-- theorem qu_aux {X : C} {j : J } :
--     colimit.ι (F ⋙ (evaluation Cᵒᵖ (Type v)).obj (op X) ⋙ uliftFunctor.{u, v}) j ≫
--     (preservesColimitIso uliftFunctor.{u, v} ((Functor.flip F).obj (op X))).inv =
--       (uliftFunctor.{u, v}).map (colimit.ι (F.flip.obj (op X)) j) :=
--   ι_preservesColimitsIso_inv (uliftFunctor.{u, v}) (F.flip.obj (op X)) j

#check op

-- attribute [local simp] flip_obj in
-- attribute [simps! hom_app_app] largeCurriedYonedaLemma

-- set_option trace.Meta.Tactic.simp.rewrite true
theorem qu {X : C} : ((yonedaYonedaColimit₂ F).app (op X)).inv = (colimitObjIsoColimitCompEvaluation _ _).hom
      ≫ (colimit.post F (coyoneda.obj (Opposite.op (yoneda.obj X)))) := by
  dsimp [yonedaYonedaColimit₂]
  simp only [Category.id_comp, Iso.cancel_iso_hom_left]
  apply colimit.hom_ext
  intro j
  -- rw [ι_preservesColimitsIso_inv_assoc]
  -- rw [largeCurriedYonedaLemma_hom_app_app]
  -- rw [myYonedaLemma]
  simp only [Functor.comp_obj]


  simp only [Functor.comp_obj, coyoneda_obj_obj, flip_obj, whiskeringRight_obj_obj,
    Functor.op_obj, whiskeringLeft_obj_obj, evaluation_obj_obj, uliftFunctor_obj, op_unop,
    NatIso.ofComponents_inv_app, ι_colimMap_assoc, Equiv.toIso_inv,
    ι_preservesColimitsIso_inv_assoc, ← Functor.map_comp_assoc,
    colimitObjIsoColimitCompEvaluation_ι_inv, colimit.ι_post]
  -- rw [ι_preservesColimitsIso_inv_assoc]
  -- simp? [← Functor.map_comp_assoc, -Functor.map_comp, flip_obj, myYonedaLemma]
  -- simp only [Functor.comp_obj, coyoneda_obj_obj, ι_colimMap_assoc, evaluation_obj_obj,
  --   uliftFunctor_obj, whiskerLeft_app, largeCurriedYonedaLemma_hom_app_app, colimit.ι_post]
  ext η Y f
  simp [yonedaOpCompYonedaObj, map_yonedaEquiv, largeCurriedYonedaLemma,
    FunctorToTypes.colimit.map_ι_apply, flip_obj]

noncomputable instance {X : C} : PreservesColimit F (coyoneda.obj (op (yoneda.obj X))) := by
  suffices IsIso (colimit.post F (coyoneda.obj (op (yoneda.obj X)))) from
    preservesColimitOfIsIsoPost _ _
  suffices colimit.post F (coyoneda.obj (op (yoneda.obj X))) =
      (colimitObjIsoColimitCompEvaluation _ _).inv ≫ ((yonedaYonedaColimit₂ F).app (op X)).inv from
    this ▸ inferInstance
  rw [qu, Iso.inv_hom_id_assoc]

end CategoryTheory
