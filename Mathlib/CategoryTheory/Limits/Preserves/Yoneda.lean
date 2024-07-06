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

We prove the isomorphism `Hom(YX, colim_i Fi) ≅ colim_i Hom(YX, Fi)`, where `Y` is the Yoneda
embedding.

We state this in two ways. One is functorial in `X` and stated as a natural isomorphism of functors
`yoneda.op ⋙ yoneda.obj (colimit F) ≅ yoneda.op ⋙ colimit (F ⋙ yoneda)`, and the other is the
more traditional preservation statement `PreservesColimit F (coyoneda.obj (op (yoneda.obj X)))`.

The proof combines the Yoneda lemma with the fact that colimits in functor categories are computed
pointwise.

## See also

There is also a relative version of this statement where `F` lands in `Over A` for some presheaf
`A`, see `CategoryTheory.Comma.Presheaf`.

-/

universe v u

namespace CategoryTheory

open CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C]

variable {J : Type v} [SmallCategory J] (F : J ⥤ Cᵒᵖ ⥤ Type v)

-- coyoneda ⋙ (whiskeringLeft J (Cᵒᵖ ⥤ Type v) (Type (max u v))).obj F ≅ Functor.flip (F ⋙ yoneda)

@[simps! (config := { fullyApplied := false }) hom_app_app]
def blu₁ : (F ⋙ yoneda).flip ≅ yoneda.flip ⋙ (whiskeringLeft _ _ _).obj F :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => Iso.refl _))

@[simps! (config := { fullyApplied := false }) hom_app_app]
def blu₂ : yoneda.flip ≅ (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v) :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => Iso.refl _))

@[simps! (config := { fullyApplied := false }) hom_app_app inv_app_app]
def myYonedaLemma : F.flip ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ≅
    yoneda.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj F :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => by
    -- dsimp
    apply Equiv.toIso
    exact Equiv.trans Equiv.ulift (yonedaEquiv).symm
    ) (by
      intros j j' f
      ext x
      dsimp at x
      simp
      apply yonedaEquiv.injective
      simp only [op_unop, Equiv.apply_symm_apply]
      rw [yonedaEquiv_comp]
      simp
    )) (by
      intros X Y f
      ext j x
      dsimp at x
      simp
      apply yonedaEquiv.injective
      simp only [op_unop, Equiv.apply_symm_apply]
      rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      simp [yonedaEquiv])

/-- Naturally in `X`, we have `Hom(YX, colim_i Fi) ≅ colim_i Hom(YX, Fi)`. -/
noncomputable def yonedaYonedaColimit₂ :
    yoneda.op ⋙ yoneda.obj (colimit F) ≅ yoneda.op ⋙ colimit (F ⋙ yoneda) := calc
  yoneda.op ⋙ yoneda.obj (colimit F)
    ≅ colimit F ⋙ uliftFunctor.{u} := yonedaOpCompYonedaObj (colimit F)
  _ ≅ F.flip ⋙ colim ⋙ uliftFunctor.{u} :=
        isoWhiskerRight (colimitIsoFlipCompColim F) uliftFunctor.{u}
  _ ≅ F.flip ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙ colim :=
        isoWhiskerLeft F.flip (preservesColimitNatIso uliftFunctor.{u})
  _ ≅ (F.flip ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙ colim) :=
        (Functor.associator _ _ _).symm
  _ ≅ (yoneda.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj F) ⋙ colim :=
        isoWhiskerRight (myYonedaLemma F) colim
  _ ≅ yoneda.op ⋙ (coyoneda ⋙ (whiskeringLeft _ _ _).obj F) ⋙ colim :=
        Functor.associator _ _ _
  _ ≅ yoneda.op ⋙ (yoneda.flip ⋙ (whiskeringLeft _ _ _).obj F) ⋙ colim :=
        isoWhiskerLeft yoneda.op (isoWhiskerRight (isoWhiskerRight blu₂.symm _) colim)
  _ ≅ yoneda.op ⋙ (F ⋙ yoneda).flip ⋙ colim :=
        isoWhiskerLeft yoneda.op (isoWhiskerRight (blu₁ F).symm colim)
  _ ≅ yoneda.op ⋙ colimit (F ⋙ yoneda) :=
        isoWhiskerLeft yoneda.op (colimitIsoFlipCompColim (F ⋙ yoneda)).symm

theorem qu_aux {X : C} {j : J } :
    colimit.ι (F ⋙ (evaluation Cᵒᵖ (Type v)).obj (op X) ⋙ uliftFunctor.{u, v}) j ≫
    (preservesColimitIso uliftFunctor.{u, v} ((Functor.flip F).obj (op X))).inv =
      (uliftFunctor.{u, v}).map (colimit.ι (F.flip.obj (op X)) j) :=
  ι_preservesColimitsIso_inv (uliftFunctor.{u, v}) (F.flip.obj (op X)) j

theorem qu {X : C} : ((yonedaYonedaColimit₂ F).app (op X)).inv = (colimitObjIsoColimitCompEvaluation _ _).hom
      ≫ (colimit.post F (coyoneda.obj (Opposite.op (yoneda.obj X)))) := by
  dsimp [yonedaYonedaColimit₂]
  simp only [Iso.cancel_iso_hom_left]
  -- simp?
  apply colimit.hom_ext
  intro j
  simp
  erw [colimit.ι_post F (coyoneda.obj _)]
  rw [← Functor.map_comp_assoc]
  erw [colimitObjIsoColimitCompEvaluation_ι_inv]
  ext η Y f
  simp [yonedaOpCompYonedaObj, largeCurriedYonedaLemma]

  have := congrFun ((colimit.ι F j).naturality f.op).symm
  dsimp at this
  rw [this]
  -- ???????
  rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

noncomputable instance {X : C} : PreservesColimit F (coyoneda.obj (op (yoneda.obj X))) := by
  suffices IsIso (colimit.post F (coyoneda.obj (op (yoneda.obj X)))) from
    preservesColimitOfIsIsoPost _ _
  suffices colimit.post F (coyoneda.obj (op (yoneda.obj X))) =
      (colimitObjIsoColimitCompEvaluation _ _).inv ≫ ((yonedaYonedaColimit₂ F).app (op X)).inv from
    this ▸ inferInstance
  rw [qu]
  simp

end CategoryTheory
