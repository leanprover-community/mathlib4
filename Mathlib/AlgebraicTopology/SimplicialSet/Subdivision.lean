/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NonsingularColimit
public import Mathlib.AlgebraicTopology.SimplicialSet.NonemptyFiniteChains
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# The subdivision functors

In this file, we define the subdivision functor `sd : SSet ⥤ SSet`
and its right adjoint `ex`.

## References
* [J. F. Jardine, *Simplicial approximation*][jardine-2004]

-/

@[expose] public section

universe v u

open CategoryTheory Limits

/-- The functor `SimplexCategory ⥤ SSet` which sends `⦋n⦌` to the nerve of the
partially ordered type of nonempty finite chains in `{0, ..., n}` (ulifted to `Type u`).
Vertices in `SimplexCategory.sd.obj ⦋n⦌` identify to nonempty subsets of `{0, ..., n}`. -/
noncomputable def SimplexCategory.sd : SimplexCategory ⥤ SSet.{u} :=
  toPartOrd ⋙ PartOrd.nonemptyFiniteChainsFunctor ⋙ PartOrd.nerveFunctor

noncomputable def PartOrd.nerveFunctorCompNIso :
    nerveFunctor.{u} ⋙ SSet.N.functor ≅ nonemptyFiniteChainsFunctor :=
      NatIso.ofComponents
        (fun _ ↦ PartOrd.Iso.mk (PartialOrder.NonemptyFiniteChains.nerveNEquiv)) (by
          intro X Y f
          ext x : 3
          dsimp at x ⊢
          ext y : 2
          simp [SSet.mapN_coe, nerveMap_app,
            PartialOrder.NonemptyFiniteChains.range_toN_simplex_obj.{u}])

def SSet.stdSimplex.toPartOrdCompNerveFunctorIso :
    SSet.stdSimplex.{u} ≅ SimplexCategory.toPartOrd ⋙ PartOrd.nerveFunctor :=
  NatIso.ofComponents (fun _ ↦ isoNerve _)

namespace SSet

/-- The subdivision functor on simplicial sets. -/
noncomputable def sd : SSet.{u} ⥤ SSet.{u} :=
  stdSimplex.leftKanExtension SimplexCategory.sd

/-- The right adjoint to the subdivision functor on simplicial sets. -/
noncomputable def ex : SSet.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} SimplexCategory.sd

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction between the subdivision functor `sd` and `ex`. -/
noncomputable def sdExAdjunction : sd.{u} ⊣ ex :=
  Presheaf.uliftYonedaAdjunction.{0}
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.sd)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.sd)

instance : sd.{u}.IsLeftAdjoint := sdExAdjunction.isLeftAdjoint

instance : ex.{u}.IsRightAdjoint := sdExAdjunction.isRightAdjoint

/-- An alternative subdivision functor for simplicial sets. It sends `X : SSet` to
the nerve of the partially ordered type `X.N` of nondegenerate simplices in `X`.li
There is a natural transformation `sdToSd' : sd ⟶ sd'` which is an isomorphism when
evaluated on a nonsingular simplicial set. -/
@[simps!, implicit_reducible]
noncomputable def sd' : SSet.{u} ⥤ SSet.{u} :=
  SSet.N.functor ⋙ PartOrd.nerveFunctor

namespace stdSimplex

/-- The natural isomorphism `stdSimplex ⋙ sd ≅ SimplexCategory.sd`. -/
noncomputable def sdIso : stdSimplex.{u} ⋙ sd ≅ SimplexCategory.sd :=
  Presheaf.isExtensionAlongULiftYoneda _

open Functor in
noncomputable def sd'Iso : stdSimplex.{u} ⋙ sd' ≅ SimplexCategory.sd :=
  isoWhiskerRight (SSet.stdSimplex.toPartOrdCompNerveFunctorIso) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    isoWhiskerLeft _ (isoWhiskerRight PartOrd.nerveFunctorCompNIso PartOrd.nerveFunctor)

end stdSimplex

instance : sd.{u}.IsLeftKanExtension stdSimplex.sdIso.inv :=
  inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.leftKanExtensionUnit SimplexCategory.sd.{u}))

noncomputable def sdToSd' : sd.{u} ⟶ sd'.{u} :=
  sd.{u}.descOfIsLeftKanExtension stdSimplex.sdIso.inv _ stdSimplex.sd'Iso.{u}.inv

@[reassoc]
lemma sdToSd'_app_stdSimplex_obj (n : SimplexCategory) :
    sdToSd'.{u}.app (stdSimplex.obj n) =
      stdSimplex.sdIso.hom.app n ≫ stdSimplex.sd'Iso.inv.app n := by
  simp only [← sd.{u}.descOfIsLeftKanExtension_fac_app
    stdSimplex.sdIso.inv _ stdSimplex.sd'Iso.{u}.inv n, Iso.hom_inv_id_app_assoc, sdToSd']

instance (n : SimplexCategory) : IsIso (sdToSd'.{u}.app (stdSimplex.obj n)) := by
  rw [sdToSd'_app_stdSimplex_obj]
  infer_instance

instance : IsIso (Functor.whiskerLeft stdSimplex sdToSd') := by
  rw [NatTrans.isIso_iff_isIso_app]
  dsimp
  infer_instance

noncomputable def isColimitSd'MapCoconeCoconeN (X : SSet.{u}) [Nonsingular X] :
    IsColimit (sd'.mapCocone X.coconeN) :=
  sorry

noncomputable def isColimitSd'MapCoconeCoconeN' (X : SSet.{u}) [Nonsingular X] :
    IsColimit (sd'.mapCocone X.coconeN') := by
  refine (IsColimit.equivOfNatIsoOfIso
    (Functor.isoWhiskerRight X.functorN'Iso.symm _) _ _ ?_).1 X.isColimitSd'MapCoconeCoconeN
  exact Cocone.ext (Iso.refl _) (fun x ↦ (by simp [← Functor.map_comp]))

instance (X : SSet.{u}) [Nonsingular X] : IsIso (sdToSd'.app X) :=
  MorphismProperty.colimitsOfShape_le (W := .isomorphisms SSet.{u}) _
    (.mk' _ _ _ _ (isColimitOfPreserves sd X.isColimitCoconeN')
      X.isColimitSd'MapCoconeCoconeN' (Functor.whiskerLeft _ sdToSd')
      (fun s ↦ (by dsimp; infer_instance)) _ (fun x ↦ by simp))

end SSet
