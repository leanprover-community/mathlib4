/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAtYoneda

/-!
# The co-Yoneda embedding is dense

Some of the results of the Yoneda embedding from the file
`Mathlib/CategoryTheory/Functor/KanExtension/DenseAtYoneda.lean`
are dualised here for the co-Yoneda embedding.

## References

* https://ncatlab.org/nlab/show/dense+subcategory

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C]

namespace Functor.Elements

variable [LocallySmall.{w} C] (P : C ⥤ Type w)

@[implicit_reducible, simps]
noncomputable def shrinkCoyonedaCocone :
    Cocone ((π P).op ⋙ shrinkCoyoneda.{w}) where
  pt := P
  ι.app x := shrinkCoyonedaEquiv.symm x.unop.2
  ι.naturality x y f := by
    dsimp
    simp only [← f.unop.2, shrinkCoyonedaEquiv_symm_map.{w}, Category.comp_id]

@[reassoc]
lemma shrinkYoneda_map_app_shrinkCoyonedaCocone_ι_app_app
    {X Y : C} (f : X ⟶ Y) (u : P.Elementsᵒᵖ) :
    dsimp% (shrinkYoneda.{w}.map f).app _ ≫ ((shrinkCoyonedaCocone P).ι.app u).app Y =
    ((shrinkCoyonedaCocone P).ι.app u).app X ≫ P.map f := by
  ext x
  obtain ⟨x, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective x
  simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w},
    shrinkCoyonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm_comp.{w}]

@[no_expose]
noncomputable def isColimitShrinkCoyonedaCoconeObj (X : C) :
    IsColimit (((evaluation _ _).obj X).mapCocone (shrinkCoyonedaCocone P)) := by
  refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).1
    (IsColimit.whiskerEquivalence
      (isColimitShrinkYonedaCoconeObj ((opOpEquivalence C).functor ⋙ P) (op (op X)))
      ((opOpEquivalence C).congrElements P).op)
  · refine NatIso.ofComponents (fun x ↦
      (shrinkYonedaObjObjEquiv.trans (.trans Quiver.Hom.opEquiv.symm
        shrinkYonedaObjObjEquiv.symm)).toIso) (fun f ↦ ?_)
    ext g
    obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
    simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w},
      shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}]
  · refine Cocone.ext (Iso.refl _) (fun ⟨j⟩ ↦ ?_)
    ext f
    obtain ⟨f : j.obj ⟶ X, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective f
    simp [shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm.{w},
      shrinkCoyonedaEquiv_symm_app_shrinkCoyonedaObjObjEquiv_symm.{w}]

@[no_expose]
noncomputable def isColimitShrinkCoyonedaCocone :
    IsColimit (shrinkCoyonedaCocone P) :=
  evaluationJointlyReflectsColimits _ (isColimitShrinkCoyonedaCoconeObj _)

variable [HasColimitsOfShape P.Elementsᵒᵖ (Type w)]

/-- If `F : C ⥤ Type w` and `C` is locally `w`-small, then `F` identifies to the composition
`shrinkYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π F).op ⋙ colim`. -/
@[no_expose]
noncomputable def shrinkYonedaCompWhiskeringLeftObjπCompColimIso :
    shrinkYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ _).obj (π P).op ⋙
      colim ≅ P :=
  (colim.isColimitCoconeCompFlip _ _).coconePointUniqueUpToIso
    (isColimitShrinkCoyonedaCocone P)

lemma shrinkYonedaCompWhiskeringLeftObjπCompColimIso_inv_app_apply (u : P.Elements) :
      (shrinkYonedaCompWhiskeringLeftObjπCompColimIso P).inv.app _ u.val =
      (colimit.ι ((π P).op ⋙ shrinkYoneda.{w}.obj u.obj) (op u)
        (shrinkYonedaObjObjEquiv.symm (𝟙 _))) := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app
    ((colim.isColimitCoconeCompFlip _ _).comp_coconePointUniqueUpToIso_inv
      (isColimitShrinkCoyonedaCocone P) (op u)) u.1) (shrinkYonedaObjObjEquiv.symm (𝟙 _))
  simp [shrinkYonedaCompWhiskeringLeftObjπCompColimIso, ← dsimp% this,
    shrinkCoyonedaEquiv_symm_app_shrinkCoyonedaObjObjEquiv_symm.{w}]

end Functor.Elements

instance [LocallySmall.{w} C] : (shrinkCoyoneda.{w} (C := C)).IsDense where
  isDenseAt P :=
    ⟨(IsColimit.whiskerEquivalenceEquiv
      (Functor.Elements.costructuredArrowShrinkCoyonedaEquivalence P)).2
        (Functor.Elements.isColimitShrinkCoyonedaCocone.{w} P)⟩

instance : (coyoneda (C := C)).IsDense :=
  .of_iso shrinkCoyonedaIsoCoyoneda

@[no_expose]
noncomputable def denseAtShrinkCoyoneda [LocallySmall.{w} C] (P : C ⥤ Type w) :
    shrinkCoyoneda.DenseAt P :=
  Functor.denseAt _ _

@[no_expose]
noncomputable def denseAtCoyoneda (P : C ⥤ Type v) :
    coyoneda.DenseAt P :=
  Functor.denseAt _ _

end CategoryTheory
