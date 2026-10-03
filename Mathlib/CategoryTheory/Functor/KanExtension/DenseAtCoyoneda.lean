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

namespace Equivalence -- to be moved

variable {C D : Type*} [Category* C] [Category* D] (e : C ≌ D) (P : D ⥤ Type w)

@[implicit_reducible, simps]
def congrElements : P.Elements ≌ (e.functor ⋙ P).Elements where
  functor.obj x :=
    Functor.elementsMk _ (e.inverse.obj x.1) (P.map (e.counitIso.inv.app x.1) x.2)
  functor.map f :=
    Functor.Elements.homMk (e.inverse.map f.1) (by
      simp only [← f.2, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        fun_inv_map, Functor.comp_obj, Functor.id_obj, Iso.inv_hom_id_app_assoc,
        Functor.comp_map])
  inverse.obj x := Functor.elementsMk _ (e.functor.obj x.1) x.2
  inverse.map f := Functor.Elements.homMk (e.functor.map f.1) f.2
  unitIso :=
    NatIso.ofComponents
      (fun x ↦ Functor.Elements.isoMk (e.counitIso.symm.app x.1) (by cat_disch))
  counitIso :=
    NatIso.ofComponents
      (fun x ↦ Functor.Elements.isoMk (e.unitIso.symm.app x.1) (by
        simp [← ConcreteCategory.comp_apply, ← Functor.map_comp]))

end Equivalence

namespace Limits -- to be moved

variable {C J J' E : Type*} [Category* C] [Category* J] [Category* J'] [Category* E]
  [HasColimitsOfShape J' E] (F : J' ⥤ J) (G : C ⥤ J ⥤ E)

@[implicit_reducible, simps]
noncomputable def colim.coconeCompFlip : Cocone (F ⋙ G.flip) where
  pt := G ⋙ (Functor.whiskeringLeft _ _ _).obj F ⋙ colim
  ι.app j' := { app X := colimit.ι (F ⋙ G.obj X) j' }
  ι.naturality j' j'' f := by
    ext X
    simpa using colimit.w (F ⋙ G.obj X) f

@[no_expose]
noncomputable def colim.isColimitCoconeCompFlip :
    IsColimit (coconeCompFlip F G) :=
  evaluationJointlyReflectsColimits _ (fun _ ↦ colimit.isColimit _)

end Limits -- to be moved

variable {C : Type u} [Category.{v} C]

namespace Functor.Elements

variable [LocallySmall.{w} C] (P : C ⥤ Type w)

/-- The (colimit) cocone which expresses a functor `P : C ⥤ Type w` as
as a colimit (indexed by `P.Elementsᵒᵖ`) of corepresentable presheaves
(defined using `shrinkCoyoneda`). -/
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

/-- For any functor `P : C ⥤ Type w`, the cocone `shrinkCoyonedaCocone P`
becomes a colimit after applying the evaluation functor at any `X : C`. -/
@[no_expose]
noncomputable def isColimitShrinkCoyonedaCoconeObj (X : C) :
    IsColimit (((evaluation _ _).obj X).mapCocone (shrinkCoyonedaCocone.{w} P)) := by
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

/-- Any functor `P : C ⥤ Type w` is a colimit of corepresentable functors
(defined using `shrinkCoyoneda`) indexed by the opposite category of the category
of elements in `P`. -/
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

/-- When `C` is a locally `w`-small category, the functor `shrinkCoyoneda : Cᵒᵖ ⥤ C ⥤ Type w`
is dense at any `P : C ⥤ Type w`: the functor `P` identifies to the colimit
of the canonical cocone of corepresentable functors indexed by the
category `CostructuredArrow shrinkCoyoneda P`. -/
@[no_expose]
noncomputable def denseAtShrinkCoyoneda [LocallySmall.{w} C] (P : C ⥤ Type w) :
    shrinkCoyoneda.DenseAt P :=
  Functor.denseAt _ _

/-- The functor `coyoneda : Cᵒᵖ ⥤ C ⥤ Type v` is dense at any `P : C ⥤ Type v`:
the functor `P` identifies to the colimit of the canonical cocone of corepresentable
functors indexed by the category `CostructuredArrow coyoneda P`. -/
@[no_expose]
noncomputable def denseAtCoyoneda (P : C ⥤ Type v) :
    coyoneda.DenseAt P :=
  Functor.denseAt _ _

end CategoryTheory
