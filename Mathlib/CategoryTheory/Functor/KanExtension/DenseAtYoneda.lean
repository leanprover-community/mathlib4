/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Comma.Presheaf.Basic

/-!
# The Yoneda embedding is dense

Any presheaf of types is a colimit of representable presheaves.
This is stated in two ways for each of the variants of the
Yoneda embedding (`yoneda`, `yonedaULift` and `shrinkYoneda`):
* as the fact that for any `P : Cᵒᵖ ⥤ Type _`, there is a colimit
cocone involving representable presheaves that is indexed by
the opposite category of the category of elements of `P`,
see `Functor.Elements.isColimitShrinkYonedaCocone` for the case
of `shrinkYoneda`.
* when the opposite of the category of elements is replaced by
categories of costructured arrows for the Yoneda embedding,
we get definitions like `denseAtShrinkYoneda`, which expresses
that the Yoneda embedding is a dense functor, a fact which is
also stated using `Functor.IsDense` instances.

## References

* https://ncatlab.org/nlab/show/dense+subcategory

-/

@[expose] public section

universe w v u

namespace CategoryTheory

namespace Equivalence -- to be moved

variable {C D : Type*} [Category* C] [Category* D] (e : C ≌ D) (P : D ⥤ Type w)

@[implicit_reducible, simps]
def congrElements : P.Elements ≌ (e.functor ⋙ P).Elements where
  functor.obj x :=
    Functor.elementsMk _ (e.inverse.obj x.1) (P.map (e.counitIso.inv.app x.1) x.2)
  functor.map f :=
    CategoryOfElements.homMk _ _ (e.inverse.map f.1) (by
      simp only [← f.2, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        fun_inv_map, Functor.comp_obj, Functor.id_obj, Iso.inv_hom_id_app_assoc,
        Functor.comp_map])
  inverse.obj x := Functor.elementsMk _ (e.functor.obj x.1) x.2
  inverse.map f := CategoryOfElements.homMk _ _ (e.functor.map f.1) f.2
  unitIso :=
    NatIso.ofComponents
      (fun x ↦ CategoryOfElements.isoMk _ _ (e.counitIso.symm.app x.1) (by cat_disch))
  counitIso :=
    NatIso.ofComponents
      (fun x ↦ CategoryOfElements.isoMk _ _ (e.unitIso.symm.app x.1) (by
        simp [← ConcreteCategory.comp_apply, ← Functor.map_comp]))

end Equivalence

namespace Limits -- to be moved

variable {C J J' E : Type*} [Category* C] [Category* J] [Category* J'] [Category* E]
  [HasColimitsOfShape J' E]
  (F : J' ⥤ J) (G : C ⥤ J ⥤ E)

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

open Opposite Limits

variable {C : Type u} [Category.{v} C]

namespace Functor.Elements

/-- The (colimit) cocone which expresses a presheaf `P : Cᵒᵖ ⥤ Type w` as
as a colimit (indexed by `P.Elementsᵒᵖ`) of representable presheaves
(defined using `shrinkYoneda`). -/
@[implicit_reducible, simps]
noncomputable def shrinkYonedaCocone [LocallySmall.{w} C] (P : Cᵒᵖ ⥤ Type w) :
    Cocone ((CategoryOfElements.π P).leftOp ⋙ shrinkYoneda.{w}) where
  pt := P
  ι.app x := shrinkYonedaEquiv.symm x.unop.snd
  ι.naturality x y f := by simp [← shrinkYonedaEquiv_symm_map.{w}]

@[no_expose]
noncomputable def isColimitShrinkYonedaCoconeObj
    [LocallySmall.{w} C] (P : Cᵒᵖ ⥤ Type w) (X : Cᵒᵖ) :
    IsColimit (((evaluation _ _).obj X).mapCocone (shrinkYonedaCocone.{w} P)) :=
  Nonempty.some (by
    rw [Types.isColimit_iff_coconeTypesIsColimit]
    refine ⟨⟨fun y₁ y₂ hy ↦ ?_, fun x ↦ ?_⟩⟩
    · obtain ⟨⟨Y₁⟩, y₁, rfl⟩ := Functor.ιColimitType_jointly_surjective _ y₁
      obtain ⟨⟨Y₂⟩, y₂, rfl⟩ := Functor.ιColimitType_jointly_surjective _ y₂
      have (Y : P.Elements) (y : (shrinkYoneda.{w}.obj (Y.fst.unop)).obj X) :
          (((CategoryOfElements.π P).leftOp ⋙ shrinkYoneda.{w}) ⋙
            (evaluation _ _).obj X).ιColimitType (op Y) y =
          Functor.ιColimitType _
            (op (elementsMk _ _ (P.map (shrinkYonedaObjObjEquiv y).op Y.snd)))
              (by exact shrinkYonedaObjObjEquiv.symm (𝟙 _)) :=
        Functor.ιColimitType_eq_of_map_eq_map _ _ _ (𝟙 _)
          ((CategoryOfElements.homMk _ _
            ((shrinkYonedaObjObjEquiv y).op) (by simp)).op) (by
              simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm])
      rw [this Y₁ y₁, this Y₂ y₂]
      congr 3
    · refine ⟨Functor.ιColimitType _ (op (elementsMk _ _ x))
        (shrinkYonedaObjObjEquiv.symm (𝟙 _)), ?_⟩
      simp [shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm.{w}])

/-- Any presheaf `P` is a colimit of representable presheaves
(defined using `shrinkYoneda`) indexed by the opposite category of elements in `P`. -/
@[no_expose]
noncomputable def isColimitShrinkYonedaCocone [LocallySmall.{w} C] (P : Cᵒᵖ ⥤ Type w) :
    IsColimit (shrinkYonedaCocone.{w} P) :=
  evaluationJointlyReflectsColimits _ (isColimitShrinkYonedaCoconeObj.{w} P)

/-- The (colimit) cocone which expresses a presheaf `P : Cᵒᵖ ⥤ Type v` as
as a colimit (indexed by `P.Elementsᵒᵖ`) of representable presheaves
(defined using `yoneda`). -/
@[implicit_reducible, simps]
def yonedaCocone (P : Cᵒᵖ ⥤ Type v) :
    Cocone ((CategoryOfElements.π P).leftOp ⋙ yoneda) where
  pt := P
  ι.app x := yonedaEquiv.symm x.unop.snd
  ι.naturality x y f := by simp [yonedaEquiv_symm_naturality_left f.unop.1.unop]

@[no_expose]
noncomputable def isColimitYonedaCoconeObj (P : Cᵒᵖ ⥤ Type v) (X : Cᵒᵖ) :
    IsColimit (((evaluation _ _).obj X).mapCocone (yonedaCocone P)) := by
  refine (IsColimit.equivOfNatIsoOfIso
    (isoWhiskerRight (isoWhiskerLeft _ shrinkYonedaIsoYoneda) _) _ _ ?_).1
    (isColimitShrinkYonedaCoconeObj.{v} P X)
  refine Cocone.ext (Iso.refl _) (fun _ ↦ ?_)
  ext
  simp [shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm.{v}, yonedaEquiv]

/-- Any presheaf `P` is a colimit of representable presheaves
(defined using `yoneda`) indexed by the opposite category of elements in `P`. -/
@[no_expose]
noncomputable def isColimitYonedaCocone (P : Cᵒᵖ ⥤ Type v) :
    IsColimit (yonedaCocone P) :=
  evaluationJointlyReflectsColimits _ (isColimitYonedaCoconeObj P)

/-- The (colimit) cocone which expresses a presheaf `P : Cᵒᵖ ⥤ Type max w v` as
as a colimit (indexed by `P.Elementsᵒᵖ`) of representable presheaves
(defined using `uliftYoneda`). -/
@[implicit_reducible, simps]
def uliftYonedaCocone (P : Cᵒᵖ ⥤ Type max w v) :
    Cocone ((CategoryOfElements.π P).leftOp ⋙ uliftYoneda.{w}) where
  pt := P
  ι.app x := uliftYonedaEquiv.symm x.unop.snd
  ι.naturality x y f := by simp [uliftYonedaEquiv_symm_naturality_left f.unop.1.unop]

attribute [local implicit_reducible] Equiv.ulift in
@[no_expose]
noncomputable def isColimitUliftYonedaCoconeObj (P : Cᵒᵖ ⥤ Type max w v) (X : Cᵒᵖ) :
    IsColimit (((evaluation _ _).obj X).mapCocone (uliftYonedaCocone.{w} P)) := by
  refine (IsColimit.equivOfNatIsoOfIso
    (isoWhiskerRight (isoWhiskerLeft _ uliftYonedaIsoShrinkYoneda.symm) _) _ _ ?_).1
    (isColimitShrinkYonedaCoconeObj.{max w v} P X)
  refine Cocone.ext (Iso.refl _) (fun _ ↦ ?_)
  ext x
  simp [uliftYonedaIsoShrinkYoneda,
    shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm.{max w v},
    uliftYonedaEquiv, Equiv.ulift]

/-- Any presheaf `P` is a colimit of representable presheaves
(defined using `uliftYoneda`) indexed by the opposite category of elements in `P`. -/
@[no_expose]
noncomputable def isColimitUliftYonedaCocone (P : Cᵒᵖ ⥤ Type max w v) :
    IsColimit (uliftYonedaCocone.{w} P) :=
  evaluationJointlyReflectsColimits _ (isColimitUliftYonedaCoconeObj P)

end Functor.Elements

instance [LocallySmall.{w} C] : (shrinkYoneda.{w} (C := C)).IsDense where
  isDenseAt P :=
    ⟨(IsColimit.whiskerEquivalenceEquiv
      (CategoryOfElements.costructuredArrowShrinkYonedaEquivalence P)).2
        (Functor.Elements.isColimitShrinkYonedaCocone.{w} P)⟩

instance : (uliftYoneda.{w} (C := C)).IsDense :=
  .of_iso uliftYonedaIsoShrinkYoneda.symm

instance : (yoneda (C := C)).IsDense :=
  .of_iso uliftYonedaIsoYoneda

/-- When `C` is a locally `w`-small category, the functor `shrinkYoneda : C ⥤ Cᵒᵖ ⥤ Type w`
is dense at any `P : Cᵒᵖ ⥤ Type w`: the presheaf `P` identifies to the colimit
of the canonical cocone of representable presheaves indexed by the
category `CostructuredArrow shrinkYoneda P`. -/
@[no_expose]
noncomputable def denseAtShrinkYoneda [LocallySmall.{w} C] (P : Cᵒᵖ ⥤ Type w) :
    shrinkYoneda.DenseAt P :=
  Functor.denseAt _ _

@[no_expose]
noncomputable def denseAtYoneda (P : Cᵒᵖ ⥤ Type v) : yoneda.DenseAt P :=
  Functor.denseAt _ _

/-- When `C` is a category where morphisms are in `Type v`,
the functor `uliftYoneda.{w} : C ⥤ Cᵒᵖ ⥤ Type max w v` is dense at
any `P : Cᵒᵖ ⥤ Type max w v`: the presheaf `P` identifies to the colimit
of the canonical cocone of representable presheaves indexed by the
category `CostructuredArrow uliftYoneda P`. -/
@[no_expose]
noncomputable def denseAtUliftYoneda (P : Cᵒᵖ ⥤ Type max w v) : uliftYoneda.DenseAt P :=
  Functor.denseAt _ _

set_option backward.isDefEq.respectTransparency false in
/-- Given a functor `F : I ⥤ C`, a cocone `c` on `F ⋙ yoneda : I ⥤ Cᵒᵖ ⥤ Type v₁` induces a
    functor `I ⥤ CostructuredArrow yoneda c.pt` which maps `i : I` to the leg
    `yoneda.obj (F.obj i) ⟶ c.pt`. If `c` is a colimit cocone, then that functor is
    final.

    Proposition 2.6.3(ii) in [Kashiwara2006] -/
theorem Presheaf.final_toCostructuredArrow_comp_pre
    {I : Type v} [SmallCategory I] (F : I ⥤ C)
    {c : Cocone (F ⋙ yoneda)} (hc : IsColimit c) :
    Functor.Final (c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) := by
  apply Functor.final_of_isTerminal_colimit_comp_yoneda
  suffices IsTerminal (colimit ((c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) ⋙
      CostructuredArrow.toOver yoneda c.pt)) by
    apply IsTerminal.isTerminalOfObj (overEquivPresheafCostructuredArrow c.pt).inverse
    apply IsTerminal.ofIso this
    refine ?_ ≪≫ (preservesColimitIso (overEquivPresheafCostructuredArrow c.pt).inverse _).symm
    apply HasColimit.isoOfNatIso
    exact Functor.isoWhiskerLeft _
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow c.pt).isoCompInverse
  let isc := isColimitOfPreserves (Over.forget _)
    (colimit.isColimit ((c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) ⋙
      CostructuredArrow.toOver yoneda c.pt))
  exact IsTerminal.ofIso Over.mkIdTerminal
    (Over.isoMk (hc.coconePointUniqueUpToIso isc) (hc.hom_ext (fun i ↦ by simp)))

namespace Functor.Elements

variable [LocallySmall.{w} C] (P : C ⥤ Type w)

@[implicit_reducible, simps]
noncomputable def shrinkCoyonedaCocone :
    Cocone ((CategoryOfElements.π P).op ⋙ shrinkCoyoneda.{w}) where
  pt := P
  ι.app x := shrinkCoyonedaEquiv.symm x.unop.2
  ι.naturality x y f := by
    dsimp
    simp only [← f.unop.2, shrinkCoyonedaEquiv_symm_map.{w}, Category.comp_id]

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
    obtain ⟨f : j.fst ⟶ X, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective f
    simp [shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm.{w},
      dsimp% shrinkCoyonedaEquiv_symm_app_shrinkCoyonedaObjObjEquiv_symm j.2 f.op]

@[no_expose]
noncomputable def isColimitShrinkCoyonedaCocone :
    IsColimit (shrinkCoyonedaCocone P) :=
  evaluationJointlyReflectsColimits _ (isColimitShrinkCoyonedaCoconeObj _)

variable [HasColimitsOfShape P.Elementsᵒᵖ (Type w)]

/-- If `F : C ⥤ Type w` and `C` is locally `w`-small, then `F` identifies to the composition
`shrinkYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π F).op ⋙ colim`. -/
@[no_expose]
noncomputable def shrinkYonedaCompWhiskeringLeftObjπCompColimIso :
    shrinkYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π P).op ⋙
      colim ≅ P :=
  (colim.isColimitCoconeCompFlip _ _).coconePointUniqueUpToIso
    (isColimitShrinkCoyonedaCocone P)

lemma shrinkYonedaCompWhiskeringLeftObjπCompColimIso_inv_app_apply (u : P.Elements) :
      (shrinkYonedaCompWhiskeringLeftObjπCompColimIso P).inv.app _ u.snd =
      (colimit.ι ((CategoryOfElements.π P).op ⋙ shrinkYoneda.{w}.obj u.fst) (op u)
        (shrinkYonedaObjObjEquiv.symm (𝟙 _))) := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app
    ((colim.isColimitCoconeCompFlip _ _).comp_coconePointUniqueUpToIso_inv
      (isColimitShrinkCoyonedaCocone P) (op u)) u.1) (shrinkYonedaObjObjEquiv.symm (𝟙 _))
  simp [shrinkYonedaCompWhiskeringLeftObjπCompColimIso, ← dsimp% this,
    dsimp% shrinkCoyonedaEquiv_symm_app_shrinkCoyonedaObjObjEquiv_symm.{w} u.2 (𝟙 (op u.1))]

end Functor.Elements

end CategoryTheory
