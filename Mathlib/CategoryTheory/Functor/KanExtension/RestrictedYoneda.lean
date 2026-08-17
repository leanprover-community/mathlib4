/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.RestrictedYoneda

/-!
# ...

-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Presheaf

open Limits Opposite

section shrinkYoneda

variable [LocallySmall.{w} C] [LocallySmall.{w} D] {L : (Cᵒᵖ ⥤ Type w) ⥤ D}
  {A : C ⥤ D} [shrinkYoneda.{w}.HasPointwiseLeftKanExtension A]
  (α : A ⟶ shrinkYoneda.{w} ⋙ L) [L.IsLeftKanExtension α]

variable (A) in
noncomputable def restrictedShrinkYonedaHomEquivAux (P : Cᵒᵖ ⥤ Type w) (E : D) :
    (CostructuredArrow.proj shrinkYoneda.{w} P ⋙ A ⟶
      (Functor.const (CostructuredArrow shrinkYoneda.{w} P)).obj E) ≃
    (P ⟶ (restrictedShrinkYoneda A).obj E) where
  toFun f :=
    { app X := ↾(fun x ↦ shrinkYonedaObjObjEquiv.symm
        (f.app (CostructuredArrow.mk (shrinkYonedaEquiv.symm x))))
      naturality X Y g := by
        ext x
        let φ : CostructuredArrow.mk (shrinkYonedaEquiv.{w}.symm (P.map g x)) ⟶
            CostructuredArrow.mk (shrinkYonedaEquiv.symm x) :=
          CostructuredArrow.homMk g.unop (by simp [shrinkYonedaEquiv_symm_map.{w}])
        simp [← shrinkYonedaObjObjEquiv_symm_comp.{w},
          dsimp% [φ] f.naturality φ] }
  invFun g :=
    { app y := shrinkYonedaObjObjEquiv.{w} (shrinkYonedaEquiv (y.hom ≫ g) :)
      naturality y y' f := by
        dsimp
        simp only [← CostructuredArrow.w f, Category.comp_id, Category.assoc,
          ← dsimp% shrinkYonedaObjObjEquiv_obj_map (A.map f.left).op,
          ← shrinkYonedaEquiv_naturality]
        dsimp }
  left_inv f := by
    ext X
    let e : (CostructuredArrow.mk (shrinkYonedaEquiv.symm ((X.hom.app (op X.left))
        (shrinkYonedaObjObjEquiv.symm (𝟙 X.left))))) ≅ X :=
      CostructuredArrow.isoMk (Iso.refl _)
        (shrinkYonedaEquiv.injective (by simp [shrinkYonedaEquiv_apply]))
    simpa [e, shrinkYonedaEquiv_apply] using f.naturality e.inv
  right_inv g := by ext; simp [shrinkYonedaEquiv_symm_comp.{w}]

noncomputable def restrictedShrinkYonedaHomEquiv {P : Cᵒᵖ ⥤ Type w} {E : D} :
    (L.obj P ⟶ E) ≃ (P ⟶ (restrictedShrinkYoneda.{w} A).obj E) :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α P).homEquiv.trans
    (restrictedShrinkYonedaHomEquivAux A P E)

@[reassoc (attr := simp)]
lemma comp_restrictedShrinkYonedaHomEquiv_symm_apply
    {P : Cᵒᵖ ⥤ Type w} {E : D} (f : P ⟶ (restrictedShrinkYoneda A).obj E)
    (j : CostructuredArrow shrinkYoneda.{w} P) :
    α.app j.left ≫ L.map j.hom ≫ (restrictedShrinkYonedaHomEquiv α).symm f =
      shrinkYonedaObjObjEquiv (f.app (op j.left) (shrinkYonedaEquiv j.hom)) := by
  simpa using! (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P).fac
    (Cocone.mk _ ((restrictedShrinkYonedaHomEquivAux A P E).symm f)) j

@[reassoc]
lemma restrictedShrinkYonedaHomEquiv_symm_naturality_left
    {P P' : Cᵒᵖ ⥤ Type w} {E : D} (f : P ⟶ P') (g : P' ⟶ (restrictedShrinkYoneda.{w} A).obj E) :
    (restrictedShrinkYonedaHomEquiv α).symm (f ≫ g) =
      L.map f ≫ (restrictedShrinkYonedaHomEquiv α).symm g :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P).hom_ext (fun j ↦ by
    let j' := CostructuredArrow.mk (j.hom ≫ f)
    trans α.app j'.left ≫ L.map j'.hom ≫ (restrictedShrinkYonedaHomEquiv α).symm g
    · simp
      simp [j', shrinkYonedaEquiv_apply]
    · simp [j'])

@[reassoc]
lemma restrictedShrinkYonedaHomEquiv_naturality_left
    {P P' : Cᵒᵖ ⥤ Type w} {E : D} (f : P ⟶ P') (g : L.obj P' ⟶ E) :
    (restrictedShrinkYonedaHomEquiv α) (L.map f ≫ g) =
      f ≫ restrictedShrinkYonedaHomEquiv α g :=
  (restrictedShrinkYonedaHomEquiv α).symm.injective
    (by simp [restrictedShrinkYonedaHomEquiv_symm_naturality_left])

@[reassoc]
lemma restrictedShrinkYonedaHomEquiv_symm_naturality_right
    {P : Cᵒᵖ ⥤ Type w} {E E' : D} (f : P ⟶ (restrictedShrinkYoneda.{w} A).obj E) (g : E ⟶ E') :
    (restrictedShrinkYonedaHomEquiv α).symm (f ≫ (restrictedShrinkYoneda.{w} A).map g) =
      (restrictedShrinkYonedaHomEquiv α).symm f ≫ g :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P).hom_ext
    (by simp [shrinkYonedaObjObjEquiv_map_app.{w}])

@[reassoc]
lemma restrictedShrinkYonedaHomEquiv_naturality_right
    {P : Cᵒᵖ ⥤ Type w} {E E' : D} (f : L.obj P ⟶ E) (g : E ⟶ E') :
    restrictedShrinkYonedaHomEquiv α (f ≫ g) =
    restrictedShrinkYonedaHomEquiv α f ≫ (restrictedShrinkYoneda A).map g :=
  (restrictedShrinkYonedaHomEquiv α).symm.injective
    (by simp [restrictedShrinkYonedaHomEquiv_symm_naturality_right])

attribute [local simp] restrictedShrinkYonedaHomEquiv_naturality_right
  restrictedShrinkYonedaHomEquiv_symm_naturality_left in
noncomputable def restrictedShrinkYonedaAdjunction : L ⊣ restrictedShrinkYoneda.{w} A :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := restrictedShrinkYonedaHomEquiv α }

include α in
/-- Any left Kan extension along the Yoneda embedding preserves colimits. -/
lemma preservesColimitsOfSize_of_isLeftKanExtension :
    PreservesColimitsOfSize.{v₃, u₃} L :=
  (restrictedShrinkYonedaAdjunction α).leftAdjoint_preservesColimits

end shrinkYoneda

section uliftYoneda

variable {L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ D}
  {A : C ⥤ D} [uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension A]
  (α : A ⟶ uliftYoneda.{max w v₂} ⋙ L) [L.IsLeftKanExtension α]

noncomputable def restrictedULiftYonedaAdjunction : L ⊣ restrictedULiftYoneda.{max w v₁} A :=
  have : shrinkYoneda.{max w v₁ v₂}.HasPointwiseLeftKanExtension A := fun Y ↦ by
    rw [← Functor.hasPointwiseLeftKanExtensionAt_iff_of_natIso
      uliftYonedaIsoShrinkYoneda.{max w v₂} (Iso.refl A)]
    infer_instance
  (restrictedShrinkYonedaAdjunction (α ≫ Functor.whiskerRight
    (uliftYonedaIsoShrinkYoneda).hom L)).ofNatIsoRight (restrictedULiftYonedaIso A).symm

lemma restrictedULiftYonedaAdjunction_unit_app_app_down
    (P : Cᵒᵖ ⥤ Type (max w v₁ v₂)) {X : Cᵒᵖ} (x : P.obj X) :
    (((restrictedULiftYonedaAdjunction α).unit.app P).app X x).down =
      α.app X.unop ≫ L.map (uliftYonedaEquiv.symm x) := by
  dsimp
  sorry

instance : IsIso α := by
  have : uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension A := inferInstance
  have : L.IsLeftKanExtension α := inferInstance
  sorry

end uliftYoneda

lemma isLeftAdjoint_of_preservesColimits [LocallySmall.{w} C] (L : (C ⥤ Type w) ⥤ D)
    [PreservesColimitsOfSize.{v₁, max w u₁} L]
    [shrinkYoneda.{w}.HasPointwiseLeftKanExtension
      (shrinkYoneda.{w} ⋙ (opOpEquivalence C).congrLeft.functor.comp L)] :
    L.IsLeftAdjoint := sorry

end Presheaf

end CategoryTheory
