/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAtYoneda
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
  (α : A ⟶ shrinkYoneda.{w} ⋙ L)

section

variable [L.IsLeftKanExtension α]

variable (A) in
private noncomputable def restrictedShrinkYonedaHomEquivAux (P : Cᵒᵖ ⥤ Type w) (E : D) :
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

@[no_expose]
noncomputable def restrictedShrinkYonedaHomEquiv {P : Cᵒᵖ ⥤ Type w} {E : D} :
    (L.obj P ⟶ E) ≃ (P ⟶ (restrictedShrinkYoneda.{w} A).obj E) :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α P).homEquiv.trans
    (restrictedShrinkYonedaHomEquivAux A P E)

@[reassoc (attr := simp)]
lemma comp_restrictedShrinkYonedaHomEquiv_symm_apply
    {P : Cᵒᵖ ⥤ Type w} {E : D} (f : P ⟶ (restrictedShrinkYoneda A).obj E)
    {X : C} (g : shrinkYoneda.{w}.obj X ⟶ P) :
    α.app X ≫ L.map g ≫ (restrictedShrinkYonedaHomEquiv α).symm f =
      shrinkYonedaObjObjEquiv (f.app (op X) (shrinkYonedaEquiv g)) := by
  simpa using! (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P).fac
    (Cocone.mk _ ((restrictedShrinkYonedaHomEquivAux A P E).symm f)) (CostructuredArrow.mk g)

lemma restrictedShrinkYonedaHomEquiv_app_apply
    {P : Cᵒᵖ ⥤ Type w} {E : D} (f : L.obj P ⟶ E) {X : Cᵒᵖ} (x : P.obj X) :
    (restrictedShrinkYonedaHomEquiv α f).app X x =
      shrinkYonedaObjObjEquiv.symm (α.app X.unop ≫ L.map (shrinkYonedaEquiv.symm x) ≫ f) := by
  obtain ⟨f, rfl⟩ := (restrictedShrinkYonedaHomEquiv α).symm.surjective f
  exact shrinkYonedaObjObjEquiv.injective (by simp)

@[reassoc]
lemma restrictedShrinkYonedaHomEquiv_symm_naturality_left
    {P P' : Cᵒᵖ ⥤ Type w} {E : D} (f : P ⟶ P') (g : P' ⟶ (restrictedShrinkYoneda.{w} A).obj E) :
    (restrictedShrinkYonedaHomEquiv α).symm (f ≫ g) =
      L.map f ≫ (restrictedShrinkYonedaHomEquiv α).symm g :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P).hom_ext (fun j ↦ by
    trans α.app j.left ≫ L.map (j.hom ≫ f) ≫ (restrictedShrinkYonedaHomEquiv α).symm g
    · dsimp
      simp only [comp_restrictedShrinkYonedaHomEquiv_symm_apply, Category.assoc]
      simp [shrinkYonedaEquiv_apply]
    · simp)

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

lemma restrictedShrinkYonedaAdjunction_homEquiv (P : Cᵒᵖ ⥤ Type w) (E : D) :
    (restrictedShrinkYonedaAdjunction.{w} α).homEquiv P E =
      restrictedShrinkYonedaHomEquiv α := by
  simp [restrictedShrinkYonedaAdjunction]

lemma restrictedShrinkYonedaAdjunction_unit_app_app
    (P : Cᵒᵖ ⥤ Type w) {X : Cᵒᵖ} (x : P.obj X) :
    ((restrictedShrinkYonedaAdjunction.{w} α).unit.app P).app X x =
      shrinkYonedaObjObjEquiv.symm
        (α.app X.unop ≫ L.map (shrinkYonedaEquiv.symm x)) := by
  simp [restrictedShrinkYonedaAdjunction, restrictedShrinkYonedaHomEquiv_app_apply.{w}]

include α in
/-- Any left Kan extension along the Yoneda embedding preserves colimits. -/
lemma preservesColimitsOfSize_of_isLeftKanExtension :
    PreservesColimitsOfSize.{v₃, u₃} L :=
  (restrictedShrinkYonedaAdjunction α).leftAdjoint_preservesColimits

instance isIso_of_isLeftKanExtension : IsIso α :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α).isIso_hom

end

lemma isLeftKanExtension_along_shrinkYoneda_iff :
    L.IsLeftKanExtension α ↔
      (IsIso α ∧ PreservesColimitsOfSize.{v₁, max w u₁} L) := by
  refine ⟨fun _ ↦ ⟨inferInstance, preservesColimitsOfSize_of_isLeftKanExtension α⟩,
    fun ⟨_, _⟩ ↦
      Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftKanExtension
        (E := Functor.LeftExtension.mk _ α) (fun P ↦ ?_)⟩
  refine (IsColimit.equivOfNatIsoOfIso
    (Functor.isoWhiskerLeft _ (asIso α) ≪≫ (Functor.associator _ _ _).symm) _ _ ?_).symm
    (isColimitOfPreserves L (denseAtShrinkYoneda.{w} P))
  exact Cocone.ext (Iso.refl _)

end shrinkYoneda

section uliftYoneda

variable {L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ D}
  {A : C ⥤ D} [uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension A]
  (α : A ⟶ uliftYoneda.{max w v₂} ⋙ L) [L.IsLeftKanExtension α]

@[no_expose]
noncomputable def restrictedULiftYonedaAdjunction : L ⊣ restrictedULiftYoneda.{max w v₁} A :=
  have : shrinkYoneda.{max w v₁ v₂}.HasPointwiseLeftKanExtension A := fun Y ↦ by
    rw [← Functor.hasPointwiseLeftKanExtensionAt_iff_of_natIso
      uliftYonedaIsoShrinkYoneda.{max w v₂} (Iso.refl A)]
    infer_instance
  (restrictedShrinkYonedaAdjunction (α ≫ Functor.whiskerRight
    (uliftYonedaIsoShrinkYoneda).hom L)).ofNatIsoRight (restrictedULiftYonedaIso A).symm

lemma restrictedULiftYonedaAdjunction_unit_app_app
    (P : Cᵒᵖ ⥤ Type max w v₁ v₂) {X : Cᵒᵖ} (x : P.obj X) :
    dsimp% ((restrictedULiftYonedaAdjunction.{w} α).unit.app P).app X x =
      ULift.up (α.app X.unop ≫ L.map (uliftYonedaEquiv.symm x)) := by
  have : shrinkYoneda.{max w v₁ v₂}.HasPointwiseLeftKanExtension A := fun _ ↦ by
    rw [← Functor.hasPointwiseLeftKanExtensionAt_iff_of_natIso
      uliftYonedaIsoShrinkYoneda.{max w v₂} (Iso.refl A)]
    infer_instance
  simp [restrictedULiftYonedaAdjunction, restrictedShrinkYonedaAdjunction_unit_app_app
    (α ≫ Functor.whiskerRight uliftYonedaIsoShrinkYoneda.{max w v₂}.hom L),
    uliftYonedaIsoShrinkYoneda_inv_app_app.{max w v₁}, ← Functor.map_comp,
    uliftYonedaIsoShrinkYoneda_hom_app_comp_shrinkYoneda_symm.{max w v₂}]

@[simp]
lemma restrictedULiftYonedaAdjunction_homEquiv_app {P : Cᵒᵖ ⥤ Type max w v₁ v₂}
    {Y : D} (f : L.obj P ⟶ Y) {Z : Cᵒᵖ} (z : P.obj Z) :
    ((restrictedULiftYonedaAdjunction.{w} α).homEquiv P Y f).app Z z =
      ULift.up (α.app Z.unop ≫ L.map (uliftYonedaEquiv.symm z) ≫ f) := by
  simp [Adjunction.homEquiv_unit, restrictedULiftYonedaAdjunction_unit_app_app]

instance : IsIso α :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α).isIso_hom

end uliftYoneda

lemma isLeftAdjoint_of_preservesColimits [LocallySmall.{w} C] [LocallySmall.{w} D]
    (L : (C ⥤ Type w) ⥤ D)
    [PreservesColimitsOfSize.{v₁, max w u₁} L]
    [shrinkYoneda.{w}.HasPointwiseLeftKanExtension
      (shrinkYoneda.{w} ⋙ (opOpEquivalence C).congrLeft.functor.comp L)] :
    L.IsLeftAdjoint := by
  let L' := (opOpEquivalence C).congrLeft.functor ⋙ L
  have : L'.IsLeftKanExtension (𝟙 (shrinkYoneda.{w} ⋙ L')) := by
    rw [isLeftKanExtension_along_shrinkYoneda_iff]
    constructor <;> infer_instance
  have := (restrictedShrinkYonedaAdjunction.{w} (𝟙 (shrinkYoneda.{w} ⋙ L'))).isLeftAdjoint
  exact Functor.isLeftAdjoint_of_iso ((opOpEquivalence C).congrLeft.invFunIdAssoc L)

end Presheaf

end CategoryTheory
