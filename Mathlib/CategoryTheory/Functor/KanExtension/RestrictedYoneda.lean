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
  {A : C ⥤ D} (α : A ⟶ shrinkYoneda.{w} ⋙ L)

open Functor.Elements in
@[no_expose]
noncomputable def isPointwiseLeftKanExtensionAlongShrinkYoneda [IsIso α]
    [∀ (P : Cᵒᵖ ⥤ Type w),
      PreservesColimit ((CategoryOfElements.π P).leftOp ⋙ shrinkYoneda.{w}) L] :
    (Functor.LeftExtension.mk _ α).IsPointwiseLeftKanExtension :=
  fun P ↦ by
    let c (s : Cocone (CostructuredArrow.proj shrinkYoneda.{w} P ⋙ A)) :
      Cocone (((CategoryOfElements.π P).leftOp ⋙ shrinkYoneda.{w, v₁, u₁}) ⋙ L) :=
      { pt := s.pt
        ι.app x :=
          inv (α.app x.unop.1.unop) ≫ s.ι.app (CostructuredArrow.mk
            (shrinkYonedaEquiv.symm x.unop.2))
        ι.naturality x y f := by
          dsimp
          let φ : CostructuredArrow.mk (shrinkYonedaEquiv.symm x.unop.2) ⟶
              CostructuredArrow.mk (shrinkYonedaEquiv.symm y.unop.2) :=
            CostructuredArrow.homMk f.unop.1.unop
              (by simp [← shrinkYonedaEquiv_symm_map.{w}])
          simp [dsimp% [φ] s.w φ, ← dsimp% α.naturality_assoc f.unop.1.unop]}
    exact
    { desc s := (isColimitOfPreserves L (isColimitShrinkYonedaCocone P)).desc (c s)
      fac s j := by
        obtain ⟨X, f, rfl⟩ := CostructuredArrow.mk_surjective j
        obtain ⟨f, rfl⟩ := shrinkYonedaEquiv.symm.surjective f
        simp [dsimp% (isColimitOfPreserves L (isColimitShrinkYonedaCocone P)).fac (c s)
          (op (Functor.elementsMk _ _ f)), c]
      uniq s m hm :=
        (isColimitOfPreserves L (isColimitShrinkYonedaCocone P)).hom_ext (fun ⟨x⟩ ↦ by
          rw [← cancel_epi (α.app _)]
          have := hm (CostructuredArrow.mk (shrinkYonedaEquiv.symm x.2))
          dsimp at this ⊢
          simp only [Category.assoc] at this
          simp [dsimp% (isColimitOfPreserves L (isColimitShrinkYonedaCocone P)).fac (c s) ⟨x⟩,
            this, c]) }

section

variable [shrinkYoneda.{w}.HasPointwiseLeftKanExtension A]
  [L.IsLeftKanExtension α]

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

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
instance :
    PreservesColimitsOfSize.{v₃, u₃} (shrinkYoneda.{w}.leftKanExtension A) :=
  (restrictedShrinkYonedaAdjunction
    (shrinkYoneda.leftKanExtensionUnit A)).leftAdjoint_preservesColimits

instance isIso_of_isLeftKanExtension : IsIso α :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α).isIso_hom

end

lemma isLeftKanExtension_along_shrinkYoneda_iff
    [shrinkYoneda.{w}.HasPointwiseLeftKanExtension A] :
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

lemma isLeftKanExtension_along_shrinkYoneda_of_preservesColimits
    [shrinkYoneda.{w}.HasPointwiseLeftKanExtension A]
    (e : shrinkYoneda.{w} ⋙ L ≅ A) [PreservesColimitsOfSize.{v₁, max w u₁} L] :
    L.IsLeftKanExtension e.inv := by
  rw [isLeftKanExtension_along_shrinkYoneda_iff]
  constructor <;> infer_instance

instance (L : (Cᵒᵖ ⥤ Type w) ⥤ D) [PreservesColimitsOfSize.{v₁, max w u₁} L]
    [shrinkYoneda.{w}.HasPointwiseLeftKanExtension (shrinkYoneda.{w} ⋙ L)] :
    L.IsLeftKanExtension (𝟙 _ : shrinkYoneda.{w} ⋙ L ⟶ _) :=
  isLeftKanExtension_along_shrinkYoneda_of_preservesColimits (Iso.refl _)

lemma isLeftAdjoint_of_preservesColimits (L : (C ⥤ Type w) ⥤ D)
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

end shrinkYoneda

section uliftYoneda

variable {L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ D}
  {A : C ⥤ D} [uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension A]
  (α : A ⟶ uliftYoneda.{max w v₂} ⋙ L)

variable (A) in
lemma hasPointwiseLeftKanExtension_shrinkYoneda_of_uliftYoneda :
    shrinkYoneda.{max w v₁ v₂}.HasPointwiseLeftKanExtension A := by
  intro
  rw [← Functor.hasPointwiseLeftKanExtensionAt_iff_of_natIso
      uliftYonedaIsoShrinkYoneda.{max w v₂} (Iso.refl A)]
  infer_instance

lemma isLeftKanExtension_along_uliftYoneda_iff :
    L.IsLeftKanExtension α ↔
      (IsIso α ∧ PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L) := by
  have := hasPointwiseLeftKanExtension_shrinkYoneda_of_uliftYoneda A
  let α' := α ≫ Functor.whiskerRight uliftYonedaIsoShrinkYoneda.hom _
  have h₁ : L.IsLeftKanExtension α ↔ L.IsLeftKanExtension α' :=
    ⟨fun _ ↦ inferInstance, fun _ ↦ by
      have : L.IsLeftKanExtension (α' ≫
        Functor.whiskerRight uliftYonedaIsoShrinkYoneda.{max w v₂}.inv _) := inferInstance
      simpa [α', ← Functor.whiskerRight_comp] using this⟩
  have h₂ : IsIso α ↔ IsIso α' := by simp [α']
  rw [h₁, isLeftKanExtension_along_shrinkYoneda_iff, h₂]

lemma isLeftKanExtension_along_uliftYoneda_of_preservesColimits
    {L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ D} (e : uliftYoneda.{max w v₂} ⋙ L ≅ A)
    [PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L] :
    L.IsLeftKanExtension e.inv := by
  rw [isLeftKanExtension_along_uliftYoneda_iff]
  constructor <;> infer_instance

instance (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ D) [PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L]
    [uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension (uliftYoneda.{max w v₂} ⋙ L)] :
    L.IsLeftKanExtension (𝟙 _ : uliftYoneda.{max w v₂} ⋙ L ⟶ _) :=
  isLeftKanExtension_along_uliftYoneda_of_preservesColimits (Iso.refl _)

section

variable [L.IsLeftKanExtension α]

@[no_expose]
noncomputable def restrictedULiftYonedaAdjunction : L ⊣ restrictedULiftYoneda.{max w v₁} A :=
  have := hasPointwiseLeftKanExtension_shrinkYoneda_of_uliftYoneda A
  (restrictedShrinkYonedaAdjunction (α ≫ Functor.whiskerRight
    (uliftYonedaIsoShrinkYoneda).hom L)).ofNatIsoRight (restrictedULiftYonedaIso A).symm

lemma restrictedULiftYonedaAdjunction_unit_app_app
    (P : Cᵒᵖ ⥤ Type max w v₁ v₂) {X : Cᵒᵖ} (x : P.obj X) :
    dsimp% ((restrictedULiftYonedaAdjunction.{w} α).unit.app P).app X x =
      ULift.up (α.app X.unop ≫ L.map (uliftYonedaEquiv.symm x)) := by
  have := hasPointwiseLeftKanExtension_shrinkYoneda_of_uliftYoneda A
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

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
instance preservesColimitsOfSize_leftKanExtension :
    PreservesColimitsOfSize.{v₃, u₃} (uliftYoneda.{max w v₂}.leftKanExtension A) :=
  (restrictedULiftYonedaAdjunction
    (uliftYoneda.leftKanExtensionUnit A)).leftAdjoint_preservesColimits

end

end uliftYoneda

end Presheaf

end CategoryTheory
