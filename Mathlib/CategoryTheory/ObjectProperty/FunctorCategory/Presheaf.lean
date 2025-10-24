/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.Limits
import Mathlib.CategoryTheory.ObjectProperty.Local
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Presheaves of types which preserves a limit

Let `F : J ⥤ Cᵒᵖ` be a functor. We show that a presheaf `P : Cᵒᵖ ⥤ Type w`
preserves the limit of `F` iff `P` is a local object with respect to a suitable
family of morphisms in `Cᵒᵖ ⥤ Type w` (this family contains `1` or `0` morphism
depending on whether the limit of `F` exists or not).

-/

universe w w' v v' u u'

namespace CategoryTheory

open Limits Opposite

section

variable {C : Type u} [Category.{v} C]

namespace FunctorToTypes

protected abbrev Small (F : C ⥤ Type w') := ∀ (X : C), _root_.Small.{w} (F.obj X)

@[simps]
noncomputable def shrink (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F] :
    C ⥤ Type w where
  obj X := Shrink.{w} (F.obj X)
  map {X Y} f := equivShrink.{w} _ ∘ F.map f ∘ (equivShrink.{w} _).symm

attribute [local simp] FunctorToTypes.naturality in
@[simps]
noncomputable def shrinkMap {F G : C ⥤ Type w'} (τ : F ⟶ G) [FunctorToTypes.Small.{w} F]
    [FunctorToTypes.Small.{w} G] :
    shrink.{w} F ⟶ shrink.{w} G where
  app X := equivShrink.{w} _ ∘ τ.app X ∘ (equivShrink.{w} _).symm

end FunctorToTypes

section

variable [LocallySmall.{w} C]

instance (X : C) : FunctorToTypes.Small.{w} (yoneda.obj X) :=
  fun _ ↦ by dsimp; infer_instance

-- to be moved
@[pp_with_univ, simps -isSimp obj map]
noncomputable def shrinkYoneda :
    C ⥤ Cᵒᵖ ⥤ Type w where
  obj X := FunctorToTypes.shrink (yoneda.obj X)
  map f := FunctorToTypes.shrinkMap (yoneda.map f)

noncomputable def shrinkYonedaObjObjEquiv {X : C} {Y : Cᵒᵖ} :
    ((shrinkYoneda.{w}.obj X).obj Y) ≃ (Y.unop ⟶ X) :=
  (equivShrink _).symm

noncomputable def shrinkYonedaEquiv {X : C} {P : Cᵒᵖ ⥤ Type w} :
    (shrinkYoneda.{w}.obj X ⟶ P) ≃ P.obj (op X) where
  toFun τ := τ.app _ (equivShrink.{w} _ (𝟙 X))
  invFun x :=
    { app Y f := P.map ((equivShrink.{w} _).symm f).op x
      naturality Y Z g := by ext; simp [shrinkYoneda] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYoneda] using congr_fun (τ.naturality f.op).symm (equivShrink _ (𝟙 X))
  right_inv x := by simp

lemma map_shrinkYonedaEquiv {X Y : C} {P : Cᵒᵖ ⥤ Type w} (f : shrinkYoneda.obj X ⟶ P)
    (g : Y ⟶ X) : P.map g.op (shrinkYonedaEquiv f) =
      f.app (op Y) (shrinkYonedaObjObjEquiv.symm g) := by
  simp [shrinkYonedaObjObjEquiv, shrinkYonedaEquiv, shrinkYoneda,
    ← FunctorToTypes.naturality]

lemma shrinkYonedaEquiv_shrinkYoneda_map {X Y : C} (f : X ⟶ Y) :
    shrinkYonedaEquiv (shrinkYoneda.{w}.map f) = shrinkYonedaObjObjEquiv.symm f := by
  simp [shrinkYonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv]

lemma shrinkYonedaEquiv_comp {X : C} {P Q : Cᵒᵖ ⥤ Type w} (α : shrinkYoneda.obj X ⟶ P)
    (β : P ⟶ Q) :
    shrinkYonedaEquiv (α ≫ β) = β.app _ (shrinkYonedaEquiv α) := by
  simp [shrinkYonedaEquiv]

lemma shrinkYonedaEquiv_naturality {X Y : C} {P : Cᵒᵖ ⥤ Type w}
    (f : shrinkYoneda.obj X ⟶ P) (g : Y ⟶ X) :
    P.map g.op (shrinkYonedaEquiv f) = shrinkYonedaEquiv (shrinkYoneda.map g ≫ f) := by
  simpa [shrinkYonedaEquiv, shrinkYoneda]
    using congr_fun (f.naturality g.op).symm ((equivShrink _) (𝟙 _))

@[reassoc]
lemma shrinkYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {P : Cᵒᵖ ⥤ Type w} (t : P.obj X) :
    shrinkYonedaEquiv.symm (P.map f t) =
      shrinkYoneda.map f.unop ≫ shrinkYonedaEquiv.symm t :=
  shrinkYonedaEquiv.injective (by
    obtain ⟨t, rfl⟩ := shrinkYonedaEquiv.surjective t
    rw [← shrinkYonedaEquiv_naturality]
    simp)

@[reassoc]
lemma shrinkYonedaEquiv_symm_comp {X : Cᵒᵖ} {P Q : Cᵒᵖ ⥤ Type w} (x : P.obj X) (α : P ⟶ Q) :
    shrinkYonedaEquiv.symm x ≫ α = shrinkYonedaEquiv.symm (α.app _ x) :=
  shrinkYonedaEquiv.injective (by simp [shrinkYonedaEquiv])

end

end

namespace Presheaf

section

variable {C : Type u} [Category.{v} C]
  {J : Type u'} [Category.{v'} J] [LocallySmall.{w} C]
  {F : J ⥤ Cᵒᵖ} (c : Cone F) {c' : Cocone (F.leftOp ⋙ shrinkYoneda.{w})}
  (hc : IsLimit c) (hc' : IsColimit c') (P : Cᵒᵖ ⥤ Type w)

variable {P} in
@[simps -isSimp symm_apply apply_coe]
noncomputable def coconeCompShrinkYonedaHomEquiv :
    (c'.pt ⟶ P) ≃ (F ⋙ P).sections where
  toFun f :=
    { val j := shrinkYonedaEquiv (c'.ι.app (op j) ≫ f)
      property {X X'} g := by
        have h₁ := c'.w g.op
        dsimp at h₁ ⊢
        rw [← h₁, Category.assoc]
        conv_rhs => rw [shrinkYonedaEquiv_comp]
        erw [map_shrinkYonedaEquiv]
        rw [shrinkYonedaEquiv_shrinkYoneda_map]
        rfl }
  invFun s := hc'.desc (Cocone.mk _
    { app j := shrinkYonedaEquiv.symm (s.val j.unop)
      naturality j₁ j₂ f := by
        rw [← s.property f.unop]
        dsimp
        rw [shrinkYonedaEquiv_symm_map, Category.comp_id] })
  left_inv f := hc'.hom_ext (by simp)
  right_inv u := by ext; simp

noncomputable def coconePtToShrinkYoneda :
    c'.pt ⟶ shrinkYoneda.{w}.obj c.pt.unop :=
  hc'.desc (shrinkYoneda.{w}.mapCocone (coconeLeftOpOfCone c))

variable {P} in
@[reassoc]
lemma coconePtToShrinkYoneda_comp (x : P.obj c.pt) :
    coconePtToShrinkYoneda c hc' ≫ shrinkYonedaEquiv.symm x =
      (coconeCompShrinkYonedaHomEquiv hc').symm
        (Types.sectionOfCone (P.mapCone c) x) := by
  refine hc'.hom_ext (fun j ↦ ?_)
  dsimp [coconePtToShrinkYoneda, coconeCompShrinkYonedaHomEquiv_symm_apply]
  rw [hc'.fac_assoc, hc'.fac]
  dsimp
  rw [shrinkYonedaEquiv_symm_map]

lemma nonempty_isLimit_mapCone_iff :
    Nonempty (IsLimit (P.mapCone c)) ↔
      (MorphismProperty.single (coconePtToShrinkYoneda c hc')).isLocal P := by
  -- this should be a separate lemma
  have h : (MorphismProperty.single (coconePtToShrinkYoneda c hc')).isLocal P ↔
      (Function.Bijective (fun (f : _ ⟶ P) ↦ coconePtToShrinkYoneda c hc' ≫ f)) :=
    ⟨fun h ↦ h _ ⟨⟨⟩⟩, fun h ↦ by rintro _ _ _ ⟨_⟩; exact h⟩
  rw [Types.isLimit_iff_bijective_sectionOfCone, h, ← Function.Bijective.of_comp_iff'
    (coconeCompShrinkYonedaHomEquiv hc').symm.bijective,
    ← Function.Bijective.of_comp_iff _ shrinkYonedaEquiv.bijective]
  convert Iff.rfl using 2
  ext : 1
  simp [← coconePtToShrinkYoneda_comp]

variable {c}

include hc in
lemma preservesLimit_eq_isLocal_single :
    Functor.preservesLimit (Type w) F =
      (MorphismProperty.single (coconePtToShrinkYoneda c hc')).isLocal := by
  ext P
  rw [← nonempty_isLimit_mapCone_iff c hc' P]
  exact ⟨fun _ ↦ ⟨isLimitOfPreserves P hc⟩,
    fun ⟨h⟩ ↦ preservesLimit_of_preserves_limit_cone hc h⟩

variable (F)

variable [Small.{w} J]
noncomputable def preservesLimitHomFamilySrc :=
  colimit (F.leftOp ⋙ shrinkYoneda)

noncomputable def preservesLimitHomFamilyTgt (h : PLift (HasLimit F)) :=
  letI := h.down
  shrinkYoneda.obj (limit F).unop

--coconePtToShrinkYoneda (limit.cone F) (colimit.isColimit _)
noncomputable def preservesLimitHomFamily (h : PLift (HasLimit F)) :
    preservesLimitHomFamilySrc F ⟶ preservesLimitHomFamilyTgt F h :=
  letI := h.down
  coconePtToShrinkYoneda (limit.cone F) (colimit.isColimit _)

lemma preservesLimit_eq_isLocal :
    Functor.preservesLimit (Type w) F =
      (MorphismProperty.ofHoms (preservesLimitHomFamily F)).isLocal := by
  ext G
  by_cases hF : HasLimit F
  · rw [preservesLimit_eq_isLocal_single (limit.isLimit F) (colimit.isColimit _)]
    convert Iff.rfl
    ext _ _ f
    exact ⟨fun ⟨_⟩ ↦ ⟨⟨⟩⟩, fun ⟨_⟩ ↦ ⟨⟨hF⟩⟩⟩
  · exact ⟨fun _ _ _ _ ⟨h⟩ ↦ (hF h.down).elim,
      fun _ ↦ ⟨fun hc ↦ (hF ⟨_, hc⟩).elim⟩⟩

lemma preservesLimitsOfShape_eq_isLocal :
    Functor.preservesLimitsOfShape Cᵒᵖ (Type w) J =
      (⨆ (F : J ⥤ Cᵒᵖ), MorphismProperty.ofHoms (preservesLimitHomFamily F)).isLocal := by
  simp only [Functor.preservesLimitsOfShape,
    MorphismProperty.isLocal_iSup, preservesLimit_eq_isLocal]

end

end Presheaf

end CategoryTheory
