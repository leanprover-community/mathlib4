/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# The yoneda embedding

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

@[pp_with_univ, simps -isSimp obj map]
noncomputable def shrinkYoneda :
    C ⥤ Cᵒᵖ ⥤ Type w where
  obj X := FunctorToTypes.shrink (yoneda.obj X)
  map f := FunctorToTypes.shrinkMap (yoneda.map f)

noncomputable def shrinkYonedaObjObjEquiv {X : C} {Y : Cᵒᵖ} :
    ((shrinkYoneda.{w}.obj X).obj Y) ≃ (Y.unop ⟶ X) :=
  (equivShrink _).symm

lemma shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm
    {Y : C} {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y) :
    (shrinkYoneda.{w}.obj Y).map f.op (shrinkYonedaObjObjEquiv.symm g) =
      (shrinkYonedaObjObjEquiv.symm (f ≫ g)) := by
  simp [shrinkYonedaObjObjEquiv, shrinkYoneda_obj]

noncomputable def shrinkYonedaFlipObjCompUliftFunctorIso (X : C) :
    shrinkYoneda.{w}.flip.obj (op X) ⋙ uliftFunctor.{v} ≅
      coyoneda.obj (op X) ⋙ uliftFunctor.{w} :=
  NatIso.ofComponents
    (fun Y ↦ Equiv.toIso (Equiv.ulift.trans ((equivShrink _).symm.trans Equiv.ulift.symm)))
    (fun _ ↦ by ext; simp [shrinkYoneda])

@[simps!]
noncomputable def shrinkYonedaMap
    {D : Type u'} [Category.{v'} D] [LocallySmall.{w} D] (F : C ⥤ D) (X : C) :
    shrinkYoneda.{w}.obj X ⟶ F.op ⋙ shrinkYoneda.{w}.obj (F.obj X) where
  app X := equivShrink _ ∘ F.map ∘ (equivShrink _).symm
  naturality _ _ _ := by ext; simp [shrinkYoneda]

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

@[simp]
lemma shrinkYonedaEquiv_app_shrinkYonedaObjObjEquiv_symm {X : C} {P : Cᵒᵖ ⥤ Type w}
    (x : P.obj (op X)) {Y : C} (f : Y ⟶ X) :
    (shrinkYonedaEquiv.symm x).app (op Y) (shrinkYonedaObjObjEquiv.symm f) =
      P.map f.op x := by
  dsimp [shrinkYonedaEquiv, shrinkYonedaObjObjEquiv]
  apply congr_fun
  congr
  apply Equiv.symm_apply_apply

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

instance (X : C) (J : Type*) [Category J] :
    PreservesLimitsOfShape J (shrinkYoneda.{w}.obj X) where
  preservesLimit {F} := ⟨fun {c} hc ↦ by
    rw [Types.isLimit_iff_bijective_sectionOfCone]
    refine ⟨fun f₁ f₂ h ↦ ?_, fun s ↦ ?_⟩
    · obtain ⟨f₁, rfl⟩ := (equivShrink _).surjective f₁
      obtain ⟨f₂, rfl⟩ := (equivShrink _).surjective f₂
      apply (equivShrink _).symm.injective
      simp only [Equiv.symm_apply_apply]
      apply Quiver.Hom.op_inj
      refine hc.hom_ext (fun j ↦ Quiver.Hom.unop_inj ?_)
      have := congr_fun (congr_arg Subtype.val h) j
      simpa [shrinkYoneda] using congr_fun (congr_arg Subtype.val h) j
    · refine ⟨equivShrink _ ((hc.homEquiv.symm
        { app j := ((equivShrink _).symm (s.1 j)).op
          naturality _ _ f := Quiver.Hom.unop_inj
            (by simp [-Functor.sections_property, shrinkYoneda, ← s.2 f])}).unop), ?_⟩
      ext
      apply (equivShrink _).symm.injective (Quiver.Hom.op_inj (by simp [shrinkYoneda]))⟩

end

end

end CategoryTheory
