/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# The Yoneda functor for locally small categories

Let `C` be a locally `w`-small category. We define the Yoneda
embedding `shrinkYoneda : C ⥤ Cᵒᵖ ⥤ Type w`. (See the
file `CategoryTheory.Yoneda` for the other variants `yoneda` and
`uliftYoneda`.)

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace FunctorToTypes

/-- A functor to types `F : C ⥤ Type w'` is `w`-small if for any `X : C`,
the type `F.obj X` is `w`-small. -/
@[pp_with_univ]
protected abbrev Small (F : C ⥤ Type w') := ∀ (X : C), _root_.Small.{w} (F.obj X)

/-- If a functor `F : C ⥤ Type w'` is `w`-small, this is the functor `C ⥤ Type w`
obtained by shrinking `F.obj X` for all `X : C`. -/
@[simps, pp_with_univ]
noncomputable def shrink (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F] :
    C ⥤ Type w where
  obj X := Shrink.{w} (F.obj X)
  map f := equivShrink.{w} _ ∘ F.map f ∘ (equivShrink.{w} _).symm

attribute [local simp] FunctorToTypes.naturality in
/-- The natural transformation `shrink.{w} F ⟶ shrink.{w} G` induces by a natural
transformation `τ : F ⟶ G` between `w`-small functors to types. -/
@[simps]
noncomputable def shrinkMap {F G : C ⥤ Type w'} (τ : F ⟶ G) [FunctorToTypes.Small.{w} F]
    [FunctorToTypes.Small.{w} G] :
    shrink.{w} F ⟶ shrink.{w} G where
  app X := equivShrink.{w} _ ∘ τ.app X ∘ (equivShrink.{w} _).symm

end FunctorToTypes

variable [LocallySmall.{w} C]

instance (X : C) : FunctorToTypes.Small.{w} (yoneda.obj X) :=
  fun _ ↦ by dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda embedding `C ⥤ Cᵒᵖ ⥤ Type w` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
noncomputable def shrinkYoneda :
    C ⥤ Cᵒᵖ ⥤ Type w where
  obj X := FunctorToTypes.shrink (yoneda.obj X)
  map f := FunctorToTypes.shrinkMap (yoneda.map f)

/-- The type `(shrinkYoneda.obj X).obj Y` is equivalent to `Y.unop ⟶ X`. -/
noncomputable def shrinkYonedaObjObjEquiv {X : C} {Y : Cᵒᵖ} :
    ((shrinkYoneda.{w}.obj X).obj Y) ≃ (Y.unop ⟶ X) :=
  (equivShrink _).symm

lemma shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm
    {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ X) :
    (shrinkYoneda.obj _).map g (shrinkYonedaObjObjEquiv.symm f) =
      shrinkYonedaObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYoneda, shrinkYonedaObjObjEquiv]

lemma shrinkYonedaObjObjEquiv_symm_comp {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X) :
    shrinkYonedaObjObjEquiv.symm (g ≫ f) =
    (shrinkYoneda.obj _).map g.op (shrinkYonedaObjObjEquiv.symm f) :=
  (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op f).symm

lemma shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm
    {X X' : C} {Y : Cᵒᵖ} (f : Y.unop ⟶ X) (g : X ⟶ X') :
    (shrinkYoneda.map g).app _ (shrinkYonedaObjObjEquiv.symm f) =
      shrinkYonedaObjObjEquiv.symm (f ≫ g) := by
  simp [shrinkYoneda, shrinkYonedaObjObjEquiv]

set_option backward.isDefEq.respectTransparency false in
/-- The type of natural transformations `shrinkYoneda.{w}.obj X ⟶ P`
with `X : C` and `P : Cᵒᵖ ⥤ Type w` is equivalent to `P.obj (op X)`. -/
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

set_option backward.isDefEq.respectTransparency false in
lemma map_shrinkYonedaEquiv {X Y : C} {P : Cᵒᵖ ⥤ Type w} (f : shrinkYoneda.obj X ⟶ P)
    (g : Y ⟶ X) : P.map g.op (shrinkYonedaEquiv f) =
      f.app (op Y) (shrinkYonedaObjObjEquiv.symm g) := by
  simp [shrinkYonedaObjObjEquiv, shrinkYonedaEquiv, shrinkYoneda,
    ← FunctorToTypes.naturality]

set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaEquiv_shrinkYoneda_map {X Y : C} (f : X ⟶ Y) :
    shrinkYonedaEquiv (shrinkYoneda.{w}.map f) = shrinkYonedaObjObjEquiv.symm f := by
  simp [shrinkYonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv]

lemma shrinkYonedaEquiv_comp {X : C} {P Q : Cᵒᵖ ⥤ Type w} (α : shrinkYoneda.obj X ⟶ P)
    (β : P ⟶ Q) :
    shrinkYonedaEquiv (α ≫ β) = β.app _ (shrinkYonedaEquiv α) := by
  simp [shrinkYonedaEquiv]

set_option backward.isDefEq.respectTransparency false in
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

variable (C) in
/-- The functor `shrinkYoneda : C ⥤ Cᵒᵖ ⥤ Type w` for a locally `w`-small category `C`
is fully faithful. -/
noncomputable def fullyFaithfulShrinkYoneda :
    (shrinkYoneda.{w} (C := C)).FullyFaithful where
  preimage f := shrinkYonedaObjObjEquiv (shrinkYonedaEquiv f)
  map_preimage f := by
    obtain ⟨f, rfl⟩ := shrinkYonedaEquiv.symm.surjective f
    cat_disch
  preimage_map f := by simp [shrinkYonedaEquiv_shrinkYoneda_map]

instance : (shrinkYoneda.{w} (C := C)).Faithful := (fullyFaithfulShrinkYoneda C).faithful

instance : (shrinkYoneda.{w} (C := C)).Full := (fullyFaithfulShrinkYoneda C).full

end CategoryTheory
