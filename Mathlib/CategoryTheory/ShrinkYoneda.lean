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
embedding `shrinkYoneda : C ⥤ Cᵒᵖ ⥤ TypeCat.{w}`. (See the
file `CategoryTheory.Yoneda` for the other variants `yoneda` and
`uliftYoneda`.)

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace FunctorToTypes

/-- A functor to types `F : C ⥤ TypeCat.{w'}` is `w`-small if for any `X : C`,
the type `F.obj X` is `w`-small. -/
@[pp_with_univ]
protected abbrev Small (F : C ⥤ TypeCat.{w'}) := ∀ (X : C), _root_.Small.{w} (F.obj X)

/-- If a functor `F : C ⥤ TypeCat.{w'}` is `w`-small, this is the functor `C ⥤ TypeCat.{w}`
obtained by shrinking `F.obj X` for all `X : C`. -/
@[simps obj map, pp_with_univ]
noncomputable def shrink (F : C ⥤ TypeCat.{w'}) [FunctorToTypes.Small.{w} F] :
    C ⥤ TypeCat.{w} where
  obj X := TypeCat.of <| Shrink.{w} (F.obj X)
  map f := TypeCat.ofHom ⟨equivShrink.{w} _ ∘ F.map f ∘ (equivShrink.{w} _).symm⟩

/-- The natural transformation `shrink.{w} F ⟶ shrink.{w} G` induces by a natural
transformation `τ : F ⟶ G` between `w`-small functors to types. -/
@[simps]
noncomputable def shrinkMap {F G : C ⥤ TypeCat.{w'}} (τ : F ⟶ G) [FunctorToTypes.Small.{w} F]
    [FunctorToTypes.Small.{w} G] :
    shrink.{w} F ⟶ shrink.{w} G where
  app X := TypeCat.ofHom ⟨equivShrink.{w} _ ∘ τ.app X ∘ (equivShrink.{w} _).symm⟩

end FunctorToTypes

variable [LocallySmall.{w} C]

instance (X : C) : FunctorToTypes.Small.{w} (yoneda.obj X) :=
  fun _ ↦ by dsimp; infer_instance

/-- The Yoneda embedding `C ⥤ Cᵒᵖ ⥤ TypeCat.{w}` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
noncomputable def shrinkYoneda :
    C ⥤ Cᵒᵖ ⥤ TypeCat.{w} where
  obj X := FunctorToTypes.shrink (yoneda.obj X)
  map f := FunctorToTypes.shrinkMap (yoneda.map f)

/-- The type `(shrinkYoneda.obj X).obj Y` is equivalent to `Y.unop ⟶ X`. -/
noncomputable def shrinkYonedaObjObjEquiv {X : C} {Y : Cᵒᵖ} :
    ((shrinkYoneda.{w}.obj X).obj Y) ≃ (Y.unop ⟶ X) :=
  (equivShrink _).symm

/-- The type of natural transformations `shrinkYoneda.{w}.obj X ⟶ P`
with `X : C` and `P : Cᵒᵖ ⥤ TypeCat.{w}` is equivalent to `P.obj (op X)`. -/
noncomputable def shrinkYonedaEquiv {X : C} {P : Cᵒᵖ ⥤ TypeCat.{w}} :
    (shrinkYoneda.{w}.obj X ⟶ P) ≃ P.obj (op X) where
  toFun τ := τ.app _ (equivShrink.{w} _ (𝟙 X))
  invFun x :=
    { app Y := TypeCat.ofHom ⟨fun f ↦ P.map ((equivShrink.{w} _).symm f).op x⟩
      naturality Y Z g := by ext; simp [shrinkYoneda] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYoneda] using ((τ.naturality_apply f.op) (equivShrink _ (𝟙 X))).symm
  right_inv x := by simp

lemma map_shrinkYonedaEquiv {X Y : C} {P : Cᵒᵖ ⥤ TypeCat.{w}} (f : shrinkYoneda.obj X ⟶ P)
    (g : Y ⟶ X) : P.map g.op (shrinkYonedaEquiv f) =
      f.app (op Y) (shrinkYonedaObjObjEquiv.symm g) := by
  simp [shrinkYonedaObjObjEquiv, shrinkYonedaEquiv, shrinkYoneda,
    ← comp_apply, ← NatTrans.naturality]
  simp

lemma shrinkYonedaEquiv_shrinkYoneda_map {X Y : C} (f : X ⟶ Y) :
    shrinkYonedaEquiv (shrinkYoneda.{w}.map f) = shrinkYonedaObjObjEquiv.symm f := by
  simp [shrinkYonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv]

lemma shrinkYonedaEquiv_comp {X : C} {P Q : Cᵒᵖ ⥤ TypeCat.{w}} (α : shrinkYoneda.obj X ⟶ P)
    (β : P ⟶ Q) :
    shrinkYonedaEquiv (α ≫ β) = β.app _ (shrinkYonedaEquiv α) := by
  simp [shrinkYonedaEquiv]

lemma shrinkYonedaEquiv_naturality {X Y : C} {P : Cᵒᵖ ⥤ TypeCat.{w}}
    (f : shrinkYoneda.obj X ⟶ P) (g : Y ⟶ X) :
    P.map g.op (shrinkYonedaEquiv f) = shrinkYonedaEquiv (shrinkYoneda.map g ≫ f) := by
  simpa [shrinkYonedaEquiv, shrinkYoneda]
    using (f.naturality_apply g.op ((equivShrink _) (𝟙 _))).symm

@[reassoc]
lemma shrinkYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {P : Cᵒᵖ ⥤ TypeCat.{w}} (t : P.obj X) :
    shrinkYonedaEquiv.symm (P.map f t) =
      shrinkYoneda.map f.unop ≫ shrinkYonedaEquiv.symm t :=
  shrinkYonedaEquiv.injective (by
    obtain ⟨t, rfl⟩ := shrinkYonedaEquiv.surjective t
    rw [← shrinkYonedaEquiv_naturality]
    simp)

variable (C) in
/-- The functor `shrinkYoneda : C ⥤ Cᵒᵖ ⥤ TypeCat.{w}` for a locally `w`-small category `C`
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
