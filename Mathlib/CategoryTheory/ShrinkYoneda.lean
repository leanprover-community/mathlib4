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

universe w w' w'' v u

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
@[simps obj map, pp_with_univ]
noncomputable def shrink (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F] :
    C ⥤ Type w where
  obj X := Shrink.{w} (F.obj X)
  map f := TypeCat.ofHom (equivShrink.{w} _ ∘ F.map f ∘ (equivShrink.{w} _).symm)

/-- The natural transformation `shrink.{w} F ⟶ shrink.{w} G` induces by a natural
transformation `τ : F ⟶ G` between `w`-small functors to types. -/
@[simps]
noncomputable def shrinkMap {F G : C ⥤ Type w'} (τ : F ⟶ G) [FunctorToTypes.Small.{w} F]
    [FunctorToTypes.Small.{w} G] :
    shrink.{w} F ⟶ shrink.{w} G where
  app X := TypeCat.ofHom (equivShrink.{w} _ ∘ τ.app X ∘ (equivShrink.{w} _).symm)

/-- Shrinking `F` to `Type w` followed by universe lifting is the same as shrinking to
`Type (max w w')`. -/
@[simps! hom_app inv_app]
noncomputable
def shrinkCompUliftFunctorIso (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F]
    [FunctorToTypes.Small.{max w w''} F] :
    shrink.{w} F ⋙ uliftFunctor.{w'', w} ≅ shrink.{max w w''} F :=
  NatIso.ofComponents
    (fun X ↦ Equiv.toIso ((Equiv.ulift.trans (equivShrink _).symm).trans (equivShrink _)))

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

set_option backward.isDefEq.respectTransparency false in
lemma shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm
    {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ X) :
    (shrinkYoneda.obj _).map g (shrinkYonedaObjObjEquiv.symm f) =
      shrinkYonedaObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYoneda, shrinkYonedaObjObjEquiv]

lemma shrinkYonedaObjObjEquiv_symm_comp {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X) :
    shrinkYonedaObjObjEquiv.symm (g ≫ f) =
    (shrinkYoneda.obj _).map g.op (shrinkYonedaObjObjEquiv.symm f) :=
  (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op f).symm

set_option backward.isDefEq.respectTransparency false in
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
    { app Y := TypeCat.ofHom (fun f ↦ P.map ((equivShrink.{w} _).symm f).op x)
      naturality Y Z g := by ext; simp [shrinkYoneda] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYoneda] using ((τ.naturality_apply f.op) (equivShrink _ (𝟙 X))).symm
  right_inv x := by simp

set_option backward.isDefEq.respectTransparency false in
lemma map_shrinkYonedaEquiv {X Y : C} {P : Cᵒᵖ ⥤ Type w} (f : shrinkYoneda.obj X ⟶ P)
    (g : Y ⟶ X) : P.map g.op (shrinkYonedaEquiv f) =
      f.app (op Y) (shrinkYonedaObjObjEquiv.symm g) := by
  simp [shrinkYonedaObjObjEquiv, shrinkYonedaEquiv, shrinkYoneda,
    ← comp_apply, ← NatTrans.naturality]

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
    using (f.naturality_apply g.op ((equivShrink _) (𝟙 _))).symm

@[reassoc]
lemma shrinkYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {P : Cᵒᵖ ⥤ Type w} (t : P.obj X) :
    shrinkYonedaEquiv.symm (P.map f t) =
      shrinkYoneda.map f.unop ≫ shrinkYonedaEquiv.symm t :=
  shrinkYonedaEquiv.injective (by
    obtain ⟨t, rfl⟩ := shrinkYonedaEquiv.surjective t
    rw [← shrinkYonedaEquiv_naturality]
    simp)

lemma shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm {X : C} {P : Cᵒᵖ ⥤ Type w}
    (s : P.obj (op X)) {Y : C} (f : Y ⟶ X) :
    (shrinkYonedaEquiv.symm s).app (op Y) (shrinkYonedaObjObjEquiv.symm f) =
      P.map f.op s := by
  obtain ⟨g, rfl⟩ := shrinkYonedaEquiv.surjective s
  simp [map_shrinkYonedaEquiv]

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

set_option backward.isDefEq.respectTransparency false in
/-- `shrinkYoneda` is compatible with `uliftFunctor`. -/
noncomputable
def shrinkYonedaUliftFunctorIso [LocallySmall.{max w w'} C] :
    shrinkYoneda.{w} ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj uliftFunctor.{w', w} ≅
      shrinkYoneda :=
  NatIso.ofComponents
    (fun X ↦ FunctorToTypes.shrinkCompUliftFunctorIso.{w, v} (yoneda.obj X))
    fun _ ↦ by ext; simp [shrinkYoneda]

/-- `uliftYoneda` identifies to `shrinkYoneda`. -/
noncomputable def uliftYonedaIsoShrinkYoneda :
    uliftYoneda.{w'} (C := C) ≅ shrinkYoneda.{max w' v} :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ (Equiv.ulift.trans shrinkYonedaObjObjEquiv.symm).toIso) (fun f ↦ by
      ext
      exact (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm _ _).symm)) (fun g ↦ by
      ext
      exact (shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm _ _).symm)

/-- The functor `shrinkYoneda.{w}` followed by the evaluation
at `Y : Cᵒᵖ` and `uliftFunctor.{v}` identifies to `coyoneda.obj Y` followed
by `uliftFunctor.{w}`. -/
noncomputable def shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor (Y : Cᵒᵖ) :
    shrinkYoneda.{w} ⋙ (evaluation Cᵒᵖ _).obj Y ⋙ uliftFunctor.{v} ≅
      coyoneda.obj Y ⋙ uliftFunctor.{w} :=
  NatIso.ofComponents (fun X ↦ (Equiv.ulift.trans
    (shrinkYonedaObjObjEquiv.trans Equiv.ulift.symm)).toIso) (fun f ↦ by
      ext ⟨g⟩
      obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
      simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm])

/-- `shrinkYoneda.obj X` is represented by `X`. -/
@[simps]
noncomputable
def shrinkYonedaRepresentableBy (X : C) : (shrinkYoneda.{w}.obj X).RepresentableBy X where
  homEquiv := shrinkYonedaObjObjEquiv.symm
  homEquiv_comp := shrinkYonedaObjObjEquiv_symm_comp

instance (X : C) : (shrinkYoneda.{w}.obj X).IsRepresentable :=
  (shrinkYonedaRepresentableBy X).isRepresentable

end CategoryTheory
