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
  map f := ↾(equivShrink.{w} _ ∘ F.map f ∘ (equivShrink.{w} _).symm)

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `shrink.{w} F ⟶ shrink.{w} G` induces by a natural
transformation `τ : F ⟶ G` between `w`-small functors to types. -/
@[simps]
noncomputable def shrinkMap {F G : C ⥤ Type w'} (τ : F ⟶ G) [FunctorToTypes.Small.{w} F]
    [FunctorToTypes.Small.{w} G] :
    shrink.{w} F ⟶ shrink.{w} G where
  app X := ↾(equivShrink.{w} _ ∘ τ.app X ∘ (equivShrink.{w} _).symm)

set_option backward.defeqAttrib.useBackward true in
/-- Shrinking `F` to `Type w` followed by universe lifting is the same as shrinking to
`Type (max w w')`. -/
@[simps! hom_app inv_app]
noncomputable
def shrinkCompUliftFunctorIso (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F]
    [FunctorToTypes.Small.{max w w''} F] :
    shrink.{w} F ⋙ uliftFunctor.{w'', w} ≅ shrink.{max w w''} F :=
  NatIso.ofComponents
    (fun X ↦ Equiv.toIso ((Equiv.ulift.trans (equivShrink _).symm).trans (equivShrink _)))

unif_hint (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F] (X : C) where ⊢
  Shrink (F.obj X) ≟ (FunctorToTypes.shrink F).obj X

end FunctorToTypes

variable [LocallySmall.{w} C]

section Yoneda

set_option backward.defeqAttrib.useBackward true in
instance (X : C) : FunctorToTypes.Small.{w} (yoneda.obj X) :=
  fun _ ↦ by dsimp; infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- The Yoneda embedding `C ⥤ Cᵒᵖ ⥤ Type w` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
noncomputable def shrinkYoneda :
    C ⥤ Cᵒᵖ ⥤ Type w where
  obj X := FunctorToTypes.shrink (yoneda.obj X)
  map f := FunctorToTypes.shrinkMap (yoneda.map f)

set_option backward.isDefEq.respectTransparency.types false in
/-- The type `(shrinkYoneda.obj X).obj Y` is equivalent to `Y.unop ⟶ X`. -/
noncomputable def shrinkYonedaObjObjEquiv {X : C} {Y : Cᵒᵖ} :
    ((shrinkYoneda.{w}.obj X).obj Y) ≃ (Y.unop ⟶ X) :=
  (equivShrink _).symm

lemma shrinkYoneda_obj_map {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : (shrinkYoneda.obj X).obj Y) :
    (shrinkYoneda.obj _).map g f =
      shrinkYonedaObjObjEquiv.symm (g.unop ≫ shrinkYonedaObjObjEquiv f) :=
  rfl

lemma shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm
    {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ X) :
    (shrinkYoneda.obj _).map g (shrinkYonedaObjObjEquiv.symm f) =
      shrinkYonedaObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYoneda_obj_map]

lemma shrinkYonedaObjObjEquiv_symm_comp {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X) :
    shrinkYonedaObjObjEquiv.symm (g ≫ f) =
    (shrinkYoneda.obj _).map g.op (shrinkYonedaObjObjEquiv.symm f) :=
  (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op f).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm
    {X X' : C} {Y : Cᵒᵖ} (f : Y.unop ⟶ X) (g : X ⟶ X') :
    (shrinkYoneda.map g).app _ (shrinkYonedaObjObjEquiv.symm f) =
      shrinkYonedaObjObjEquiv.symm (f ≫ g) := by
  simp [shrinkYoneda, shrinkYonedaObjObjEquiv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma shrinkYonedaObjObjEquiv_map_app
    {X X' : C} {Y : Cᵒᵖ} (f : (shrinkYoneda.{w, v, u}.obj X).obj Y) (g : X ⟶ X') :
    shrinkYonedaObjObjEquiv ((shrinkYoneda.map g).app Y f) =
      shrinkYonedaObjObjEquiv f ≫ g := by
  simp [shrinkYoneda, shrinkYonedaObjObjEquiv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma shrinkYonedaObjObjEquiv_obj_map {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y')
    (f : (shrinkYoneda.{w}.obj X).obj Y) :
    shrinkYonedaObjObjEquiv ((shrinkYoneda.{w}.obj X).map g f) =
      g.unop ≫ shrinkYonedaObjObjEquiv f := by
  simp [shrinkYonedaObjObjEquiv, shrinkYoneda]

set_option backward.isDefEq.respectTransparency false in
/-- The type of natural transformations `shrinkYoneda.{w}.obj X ⟶ P`
with `X : C` and `P : Cᵒᵖ ⥤ Type w` is equivalent to `P.obj (op X)`. -/
noncomputable def shrinkYonedaEquiv {X : C} {P : Cᵒᵖ ⥤ Type w} :
    (shrinkYoneda.{w}.obj X ⟶ P) ≃ P.obj (op X) where
  toFun τ := τ.app _ (equivShrink.{w} _ (𝟙 X))
  invFun x :=
    { app Y := ↾fun f ↦ P.map ((equivShrink.{w} _).symm f).op x
      naturality Y Z g := by ext; simp [shrinkYoneda] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYoneda] using ((τ.naturality_apply f.op) (equivShrink _ (𝟙 X))).symm
  right_inv x := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma map_shrinkYonedaEquiv {X Y : C} {P : Cᵒᵖ ⥤ Type w} (f : shrinkYoneda.obj X ⟶ P)
    (g : Y ⟶ X) : P.map g.op (shrinkYonedaEquiv f) =
      f.app (op Y) (shrinkYonedaObjObjEquiv.symm g) := by
  simp [shrinkYonedaObjObjEquiv, shrinkYonedaEquiv, shrinkYoneda,
    ← comp_apply, ← NatTrans.naturality]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaEquiv_shrinkYoneda_map {X Y : C} (f : X ⟶ Y) :
    shrinkYonedaEquiv (shrinkYoneda.{w}.map f) = shrinkYonedaObjObjEquiv.symm f := by
  simp [shrinkYonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv]

set_option backward.isDefEq.respectTransparency.types false in
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

set_option backward.isDefEq.respectTransparency.types false in
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

set_option backward.defeqAttrib.useBackward true in
/-- `shrinkYoneda` at the morphism universe level is `yoneda`. -/
@[simps! hom_app inv_app]
noncomputable
def shrinkYonedaIsoYoneda : shrinkYoneda.{v} ≅ yoneda (C := C) :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents (fun Y ↦ shrinkYonedaObjObjEquiv.toIso)
      (by intros; ext; simp [shrinkYonedaObjObjEquiv_obj_map]))
    (by intros; ext; simp [shrinkYonedaObjObjEquiv_map_app])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
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

set_option backward.defeqAttrib.useBackward true in
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

end Yoneda

section Coyoneda

set_option backward.defeqAttrib.useBackward true in
instance (X : Cᵒᵖ) : FunctorToTypes.Small.{w} (coyoneda.obj X) :=
  fun _ ↦ by dsimp; infer_instance

/-- The co-Yoneda embedding `Cᵒᵖ ⥤ C ⥤ Type w` for a locally `w`-small category `C`. -/
@[pp_with_univ]
noncomputable abbrev shrinkCoyoneda : Cᵒᵖ ⥤ C ⥤ Type w := shrinkYoneda.flip

lemma shrinkCoyoneda_obj {X : Cᵒᵖ} :
    shrinkCoyoneda.obj X = FunctorToTypes.shrink (coyoneda.obj X) := rfl

lemma shrinkCoyoneda_map {X Y : Cᵒᵖ} {f : X ⟶ Y} :
    shrinkCoyoneda.map f = FunctorToTypes.shrinkMap (coyoneda.map f) := rfl

/-- The type `(shrinkCoyoneda.obj X).obj Y` is equivalent to `X.unop ⟶ Y`. -/
noncomputable abbrev shrinkCoyonedaObjObjEquiv {X : Cᵒᵖ} {Y : C} :
    ((shrinkCoyoneda.{w}.obj X).obj Y) ≃ (X.unop ⟶ Y) :=
  shrinkYonedaObjObjEquiv

lemma shrinkCoyoneda_obj_map {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y') (f : (shrinkCoyoneda.obj X).obj Y) :
    (shrinkCoyoneda.obj _).map g f =
      shrinkCoyonedaObjObjEquiv.symm (shrinkCoyonedaObjObjEquiv f ≫ g) :=
  rfl

lemma shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm
    {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y') (f : X.unop ⟶ Y) :
    (shrinkCoyoneda.obj _).map g (shrinkCoyonedaObjObjEquiv.symm f) =
      shrinkCoyonedaObjObjEquiv.symm (f ≫ g) :=
  shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm f g

lemma shrinkCoyonedaObjObjEquiv_symm_comp {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X) :
    shrinkCoyonedaObjObjEquiv.symm (g ≫ f) =
    (shrinkCoyoneda.obj _).map f (shrinkCoyonedaObjObjEquiv.symm g) :=
  (shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm f g).symm

lemma shrinkCoyoneda_map_app_shrinkCoyonedaObjObjEquiv_symm
    {X X' : Cᵒᵖ} {Y : C} (f : X.unop ⟶ Y) (g : X ⟶ X') :
    (shrinkCoyoneda.map g).app _ (shrinkCoyonedaObjObjEquiv.symm f) =
      shrinkCoyonedaObjObjEquiv.symm (g.unop ≫ f) :=
  shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g f

@[reassoc]
lemma shrinkCoyonedaObjObjEquiv_map_app
    {X X' : Cᵒᵖ} {Y : C} (f : (shrinkCoyoneda.{w, v, u}.obj X).obj Y) (g : X ⟶ X') :
    shrinkCoyonedaObjObjEquiv ((shrinkCoyoneda.map g).app Y f) =
      g.unop ≫ shrinkCoyonedaObjObjEquiv f :=
  shrinkYonedaObjObjEquiv_obj_map g f

@[reassoc]
lemma shrinkCoyonedaObjObjEquiv_obj_map {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y')
    (f : (shrinkCoyoneda.{w}.obj X).obj Y) :
    shrinkCoyonedaObjObjEquiv ((shrinkCoyoneda.{w}.obj X).map g f) =
      shrinkCoyonedaObjObjEquiv f ≫ g :=
  shrinkYonedaObjObjEquiv_map_app f g

set_option backward.isDefEq.respectTransparency false in
/-- The type of natural transformations `shrinkCoyoneda.{w}.obj X ⟶ P`
with `X : Cᵒᵖ` and `P : C ⥤ Type w` is equivalent to `P.obj (op X)`. -/
noncomputable def shrinkCoyonedaEquiv {X : Cᵒᵖ} {P : C ⥤ Type w} :
    (shrinkCoyoneda.{w}.obj X ⟶ P) ≃ P.obj X.unop where
  toFun τ := τ.app _ (equivShrink.{w} _ (𝟙 X.unop))
  invFun x :=
    { app Y := ↾fun f ↦ P.map ((equivShrink.{w} _).symm f) x
      naturality Y Z g := by ext; simp [shrinkYoneda] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYoneda] using ((τ.naturality_apply f) (equivShrink _ (𝟙 X.unop))).symm
  right_inv x := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma map_shrinkCoyonedaEquiv {X Y : Cᵒᵖ} {P : C ⥤ Type w} (f : shrinkCoyoneda.obj X ⟶ P)
    (g : Y ⟶ X) : P.map g.unop (shrinkCoyonedaEquiv f) =
      f.app Y.unop (shrinkCoyonedaObjObjEquiv.symm g.unop) := by
  simp [shrinkYonedaObjObjEquiv, shrinkCoyonedaEquiv, shrinkYoneda,
    ← comp_apply, ← NatTrans.naturality]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma shrinkCoyonedaEquiv_shrinkCoyoneda_map {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    shrinkCoyonedaEquiv (shrinkCoyoneda.{w}.map f) = shrinkCoyonedaObjObjEquiv.symm f.unop := by
  simp [shrinkCoyonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv]

set_option backward.isDefEq.respectTransparency.types false in
lemma shrinkCoyonedaEquiv_comp {X : Cᵒᵖ} {P Q : C ⥤ Type w} (α : shrinkCoyoneda.obj X ⟶ P)
    (β : P ⟶ Q) :
    shrinkCoyonedaEquiv (α ≫ β) = β.app _ (shrinkCoyonedaEquiv α) := by
  simp [shrinkCoyonedaEquiv]

set_option backward.isDefEq.respectTransparency false in
lemma shrinkCoyonedaEquiv_naturality {X Y : Cᵒᵖ} {P : C ⥤ Type w}
    (f : shrinkCoyoneda.obj X ⟶ P) (g : Y ⟶ X) :
    P.map g.unop (shrinkCoyonedaEquiv f) = shrinkCoyonedaEquiv (shrinkCoyoneda.map g ≫ f) := by
  simpa [shrinkCoyonedaEquiv, shrinkYoneda]
    using (f.naturality_apply g.unop ((equivShrink _) (𝟙 _))).symm

@[reassoc]
lemma shrinkCoyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {P : C ⥤ Type w} (t : P.obj X) :
    shrinkCoyonedaEquiv.symm (P.map f t) =
      shrinkCoyoneda.map f.op ≫ shrinkCoyonedaEquiv.symm t :=
  shrinkCoyonedaEquiv.injective (by
    obtain ⟨t, rfl⟩ := shrinkCoyonedaEquiv.surjective t
    rw [← shrinkCoyonedaEquiv_naturality]
    simp)

lemma shrinkCoyonedaEquiv_symm_app_shrinkCoyonedaObjObjEquiv_symm {X : Cᵒᵖ} {P : C ⥤ Type w}
    (s : P.obj X.unop) {Y : Cᵒᵖ} (f : Y ⟶ X) :
    (shrinkCoyonedaEquiv.symm s).app Y.unop (shrinkCoyonedaObjObjEquiv.symm f.unop) =
      P.map f.unop s := by
  obtain ⟨g, rfl⟩ := shrinkCoyonedaEquiv.surjective s
  simp [map_shrinkCoyonedaEquiv]

variable (C) in
/-- The functor `shrinkCoyoneda : Cᵒᵖ ⥤ C ⥤ Type w` for a locally `w`-small category `C`
is fully faithful. -/
noncomputable def fullyFaithfulShrinkCoyoneda :
    (shrinkCoyoneda.{w} (C := C)).FullyFaithful where
  preimage f := (shrinkCoyonedaObjObjEquiv (shrinkCoyonedaEquiv f)).op
  map_preimage f := by
    obtain ⟨f, rfl⟩ := shrinkCoyonedaEquiv.symm.surjective f
    cat_disch
  preimage_map f := by simp [shrinkCoyonedaEquiv_shrinkCoyoneda_map]

instance : (shrinkCoyoneda.{w} (C := C)).Faithful := (fullyFaithfulShrinkCoyoneda C).faithful

instance : (shrinkCoyoneda.{w} (C := C)).Full := (fullyFaithfulShrinkCoyoneda C).full

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `shrinkCoyoneda` at the morphism universe level is `coyoneda`. -/
@[simps! hom_app inv_app]
noncomputable
def shrinkCoyonedaIsoCoyoneda : shrinkCoyoneda.{v} ≅ coyoneda (C := C) :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents (fun Y ↦ shrinkCoyonedaObjObjEquiv.toIso)
      (by intros; ext; simp [shrinkYonedaObjObjEquiv_map_app]))
    (by intros; ext; simp [shrinkYonedaObjObjEquiv_obj_map])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `shrinkCoyoneda` is compatible with `uliftFunctor`. -/
noncomputable
def shrinkCoyonedaUliftFunctorIso [LocallySmall.{max w w'} C] :
    shrinkCoyoneda.{w} ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj uliftFunctor.{w', w} ≅
      shrinkCoyoneda :=
  NatIso.ofComponents
    (fun X ↦ FunctorToTypes.shrinkCompUliftFunctorIso.{w, v} (coyoneda.obj X))
    fun _ ↦ by ext; simp [shrinkYoneda]

/-- `uliftCoyoneda` identifies to `shrinkCoyoneda`. -/
noncomputable def uliftYonedaIsoShrinkCoyoneda :
    uliftCoyoneda.{w'} (C := C) ≅ shrinkCoyoneda.{max w' v} :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ (Equiv.ulift.trans shrinkCoyonedaObjObjEquiv.symm).toIso) (fun f ↦ by
      ext
      exact (shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm _ _).symm)) (fun g ↦ by
      ext
      exact (shrinkCoyoneda_map_app_shrinkCoyonedaObjObjEquiv_symm _ _).symm)

set_option backward.defeqAttrib.useBackward true in
/-- The functor `shrinkCoyoneda.{w}` followed by the evaluation
at `Y : C` and `uliftFunctor.{v}` identifies to `yoneda.obj Y` followed
by `uliftFunctor.{w}`. -/
noncomputable def shrinkCoyonedaCompEvaluationCompUliftFunctorIsoUliftFunctor (Y : C) :
    shrinkCoyoneda.{w} ⋙ (evaluation C _).obj Y ⋙ uliftFunctor.{v} ≅
      yoneda.obj Y ⋙ uliftFunctor.{w} :=
  NatIso.ofComponents (fun X ↦ (Equiv.ulift.trans
    (shrinkCoyonedaObjObjEquiv.trans Equiv.ulift.symm)).toIso) (fun f ↦ by
      ext ⟨g⟩
      obtain ⟨g, rfl⟩ := shrinkCoyonedaObjObjEquiv.symm.surjective g
      simp [shrinkYoneda, shrinkYonedaObjObjEquiv])

/-- `shrinkCoyoneda.obj X` is corepresented by `X`. -/
@[simps]
noncomputable
def shrinkCoyonedaCorepresentableBy (X : Cᵒᵖ) :
    (shrinkCoyoneda.{w}.obj X).CorepresentableBy X.unop where
  homEquiv := shrinkCoyonedaObjObjEquiv.symm
  homEquiv_comp f g := shrinkCoyonedaObjObjEquiv_symm_comp g f

instance (X : Cᵒᵖ) : (shrinkCoyoneda.{w}.obj X).IsCorepresentable :=
  (shrinkCoyonedaCorepresentableBy X).isCorepresentable

end Coyoneda

end CategoryTheory
