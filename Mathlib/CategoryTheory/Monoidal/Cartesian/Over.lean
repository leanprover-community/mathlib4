/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!

# `CartesianMonoidalCategory` for `Over X`

We provide a `CartesianMonoidalCategory (Over X)` instance via pullbacks, and provide simp lemmas
for the induced `MonoidalCategory (Over X)` instance.

-/

namespace CategoryTheory.Over

open Limits CartesianMonoidalCategory

variable {C : Type*} [Category C] [HasPullbacks C]

/-- A choice of finite products of `Over X` given by `Limits.pullback`. -/
noncomputable abbrev cartesianMonoidalCategory (X : C) : CartesianMonoidalCategory (Over X) :=
  .ofChosenFiniteProducts
    ⟨asEmptyCone (Over.mk (𝟙 X)), IsTerminal.ofUniqueHom (fun Y ↦ Over.homMk Y.hom)
      fun Y m ↦ Over.OverMorphism.ext (by simpa using m.w)⟩
    fun Y Z ↦ ⟨pullbackConeEquivBinaryFan.functor.obj (pullback.cone Y.hom Z.hom),
    (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor⟩

@[deprecated (since := "2025-05-15")] alias chosenFiniteProducts := cartesianMonoidalCategory

attribute [local instance] cartesianMonoidalCategory

/-- `Over X` is braided wrt the cartesian monoidal structure given by `Limits.pullback`. -/
noncomputable abbrev braidedCategory (X : C) : BraidedCategory (Over X) :=
  .ofCartesianMonoidalCategory

attribute [local instance] braidedCategory

open MonoidalCategory

variable {X : C}

@[ext]
lemma tensorObj_ext {R : C} {S T : Over X} (f₁ f₂ : R ⟶ (S ⊗ T).left)
    (e₁ : f₁ ≫ pullback.fst _ _ = f₂ ≫ pullback.fst _ _)
    (e₂ : f₁ ≫ pullback.snd _ _ = f₂ ≫ pullback.snd _ _) : f₁ = f₂ :=
  pullback.hom_ext e₁ e₂

@[simp]
lemma tensorObj_left (R S : Over X) : (R ⊗ S).left = pullback R.hom S.hom := rfl

@[simp]
lemma tensorObj_hom (R S : Over X) : (R ⊗ S).hom = pullback.fst R.hom S.hom ≫ R.hom := rfl

@[simp]
lemma tensorUnit_left : (𝟙_ (Over X)).left = X := rfl

@[simp]
lemma tensorUnit_hom : (𝟙_ (Over X)).hom = 𝟙 X := rfl

@[simp]
lemma lift_left {R S T : Over X} (f : R ⟶ S) (g : R ⟶ T) :
    (lift f g).left = pullback.lift f.left g.left (f.w.trans g.w.symm) := rfl

@[simp]
lemma toUnit_left {R : Over X} : (toUnit R).left = R.hom := rfl

@[reassoc (attr := simp)]
lemma associator_hom_left_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.fst _ (pullback.fst _ _ ≫ _) =
      pullback.fst _ _ ≫ pullback.fst _ _ :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma associator_hom_left_snd_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.snd _ (pullback.fst _ _ ≫ _) ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
lemma associator_hom_left_snd_snd (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.snd _ (pullback.fst _ _ ≫ _) ≫ pullback.snd _ _ =
      pullback.snd _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
lemma associator_inv_left_fst_fst (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.fst (pullback.fst _ _ ≫ _) _ ≫ pullback.fst _ _ =
      pullback.fst _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
lemma associator_inv_left_fst_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.fst (pullback.fst _ _ ≫ _) _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
lemma associator_inv_left_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.snd (pullback.fst _ _ ≫ _) _ =
      pullback.snd _ _ ≫ pullback.snd _ _ :=
  limit.lift_π _ _

@[simp]
lemma leftUnitor_hom_left (Y : Over X) :
    (λ_ Y).hom.left = pullback.snd _ _ := rfl

@[reassoc (attr := simp)]
lemma leftUnitor_inv_left_fst (Y : Over X) :
    (λ_ Y).inv.left ≫ pullback.fst (𝟙 X) _ = Y.hom :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma leftUnitor_inv_left_snd (Y : Over X) :
    (λ_ Y).inv.left ≫ pullback.snd (𝟙 X) _ = 𝟙 Y.left :=
  limit.lift_π _ _

@[simp]
lemma rightUnitor_hom_left (Y : Over X) :
    (ρ_ Y).hom.left = pullback.fst _ (𝟙 X) := rfl

@[reassoc (attr := simp)]
lemma rightUnitor_inv_left_fst (Y : Over X) :
    (ρ_ Y).inv.left ≫ pullback.fst _ (𝟙 X) = 𝟙 _ :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma rightUnitor_inv_left_snd (Y : Over X) :
    (ρ_ Y).inv.left ≫ pullback.snd _ (𝟙 X) = Y.hom :=
  limit.lift_π _ _

lemma whiskerLeft_left {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left = pullback.map _ _ _ _ (𝟙 _) f.left (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
lemma whiskerLeft_left_fst {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (limit.lift_π _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
lemma whiskerLeft_left_snd {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ pullback.snd _ _ = pullback.snd _ _ ≫ f.left :=
  limit.lift_π _ _

lemma whiskerRight_left {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left = pullback.map _ _ _ _ f.left (𝟙 _) (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
lemma whiskerRight_left_fst {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.left :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma whiskerRight_left_snd {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (limit.lift_π _ _).trans (Category.comp_id _)

lemma tensorHom_left {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ₘ g).left = pullback.map _ _ _ _ f.left g.left (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
lemma tensorHom_left_fst {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ₘ g).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.left :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma tensorHom_left_snd {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ₘ g).left ≫ pullback.snd _ _ = pullback.snd _ _ ≫ g.left :=
  limit.lift_π _ _

@[simp]
lemma braiding_hom_left {R S : Over X} :
    (β_ R S).hom.left = (pullbackSymmetry _ _).hom := rfl

@[simp]
lemma braiding_inv_left {R S : Over X} :
    (β_ R S).inv.left = (pullbackSymmetry _ _).hom := rfl

end CategoryTheory.Over
