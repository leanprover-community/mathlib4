/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike

/-!
# Preadditive monoidal categories

A monoidal category is `MonoidalPreadditive` if it is preadditive and tensor product of morphisms
is linear in both factors.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

variable (C : Type*) [Category* C] [Preadditive C] [MonoidalCategory C]

/-- A category is `MonoidalPreadditive` if tensoring is additive in both factors.

Note we don't `extend Preadditive C` here, as `Abelian C` already extends it,
and we'll need to have both typeclasses sometimes.
-/
class MonoidalPreadditive : Prop where
  whiskerLeft_zero : ∀ {X Y Z : C}, X ◁ (0 : Y ⟶ Z) = 0 := by cat_disch
  zero_whiskerRight : ∀ {X Y Z : C}, (0 : Y ⟶ Z) ▷ X = 0 := by cat_disch
  whiskerLeft_add : ∀ {X Y Z : C} (f g : Y ⟶ Z), X ◁ (f + g) = X ◁ f + X ◁ g := by cat_disch
  add_whiskerRight : ∀ {X Y Z : C} (f g : Y ⟶ Z), (f + g) ▷ X = f ▷ X + g ▷ X := by cat_disch

attribute [simp] MonoidalPreadditive.whiskerLeft_zero MonoidalPreadditive.zero_whiskerRight
attribute [simp] MonoidalPreadditive.whiskerLeft_add MonoidalPreadditive.add_whiskerRight

variable {C}
variable [MonoidalPreadditive C]

namespace MonoidalPreadditive

-- The priority setting will not be needed when we replace `𝟙 X ⊗ₘ f` by `X ◁ f`.
@[simp (low)]
theorem tensor_zero {W X Y Z : C} (f : W ⟶ X) : f ⊗ₘ (0 : Y ⟶ Z) = 0 := by
  simp [tensorHom_def]

-- The priority setting will not be needed when we replace `f ⊗ₘ 𝟙 X` by `f ▷ X`.
@[simp (low)]
theorem zero_tensor {W X Y Z : C} (f : Y ⟶ Z) : (0 : W ⟶ X) ⊗ₘ f = 0 := by
  simp [tensorHom_def]

theorem tensor_add {W X Y Z : C} (f : W ⟶ X) (g h : Y ⟶ Z) : f ⊗ₘ (g + h) = f ⊗ₘ g + f ⊗ₘ h := by
  simp [tensorHom_def]

theorem add_tensor {W X Y Z : C} (f g : W ⟶ X) (h : Y ⟶ Z) : (f + g) ⊗ₘ h = f ⊗ₘ h + g ⊗ₘ h := by
  simp [tensorHom_def]

instance (X : C) : (tensorLeft X).Additive where
instance (X : C) : (tensorRight X).Additive where
instance : (curriedTensor C).Additive where
instance : (curriedTensor C).flip.Additive where

end MonoidalPreadditive

instance tensorLeft_additive (X : C) : (tensorLeft X).Additive where

instance tensorRight_additive (X : C) : (tensorRight X).Additive where

instance tensoringLeft_additive (X : C) : ((tensoringLeft C).obj X).Additive where

instance tensoringRight_additive (X : C) : ((tensoringRight C).obj X).Additive where

/-- A faithful additive monoidal functor to a monoidal preadditive category
ensures that the domain is monoidal preadditive. -/
theorem monoidalPreadditive_of_faithful {D} [Category* D] [Preadditive D] [MonoidalCategory D]
    (F : D ⥤ C) [F.Monoidal] [F.Faithful] [F.Additive] :
    MonoidalPreadditive D :=
  { whiskerLeft_zero := by
      intros
      apply F.map_injective
      simp [Functor.Monoidal.map_whiskerLeft]
    zero_whiskerRight := by
      intros
      apply F.map_injective
      simp [Functor.Monoidal.map_whiskerRight]
    whiskerLeft_add := by
      intros
      apply F.map_injective
      simp only [Functor.Monoidal.map_whiskerLeft, Functor.map_add, Preadditive.comp_add,
        Preadditive.add_comp, MonoidalPreadditive.whiskerLeft_add]
    add_whiskerRight := by
      intros
      apply F.map_injective
      simp only [Functor.Monoidal.map_whiskerRight, Functor.map_add, Preadditive.comp_add,
        Preadditive.add_comp, MonoidalPreadditive.add_whiskerRight] }

theorem whiskerLeft_sum (P : C) {Q R : C} {J : Type*} (s : Finset J) (g : J → (Q ⟶ R)) :
    P ◁ ∑ j ∈ s, g j = ∑ j ∈ s, P ◁ g j :=
  map_sum ((tensoringLeft C).obj P).mapAddHom g s

theorem sum_whiskerRight {Q R : C} {J : Type*} (s : Finset J) (g : J → (Q ⟶ R)) (P : C) :
    (∑ j ∈ s, g j) ▷ P = ∑ j ∈ s, g j ▷ P :=
  map_sum ((tensoringRight C).obj P).mapAddHom g s

theorem tensor_sum {P Q R S : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J → (R ⟶ S)) :
    (f ⊗ₘ ∑ j ∈ s, g j) = ∑ j ∈ s, f ⊗ₘ g j := by
  simp only [tensorHom_def, whiskerLeft_sum, Preadditive.comp_sum]

theorem sum_tensor {P Q R S : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J → (R ⟶ S)) :
    (∑ j ∈ s, g j) ⊗ₘ f = ∑ j ∈ s, g j ⊗ₘ f := by
  simp only [tensorHom_def, sum_whiskerRight, Preadditive.sum_comp]

set_option backward.isDefEq.respectTransparency false in
-- In a closed monoidal category, this would hold because
-- `tensorLeft X` is a left adjoint and hence preserves all colimits.
-- In any case it is true in any preadditive category.
instance (X : C) : PreservesFiniteBiproducts (tensorLeft X) where
  preserves {J} :=
    let ⟨_⟩ := nonempty_fintype J
    { preserves := fun {f} =>
        { preserves := fun {b} i => ⟨isBilimitOfTotal _ (by
            dsimp
            simp_rw [← id_tensorHom]
            simp only [tensorHom_comp_tensorHom, Category.comp_id, ← tensor_sum, ← id_tensorHom_id,
              IsBilimit.total i])⟩ } }

set_option backward.isDefEq.respectTransparency false in
instance (X : C) : PreservesFiniteBiproducts (tensorRight X) where
  preserves {J} :=
    let ⟨_⟩ := nonempty_fintype J
    { preserves := fun {f} =>
        { preserves := fun {b} i => ⟨isBilimitOfTotal _ (by
            dsimp
            simp_rw [← tensorHom_id]
            simp only [tensorHom_comp_tensorHom, Category.comp_id, ← sum_tensor, ← id_tensorHom_id,
               IsBilimit.total i])⟩ } }

variable [HasFiniteBiproducts C]

/-- The isomorphism showing how tensor product on the left distributes over direct sums. -/
def leftDistributor {J : Type} [Finite J] (X : C) (f : J → C) : X ⊗ ⨁ f ≅ ⨁ fun j => X ⊗ f j :=
  (tensorLeft X).mapBiproduct f

theorem leftDistributor_hom {J : Type} [Fintype J] (X : C) (f : J → C) :
    (leftDistributor X f).hom =
      ∑ j : J, (X ◁ biproduct.π f j) ≫ biproduct.ι (fun j => X ⊗ f j) j := by
  classical
  ext
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  erw [biproduct.lift_π]
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem leftDistributor_inv {J : Type} [Fintype J] (X : C) (f : J → C) :
    (leftDistributor X f).inv = ∑ j : J, biproduct.π _ j ≫ (X ◁ biproduct.ι f j) := by
  classical
  ext
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  simp only [Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp, zero_comp,
    Finset.sum_dite_eq, Finset.mem_univ, ite_true, eqToHom_refl, Category.id_comp,
    biproduct.ι_desc]

@[reassoc (attr := simp)]
theorem leftDistributor_hom_comp_biproduct_π {J : Type} [Finite J] (X : C) (f : J → C) (j : J) :
    (leftDistributor X f).hom ≫ biproduct.π _ j = X ◁ biproduct.π _ j := by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_hom, Preadditive.sum_comp, biproduct.ι_π, comp_dite]

@[reassoc (attr := simp)]
theorem biproduct_ι_comp_leftDistributor_hom {J : Type} [Finite J] (X : C) (f : J → C) (j : J) :
    (X ◁ biproduct.ι _ j) ≫ (leftDistributor X f).hom = biproduct.ι (fun j => X ⊗ f j) j := by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_hom, Preadditive.comp_sum, ← whiskerLeft_comp_assoc,
    biproduct.ι_π, whiskerLeft_dite, dite_comp]

@[reassoc (attr := simp)]
theorem leftDistributor_inv_comp_biproduct_π {J : Type} [Finite J] (X : C) (f : J → C) (j : J) :
    (leftDistributor X f).inv ≫ (X ◁ biproduct.π _ j) = biproduct.π _ j := by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_inv, Preadditive.sum_comp, ← whiskerLeft_comp,
    biproduct.ι_π, whiskerLeft_dite, comp_dite]

@[reassoc (attr := simp)]
theorem biproduct_ι_comp_leftDistributor_inv {J : Type} [Finite J] (X : C) (f : J → C) (j : J) :
    biproduct.ι _ j ≫ (leftDistributor X f).inv = X ◁ biproduct.ι _ j := by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_inv, Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp]

theorem leftDistributor_assoc {J : Type} [Finite J] (X Y : C) (f : J → C) :
    (asIso (𝟙 X) ⊗ᵢ leftDistributor Y f) ≪≫ leftDistributor X _ =
      (α_ X Y (⨁ f)).symm ≪≫ leftDistributor (X ⊗ Y) f ≪≫ biproduct.mapIso fun _ => α_ X Y _ := by
  classical
  cases nonempty_fintype J
  ext
  simp only [Category.comp_id, Category.assoc, eqToHom_refl, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, comp_zero, comp_dite, Preadditive.sum_comp, Preadditive.comp_sum, tensor_sum,
    id_tensor_comp, tensorIso_hom, leftDistributor_hom, biproduct.mapIso_hom, biproduct.ι_map,
    biproduct.ι_π, Finset.sum_dite_irrel, Finset.sum_dite_eq', Finset.sum_const_zero]
  simp_rw [← id_tensorHom]
  simp only [← id_tensor_comp, biproduct.ι_π]
  simp only [id_tensor_comp, tensor_dite, comp_dite]
  simp

/-- The isomorphism showing how tensor product on the right distributes over direct sums. -/
def rightDistributor {J : Type} [Finite J] (f : J → C) (X : C) : (⨁ f) ⊗ X ≅ ⨁ fun j => f j ⊗ X :=
  (tensorRight X).mapBiproduct f

theorem rightDistributor_hom {J : Type} [Fintype J] (f : J → C) (X : C) :
    (rightDistributor f X).hom =
      ∑ j : J, (biproduct.π f j ▷ X) ≫ biproduct.ι (fun j => f j ⊗ X) j := by
  classical
  ext
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  erw [biproduct.lift_π]
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id, ite_true]

set_option backward.isDefEq.respectTransparency false in
theorem rightDistributor_inv {J : Type} [Fintype J] (f : J → C) (X : C) :
    (rightDistributor f X).inv = ∑ j : J, biproduct.π _ j ≫ (biproduct.ι f j ▷ X) := by
  classical
  ext
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  simp only [biproduct.ι_desc, Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp,
    zero_comp, Finset.sum_dite_eq, Finset.mem_univ, eqToHom_refl, Category.id_comp, ite_true]

@[reassoc (attr := simp)]
theorem rightDistributor_hom_comp_biproduct_π {J : Type} [Finite J] (f : J → C) (X : C) (j : J) :
    (rightDistributor f X).hom ≫ biproduct.π _ j = biproduct.π _ j ▷ X := by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_hom, Preadditive.sum_comp, biproduct.ι_π, comp_dite]

@[reassoc (attr := simp)]
theorem biproduct_ι_comp_rightDistributor_hom {J : Type} [Finite J] (f : J → C) (X : C) (j : J) :
    (biproduct.ι _ j ▷ X) ≫ (rightDistributor f X).hom = biproduct.ι (fun j => f j ⊗ X) j := by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_hom, Preadditive.comp_sum, ← comp_whiskerRight_assoc, biproduct.ι_π,
    dite_whiskerRight, dite_comp]

@[reassoc (attr := simp)]
theorem rightDistributor_inv_comp_biproduct_π {J : Type} [Finite J] (f : J → C) (X : C) (j : J) :
    (rightDistributor f X).inv ≫ (biproduct.π _ j ▷ X) = biproduct.π _ j := by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_inv, Preadditive.sum_comp, ← comp_whiskerRight,
    biproduct.ι_π, dite_whiskerRight, comp_dite]

@[reassoc (attr := simp)]
theorem biproduct_ι_comp_rightDistributor_inv {J : Type} [Finite J] (f : J → C) (X : C) (j : J) :
    biproduct.ι _ j ≫ (rightDistributor f X).inv = biproduct.ι _ j ▷ X := by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_inv, Preadditive.comp_sum, biproduct.ι_π_assoc,
    dite_comp]

theorem rightDistributor_assoc {J : Type} [Finite J] (f : J → C) (X Y : C) :
    (rightDistributor f X ⊗ᵢ asIso (𝟙 Y)) ≪≫ rightDistributor _ Y =
      α_ (⨁ f) X Y ≪≫ rightDistributor f (X ⊗ Y) ≪≫ biproduct.mapIso fun _ => (α_ _ X Y).symm := by
  classical
  cases nonempty_fintype J
  ext
  simp only [Category.comp_id, Category.assoc, eqToHom_refl, Iso.symm_hom, Iso.trans_hom,
    asIso_hom, comp_zero, comp_dite, Preadditive.sum_comp, Preadditive.comp_sum, sum_tensor,
    comp_tensor_id, tensorIso_hom, rightDistributor_hom, biproduct.mapIso_hom, biproduct.ι_map,
    biproduct.ι_π, Finset.sum_dite_irrel, Finset.sum_dite_eq', Finset.sum_const_zero,
    Finset.mem_univ, if_true]
  simp_rw [← tensorHom_id]
  simp only [← comp_tensor_id, biproduct.ι_π, dite_tensor, comp_dite]
  simp

theorem leftDistributor_rightDistributor_assoc {J : Type _} [Finite J]
    (X : C) (f : J → C) (Y : C) :
    (leftDistributor X f ⊗ᵢ asIso (𝟙 Y)) ≪≫ rightDistributor _ Y =
      α_ X (⨁ f) Y ≪≫
        (asIso (𝟙 X) ⊗ᵢ rightDistributor _ Y) ≪≫
          leftDistributor X _ ≪≫ biproduct.mapIso fun _ => (α_ _ _ _).symm := by
  classical
  cases nonempty_fintype J
  ext
  simp only [Category.comp_id, Category.assoc, eqToHom_refl, Iso.symm_hom, Iso.trans_hom,
    asIso_hom, comp_zero, comp_dite, Preadditive.sum_comp, Preadditive.comp_sum, sum_tensor,
    tensor_sum, comp_tensor_id, tensorIso_hom, leftDistributor_hom, rightDistributor_hom,
    biproduct.mapIso_hom, biproduct.ι_map, biproduct.ι_π, Finset.sum_dite_irrel,
    Finset.sum_dite_eq', Finset.sum_const_zero, Finset.mem_univ, if_true]
  simp_rw [← tensorHom_id, ← id_tensorHom]
  simp only [← comp_tensor_id, ← id_tensor_comp_assoc, Category.assoc, biproduct.ι_π, comp_dite,
    dite_comp, tensor_dite, dite_tensor]
  simp

@[ext]
theorem leftDistributor_ext_left {J : Type} [Finite J] {X Y : C} {f : J → C} {g h : X ⊗ ⨁ f ⟶ Y}
    (w : ∀ j, (X ◁ biproduct.ι f j) ≫ g = (X ◁ biproduct.ι f j) ≫ h) : g = h := by
  classical
  cases nonempty_fintype J
  apply (cancel_epi (leftDistributor X f).inv).mp
  ext
  simp [w]

@[ext]
theorem leftDistributor_ext_right {J : Type} [Finite J] {X Y : C} {f : J → C} {g h : X ⟶ Y ⊗ ⨁ f}
    (w : ∀ j, g ≫ (Y ◁ biproduct.π f j) = h ≫ (Y ◁ biproduct.π f j)) : g = h := by
  classical
  cases nonempty_fintype J
  apply (cancel_mono (leftDistributor Y f).hom).mp
  ext
  simp [w]

-- One might wonder how many iterated tensor products we need simp lemmas for.
-- The answer is two: this lemma is needed to verify the pentagon identity.
@[ext]
theorem leftDistributor_ext₂_left {J : Type} [Finite J]
    {X Y Z : C} {f : J → C} {g h : X ⊗ (Y ⊗ ⨁ f) ⟶ Z}
    (w : ∀ j, (X ◁ (Y ◁ biproduct.ι f j)) ≫ g = (X ◁ (Y ◁ biproduct.ι f j)) ≫ h) :
    g = h := by
  apply (cancel_epi (α_ _ _ _).hom).mp
  ext
  simp [w]

@[ext]
theorem leftDistributor_ext₂_right {J : Type} [Finite J]
    {X Y Z : C} {f : J → C} {g h : X ⟶ Y ⊗ (Z ⊗ ⨁ f)}
    (w : ∀ j, g ≫ (Y ◁ (Z ◁ biproduct.π f j)) = h ≫ (Y ◁ (Z ◁ biproduct.π f j))) :
    g = h := by
  apply (cancel_mono (α_ _ _ _).inv).mp
  ext
  simp [w]

@[ext]
theorem rightDistributor_ext_left {J : Type} [Finite J]
    {f : J → C} {X Y : C} {g h : (⨁ f) ⊗ X ⟶ Y}
    (w : ∀ j, (biproduct.ι f j ▷ X) ≫ g = (biproduct.ι f j ▷ X) ≫ h) : g = h := by
  classical
  cases nonempty_fintype J
  apply (cancel_epi (rightDistributor f X).inv).mp
  ext
  simp [w]

@[ext]
theorem rightDistributor_ext_right {J : Type} [Finite J]
    {f : J → C} {X Y : C} {g h : X ⟶ (⨁ f) ⊗ Y}
    (w : ∀ j, g ≫ (biproduct.π f j ▷ Y) = h ≫ (biproduct.π f j ▷ Y)) : g = h := by
  classical
  cases nonempty_fintype J
  apply (cancel_mono (rightDistributor f Y).hom).mp
  ext
  simp [w]

@[ext]
theorem rightDistributor_ext₂_left {J : Type} [Finite J]
    {f : J → C} {X Y Z : C} {g h : ((⨁ f) ⊗ X) ⊗ Y ⟶ Z}
    (w : ∀ j, ((biproduct.ι f j ▷ X) ▷ Y) ≫ g = ((biproduct.ι f j ▷ X) ▷ Y) ≫ h) :
    g = h := by
  apply (cancel_epi (α_ _ _ _).inv).mp
  ext
  simp [w]

@[ext]
theorem rightDistributor_ext₂_right {J : Type} [Finite J]
    {f : J → C} {X Y Z : C} {g h : X ⟶ ((⨁ f) ⊗ Y) ⊗ Z}
    (w : ∀ j, g ≫ ((biproduct.π f j ▷ Y) ▷ Z) = h ≫ ((biproduct.π f j ▷ Y) ▷ Z)) :
    g = h := by
  apply (cancel_mono (α_ _ _ _).hom).mp
  ext
  simp [w]

end CategoryTheory
