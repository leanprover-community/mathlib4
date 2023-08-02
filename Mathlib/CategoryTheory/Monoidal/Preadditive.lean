/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Functor

#align_import category_theory.monoidal.preadditive from "leanprover-community/mathlib"@"986c4d5761f938b2e1c43c01f001b6d9d88c2055"

/-!
# Preadditive monoidal categories

A monoidal category is `MonoidalPreadditive` if it is preadditive and tensor product of morphisms
is linear in both factors.
-/


noncomputable section

open Classical

namespace CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

variable (C : Type _) [Category C] [Preadditive C] [MonoidalCategory C]

/-- A category is `MonoidalPreadditive` if tensoring is additive in both factors.

Note we don't `extend Preadditive C` here, as `Abelian C` already extends it,
and we'll need to have both typeclasses sometimes.
-/
class MonoidalPreadditive : Prop where
  whiskerLeft_zero : ∀ {X Y Z : C}, X ◁ (0 : Y ⟶ Z) = 0 := by aesop_cat
  zero_whiskerRight : ∀ {X Y Z : C}, (0 : Y ⟶ Z) ▷ X = 0 := by aesop_cat
  whiskerLeft_add : ∀ {X Y Z : C} (f g : Y ⟶ Z), X ◁ (f + g) = X ◁ f + X ◁ g := by aesop_cat
  add_whiskerRight : ∀ {X Y Z : C} (f g : Y ⟶ Z), (f + g) ▷ X = f ▷ X + g ▷ X := by aesop_cat
#align category_theory.monoidal_preadditive CategoryTheory.MonoidalPreadditive

-- attribute [simp] MonoidalPreadditive.tensor_zero MonoidalPreadditive.zero_tensor
attribute [simp] MonoidalPreadditive.whiskerLeft_zero MonoidalPreadditive.zero_whiskerRight
attribute [simp] MonoidalPreadditive.whiskerLeft_add MonoidalPreadditive.add_whiskerRight

variable {C}
variable [MonoidalPreadditive C]

-- attribute [local simp] MonoidalPreadditive.tensor_add MonoidalPreadditive.add_tensor

instance tensorLeft_additive (X : C) : (tensorLeft X).Additive where
#align category_theory.tensor_left_additive CategoryTheory.tensorLeft_additive

instance tensorRight_additive (X : C) : (tensorRight X).Additive where
#align category_theory.tensor_right_additive CategoryTheory.tensorRight_additive

instance tensoringLeft_additive (X : C) : ((tensoringLeft C).obj X).Additive where
#align category_theory.tensoring_left_additive CategoryTheory.tensoringLeft_additive

instance tensoringRight_additive (X : C) : ((tensoringRight C).obj X).Additive where
#align category_theory.tensoring_right_additive CategoryTheory.tensoringRight_additive

/-- A faithful additive monoidal functor to a monoidal preadditive category
ensures that the domain is monoidal preadditive. -/
theorem monoidalPreadditive_of_faithful {D} [Category D] [Preadditive D] [MonoidalCategory D]
    (F : MonoidalFunctor D C) [Faithful F.toFunctor] [F.toFunctor.Additive] :
    MonoidalPreadditive D :=
  { whiskerLeft_zero := by
      intros
      apply F.toFunctor.map_injective
      simp [F.map_whiskerLeft]
    zero_whiskerRight := by
      intros
      apply F.toFunctor.map_injective
      simp [F.map_whiskerRight]
    whiskerLeft_add := by
      intros
      apply F.toFunctor.map_injective
      simp only [F.map_whiskerLeft, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp,
        MonoidalPreadditive.whiskerLeft_add]
    add_whiskerRight := by
      intros
      apply F.toFunctor.map_injective
      simp only [F.map_whiskerRight, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp,
        MonoidalPreadditive.add_whiskerRight] }
#align category_theory.monoidal_preadditive_of_faithful CategoryTheory.monoidalPreadditive_of_faithful

open BigOperators

attribute [local simp] tensorHom_def

theorem whiskerLeft_sum (P : C) {Q R : C} {J : Type _} (s : Finset J) (g : J → (Q ⟶ R)) :
    P ◁ ∑ j in s, g j = ∑ j in s, P ◁ g j :=
  map_sum ((tensoringLeft C).obj P).mapAddHom g s

theorem sum_whiskerRight {Q R : C} {J : Type _} (s : Finset J) (g : J → (Q ⟶ R)) (P : C) :
    (∑ j in s, g j) ▷ P = ∑ j in s, g j ▷ P :=
  map_sum ((tensoringRight C).obj P).mapAddHom g s

theorem tensor_sum {P Q R S : C} {J : Type _} (s : Finset J) (f : P ⟶ Q) (g : J → (R ⟶ S)) :
    (f ⊗ ∑ j in s, g j) = ∑ j in s, f ⊗ g j := by
  simp [whiskerLeft_sum, sum_whiskerRight, Preadditive.sum_comp]
#align category_theory.tensor_sum CategoryTheory.tensor_sum

theorem sum_tensor {P Q R S : C} {J : Type _} (s : Finset J) (f : P ⟶ Q) (g : J → (R ⟶ S)) :
    (∑ j in s, g j) ⊗ f = ∑ j in s, g j ⊗ f := by
  simp [whiskerLeft_sum, sum_whiskerRight, Preadditive.comp_sum]
#align category_theory.sum_tensor CategoryTheory.sum_tensor

-- In a closed monoidal category, this would hold because
-- `tensorLeft X` is a left adjoint and hence preserves all colimits.
-- In any case it is true in any preadditive category.
instance (X : C) : PreservesFiniteBiproducts (tensorLeft X) where
  preserves {J} :=
    { preserves := fun {f} =>
        { preserves := fun {b} i => isBilimitOfTotal _ (by
            dsimp
            simp_rw [← whiskerLeft_comp]
            simp_rw [← tensorHom_id, ← id_tensorHom]
            simp only [← tensor_comp, Category.comp_id, ← tensor_sum, ← tensor_id,
              IsBilimit.total i]) } }

instance (X : C) : PreservesFiniteBiproducts (tensorRight X) where
  preserves {J} :=
    { preserves := fun {f} =>
        { preserves := fun {b} i => isBilimitOfTotal _ (by
            dsimp
            simp_rw [← tensorHom_id, ← id_tensorHom]
            simp only [← tensor_comp, Category.comp_id, ← sum_tensor, ← tensor_id,
               IsBilimit.total i]) } }

variable [HasFiniteBiproducts C]

/-- The isomorphism showing how tensor product on the left distributes over direct sums. -/
def leftDistributor {J : Type} [Fintype J] (X : C) (f : J → C) : X ⊗ ⨁ f ≅ ⨁ fun j => X ⊗ f j :=
  (tensorLeft X).mapBiproduct f
#align category_theory.left_distributor CategoryTheory.leftDistributor

@[simp]
theorem leftDistributor_hom {J : Type} [Fintype J] (X : C) (f : J → C) :
    (leftDistributor X f).hom =
      ∑ j : J, (X ◁ biproduct.π f j) ≫ biproduct.ι (fun j => X ⊗ f j) j := by
  ext
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  erw [biproduct.lift_π]
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]
#align category_theory.left_distributor_hom CategoryTheory.leftDistributor_hom

@[simp]
theorem leftDistributor_inv {J : Type} [Fintype J] (X : C) (f : J → C) :
    (leftDistributor X f).inv = ∑ j : J, biproduct.π _ j ≫ (X ◁ biproduct.ι f j) := by
  ext
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  simp only [Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp, zero_comp,
    Finset.sum_dite_eq, Finset.mem_univ, ite_true, eqToHom_refl, Category.id_comp,
    biproduct.ι_desc]
#align category_theory.left_distributor_inv CategoryTheory.leftDistributor_inv

theorem leftDistributor_assoc {J : Type} [Fintype J] (X Y : C) (f : J → C) :
    (asIso (𝟙 X) ⊗ leftDistributor Y f) ≪≫ leftDistributor X _ =
      (α_ X Y (⨁ f)).symm ≪≫ leftDistributor (X ⊗ Y) f ≪≫ biproduct.mapIso fun j => α_ X Y _ := by
  ext
  simp only [Category.comp_id, Category.assoc, eqToHom_refl, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, comp_zero, comp_dite, Preadditive.sum_comp, Preadditive.comp_sum, tensor_sum,
    id_tensor_comp, tensorIso_hom, leftDistributor_hom, biproduct.mapIso_hom, biproduct.ι_map,
    biproduct.ι_π, Finset.sum_dite_irrel, Finset.sum_dite_eq', Finset.sum_const_zero]
  simp_rw [← tensorHom_id, ← id_tensorHom]
  simp only [← id_tensor_comp, biproduct.ι_π]
  simp only [id_tensor_comp, tensor_dite, comp_dite]
  simp
#align category_theory.left_distributor_assoc CategoryTheory.leftDistributor_assoc

/-- The isomorphism showing how tensor product on the right distributes over direct sums. -/
def rightDistributor {J : Type} [Fintype J] (X : C) (f : J → C) : (⨁ f) ⊗ X ≅ ⨁ fun j => f j ⊗ X :=
  (tensorRight X).mapBiproduct f
#align category_theory.right_distributor CategoryTheory.rightDistributor

@[simp]
theorem rightDistributor_hom {J : Type} [Fintype J] (X : C) (f : J → C) :
    (rightDistributor X f).hom =
      ∑ j : J, (biproduct.π f j ▷ X) ≫ biproduct.ι (fun j => f j ⊗ X) j := by
  ext
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  erw [biproduct.lift_π]
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id, ite_true]
#align category_theory.right_distributor_hom CategoryTheory.rightDistributor_hom

@[simp]
theorem rightDistributor_inv {J : Type} [Fintype J] (X : C) (f : J → C) :
    (rightDistributor X f).inv = ∑ j : J, biproduct.π _ j ≫ (biproduct.ι f j ▷ X) := by
  ext
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  simp only [biproduct.ι_desc, Preadditive.comp_sum, ne_eq, biproduct.ι_π_assoc, dite_comp,
    zero_comp, Finset.sum_dite_eq, Finset.mem_univ, eqToHom_refl, Category.id_comp, ite_true]
#align category_theory.right_distributor_inv CategoryTheory.rightDistributor_inv

theorem rightDistributor_assoc {J : Type} [Fintype J] (X Y : C) (f : J → C) :
    (rightDistributor X f ⊗ asIso (𝟙 Y)) ≪≫ rightDistributor Y _ =
      α_ (⨁ f) X Y ≪≫ rightDistributor (X ⊗ Y) f ≪≫ biproduct.mapIso fun j => (α_ _ X Y).symm := by
  ext
  simp only [Category.comp_id, Category.assoc, eqToHom_refl, Iso.symm_hom, Iso.trans_hom,
    asIso_hom, comp_zero, comp_dite, Preadditive.sum_comp, Preadditive.comp_sum, sum_tensor,
    comp_tensor_id, tensorIso_hom, rightDistributor_hom, biproduct.mapIso_hom, biproduct.ι_map,
    biproduct.ι_π, Finset.sum_dite_irrel, Finset.sum_dite_eq', Finset.sum_const_zero,
    Finset.mem_univ, if_true]
  simp_rw [← tensorHom_id, ← id_tensorHom]
  simp only [← comp_tensor_id, biproduct.ι_π, dite_tensor, comp_dite]
  simp
#align category_theory.right_distributor_assoc CategoryTheory.rightDistributor_assoc

theorem leftDistributor_rightDistributor_assoc {J : Type _} [Fintype J] (X Y : C) (f : J → C) :
    (leftDistributor X f ⊗ asIso (𝟙 Y)) ≪≫ rightDistributor Y _ =
      α_ X (⨁ f) Y ≪≫
        (asIso (𝟙 X) ⊗ rightDistributor Y _) ≪≫
          leftDistributor X _ ≪≫ biproduct.mapIso fun j => (α_ _ _ _).symm := by
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
#align category_theory.left_distributor_right_distributor_assoc CategoryTheory.leftDistributor_rightDistributor_assoc

end CategoryTheory
