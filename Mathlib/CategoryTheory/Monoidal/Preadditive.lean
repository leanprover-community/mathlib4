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

variable (C : Type*) [Category C] [Preadditive C] [MonoidalCategory C]

/-- A category is `MonoidalPreadditive` if tensoring is additive in both factors.

Note we don't `extend Preadditive C` here, as `Abelian C` already extends it,
and we'll need to have both typeclasses sometimes.
-/
class MonoidalPreadditive : Prop where
  /-- tensoring on the right with a zero morphism gives zero -/
  tensor_zero : ∀ {W X Y Z : C} (f : W ⟶ X), f ⊗ (0 : Y ⟶ Z) = 0 := by aesop_cat
  /-- tensoring on the left with a zero morphism gives zero -/
  zero_tensor : ∀ {W X Y Z : C} (f : Y ⟶ Z), (0 : W ⟶ X) ⊗ f = 0 := by aesop_cat
  /-- left tensoring with a morphism is compatible with addition -/
  tensor_add : ∀ {W X Y Z : C} (f : W ⟶ X) (g h : Y ⟶ Z), f ⊗ (g + h) = f ⊗ g + f ⊗ h := by
    aesop_cat
  /-- right tensoring with a morphism is compatible with addition -/
  add_tensor : ∀ {W X Y Z : C} (f g : W ⟶ X) (h : Y ⟶ Z), (f + g) ⊗ h = f ⊗ h + g ⊗ h := by
    aesop_cat
#align category_theory.monoidal_preadditive CategoryTheory.MonoidalPreadditive

attribute [simp] MonoidalPreadditive.tensor_zero MonoidalPreadditive.zero_tensor

variable {C}
variable [MonoidalPreadditive C]

attribute [local simp] MonoidalPreadditive.tensor_add MonoidalPreadditive.add_tensor

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
  { tensor_zero := by
      intros
      -- ⊢ f✝ ⊗ 0 = 0
      apply F.toFunctor.map_injective
      -- ⊢ F.map (f✝ ⊗ 0) = F.map 0
      simp [F.map_tensor]
      -- 🎉 no goals
    zero_tensor := by
      intros
      -- ⊢ 0 ⊗ f✝ = 0
      apply F.toFunctor.map_injective
      -- ⊢ F.map (0 ⊗ f✝) = F.map 0
      simp [F.map_tensor]
      -- 🎉 no goals
    tensor_add := by
      intros
      -- ⊢ f✝ ⊗ (g✝ + h✝) = f✝ ⊗ g✝ + f✝ ⊗ h✝
      apply F.toFunctor.map_injective
      -- ⊢ F.map (f✝ ⊗ (g✝ + h✝)) = F.map (f✝ ⊗ g✝ + f✝ ⊗ h✝)
      simp only [F.map_tensor, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp,
        MonoidalPreadditive.tensor_add]
    add_tensor := by
      intros
      -- ⊢ (f✝ + g✝) ⊗ h✝ = f✝ ⊗ h✝ + g✝ ⊗ h✝
      apply F.toFunctor.map_injective
      -- ⊢ F.map ((f✝ + g✝) ⊗ h✝) = F.map (f✝ ⊗ h✝ + g✝ ⊗ h✝)
      simp only [F.map_tensor, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp,
        MonoidalPreadditive.add_tensor] }
#align category_theory.monoidal_preadditive_of_faithful CategoryTheory.monoidalPreadditive_of_faithful

open BigOperators

theorem tensor_sum {P Q R S : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J → (R ⟶ S)) :
    (f ⊗ ∑ j in s, g j) = ∑ j in s, f ⊗ g j := by
  rw [← tensor_id_comp_id_tensor]
  -- ⊢ (f ⊗ 𝟙 R) ≫ (𝟙 Q ⊗ ∑ j in s, g j) = ∑ j in s, f ⊗ g j
  let tQ := (((tensoringLeft C).obj Q).mapAddHom : (R ⟶ S) →+ _)
  -- ⊢ (f ⊗ 𝟙 R) ≫ (𝟙 Q ⊗ ∑ j in s, g j) = ∑ j in s, f ⊗ g j
  change _ ≫ tQ _ = _
  -- ⊢ (f ⊗ 𝟙 R) ≫ ↑tQ (∑ j in s, g j) = ∑ j in s, f ⊗ g j
  rw [tQ.map_sum, Preadditive.comp_sum]
  -- ⊢ ∑ j in s, (f ⊗ 𝟙 R) ≫ ↑tQ (g j) = ∑ j in s, f ⊗ g j
  dsimp [Functor.mapAddHom]
  -- ⊢ ∑ j in s, (f ⊗ 𝟙 R) ≫ (𝟙 Q ⊗ g j) = ∑ j in s, f ⊗ g j
  simp only [tensor_id_comp_id_tensor]
  -- 🎉 no goals
#align category_theory.tensor_sum CategoryTheory.tensor_sum

theorem sum_tensor {P Q R S : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J → (R ⟶ S)) :
    (∑ j in s, g j) ⊗ f = ∑ j in s, g j ⊗ f := by
  rw [← tensor_id_comp_id_tensor]
  -- ⊢ ((∑ j in s, g j) ⊗ 𝟙 P) ≫ (𝟙 S ⊗ f) = ∑ j in s, g j ⊗ f
  let tQ := (((tensoringRight C).obj P).mapAddHom : (R ⟶ S) →+ _)
  -- ⊢ ((∑ j in s, g j) ⊗ 𝟙 P) ≫ (𝟙 S ⊗ f) = ∑ j in s, g j ⊗ f
  change tQ _ ≫ _ = _
  -- ⊢ ↑tQ (∑ j in s, g j) ≫ (𝟙 S ⊗ f) = ∑ j in s, g j ⊗ f
  rw [tQ.map_sum, Preadditive.sum_comp]
  -- ⊢ ∑ j in s, ↑tQ (g j) ≫ (𝟙 S ⊗ f) = ∑ j in s, g j ⊗ f
  dsimp [Functor.mapAddHom]
  -- ⊢ ∑ j in s, (g j ⊗ 𝟙 P) ≫ (𝟙 S ⊗ f) = ∑ j in s, g j ⊗ f
  simp only [tensor_id_comp_id_tensor]
  -- 🎉 no goals
#align category_theory.sum_tensor CategoryTheory.sum_tensor

-- In a closed monoidal category, this would hold because
-- `tensorLeft X` is a left adjoint and hence preserves all colimits.
-- In any case it is true in any preadditive category.
instance (X : C) : PreservesFiniteBiproducts (tensorLeft X) where
  preserves {J} :=
    { preserves := fun {f} =>
        { preserves := fun {b} i => isBilimitOfTotal _ (by
            dsimp
            -- ⊢ ∑ j : J, (𝟙 X ⊗ Bicone.π b j) ≫ (𝟙 X ⊗ Bicone.ι b j) = 𝟙 (X ⊗ b.pt)
            simp only [← tensor_comp, Category.comp_id, ← tensor_sum, ← tensor_id,
              IsBilimit.total i]) } }

instance (X : C) : PreservesFiniteBiproducts (tensorRight X) where
  preserves {J} :=
    { preserves := fun {f} =>
        { preserves := fun {b} i => isBilimitOfTotal _ (by
            dsimp
            -- ⊢ ∑ j : J, (Bicone.π b j ⊗ 𝟙 X) ≫ (Bicone.ι b j ⊗ 𝟙 X) = 𝟙 (b.pt ⊗ X)
            simp only [← tensor_comp, Category.comp_id, ← sum_tensor, ← tensor_id,
               IsBilimit.total i]) } }

variable [HasFiniteBiproducts C]

/-- The isomorphism showing how tensor product on the left distributes over direct sums. -/
def leftDistributor {J : Type} [Fintype J] (X : C) (f : J → C) : X ⊗ ⨁ f ≅ ⨁ fun j => X ⊗ f j :=
  (tensorLeft X).mapBiproduct f
#align category_theory.left_distributor CategoryTheory.leftDistributor

theorem leftDistributor_hom {J : Type} [Fintype J] (X : C) (f : J → C) :
    (leftDistributor X f).hom =
      ∑ j : J, (𝟙 X ⊗ biproduct.π f j) ≫ biproduct.ι (fun j => X ⊗ f j) j := by
  ext
  -- ⊢ (leftDistributor X f).hom ≫ biproduct.π (fun j => X ⊗ f j) j✝ = (∑ j : J, (𝟙 …
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  -- ⊢ (biproduct.lift fun j => 𝟙 X ⊗ biproduct.π f j) ≫ biproduct.π (fun j => X ⊗  …
  erw [biproduct.lift_π]
  -- ⊢ 𝟙 X ⊗ biproduct.π f j✝ = (∑ j : J, (𝟙 X ⊗ biproduct.π f j) ≫ biproduct.ι (fu …
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]
#align category_theory.left_distributor_hom CategoryTheory.leftDistributor_hom

theorem leftDistributor_inv {J : Type} [Fintype J] (X : C) (f : J → C) :
    (leftDistributor X f).inv = ∑ j : J, biproduct.π _ j ≫ (𝟙 X ⊗ biproduct.ι f j) := by
  ext
  -- ⊢ biproduct.ι (fun j => X ⊗ f j) j✝ ≫ (leftDistributor X f).inv = biproduct.ι  …
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  -- ⊢ (biproduct.ι (fun j => X ⊗ f j) j✝ ≫ biproduct.desc fun j => 𝟙 X ⊗ biproduct …
  simp only [Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp, zero_comp,
    Finset.sum_dite_eq, Finset.mem_univ, ite_true, eqToHom_refl, Category.id_comp,
    biproduct.ι_desc]
#align category_theory.left_distributor_inv CategoryTheory.leftDistributor_inv

@[reassoc (attr := simp)]
theorem leftDistributor_hom_comp_biproduct_π {J : Type} [Fintype J] (X : C) (f : J → C) (j : J) :
    (leftDistributor X f).hom ≫ biproduct.π _ j = 𝟙 X ⊗ biproduct.π _ j := by
  simp [leftDistributor_hom, Preadditive.sum_comp, biproduct.ι_π, comp_dite]
  -- 🎉 no goals

@[reassoc (attr := simp)]
theorem biproduct_ι_comp_leftDistributor_hom {J : Type} [Fintype J] (X : C) (f : J → C) (j : J) :
    (𝟙 X ⊗ biproduct.ι _ j) ≫ (leftDistributor X f).hom = biproduct.ι (fun j => X ⊗ f j) j := by
  simp [leftDistributor_hom, Preadditive.comp_sum, ← id_tensor_comp_assoc, biproduct.ι_π,
    tensor_dite, dite_comp]

@[reassoc (attr := simp)]
theorem leftDistributor_inv_comp_biproduct_π {J : Type} [Fintype J] (X : C) (f : J → C) (j : J) :
    (leftDistributor X f).inv ≫ (𝟙 X ⊗ biproduct.π _ j) = biproduct.π _ j := by
  simp [leftDistributor_inv, Preadditive.sum_comp, ← id_tensor_comp, biproduct.ι_π, tensor_dite,
    comp_dite]

@[reassoc (attr := simp)]
theorem biproduct_ι_comp_leftDistributor_inv {J : Type} [Fintype J] (X : C) (f : J → C) (j : J) :
    biproduct.ι _ j ≫ (leftDistributor X f).inv = 𝟙 X ⊗ biproduct.ι _ j := by
  simp [leftDistributor_inv, Preadditive.comp_sum, ← id_tensor_comp, biproduct.ι_π_assoc, dite_comp]
  -- 🎉 no goals

theorem leftDistributor_assoc {J : Type} [Fintype J] (X Y : C) (f : J → C) :
    (asIso (𝟙 X) ⊗ leftDistributor Y f) ≪≫ leftDistributor X _ =
      (α_ X Y (⨁ f)).symm ≪≫ leftDistributor (X ⊗ Y) f ≪≫ biproduct.mapIso fun j => α_ X Y _ := by
  ext
  -- ⊢ ((asIso (𝟙 X) ⊗ leftDistributor Y f) ≪≫ leftDistributor X fun j => Y ⊗ f j). …
  simp only [Category.comp_id, Category.assoc, eqToHom_refl, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, comp_zero, comp_dite, Preadditive.sum_comp, Preadditive.comp_sum, tensor_sum,
    id_tensor_comp, tensorIso_hom, leftDistributor_hom, biproduct.mapIso_hom, biproduct.ι_map,
    biproduct.ι_π, Finset.sum_dite_irrel, Finset.sum_dite_eq', Finset.sum_const_zero]
  simp only [← id_tensor_comp, biproduct.ι_π]
  -- ⊢ (if j✝ ∈ Finset.univ then ∑ x : J, 𝟙 X ⊗ (𝟙 Y ⊗ biproduct.π f x) ≫ if h : x  …
  simp only [id_tensor_comp, tensor_dite, comp_dite]
  -- ⊢ (if j✝ ∈ Finset.univ then ∑ x : J, if h : x = j✝ then (𝟙 X ⊗ 𝟙 Y ⊗ biproduct …
  simp only [Category.comp_id, comp_zero, MonoidalPreadditive.tensor_zero, eqToHom_refl,
    tensor_id, if_true, dif_ctx_congr, Finset.sum_congr, Finset.mem_univ, Finset.sum_dite_eq']
  simp only [← tensor_id, associator_naturality, Iso.inv_hom_id_assoc]
  -- 🎉 no goals
#align category_theory.left_distributor_assoc CategoryTheory.leftDistributor_assoc

/-- The isomorphism showing how tensor product on the right distributes over direct sums. -/
def rightDistributor {J : Type} [Fintype J] (f : J → C) (X : C) : (⨁ f) ⊗ X ≅ ⨁ fun j => f j ⊗ X :=
  (tensorRight X).mapBiproduct f
#align category_theory.right_distributor CategoryTheory.rightDistributor

theorem rightDistributor_hom {J : Type} [Fintype J] (f : J → C) (X : C) :
    (rightDistributor f X).hom =
      ∑ j : J, (biproduct.π f j ⊗ 𝟙 X) ≫ biproduct.ι (fun j => f j ⊗ X) j := by
  ext
  -- ⊢ (rightDistributor f X).hom ≫ biproduct.π (fun j => f j ⊗ X) j✝ = (∑ j : J, ( …
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  -- ⊢ (biproduct.lift fun j => biproduct.π f j ⊗ 𝟙 X) ≫ biproduct.π (fun j => f j  …
  erw [biproduct.lift_π]
  -- ⊢ biproduct.π f j✝ ⊗ 𝟙 X = (∑ j : J, (biproduct.π f j ⊗ 𝟙 X) ≫ biproduct.ι (fu …
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id, ite_true]
#align category_theory.right_distributor_hom CategoryTheory.rightDistributor_hom

theorem rightDistributor_inv {J : Type} [Fintype J] (f : J → C) (X : C) :
    (rightDistributor f X).inv = ∑ j : J, biproduct.π _ j ≫ (biproduct.ι f j ⊗ 𝟙 X) := by
  ext
  -- ⊢ biproduct.ι (fun j => f j ⊗ X) j✝ ≫ (rightDistributor f X).inv = biproduct.ι …
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  -- ⊢ (biproduct.ι (fun j => f j ⊗ X) j✝ ≫ biproduct.desc fun j => biproduct.ι f j …
  simp only [biproduct.ι_desc, Preadditive.comp_sum, ne_eq, biproduct.ι_π_assoc, dite_comp,
    zero_comp, Finset.sum_dite_eq, Finset.mem_univ, eqToHom_refl, Category.id_comp, ite_true]
#align category_theory.right_distributor_inv CategoryTheory.rightDistributor_inv

@[reassoc (attr := simp)]
theorem rightDistributor_hom_comp_biproduct_π {J : Type} [Fintype J] (f : J → C) (X : C) (j : J) :
    (rightDistributor f X).hom ≫ biproduct.π _ j = biproduct.π _ j ⊗ 𝟙 X := by
  simp [rightDistributor_hom, Preadditive.sum_comp, biproduct.ι_π, comp_dite]
  -- 🎉 no goals

@[reassoc (attr := simp)]
theorem biproduct_ι_comp_rightDistributor_hom {J : Type} [Fintype J] (f : J → C) (X : C) (j : J) :
    (biproduct.ι _ j ⊗ 𝟙 X) ≫ (rightDistributor f X).hom = biproduct.ι (fun j => f j ⊗ X) j := by
  simp [rightDistributor_hom, Preadditive.comp_sum, ← comp_tensor_id_assoc, biproduct.ι_π,
    dite_tensor, dite_comp]

@[reassoc (attr := simp)]
theorem rightDistributor_inv_comp_biproduct_π {J : Type} [Fintype J] (f : J → C) (X : C) (j : J) :
    (rightDistributor f X).inv ≫ (biproduct.π _ j ⊗ 𝟙 X) = biproduct.π _ j := by
  simp [rightDistributor_inv, Preadditive.sum_comp, ← comp_tensor_id, biproduct.ι_π, dite_tensor,
    comp_dite]

@[reassoc (attr := simp)]
theorem biproduct_ι_comp_rightDistributor_inv {J : Type} [Fintype J] (f : J → C) (X : C) (j : J) :
    biproduct.ι _ j ≫ (rightDistributor f X).inv = biproduct.ι _ j ⊗ 𝟙 X := by
  simp [rightDistributor_inv, Preadditive.comp_sum, ← id_tensor_comp, biproduct.ι_π_assoc,
    dite_comp]

theorem rightDistributor_assoc {J : Type} [Fintype J] (f : J → C) (X Y : C) :
    (rightDistributor f X ⊗ asIso (𝟙 Y)) ≪≫ rightDistributor _ Y =
      α_ (⨁ f) X Y ≪≫ rightDistributor f (X ⊗ Y) ≪≫ biproduct.mapIso fun j => (α_ _ X Y).symm := by
  ext
  -- ⊢ ((rightDistributor f X ⊗ asIso (𝟙 Y)) ≪≫ rightDistributor (fun j => f j ⊗ X) …
  simp only [Category.comp_id, Category.assoc, eqToHom_refl, Iso.symm_hom, Iso.trans_hom,
    asIso_hom, comp_zero, comp_dite, Preadditive.sum_comp, Preadditive.comp_sum, sum_tensor,
    comp_tensor_id, tensorIso_hom, rightDistributor_hom, biproduct.mapIso_hom, biproduct.ι_map,
    biproduct.ι_π, Finset.sum_dite_irrel, Finset.sum_dite_eq', Finset.sum_const_zero,
    Finset.mem_univ, if_true]
  simp only [← comp_tensor_id, biproduct.ι_π, dite_tensor, comp_dite]
  -- ⊢ (∑ x : J, if h : x = j✝ then (biproduct.π f x ⊗ 𝟙 X) ≫ eqToHom (_ : f x ⊗ X  …
  simp only [Category.comp_id, comp_tensor_id, eqToHom_refl, tensor_id, comp_zero,
    MonoidalPreadditive.zero_tensor, if_true, dif_ctx_congr, Finset.mem_univ, Finset.sum_congr,
    Finset.sum_dite_eq']
  simp only [← tensor_id, associator_inv_naturality, Iso.hom_inv_id_assoc]
  -- 🎉 no goals
#align category_theory.right_distributor_assoc CategoryTheory.rightDistributor_assoc

theorem leftDistributor_rightDistributor_assoc {J : Type _} [Fintype J]
    (X : C) (f : J → C) (Y : C) :
    (leftDistributor X f ⊗ asIso (𝟙 Y)) ≪≫ rightDistributor _ Y =
      α_ X (⨁ f) Y ≪≫
        (asIso (𝟙 X) ⊗ rightDistributor _ Y) ≪≫
          leftDistributor X _ ≪≫ biproduct.mapIso fun j => (α_ _ _ _).symm := by
  ext
  -- ⊢ ((leftDistributor X f ⊗ asIso (𝟙 Y)) ≪≫ rightDistributor (fun j => X ⊗ f j)  …
  simp only [Category.comp_id, Category.assoc, eqToHom_refl, Iso.symm_hom, Iso.trans_hom,
    asIso_hom, comp_zero, comp_dite, Preadditive.sum_comp, Preadditive.comp_sum, sum_tensor,
    tensor_sum, comp_tensor_id, tensorIso_hom, leftDistributor_hom, rightDistributor_hom,
    biproduct.mapIso_hom, biproduct.ι_map, biproduct.ι_π, Finset.sum_dite_irrel,
    Finset.sum_dite_eq', Finset.sum_const_zero, Finset.mem_univ, if_true]
  simp only [← comp_tensor_id, ← id_tensor_comp_assoc, Category.assoc, biproduct.ι_π, comp_dite,
    dite_comp, tensor_dite, dite_tensor]
  simp only [Category.comp_id, Category.id_comp, Category.assoc, id_tensor_comp, comp_zero,
    zero_comp, MonoidalPreadditive.tensor_zero, MonoidalPreadditive.zero_tensor, comp_tensor_id,
    eqToHom_refl, tensor_id, if_true, dif_ctx_congr, Finset.sum_congr, Finset.mem_univ,
    Finset.sum_dite_eq']
  simp only [associator_inv_naturality, Iso.hom_inv_id_assoc]
  -- 🎉 no goals
#align category_theory.left_distributor_right_distributor_assoc CategoryTheory.leftDistributor_rightDistributor_assoc

@[ext]
theorem leftDistributor_ext_left {J : Type} [Fintype J] {X Y : C} {f : J → C} {g h : X ⊗ ⨁ f ⟶ Y}
    (w : ∀ j, (𝟙 X ⊗ biproduct.ι f j) ≫ g = (𝟙 X ⊗ biproduct.ι f j) ≫ h) : g = h := by
  apply (cancel_epi (leftDistributor X f).inv).mp
  -- ⊢ (leftDistributor X f).inv ≫ g = (leftDistributor X f).inv ≫ h
  ext
  -- ⊢ biproduct.ι (fun j => X ⊗ f j) j✝ ≫ (leftDistributor X f).inv ≫ g = biproduc …
  simp? [leftDistributor_inv, Preadditive.comp_sum_assoc, biproduct.ι_π_assoc, dite_comp] says
    simp only [leftDistributor_inv, Preadditive.comp_sum_assoc, ne_eq, biproduct.ι_π_assoc,
      dite_comp, zero_comp, Finset.sum_dite_eq, Finset.mem_univ, eqToHom_refl, Category.id_comp,
      ite_true]
  apply w
  -- 🎉 no goals

@[ext]
theorem leftDistributor_ext_right {J : Type} [Fintype J] {X Y : C} {f : J → C} {g h : X ⟶ Y ⊗ ⨁ f}
    (w : ∀ j, g ≫ (𝟙 Y ⊗ biproduct.π f j) = h ≫ (𝟙 Y ⊗ biproduct.π f j)) : g = h := by
  apply (cancel_mono (leftDistributor Y f).hom).mp
  -- ⊢ g ≫ (leftDistributor Y f).hom = h ≫ (leftDistributor Y f).hom
  ext
  -- ⊢ (g ≫ (leftDistributor Y f).hom) ≫ biproduct.π (fun j => Y ⊗ f j) j✝ = (h ≫ ( …
  simp? [leftDistributor_hom, Preadditive.sum_comp, Preadditive.comp_sum_assoc, biproduct.ι_π,
    comp_dite] says
    simp only [leftDistributor_hom, Category.assoc, Preadditive.sum_comp, ne_eq, biproduct.ι_π,
      comp_dite, comp_zero, Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id,
      ite_true]
  apply w
  -- 🎉 no goals

-- One might wonder how many iterated tensor products we need simp lemmas for.
-- The answer is two: this lemma is needed to verify the pentagon identity.
@[ext]
theorem leftDistributor_ext₂_left {J : Type} [Fintype J]
    {X Y Z : C} {f : J → C} {g h : X ⊗ (Y ⊗ ⨁ f) ⟶ Z}
    (w : ∀ j, (𝟙 X ⊗ (𝟙 Y ⊗ biproduct.ι f j)) ≫ g = (𝟙 X ⊗ (𝟙 Y ⊗ biproduct.ι f j)) ≫ h) :
    g = h := by
  apply (cancel_epi (α_ _ _ _).hom).mp
  -- ⊢ (α_ X Y (⨁ f)).hom ≫ g = (α_ X Y (⨁ f)).hom ≫ h
  ext
  -- ⊢ (𝟙 (X ⊗ Y) ⊗ biproduct.ι f j✝) ≫ (α_ X Y (⨁ f)).hom ≫ g = (𝟙 (X ⊗ Y) ⊗ bipro …
  simp_rw [← tensor_id, associator_naturality_assoc, w]
  -- 🎉 no goals

@[ext]
theorem leftDistributor_ext₂_right {J : Type} [Fintype J]
    {X Y Z : C} {f : J → C} {g h : X ⟶ Y ⊗ (Z ⊗ ⨁ f)}
    (w : ∀ j, g ≫ (𝟙 Y ⊗ (𝟙 Z ⊗ biproduct.π f j)) = h ≫ (𝟙 Y ⊗ (𝟙 Z ⊗ biproduct.π f j))) :
    g = h := by
  apply (cancel_mono (α_ _ _ _).inv).mp
  -- ⊢ g ≫ (α_ Y Z (⨁ f)).inv = h ≫ (α_ Y Z (⨁ f)).inv
  ext
  -- ⊢ (g ≫ (α_ Y Z (⨁ f)).inv) ≫ (𝟙 (Y ⊗ Z) ⊗ biproduct.π f j✝) = (h ≫ (α_ Y Z (⨁  …
  simp_rw [← tensor_id, Category.assoc, ← associator_inv_naturality, ← Category.assoc, w]
  -- 🎉 no goals

@[ext]
theorem rightDistributor_ext_left {J : Type} [Fintype J]
    {f : J → C} {X Y : C} {g h : (⨁ f) ⊗ X ⟶ Y}
    (w : ∀ j, (biproduct.ι f j ⊗ 𝟙 X) ≫ g = (biproduct.ι f j ⊗ 𝟙 X) ≫ h) : g = h := by
  apply (cancel_epi (rightDistributor f X).inv).mp
  -- ⊢ (rightDistributor f X).inv ≫ g = (rightDistributor f X).inv ≫ h
  ext
  -- ⊢ biproduct.ι (fun j => f j ⊗ X) j✝ ≫ (rightDistributor f X).inv ≫ g = biprodu …
  simp? [rightDistributor_inv, Preadditive.comp_sum_assoc, biproduct.ι_π_assoc, dite_comp] says
    simp only [rightDistributor_inv, Preadditive.comp_sum_assoc, ne_eq, biproduct.ι_π_assoc,
      dite_comp, zero_comp, Finset.sum_dite_eq, Finset.mem_univ, eqToHom_refl, Category.id_comp,
      ite_true]
  apply w
  -- 🎉 no goals

@[ext]
theorem rightDistributor_ext_right {J : Type} [Fintype J]
    {f : J → C} {X Y : C} {g h : X ⟶ (⨁ f) ⊗ Y}
    (w : ∀ j, g ≫ (biproduct.π f j ⊗ 𝟙 Y) = h ≫ (biproduct.π f j ⊗ 𝟙 Y)) : g = h := by
  apply (cancel_mono (rightDistributor f Y).hom).mp
  -- ⊢ g ≫ (rightDistributor f Y).hom = h ≫ (rightDistributor f Y).hom
  ext
  -- ⊢ (g ≫ (rightDistributor f Y).hom) ≫ biproduct.π (fun j => f j ⊗ Y) j✝ = (h ≫  …
  simp? [rightDistributor_hom, Preadditive.sum_comp, Preadditive.comp_sum_assoc, biproduct.ι_π,
    comp_dite] says
    simp only [rightDistributor_hom, Category.assoc, Preadditive.sum_comp, ne_eq, biproduct.ι_π,
      comp_dite, comp_zero, Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id,
      ite_true]
  apply w
  -- 🎉 no goals

@[ext]
theorem rightDistributor_ext₂_left {J : Type} [Fintype J]
    {f : J → C} {X Y Z : C} {g h : ((⨁ f) ⊗ X) ⊗ Y ⟶ Z}
    (w : ∀ j, ((biproduct.ι f j ⊗ 𝟙 X) ⊗ 𝟙 Y) ≫ g = ((biproduct.ι f j ⊗ 𝟙 X) ⊗ 𝟙 Y) ≫ h) :
    g = h := by
  apply (cancel_epi (α_ _ _ _).inv).mp
  -- ⊢ (α_ (⨁ f) X Y).inv ≫ g = (α_ (⨁ f) X Y).inv ≫ h
  ext
  -- ⊢ (biproduct.ι f j✝ ⊗ 𝟙 (X ⊗ Y)) ≫ (α_ (⨁ f) X Y).inv ≫ g = (biproduct.ι f j✝  …
  simp_rw [← tensor_id, associator_inv_naturality_assoc, w]
  -- 🎉 no goals

@[ext]
theorem rightDistributor_ext₂_right {J : Type} [Fintype J]
    {f : J → C} {X Y Z : C} {g h : X ⟶ ((⨁ f) ⊗ Y) ⊗ Z}
    (w : ∀ j, g ≫ ((biproduct.π f j ⊗ 𝟙 Y) ⊗ 𝟙 Z) = h ≫ ((biproduct.π f j ⊗ 𝟙 Y) ⊗ 𝟙 Z)) :
    g = h := by
  apply (cancel_mono (α_ _ _ _).hom).mp
  -- ⊢ g ≫ (α_ (⨁ f) Y Z).hom = h ≫ (α_ (⨁ f) Y Z).hom
  ext
  -- ⊢ (g ≫ (α_ (⨁ f) Y Z).hom) ≫ (biproduct.π f j✝ ⊗ 𝟙 (Y ⊗ Z)) = (h ≫ (α_ (⨁ f) Y …
  simp_rw [← tensor_id, Category.assoc, ← associator_naturality, ← Category.assoc, w]
  -- 🎉 no goals

end CategoryTheory
