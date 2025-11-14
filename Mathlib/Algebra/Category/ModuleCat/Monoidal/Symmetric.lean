/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Kim Morrison, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# The symmetric monoidal structure on `Module R`.
-/

universe v w x u

open CategoryTheory MonoidalCategory

namespace SemimoduleCat

variable {R : Type u} [CommSemiring R]

/-- (implementation) the braiding for R-modules -/
def braiding (M N : SemimoduleCat.{u} R) : M ⊗ N ≅ N ⊗ M :=
  LinearEquiv.toModuleIsoₛ (TensorProduct.comm R M N)

namespace MonoidalCategory

@[simp]
theorem braiding_naturality {X₁ X₂ Y₁ Y₂ : SemimoduleCat.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g) ≫ (Y₁.braiding Y₂).hom = (X₁.braiding X₂).hom ≫ (g ⊗ₘ f) := by
  ext : 1
  apply TensorProduct.ext'
  intro x y
  rfl

@[simp]
theorem braiding_naturality_left {X Y : SemimoduleCat R} (f : X ⟶ Y) (Z : SemimoduleCat R) :
    f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
  simp_rw [← id_tensorHom]
  apply braiding_naturality

@[simp]
theorem braiding_naturality_right (X : SemimoduleCat R) {Y Z : SemimoduleCat R} (f : Y ⟶ Z) :
    X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X := by
  simp_rw [← id_tensorHom]
  apply braiding_naturality

@[simp]
theorem hexagon_forward (X Y Z : SemimoduleCat.{u} R) :
    (α_ X Y Z).hom ≫ (braiding X _).hom ≫ (α_ Y Z X).hom =
      (braiding X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (braiding X Z).hom := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

@[simp]
theorem hexagon_reverse (X Y Z : SemimoduleCat.{u} R) :
    (α_ X Y Z).inv ≫ (braiding _ Z).hom ≫ (α_ Z X Y).inv =
      X ◁ (Y.braiding Z).hom ≫ (α_ X Z Y).inv ≫ (X.braiding Z).hom ▷ Y := by
  apply (cancel_epi (α_ X Y Z).hom).1
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

attribute [local ext] TensorProduct.ext

/-- The symmetric monoidal structure on `Module R`. -/
instance symmetricCategory : SymmetricCategory (SemimoduleCat.{u} R) where
  braiding := braiding
  braiding_naturality_left := braiding_naturality_left
  braiding_naturality_right := braiding_naturality_right
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse
  -- Porting note: this proof was automatic in Lean3
  -- now `aesop` is applying `SemimoduleCat.ext` in favour of `TensorProduct.ext`.
  symmetry _ _ := by
    ext : 1
    apply TensorProduct.ext'
    cat_disch

@[simp]
theorem braiding_hom_apply {M N : SemimoduleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).hom : M ⊗ N ⟶ N ⊗ M) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl

@[simp]
theorem braiding_inv_apply {M N : SemimoduleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).inv : N ⊗ M ⟶ M ⊗ N) (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl

theorem tensorμ_eq_tensorTensorTensorComm {A B C D : SemimoduleCat R} :
    tensorμ A B C D = ofHom (TensorProduct.tensorTensorTensorComm R A B C D).toLinearMap :=
  SemimoduleCat.hom_ext <| TensorProduct.ext <| TensorProduct.ext <| LinearMap.ext₂ fun _ _ =>
    TensorProduct.ext <| LinearMap.ext₂ fun _ _ => rfl

@[simp]
theorem tensorμ_apply
    {A B C D : SemimoduleCat R} (x : A) (y : B) (z : C) (w : D) :
    tensorμ A B C D ((x ⊗ₜ y) ⊗ₜ (z ⊗ₜ w)) = (x ⊗ₜ z) ⊗ₜ (y ⊗ₜ w) := rfl

end MonoidalCategory

end SemimoduleCat

namespace ModuleCat.MonoidalCategory

variable {R : Type u} [CommRing R]

instance : BraidedCategory (ModuleCat.{u} R) :=
  .ofFaithful equivalenceSemimoduleCat.functor (fun M N ↦ (TensorProduct.comm R M N).toModuleIso)

instance : equivalenceSemimoduleCat (R := R).functor.Braided where

instance symmetricCategory : SymmetricCategory (ModuleCat.{u} R) :=
  .ofFaithful equivalenceSemimoduleCat.functor

@[simp]
theorem braiding_hom_apply {M N : ModuleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).hom : M ⊗ N ⟶ N ⊗ M) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl

@[simp]
theorem braiding_inv_apply {M N : ModuleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).inv : N ⊗ M ⟶ M ⊗ N) (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl

theorem tensorμ_eq_tensorTensorTensorComm {A B C D : ModuleCat R} :
    tensorμ A B C D = ofHom (TensorProduct.tensorTensorTensorComm R A B C D).toLinearMap :=
  ModuleCat.hom_ext <| TensorProduct.ext <| TensorProduct.ext <| LinearMap.ext₂ fun _ _ =>
    TensorProduct.ext <| LinearMap.ext₂ fun _ _ => rfl

@[simp]
theorem tensorμ_apply
    {A B C D : ModuleCat R} (x : A) (y : B) (z : C) (w : D) :
    tensorμ A B C D ((x ⊗ₜ y) ⊗ₜ (z ⊗ₜ w)) = (x ⊗ₜ z) ⊗ₜ (y ⊗ₜ w) := rfl

end ModuleCat.MonoidalCategory
