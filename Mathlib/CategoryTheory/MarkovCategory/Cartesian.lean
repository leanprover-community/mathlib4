/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.MarkovCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Cartesian Categories as Markov Categories

Every cartesian monoidal category is a Markov category where:
- Copy is the diagonal map
- Discard is the unique map to terminal

## Main results

* Cartesian categories satisfy CopyDiscardCategory
* Cartesian categories satisfy MarkovCategory
* All morphisms are deterministic in cartesian categories

## Tags

cartesian, Markov category, deterministic
-/

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory ComonObj CommComonObj

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

namespace CartesianMarkov

/-- The diagonal morphism as copy operation. -/
def diag (X : C) : X ⟶ X ⊗ X := lift (𝟙 X) (𝟙 X)

/-- The swap morphism for products. -/
def swap (X Y : C) : X ⊗ Y ⟶ Y ⊗ X := lift (snd X Y) (fst X Y)

end CartesianMarkov

open CartesianMarkov

/-- The braiding for cartesian categories. -/
instance : BraidedCategory C where
  braiding X Y := ⟨swap X Y, swap Y X, by ext <;> simp [swap], by ext <;> simp [swap]⟩
  braiding_naturality_left := by intros; ext <;> simp [swap]
  braiding_naturality_right := by intros; ext <;> simp [swap]
  hexagon_forward := by intros; ext <;> simp [swap]
  hexagon_reverse := by intros; ext <;> simp [swap]

/-- Cartesian categories are symmetric. -/
instance : SymmetricCategory C where
  symmetry X Y := by ext <;> simp

namespace CartesianMarkov

/-- Cartesian categories have comonoid structure on every object. -/
instance instComonObj (X : C) : ComonObj X where
  comul := diag X
  counit := toUnit X
  counit_comul := by ext; simp [diag]
  comul_counit := by ext; simp [diag]
  comul_assoc := by ext <;> simp [diag]

/-- The comonoid structure in cartesian categories is commutative. -/
instance instCommComonObj (X : C) : CommComonObj X where
  isComm := by ext <;> simp [ComonObj.comul, diag]

/-- Tensor coherence for copy in cartesian categories. -/
lemma diag_tensor (X Y : C) :
    Δ[X ⊗ Y] = (Δ[X] ⊗ₘ Δ[Y]) ≫ tensorμ X X Y Y := by
  ext <;> simp

/-- Tensor coherence for discard in cartesian categories. -/
lemma toUnit_tensor (X Y : C) : ε[X ⊗ Y] = (ε[X] ⊗ₘ ε[Y]) ≫ (λ_ (𝟙_ C)).hom := by ext

/-- Copy on unit is the left unitor inverse. -/
lemma diag_unit : Δ[𝟙_ C] = (λ_ (𝟙_ C)).inv := by ext

/-- Discard on unit is the identity. -/
lemma toUnit_unit : ε[𝟙_ C] = 𝟙 (𝟙_ C) := by ext

end CartesianMarkov

open scoped ComonObj

/-- Cartesian categories have copy-discard structure. -/
instance : CopyDiscardCategory C where
  commComonObj := inferInstance  -- This should find instCommComonObj X
  copy_tensor := CartesianMarkov.diag_tensor
  discard_tensor := CartesianMarkov.toUnit_tensor
  copy_unit := CartesianMarkov.diag_unit
  discard_unit := CartesianMarkov.toUnit_unit

/-- Cartesian categories are Markov. -/
instance : MarkovCategory C where
  discard_natural {X Y} (f : X ⟶ Y) := by simp [ComonObj.counit]

namespace CartesianMarkov

/-- In cartesian categories, all morphisms preserve copy. -/
lemma deterministic {X Y : C} (f : X ⟶ Y) : f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ₘ f) := by
  ext <;> simp [ComonObj.comul, diag]

end CartesianMarkov

end CategoryTheory
