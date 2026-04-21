/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.CategoryTheory.MarkovCategory.Basic
public import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic

/-!
# Positive Categories

Markov categories where deletion is natural for all morphisms.

## Main definitions

* `PositiveCategory`: Markov category where copy is natural given deterministic composition of
  morphisms.

## Main results

* `copy_comp_natural` - Given morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, if their composition is
  deterministic, then process `f`, copy and then process `g` equals copy and process `f` and `g`
  independently.

* All isomorphisms in a positive Markov category are deterministic.

## Implementation notes

The key property `copy_comp_natural : f ≫ Δ ≫ (g ⊗ₘ 𝟙 Y) = Δ ≫ (f ≫ g ⊗ₘ f)`, given
`Deterministic (f ≫ g)`, means that after processing `f`, copying and then processing `g` is the
same as copying and processing `f` and `g` independently. The probabilistic interpretation is that
given a deterministic process that has a stochastic intermediate result, the same distribution over
both results can be obtained by computing the intermediate result independently of the
deterministic process.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
* [Moss and Perrone, *A category-theoretic proof of the ergodic
decomposition theorem*][moss2023]
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory CopyDiscardCategory ComonObj

/-- Markov category where copy is natural given deterministic composition of morphisms. -/
class PositiveCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] extends
    MarkovCategory C where
  /-- Given morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, if their composition is deterministic, then
  process `f`, copy and then process `g` equals copy and process `f` and `g` independently. -/
  copy_comp_natural {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [h : Deterministic (f ≫ g)] :
      f ≫ Δ ≫ (g ⊗ₘ 𝟙 Y) = Δ ≫ (f ≫ g ⊗ₘ f)

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

namespace PositiveCategory

variable [PositiveCategory C]

instance {X Y : C} (f : X ⟶ Y) [IsIso f] : Deterministic f where
  hom_comul := by
    calc
    _ = f ≫ Δ ≫ (inv f ⊗ₘ 𝟙 Y) ≫ (f ⊗ₘ 𝟙 Y) := by
      cat_disch
    _ = (f ≫ Δ ≫ (inv f ⊗ₘ 𝟙 Y)) ≫ (f ⊗ₘ 𝟙 Y) := by
      simp
    _ = (Δ ≫ (𝟙 X ⊗ₘ f)) ≫ (f ⊗ₘ 𝟙 Y) := by
      rw [copy_comp_natural (h := by rw [IsIso.hom_inv_id]; infer_instance)]
      simp
    _ = Δ ≫ (𝟙 X ⊗ₘ f) ≫ (f ⊗ₘ 𝟙 Y) := by
      simp
    _ = Δ ≫ ((𝟙 X ≫ f) ⊗ₘ (f ≫ 𝟙 Y)) := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
    _ = Δ ≫ (f ⊗ₘ f) := by cat_disch

end PositiveCategory

end CategoryTheory
