/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.CategoryTheory.MarkovCategory.Basic
public import Mathlib.CategoryTheory.CopyDiscardCategory.Widesubcategory
public import Mathlib.Probability.Kernel.Category.SFinKer
public import Mathlib.Probability.Kernel.Deterministic

/-!
# Stoch

The category of measurable spaces with Markov kernels is a Markov category.

## Main definition

`Stoch` is defined as the wide subcategory `WideSubcategory StochHom` of `SFinKer`, where
`StochHom` selects Markov kernels, and this construction provides in particular the instance
`MarkovCategory Stoch`.

## Main statements

* `Stoch.is_positive`: `Stoch` is a positive Markov category, in the sense of Definition 11.22 in
  [fritz2020].

* All isomorphisms in `Stoch` are deterministic. This is a consequence of `Stoch.is_positive`.

## References

* [A synthetic approach to
Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]

-/

@[expose] public section

open CategoryTheory MeasureTheory ProbabilityTheory

open scoped MonoidalCategory SFinKer ComonObj

universe u

/-- Morphism property selecting Markov kernels in `SFinKer`. -/
abbrev StochHom : MorphismProperty SFinKer := fun _ _ κ => IsMarkovKernel κ.1

instance : StochHom.IsStableUnderBraiding where
  id_mem X := by dsimp [StochHom]; infer_instance
  comp_mem κ η hκ hη := by dsimp [StochHom]; infer_instance
  whiskerLeft X Y Z κ hκ := by dsimp [StochHom]; infer_instance
  whiskerRight κ hκ Y := by dsimp [StochHom]; infer_instance
  associator_hom_mem X Y Z := Kernel.isMarkovKernel_deterministic <| MeasurableEquiv.measurable _
  associator_inv_mem X Y Z := Kernel.isMarkovKernel_deterministic <| MeasurableEquiv.measurable _
  leftUnitor_hom_mem X := Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  leftUnitor_inv_mem X := Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  rightUnitor_hom_mem X := Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  rightUnitor_inv_mem X := Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  braiding_hom_mem X Y := Kernel.instIsMarkovKernelProdSwap
  braiding_inv_mem X Y := Kernel.instIsMarkovKernelProdSwap

instance {X} : StochHom.IsStableUnderComonoid X where
  counit_mem := by dsimp [StochHom]; infer_instance
  comul_mem := by dsimp [StochHom]; infer_instance

/-- `Stoch` is the wide subcategory of `SFinKer` with Markov-kernel morphisms. -/
abbrev Stoch := WideSubcategory StochHom

instance {X Y : Stoch} (κ : X ⟶ Y) : IsMarkovKernel κ.hom.hom := κ.2

noncomputable
instance : MarkovCategory Stoch.{u} where
  discard_natural κ := by ext : 2; simp

variable {X Y : Stoch}

namespace Stoch

open Kernel

instance {κ : X ⟶ Y} [Deterministic κ] : Deterministic κ.hom where
  hom_comul := WideSubcategory.hom_ext_iff.mp <| Deterministic.copy_natural κ

instance {κ : X ⟶ Y} [Deterministic κ] : IsDeterministic κ.hom.hom where
  comp_natural' := by
    have := Deterministic.copy_natural κ.hom
    rw [SFinKer.Hom.ext_iff] at this
    dsimp at this
    rw [id_parallelComp_comp_parallelComp_id] at this
    exact this.symm

/-- `Stoch` is a positive Markov category. See Definition 11.22 in [fritz2020] -/
lemma is_positive {Z : Stoch} (κ : X ⟶ Y) (η : Y ⟶ Z) [Deterministic (κ ≫ η)] :
    κ ≫ Δ ≫ (η ⊗ₘ 𝟙 Y) = Δ ≫ ((κ ≫ η) ⊗ₘ κ) := by
  ext : 2
  dsimp
  simp only [id_parallelComp_id, id_comp, id_parallelComp_comp_parallelComp_id]
  have : IsDeterministic (κ ≫ η).hom.hom := inferInstance
  exact (parallelComp_id_comp_copy_comp).symm

end Stoch

instance {κ : X ⟶ Y} [Deterministic κ.hom] : Deterministic κ where

instance {e : X ≅ Y} : Deterministic (e.hom ≫ e.inv) where

instance {e : X ≅ Y} : Deterministic (e.inv ≫ e.hom) where

instance {e : X ≅ Y} : Deterministic e.hom where
  hom_comul := by
    have : Deterministic (e.hom ≫ e.inv) := inferInstance
    have := Stoch.is_positive (e.hom) (e.inv)
    simp only [Iso.hom_inv_id] at this
    calc
    _ = e.hom ≫ Δ ≫ (e.inv ⊗ₘ 𝟙 Y) ≫ (e.hom ⊗ₘ 𝟙 Y) := by
      cat_disch
    _ = (e.hom ≫ Δ ≫ (e.inv ⊗ₘ 𝟙 Y)) ≫ (e.hom ⊗ₘ 𝟙 Y) := by
      simp
    _ = (Δ ≫ (𝟙 X ⊗ₘ e.hom)) ≫ (e.hom ⊗ₘ 𝟙 Y) := by
      rw [this]
    _ = Δ ≫ (𝟙 X ⊗ₘ e.hom) ≫ (e.hom ⊗ₘ 𝟙 Y) := by
      simp
    _ = Δ ≫ ((𝟙 X ≫ e.hom) ⊗ₘ (e.hom ≫ 𝟙 Y)) := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
    _ = Δ ≫ (e.hom ⊗ₘ e.hom) := by cat_disch

instance : Deterministic (ε[X]) where
  hom_comul := by
    ext : 1
    simp only [WideSubcategory.comp_def, MorphismProperty.counit_hom]
    cat_disch

instance : Deterministic (Δ[X]) where
