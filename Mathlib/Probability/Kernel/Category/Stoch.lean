/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.CategoryTheory.MarkovCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Widesubcategory
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Kernel.Category.SFinKer
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Separation.Lemmas

/-!
# Stoch

The category of measurable spaces with Markov kernels is a Markov category.

## Main declarations

`Stoch` is defined as the wide subcategory `WideSubcategory StochHom` of `SFinKer`, where
`StochHom` selects Markov kernels, and this construction provides in particular the instance
`MarkovCategory Stoch`.

## References
* [A synthetic approach to
Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]

-/

@[expose] public section

open CategoryTheory ProbabilityTheory MeasureTheory

open scoped MonoidalCategory

universe u

/-- Morphism property selecting Markov kernels in `SFinKer`. -/
abbrev StochHom : MorphismProperty SFinKer := fun _ _ κ => IsMarkovKernel κ.1

instance : StochHom.IsComonStable where
  whiskerLeft X Y Z κ hκ := by
    kernel_cat
    infer_instance
  whiskerRight κ hκ Y := by
    kernel_cat
    infer_instance
  id_mem X := by
    kernel_cat
    infer_instance
  comp_mem κ η hκ hη := by
    kernel_cat
    infer_instance
  associator_hom X Y Z := by
    kernel_cat
    exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  associator_inv X Y Z := by
    kernel_cat
    exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  leftUnitor_hom X := by
    kernel_cat
    exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  leftUnitor_inv X := by
    kernel_cat
    exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  rightUnitor_hom X := by
    kernel_cat
    exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  rightUnitor_inv X := by
    kernel_cat
    exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  braiding_hom X Y := Kernel.instIsMarkovKernelProdSwap
  braiding_inv X Y := Kernel.instIsMarkovKernelProdSwap
  counit X := Kernel.instIsMarkovKernelPUnitDiscard
  comul X := Kernel.instIsMarkovKernelProdCopy

/-- `Stoch` is the wide subcategory of `SFinKer` with Markov-kernel morphisms. -/
abbrev Stoch := WideSubcategory StochHom

noncomputable
instance : MarkovCategory Stoch.{u} where
  discard_natural κ := by
    widesubcat_ext
    kernel_cat
    have : IsMarkovKernel κ.1.1 := κ.2
    exact κ.1.1.comp_discard
  copy_tensor X Y := by
    widesubcat_ext
    dsimp [MonoidalCategory.tensorμ, ComonObj.comul, BraidedCategory.braiding]
    kernel_cat
    repeat rw [Kernel.id_map (by fun_prop)]
    simp only [Kernel.copy, Kernel.id, Kernel.swap]
    repeat rw [Kernel.deterministic_parallelComp_deterministic]
    repeat rw [Kernel.deterministic_comp_deterministic]
    congr 1
  discard_tensor X Y := by
    widesubcat_ext
    kernel_cat
    simp only [ComonObj.counit, Kernel.comp_id_parallelComp]
    rw [Kernel.id_map (by fun_prop), Kernel.deterministic_comp_eq_map]
    ext x s hs
    rw [Kernel.map_apply _ (by fun_prop), Kernel.parallelComp_apply]
    simp [Kernel.discard_apply]
  copy_unit := by
    widesubcat_ext
    dsimp [ComonObj.comul]
    kernel_cat
    ext x s hs
    rw [Kernel.id_map (by fun_prop)]
    simp [Kernel.copy_apply, Kernel.deterministic_apply]
