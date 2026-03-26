/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.CategoryTheory.MarkovCategory.Basic
public import Mathlib.CategoryTheory.CopyDiscardCategory.Widesubcategory
public import Mathlib.Probability.Kernel.Category.SFinKer

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

instance : StochHom.IsStableUnderBraiding where
  whiskerLeft X Y Z κ hκ := by
    dsimp [MonoidalCategory.whiskerLeft, StochHom]
    infer_instance
  whiskerRight κ hκ Y := by
    dsimp [MonoidalCategory.whiskerRight, StochHom]
    infer_instance
  id_mem X := by
    simp only [SFinKer.id_def]
    infer_instance
  comp_mem κ η hκ hη := by
    dsimp [CategoryStruct.comp]
    infer_instance
  associator_hom_mem X Y Z := by
    exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  associator_inv_mem X Y Z := by
    exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  leftUnitor_hom_mem X := by
    exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  leftUnitor_inv_mem X := by
    exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  rightUnitor_hom_mem X := by
    exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  rightUnitor_inv_mem X := by
    exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
  braiding_hom_mem X Y := Kernel.instIsMarkovKernelProdSwap
  braiding_inv_mem X Y := Kernel.instIsMarkovKernelProdSwap

instance {X} : StochHom.IsStableUnderComonoid X where
  counit_mem := Kernel.instIsMarkovKernelPUnitDiscard
  comul_mem := Kernel.instIsMarkovKernelProdCopy

/-- `Stoch` is the wide subcategory of `SFinKer` with Markov-kernel morphisms. -/
abbrev Stoch := WideSubcategory StochHom

noncomputable
instance : MarkovCategory Stoch.{u} where
  discard_natural κ := by
    ext : 2
    simp only [WideSubcategory.tensorUnit_obj, tensorUnit_carrier, WideSubcategory.comp_def,
      SFinKer.comp_def]
    have : IsMarkovKernel κ.1.1 := κ.2
    exact κ.1.1.comp_discard
