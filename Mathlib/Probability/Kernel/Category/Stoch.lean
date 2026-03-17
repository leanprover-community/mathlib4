/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Kernel.Category.SFinKer
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Separation.Lemmas
public import Mathlib.CategoryTheory.MarkovCategory.Basic

/-!
# Stoch

The category of measurable spaces with Markov kernels is a Markov category.

## Main declarations

* `StochHom`: the morphism property selecting Markov kernels in `SFinKer`.
* `Stoch`: the wide subcategory of `SFinKer` with Markov-kernel morphisms.
* `MonoidalCategory Stoch`: `Stoch` is a monoidal category.
* `MarkovCategory Stoch`: `Stoch` is a Markov category.

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

instance {X Y : SFinKer} {κ : X ⟶ Y} {hκ : StochHom κ} : IsMarkovKernel κ.1 := hκ

instance : StochHom.IsMultiplicative where
  id_mem X := by
    kernel_cat
    infer_instance
  comp_mem κ η hκ hη := by
    kernel_cat
    infer_instance

/-- `Stoch` is the wide subcategory of `SFinKer` with Markov-kernel morphisms. -/
abbrev Stoch := WideSubcategory StochHom

noncomputable section

macro "stoch_ext" : tactic =>
  `(tactic| (rw [Subtype.ext_iff]; try simp only [WideSubcategory.comp_def]))

instance : MonoidalCategory Stoch.{u} where
  tensorObj X Y := ⟨X.obj ⊗ Y.obj⟩
  whiskerLeft X Y Z κ := by
    refine ⟨X.obj ◁ κ.1, ?_⟩
    kernel_cat
    have : IsMarkovKernel κ.1.1 := κ.2
    simp only [Set.mem_setOf_eq]
    infer_instance
  whiskerRight κ Y := by
    refine ⟨κ.1 ▷ Y.obj, ?_⟩
    kernel_cat
    have : IsMarkovKernel κ.1.1 := κ.2
    simp only [Set.mem_setOf_eq]
    infer_instance
  tensorUnit := ⟨SFinKer.of PUnit⟩
  associator X Y Z := by
    refine ⟨⟨(α_ X.obj Y.obj Z.obj).hom, ?_⟩, ⟨(α_ X.obj Y.obj Z.obj).inv, ?_⟩, ?_, ?_⟩
    · kernel_cat
      exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
    · kernel_cat
      exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
    all_goals
    stoch_ext
    simp
  leftUnitor X := by
    refine ⟨⟨(λ_ X.obj).hom, ?_⟩, ⟨(λ_ X.obj).inv, ?_⟩, ?_, ?_⟩
    · kernel_cat
      exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
    · kernel_cat
      exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
    all_goals
    stoch_ext
    simp
  rightUnitor X := by
    refine ⟨⟨(ρ_ X.obj).hom, ?_⟩, ⟨(ρ_ X.obj).inv, ?_⟩, ?_, ?_⟩
    · kernel_cat
      exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
    · kernel_cat
      exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
    all_goals
    stoch_ext
    simp
  id_tensorHom_id X Y := by
    kernel_cat
    simp
  tensorHom_comp_tensorHom κ₁ κ₂ η₁ η₂ := by
    stoch_ext
    simp only [← MonoidalCategory.tensorHom_def]
    exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
  associator_naturality κ₁ κ₂ η := by
    stoch_ext
    exact MonoidalCategory.associator_naturality _ _ _
  pentagon W X Y Z := by
    stoch_ext
    exact MonoidalCategory.pentagon _ _ _ _
  leftUnitor_naturality κ := by
    stoch_ext
    exact MonoidalCategory.leftUnitor_naturality _
  rightUnitor_naturality κ := by
    stoch_ext
    exact MonoidalCategory.rightUnitor_naturality _
  triangle X Y := by
    stoch_ext
    exact MonoidalCategory.triangle _ _

open scoped ComonObj in
instance {X : Stoch} : ComonObj X where
  counit := by
    refine ⟨ε[X.obj], ?_⟩
    exact Kernel.instIsMarkovKernelPUnitDiscard
  comul := by
    refine ⟨Δ[X.obj], ?_⟩
    exact Kernel.instIsMarkovKernelProdCopy
  counit_comul := by
    stoch_ext
    exact ComonObj.counit_comul _
  comul_counit := by
    stoch_ext
    exact ComonObj.comul_counit _
  comul_assoc := by
    stoch_ext
    exact ComonObj.comul_assoc _

instance : BraidedCategory Stoch.{u} where
  braiding X Y := by
    refine ⟨⟨(β_ X.obj Y.obj).hom, ?_⟩, ⟨(β_ X.obj Y.obj).inv, ?_⟩, ?_, ?_⟩
    · exact Kernel.instIsMarkovKernelProdSwap
    · exact Kernel.instIsMarkovKernelProdSwap
    all_goals
    stoch_ext
    simp
  braiding_naturality_right X Y Z κ := by
    stoch_ext
    exact BraidedCategory.braiding_naturality_right _ _
  braiding_naturality_left κ X := by
    stoch_ext
    exact BraidedCategory.braiding_naturality_left _ _
  hexagon_forward X Y Z := by
    stoch_ext
    exact BraidedCategory.hexagon_forward _ _ _
  hexagon_reverse X Y Z := by
    stoch_ext
    exact BraidedCategory.hexagon_reverse _ _ _

instance : SymmetricCategory Stoch.{u} where
  symmetry X Y := by
    stoch_ext
    exact SymmetricCategory.symmetry _ _

instance (X : Stoch) : IsCommComonObj X where
  comul_comm := by
    stoch_ext
    exact IsCommComonObj.comul_comm _

instance : MarkovCategory Stoch.{u} where
  discard_natural κ := by
    stoch_ext
    kernel_cat
    have : IsMarkovKernel κ.1.1 := κ.2
    exact κ.1.1.comp_discard
  copy_tensor X Y := by
    stoch_ext
    dsimp [MonoidalCategory.tensorμ, ComonObj.comul, BraidedCategory.braiding]
    kernel_cat
    repeat rw [Kernel.id_map (by fun_prop)]
    simp only [Kernel.copy, Kernel.id, Kernel.swap]
    repeat rw [Kernel.deterministic_parallelComp_deterministic]
    repeat rw [Kernel.deterministic_comp_deterministic]
    congr 1
  discard_tensor X Y := by
    stoch_ext
    kernel_cat
    simp only [ComonObj.counit, Kernel.comp_id_parallelComp]
    rw [Kernel.id_map (by fun_prop), Kernel.deterministic_comp_eq_map]
    ext x s hs
    rw [Kernel.map_apply _ (by fun_prop), Kernel.parallelComp_apply]
    simp [Kernel.discard_apply]
  copy_unit := by
    stoch_ext
    dsimp [ComonObj.comul]
    kernel_cat
    ext x s hs
    rw [Kernel.id_map (by fun_prop)]
    simp [Kernel.copy_apply, Kernel.deterministic_apply]
