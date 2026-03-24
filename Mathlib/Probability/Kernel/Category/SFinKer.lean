/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
public import Mathlib.Probability.Kernel.Composition.KernelLemmas
public import Mathlib.Probability.Kernel.Category.Tactics

/-!
# SFinKer

The category of measurable spaces with s-finite kernels is a copy-discard category.

## Main declarations

* `LargeCategory SFinKer`: the categorical structure on `SFinKer`.
* `MonoidalCategory SFinKer`: `SFinKer` is a monoidal category using the Cartesian product.
* `SymmetricCategory SFinKer`: `SFinKer` is a symmetric monoidal category.
* `CopyDiscardCategory SFinKer`: `SFinKer` is a copy-discard category.

## References
* [A synthetic approach to
Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]
-/

@[expose] public section

open CategoryTheory ProbabilityTheory MeasureTheory

universe u

/-- The category of measurable spaces and s-finite kernels. -/
structure SFinKer : Type (u + 1) where
  of ::
  /-- The underlying measurable space. -/
  carrier : Type u
  [str : MeasurableSpace carrier]

attribute [instance] SFinKer.str

instance : CoeSort SFinKer Type* :=
  ⟨SFinKer.carrier⟩

noncomputable section

instance : LargeCategory SFinKer where
  Hom X Y := { k : Kernel X Y // IsSFiniteKernel k }
  id X := ⟨Kernel.id, by kernel_instance⟩
  comp κ η := ⟨η.1 ∘ₖ κ.1, by kernel_instance⟩
  assoc κ η ξ := by simp [Kernel.comp_assoc]

instance : MonoidalCategory SFinKer.{u} where
  tensorObj X Y := SFinKer.of (X × Y)
  whiskerLeft X Y₁ Y₂ κ := ⟨Kernel.id ∥ₖ κ.1, by kernel_instance⟩
  whiskerRight κ Y := ⟨κ.1 ∥ₖ Kernel.id, by kernel_instance⟩
  tensorUnit := SFinKer.of PUnit
  associator X Y Z := by
    let f₁ := fun (x : (X × Y) × Z) ↦ (x.1.1, x.1.2, x.2)
    let f₂ := fun (x : X × Y × Z) ↦ ((x.1, x.2.1), x.2.2)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable f₂ := by fun_prop
    refine ⟨⟨Kernel.id.map f₁, by kernel_instance⟩,
      ⟨Kernel.id.map f₂, by kernel_instance⟩, ?_, ?_⟩
    · kernel_cat
      rw [Kernel.id_map hf₁, Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂,
        Kernel.deterministic_map hf₁ hf₂]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁, f₂]
    · kernel_cat
      rw [Kernel.id_map hf₂, Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁,
        Kernel.deterministic_map hf₂ hf₁]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁, f₂]
  leftUnitor X := by
    let f₁ := fun (x : X) ↦ (PUnit.unit, x)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.snd : PUnit × X → X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.snd, by kernel_instance⟩,
      ⟨Kernel.id.map f₁, by kernel_instance⟩, ?_, ?_⟩
    · kernel_cat
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · kernel_cat
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
  rightUnitor X := by
    let f₁ := fun (x : X) ↦ (x, PUnit.unit)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.fst : X × PUnit → X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.fst, by kernel_instance⟩,
      ⟨Kernel.id.map f₁, by kernel_instance⟩, ?_, ?_⟩
    · kernel_cat
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · kernel_cat
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
  whiskerLeft_id X Y := by
    kernel_cat
    simp
  id_whiskerRight X Y := by
    kernel_cat
    simp
  id_tensorHom_id X₁ X₂ := by
    kernel_cat
    simp
  leftUnitor_naturality κ := by
    kernel_cat
    rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop)]
    simp only [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext _ _ hs
    have := κ.2
    rw [Kernel.map_apply' _ (by fun_prop) _ hs, Kernel.comap_apply' _ (by fun_prop),
      Kernel.parallelComp_apply' <| measurable_snd hs]
    simp only [Kernel.id_apply, lintegral_dirac]
    congr
  rightUnitor_naturality κ := by
    kernel_cat
    rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop)]
    simp only [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext _ _ hs
    have := κ.2
    rw [Kernel.map_apply' _ (by fun_prop) _ hs, Kernel.comap_apply' _ (by fun_prop),
      Kernel.parallelComp_apply' <| measurable_fst hs]
    simp only [Kernel.id_apply, MeasurableSpace.measurableSet_top, Measure.dirac_apply']
    rw [← lintegral_indicator_one hs]
    congr
  tensorHom_comp_tensorHom κ₁ κ₂ η₁ η₂ := by
    kernel_cat
    have := η₂.2
    have := η₁.2
    have := κ₁.2
    have := κ₂.2
    simp only [Kernel.comp_id_parallelComp]
    exact Kernel.parallelComp_comp_parallelComp
  associator_naturality κ₁ κ₂ η := by
    kernel_cat
    have := κ₁.2
    have := κ₂.2
    have := η.2
    simp only [Kernel.comp_id_parallelComp]
    rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop),
      Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext _ _ hs
    rw [Kernel.map_apply' _ (by fun_prop) _ hs, Kernel.comap_apply' _ (by fun_prop)]
    repeat rw [Kernel.parallelComp_apply]
    rw [Measure.prod_apply hs, Measure.prod_apply (by measurability), lintegral_prod]
    · congr with a
      rw [Measure.prod_apply (by measurability)]
      congr
    · refine Measurable.aemeasurable ?_
      exact measurable_measure_prodMk_left (by measurability)
  pentagon W X Y Z := by
    kernel_cat
    rw [Kernel.parallelComp_id_id_map (by fun_prop), Kernel.parallelComp_id_map_id (by fun_prop),
      Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop),
      Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop)]
    simp [Kernel.deterministic_comp_deterministic]
    congr 1
  triangle X Y := by
    kernel_cat
    rw [Kernel.parallelComp_id_id_map (by fun_prop), Kernel.parallelComp_id_map_id (by fun_prop),
      Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop),
      Kernel.deterministic_comp_deterministic]
    congr

instance : SymmetricCategory SFinKer.{u} where
  braiding X Y := by
    refine ⟨⟨Kernel.swap _ _, by kernel_instance⟩, ⟨Kernel.swap _ _, by kernel_instance⟩,
      ?_, ?_⟩
    · kernel_cat
      exact Kernel.swap_swap
    · kernel_cat
      exact Kernel.swap_swap
  braiding_naturality_right X Y Z κ := by
    kernel_cat
    exact Kernel.swap_parallelComp
  braiding_naturality_left κ X := by
    kernel_cat
    exact Kernel.swap_parallelComp
  hexagon_forward X Y Z := by
    kernel_cat
    repeat rw [Kernel.id_map]
    · simp only [Kernel.id, Kernel.swap]
      repeat rw [Kernel.deterministic_parallelComp_deterministic]
      repeat rw [Kernel.deterministic_comp_deterministic]
      congr 1
    all_goals fun_prop
  hexagon_reverse X Y Z := by
    kernel_cat
    repeat rw [Kernel.id_map]
    · simp only [Kernel.id, Kernel.swap]
      repeat rw [Kernel.deterministic_parallelComp_deterministic]
      repeat rw [Kernel.deterministic_comp_deterministic]
      congr 1
    all_goals fun_prop
  symmetry X Y := by
    kernel_cat
    exact Kernel.swap_swap

instance {X : SFinKer} : ComonObj X where
  counit := ⟨Kernel.discard X, by kernel_instance⟩
  comul := ⟨Kernel.copy X, by kernel_instance⟩
  counit_comul := by
    kernel_cat
    simp only [Kernel.discard, Kernel.copy, Kernel.id]
    rw [Kernel.deterministic_parallelComp_deterministic,
      Kernel.deterministic_comp_deterministic, Kernel.deterministic_map measurable_id (by fun_prop)]
    congr 1
  comul_counit := by
    kernel_cat
    simp only [Kernel.discard, Kernel.copy, Kernel.id]
    rw [Kernel.deterministic_parallelComp_deterministic,
      Kernel.deterministic_comp_deterministic, Kernel.deterministic_map measurable_id (by fun_prop)]
    congr 1
  comul_assoc := by
    kernel_cat
    rw [Kernel.id_map (by fun_prop)]
    simp [Kernel.copy, Kernel.id, Kernel.deterministic_comp_deterministic,
      Kernel.deterministic_parallelComp_deterministic]
    congr 1

instance : CopyDiscardCategory SFinKer.{u} where
  isCommComonObj X := ⟨by kernel_cat; exact Kernel.swap_copy⟩
  copy_tensor X Y := by
    dsimp only [MonoidalCategory.tensorμ, ComonObj.comul, BraidedCategory.braiding]
    kernel_cat
    repeat rw [Kernel.id_map (by fun_prop)]
    simp only [Kernel.copy, Kernel.id, Kernel.swap]
    repeat rw [Kernel.deterministic_parallelComp_deterministic]
    repeat rw [Kernel.deterministic_comp_deterministic]
    congr 1
  discard_tensor X Y := by
    kernel_cat
    simp only [ComonObj.counit, Kernel.comp_id_parallelComp]
    rw [Kernel.id_map (by fun_prop), Kernel.deterministic_comp_eq_map]
    ext x s hs
    rw [Kernel.map_apply _ (by fun_prop), Kernel.parallelComp_apply]
    simp [Kernel.discard_apply]
  copy_unit := by
    dsimp only [ComonObj.comul]
    kernel_cat
    ext x s hs
    rw [Kernel.id_map (by fun_prop)]
    simp [Kernel.copy_apply, Kernel.deterministic_apply]

end
