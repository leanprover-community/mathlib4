/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
public import Mathlib.Probability.Kernel.Composition.KernelLemmas

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

namespace SFinKer

/-- The morphisms in `SFinKer` from `X` to `Y` are the s-finite kernels from `X` to `Y`. -/
@[ext]
structure Hom (X Y : SFinKer.{u}) where
  /-- The underlying morphism. -/
  hom : Kernel X Y
  /-- The property that the morphism satisfies. -/
  property : IsSFiniteKernel hom

instance {X Y : SFinKer} {κ : Hom X Y} : IsSFiniteKernel κ.hom := κ.property

noncomputable section

@[simps (attr := scoped simp) -isSimp]
instance : LargeCategory SFinKer where
  Hom X Y := Hom X Y
  id X := ⟨Kernel.id, inferInstance⟩
  comp κ η := ⟨η.1 ∘ₖ κ.1, inferInstance⟩
  assoc κ η ξ := by simp [Kernel.comp_assoc]

@[ext]
lemma hom_ext {X Y : SFinKer.{u}} {κ η : X ⟶ Y} (h : κ.hom = η.hom) :
    κ = η := SFinKer.Hom.ext h

open MeasurableEquiv in
@[simps (attr := scoped simp) -isSimp]
instance : MonoidalCategory SFinKer.{u} where
  tensorObj X Y := SFinKer.of (X × Y)
  whiskerLeft X Y₁ Y₂ κ := ⟨Kernel.id ∥ₖ κ.1, inferInstance⟩
  whiskerRight κ Y := ⟨κ.1 ∥ₖ Kernel.id, inferInstance⟩
  tensorUnit := SFinKer.of PUnit
  associator X Y Z := by
    refine ⟨⟨Kernel.deterministic prodAssoc (by fun_prop), inferInstance⟩,
      ⟨Kernel.deterministic prodAssoc.symm (by fun_prop), inferInstance⟩, ?_, ?_⟩
    · ext : 1; dsimp
      rw [Kernel.deterministic_comp_deterministic, Kernel.id]
      congr
    · ext : 1; dsimp
      rw [Kernel.deterministic_comp_deterministic, Kernel.id]
      congr
  leftUnitor X := by
    let f₁ := fun (x : X) ↦ (PUnit.unit, x)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.snd : PUnit × X → X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.snd, inferInstance⟩,
      ⟨Kernel.id.map f₁, inferInstance⟩, ?_, ?_⟩
    · ext : 1; dsimp
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · ext : 1; dsimp
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
  rightUnitor X := by
    let f₁ := fun (x : X) ↦ (x, PUnit.unit)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.fst : X × PUnit → X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.fst, by infer_instance⟩,
      ⟨Kernel.id.map f₁, by infer_instance⟩, ?_, ?_⟩
    · ext : 1; dsimp
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · ext : 1; dsimp
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
  leftUnitor_naturality κ := by
    ext : 1; dsimp
    rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop)]
    simp only [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext _ _ hs
    have := κ.2
    rw [Kernel.map_apply' _ (by fun_prop) _ hs, Kernel.comap_apply' _ (by fun_prop),
      Kernel.parallelComp_apply' <| measurable_snd hs]
    simp only [Kernel.id_apply, lintegral_dirac]
    congr
  rightUnitor_naturality κ := by
    ext : 1; dsimp
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
    ext : 1; dsimp
    simp only [Kernel.id_parallelComp_comp_parallelComp_id]
    exact Kernel.parallelComp_comp_parallelComp
  associator_naturality κ₁ κ₂ η := by
    ext : 1; dsimp
    simp only [Kernel.id_parallelComp_comp_parallelComp_id]
    rw [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
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
    ext : 1; dsimp
    simp only [Kernel.id]
    repeat rw [Kernel.deterministic_parallelComp_deterministic (by fun_prop) (by fun_prop)]
    simp [Kernel.deterministic_comp_deterministic]
    congr 1
  triangle X Y := by
    ext : 1; dsimp
    simp only [Kernel.id]
    repeat rw [Kernel.deterministic_map (by fun_prop) (by fun_prop)]
    repeat rw [Kernel.deterministic_parallelComp_deterministic (by fun_prop) (by fun_prop)]
    simp [Kernel.deterministic_comp_deterministic]
    congr 1

@[simps (attr := scoped simp) -isSimp]
instance : SymmetricCategory SFinKer.{u} where
  braiding X Y := by
    refine ⟨⟨Kernel.swap _ _, by rw [Kernel.swap]; infer_instance⟩,
      ⟨Kernel.swap _ _, by rw [Kernel.swap]; infer_instance⟩, ?_, ?_⟩
    · ext : 1; simp
    · ext : 1; simp
  braiding_naturality_right X Y Z κ := by
    ext : 1; dsimp
    exact Kernel.swap_parallelComp
  braiding_naturality_left κ X := by
    ext : 1; dsimp
    exact Kernel.swap_parallelComp
  hexagon_forward X Y Z := by
    ext : 1; dsimp
    simp only [Kernel.id, Kernel.swap]
    repeat rw [Kernel.deterministic_parallelComp_deterministic]
    repeat rw [Kernel.deterministic_comp_deterministic]
    congr 1
  hexagon_reverse X Y Z := by
    ext : 1; dsimp
    simp only [Kernel.id, Kernel.swap]
    repeat rw [Kernel.deterministic_parallelComp_deterministic]
    repeat rw [Kernel.deterministic_comp_deterministic]
    congr 1
  symmetry X Y := by
    ext : 1; simp

@[simps (attr := scoped simp) -isSimp]
instance {X : SFinKer} : ComonObj X where
  counit := ⟨Kernel.discard X, by rw [Kernel.discard]; infer_instance⟩
  comul := ⟨Kernel.copy X, by rw [Kernel.copy]; infer_instance⟩
  counit_comul := by
    ext : 1; dsimp
    simp only [Kernel.discard, Kernel.copy, Kernel.id]
    rw [Kernel.deterministic_parallelComp_deterministic,
      Kernel.deterministic_comp_deterministic, Kernel.deterministic_map measurable_id (by fun_prop)]
    congr 1
  comul_counit := by
    ext : 1; dsimp
    simp only [Kernel.discard, Kernel.copy, Kernel.id]
    rw [Kernel.deterministic_parallelComp_deterministic,
      Kernel.deterministic_comp_deterministic, Kernel.deterministic_map measurable_id (by fun_prop)]
    congr 1
  comul_assoc := by
    ext : 1; dsimp
    simp [Kernel.copy, Kernel.id, Kernel.deterministic_comp_deterministic,
      Kernel.deterministic_parallelComp_deterministic]
    congr 1

instance : CopyDiscardCategory SFinKer.{u} where
  isCommComonObj X := ⟨by ext : 1; dsimp; exact Kernel.swap_copy⟩
  copy_tensor X Y := by
    ext : 1; dsimp [MonoidalCategory.tensorμ]
    simp only [Kernel.copy, Kernel.id, Kernel.swap]
    repeat rw [Kernel.deterministic_parallelComp_deterministic]
    repeat rw [Kernel.deterministic_comp_deterministic]
    congr 1
  discard_tensor X Y := by
    ext : 1; dsimp
    simp only [Kernel.id_parallelComp_comp_parallelComp_id]
    rw [Kernel.id_map (by fun_prop), Kernel.deterministic_comp_eq_map]
    ext x s hs
    rw [Kernel.map_apply _ (by fun_prop), Kernel.parallelComp_apply]
    simp [Kernel.discard_apply]
  copy_unit := by
    ext : 1; dsimp
    ext x s hs
    rw [Kernel.id_map (by fun_prop)]
    simp [Kernel.copy_apply, Kernel.deterministic_apply]

end

end SFinKer
