/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.HasLaw

/-!
# Product of bernoulli distributions on a set

This file defines the product of bernoulli distributions on a set as a measure on sets.
For a set `u : Set ι` and `p` between `0` and `1`, this is the measure on `Set ι` such that each
`i ∈ u` belongs to the random set with probability `p`, and each `i ∉ u` doesn't belong to it.

## Notation

`setBer(u, p)` is the product of `p`-Bernoulli distributions on `u`.

## TODO

It is painful to convert from `unitInterval` to `ENNReal`. Should we introduce a coercion or
explicit operation (like `unitInterval.toNNReal`, note the lack of dot notation!)?
-/

public section

open MeasureTheory Measure unitInterval
open scoped ENNReal Finset

namespace ProbabilityTheory
variable {ι Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → Set ι} {s u : Set ι} {i j : ι} {p q : I}
  {P : Measure Ω}

variable (u p) in
/-- The product of bernoulli distributions with parameter `p` on the set `u : Set V` is the measure
on `Set V` such that each element of `u` is taken with probability `p`, and the elements outside of
`u` are never taken. -/
@[expose]
noncomputable def setBernoulli : Measure (Set ι) :=
  .comap (fun s i ↦ i ∈ s) <| infinitePi fun i : ι ↦
    toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False

@[inherit_doc] scoped notation "setBer(" u ", " p ")" => setBernoulli u p

instance : IsProbabilityMeasure setBer(u, p) :=
  MeasurableEquiv.setOf.symm.measurableEmbedding.isProbabilityMeasure_comap <| .of_forall fun P ↦
    ⟨{i | P i}, rfl⟩

variable (u p) in
lemma setBernoulli_eq_map :
    setBer(u, p) = .map (fun p : ι → Prop ↦ {i | p i})
      (infinitePi fun i : ι ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False) :=
  MeasurableEquiv.setOf.comap_symm

lemma setBernoulli_apply (S : Set (Set ι)) :
    setBer(u, p) S = (infinitePi fun i ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False)
      ((fun t i ↦ i ∈ t) '' S) := MeasurableEquiv.setOf.symm.measurableEmbedding.comap_apply ..

lemma setBernoulli_apply' (S : Set (Set ι)) :
    setBer(u, p) S = (infinitePi fun i ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False)
      ((fun p ↦ {i | p i}) ⁻¹' S) := MeasurableEquiv.setOf.symm.comap_apply ..

variable (u) in
@[simp] lemma setBernoulli_zero : setBer(u, 0) = dirac ∅ := by simp [setBernoulli_eq_map]

variable (u) in
@[simp] lemma setBernoulli_one : setBer(u, 1) = dirac u := by simp [setBernoulli_eq_map]

section Countable
variable [Countable ι]

lemma setBernoulli_ae_subset : ∀ᵐ s ∂setBer(u, p), s ⊆ u := by
  classical
  simp only [Filter.Eventually, mem_ae_iff, Set.compl_setOf, Set.not_subset_iff_exists_mem_notMem,
    Set.setOf_exists, Set.setOf_and, measure_iUnion_null_iff]
  rintro i
  by_cases hi : i ∈ u
  · simp [*]
  calc
    setBer(u, p) ({s | i ∈ s} ∩ {s | i ∉ u})
    _ = setBer(u, p) {s | i ∈ s} := by simp [hi]
    _ = infinitePi (fun i ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False)
          (cylinder {i} {fun _ ↦ True}) := by
      rw [setBernoulli_apply']; congr!; ext; simp [funext_iff]
    _ = 0 := by simp [infinitePi_cylinder, hi]

@[simp]
lemma setBernoulli_singleton_of_not_subset {s : Set ι} (p : I) (hs : ¬ s ⊆ u) :
    setBer(u, p) {s} = 0 :=
  Measure.mono_null (by simpa) setBernoulli_ae_subset

/-- `setBer(u, p)` only gives mass to families of sets contained in `u`. -/
lemma setBernoulli_apply_eq_apply_subsets (u : Set ι) (p : I) (S : Set (Set ι)) :
    setBer(u, p) S = setBer(u, p) {s | s ∈ S ∧ s ⊆ u} := by
  apply (measure_eq_measure_of_null_diff (by grind) ?_).symm
  exact Measure.mono_null (by grind) setBernoulli_ae_subset

variable (u p) in
@[simp] lemma setBernoulli_singleton (hsu : s ⊆ u) (hu : u.Finite) :
    setBer(u, p) {s} = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (u \ s).ncard := by
  classical
  lift u to Finset ι using hu
  calc
    setBer(u, p) {s}
    _ = ∏' i, ((if i ∈ u ↔ i ∈ s then (toNNReal p : ℝ≥0∞) else 0) +
          if i ∈ s then 0 else (toNNReal (σ p) : ℝ≥0∞)) := by
      simp [setBernoulli_apply, Set.image_singleton, Set.indicator]
      simp [ENNReal.smul_def]
    _ = ∏ i ∈ u, (if i ∈ s then (toNNReal p : ℝ≥0∞) else (toNNReal (σ p) : ℝ≥0∞)) := by
      rw [tprod_eq_prod, Finset.prod_congr rfl] <;>
        simp +contextual [ite_add_ite, mt (@hsu _), ← ENNReal.coe_add]
    _ = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (↑u \ s).ncard := by
      simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.setOf_and,
        Set.inter_eq_right.2 hsu, ← Set.compl_setOf, Set.diff_eq_compl_inter, Set.inter_comm]

@[simp]
lemma setBernoulli_real_singleton (p : I) (hsu : s ⊆ u) (hu : u.Finite) :
    setBer(u, p).real {s} = p ^ s.ncard * (1 - p : ℝ) ^ (u \ s).ncard := by
  rw [measureReal_def, setBernoulli_singleton u p hsu hu]
  norm_cast

@[simp]
lemma setBernoulli_empty : setBer((∅ : Set ι), p) = Measure.dirac ∅ := by
  ext s hs
  rw [setBernoulli_apply_eq_apply_subsets]
  by_cases h : ∅ ∈ s
  · have : {t | t ∈ s ∧ t ⊆ ∅} = {∅} := by grind
    simp_all
  · have : {t | t ∈ s ∧ t ⊆ ∅} = ∅ := by grind
    rw [this]
    simp_all

end Countable

/-! ### Bernoulli random variables -/

variable (X u p P) in
/-- A random variable `X : Ω → Set ι` is `p`-bernoulli on a set `u : Set ι` if its distribution is
the product over `u` of `p`-bernoulli distributions. -/
abbrev IsSetBernoulli : Prop := HasLaw X setBer(u, p) P

lemma isSetBernoulli_congr (hXY : X =ᵐ[P] Y) : IsSetBernoulli X u p P ↔ IsSetBernoulli Y u p P :=
  hasLaw_congr hXY

variable [Countable ι]

lemma IsSetBernoulli.ae_subset (hX : IsSetBernoulli X u p P) : ∀ᵐ ω ∂P, X ω ⊆ u :=
  (hX.ae_iff <| by fun_prop).2 setBernoulli_ae_subset

end ProbabilityTheory
