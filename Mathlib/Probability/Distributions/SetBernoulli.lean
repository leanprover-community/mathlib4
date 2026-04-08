/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.HasLaw

import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.Probability.Independence.InfinitePi

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
  .comap (fun s i ↦ i ∈ s) <| infinitePi fun i : ι ↦ Ber(i ∈ u, False, p)

@[inherit_doc] scoped notation "setBer(" u ", " p ")" => setBernoulli u p

instance : IsProbabilityMeasure setBer(u, p) :=
  MeasurableEquiv.setOf.symm.measurableEmbedding.isProbabilityMeasure_comap <| .of_forall fun P ↦
    ⟨{i | P i}, rfl⟩

variable (u p) in
lemma setBernoulli_eq_map :
    setBer(u, p) = .map (fun p : ι → Prop ↦ {i | p i})
      (infinitePi fun i : ι ↦ Ber(i ∈ u, False, p)) :=
  MeasurableEquiv.setOf.comap_symm

lemma setBernoulli_apply (S : Set (Set ι)) :
    setBer(u, p) S = (infinitePi fun i ↦ Ber(i ∈ u, False, p)) ((fun t i ↦ i ∈ t) '' S) :=
  MeasurableEquiv.setOf.symm.measurableEmbedding.comap_apply ..

lemma setBernoulli_apply' (S : Set (Set ι)) :
    setBer(u, p) S = (infinitePi fun i ↦ Ber(i ∈ u, False, p)) ((fun p ↦ {i | p i}) ⁻¹' S) :=
  MeasurableEquiv.setOf.symm.comap_apply ..

variable (u) in
@[simp] lemma setBernoulli_zero : setBer(u, 0) = dirac ∅ := by simp [setBernoulli_eq_map]

variable (u) in
@[simp] lemma setBernoulli_one : setBer(u, 1) = dirac u := by simp [setBernoulli_eq_map]

lemma setBernoulli_real_mem_of_mem (p : I) (hi : i ∈ u) :
    setBer(u, p).real {s | i ∈ s} = p := by
  rw [setBernoulli_eq_map]
  have h1 : {s : Set ι | i ∈ s} = (i ∈ ·) ⁻¹' {True} := by grind
  have h2 : (fun x ↦ i ∈ x) ∘ (fun (p : ι → Prop) ↦ {i | p i}) = Function.eval i := by grind
  rw [h1, ← map_measureReal_apply, map_map, h2, infinitePi_map_eval]
  · simp [hi]
  any_goals fun_prop
  simp

lemma setBernoulli_real_mem_of_notMem (p : I) (hi : i ∉ u) :
    setBer(u, p).real {s | i ∈ s} = 0 := by
  rw [setBernoulli_eq_map]
  have h1 : {s : Set ι | i ∈ s} = (i ∈ ·) ⁻¹' {True} := by grind
  have h2 : (fun x ↦ i ∈ x) ∘ (fun (p : ι → Prop) ↦ {i | p i}) = Function.eval i := by ext; simp
  rw [h1, ← map_measureReal_apply, map_map, h2, infinitePi_map_eval, measureReal_def]
  · simp [hi]
  any_goals fun_prop
  simp

lemma HasLaw.hasLaw_indicator_bernoulliMeasure_of_setBernoulli_of_mem (hi : i ∈ u) {S : Ω → Set ι}
    (hS : HasLaw S setBer(u, p) P) :
    HasLaw ({ω | i ∈ S ω}.indicator 1) Ber(1, 0, p) P := by
  have := hS.isProbabilityMeasure
  have : p = ⟨P.real {ω | i ∈ S ω}, by simp⟩ := by
    ext
    simp only
    rw [hS.measure_real_eq (p := (i ∈ ·)) (by measurability), ← setBernoulli_real_mem_of_mem _ hi]
  rw [this]
  exact hasLaw_indicator_one_bernoulliMeasure
    (hS.aemeasurable.nullMeasurableSet_preimage (s := {t | i ∈ t}) (by measurability))

lemma HasLaw.hasLaw_indicator_dirac_of_setBernoulli_of_notMem (hi : i ∉ u) {S : Ω → Set ι}
    (hS : HasLaw S setBer(u, p) P) :
    HasLaw ({ω | i ∈ S ω}.indicator 1) (dirac 0) P := by
  have := hS.isProbabilityMeasure
  have : (0 : I) = ⟨P.real {ω | i ∈ S ω}, by simp⟩ := by
    ext
    simp only [Set.Icc.coe_zero]
    rw [hS.measure_real_eq (p := (i ∈ ·)) (by measurability), setBernoulli_real_mem_of_notMem _ hi]
  rw [← bernoulliMeasure_zero (x := 1), this]
  exact hasLaw_indicator_one_bernoulliMeasure
    (hS.aemeasurable.nullMeasurableSet_preimage (s := {t | i ∈ t}) (by measurability))

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
    _ = infinitePi (fun i ↦ Ber(i ∈ u, False, p)) (cylinder {i} {fun _ ↦ True}) := by
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

lemma map_ncard_setBernoulli_apply (u : Set ι) (p : I) (s : Set ℕ) :
    (setBer(u, p).map Set.ncard) s = setBer(u, p) {t | t.ncard ∈ s ∧ t ⊆ u} := by
  rw [map_apply (by fun_prop) .of_discrete, setBernoulli_apply_eq_apply_subsets]
  simp

variable (u p) in
@[simp] lemma setBernoulli_singleton (hsu : s ⊆ u) (hu : u.Finite) :
    setBer(u, p) {s} = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (u \ s).ncard := by
  classical
  lift u to Finset ι using hu
  calc
    setBer(u, p) {s}
    _ = ∏' i, ((if i ∈ u ↔ i ∈ s then (toNNReal p : ℝ≥0∞) else 0) +
          if i ∈ s then 0 else (toNNReal (σ p) : ℝ≥0∞)) := by
      simp [setBernoulli_apply, Set.image_singleton, Set.indicator, bernoulliMeasure_def]
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

lemma map_ncard_setBernoulli_real_singleton {u : Set ι} (hu : u.Finite) (p : I) (k : ℕ) :
    (setBer(u, p).map Set.ncard).real {k} =
      (u.ncard.choose k) * p ^ k * (1 - p) ^ (u.ncard - k) := by
  classical
  have : {s | s.ncard ∈ ({k} : Set ℕ) ∧ s ⊆ u}.Finite :=
    hu.finite_subsets.subset (by grind)
  rw [measureReal_def, map_ncard_setBernoulli_apply, ← measureReal_def,
    ← Set.biUnion_of_singleton (setOf _)]
  simp_rw [← this.mem_toFinset]
  rw [measureReal_biUnion_finset (by simp) (by simp)]
  have h1 s (hs : s ∈ this.toFinset) :
      setBer(u, p).real {s} = p ^ k * (1 - p) ^ (u.ncard - k) := by
    simp only [Set.mem_singleton_iff, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hs
    rw [setBernoulli_real_singleton _ hs.2 hu, Set.ncard_diff' hs.2 hu, hs.1]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_assoc,
    ← Set.ncard_eq_toFinset_card _ _]
  simp [Set.ncard_powerset_ncard, hu]

lemma map_ncard_setBernoulli_singleton {u : Set ι} (hu : u.Finite) (p : I) (k : ℕ) :
    (setBer(u, p).map Set.ncard) {k} =
      ENNReal.ofReal ((u.ncard.choose k) * p ^ k * (1 - p) ^ (u.ncard - k)) := by
  rw [← ENNReal.ofReal_toReal (a := (Measure.map _ _) _) (by simp), ← measureReal_def,
    map_ncard_setBernoulli_real_singleton hu]

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

omit [Countable ι] in
lemma HasLaw.hasLaw_indicator_infinitePi_ite_of_setBernoulli [DecidablePred (· ∈ u)]
    {S : Ω → Set ι} (hS : HasLaw S setBer(u, p) P) :
    HasLaw (fun ω i ↦ {ω' | i ∈ S ω'}.indicator 1 ω)
      (infinitePi (fun i ↦ if i ∈ u then Ber(1, 0, p) else dirac 0)) P where
  aemeasurable := by
    classical
    have : (fun ω i ↦ {ω' | i ∈ S ω'}.indicator 1 ω) =
        (fun s i ↦ if i ∈ s then 1 else 0) ∘ S := by ext ω i; by_cases h : i ∈ S ω <;> simp [h]
    rw [this]
    exact Measurable.comp_aemeasurable
      (measurable_pi_lambda _ fun i ↦ .ite (by measurability) (by fun_prop) (by fun_prop))
      hS.aemeasurable
  map_eq := by
    classical
    have h1 : (fun ω i ↦ {ω' | i ∈ S ω'}.indicator 1 ω) =
        (fun s i ↦ if i ∈ s then 1 else 0) ∘ S := by ext ω i; by_cases h : i ∈ S ω <;> simp [h]
    have h2 : (fun s i ↦ if i ∈ s then 1 else 0) ∘ (fun (p : ι → Prop) ↦ {i | p i}) =
        fun p i ↦ if p i then 1 else 0 := by ext; simp
    rw [h1, ← AEMeasurable.map_map_of_aemeasurable, hS.map_eq, setBernoulli_eq_map, map_map,
      h2, infinitePi_map_pi (f := fun x q ↦ if q then 1 else 0) (μ := fun i ↦ Ber(i ∈ u, False, p))]
    · congr
      ext i : 1
      split_ifs with hi <;> simp [hi]
    any_goals fun_prop
    · exact (measurable_pi_lambda _ fun i ↦ .ite (by measurability) (by fun_prop) (by fun_prop))
    · exact Measurable.aemeasurable
        (measurable_pi_lambda _ fun i ↦ .ite (by measurability) (by fun_prop) (by fun_prop))

omit [Countable ι] in
lemma HasLaw.hasLaw_indicator_infinitePi_of_setBernoulli
    {S : Ω → Set ι} (hS : HasLaw S setBer(u, p) P) :
    HasLaw (fun ω (i : u) ↦ {ω' | i.1 ∈ S ω'}.indicator 1 ω)
      (infinitePi (fun _ ↦ Ber(1, 0, p))) P := by
  classical
  have : HasLaw u.restrict (infinitePi (fun i ↦ Ber(1, 0, p)))
      (infinitePi (fun i ↦ if i ∈ u then Ber(1, 0, p) else dirac 0)) :=
    { aemeasurable := by fun_prop
      map_eq := by simp [infinitePi_map_restrict'] }
  exact this.comp hS.hasLaw_indicator_infinitePi_ite_of_setBernoulli

omit [Countable ι] in
lemma HasLaw.hasLaw_indicator_pi_of_setBernoulli
    {u : Finset ι} {S : Ω → Set ι} (hS : HasLaw S setBer(u, p) P) :
    HasLaw (fun ω (i : u) ↦ {ω' | i.1 ∈ S ω'}.indicator 1 ω) (.pi (fun _ ↦ Ber(1, 0, p))) P := by
  rw [← infinitePi_eq_pi]
  exact hS.hasLaw_indicator_infinitePi_of_setBernoulli

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
