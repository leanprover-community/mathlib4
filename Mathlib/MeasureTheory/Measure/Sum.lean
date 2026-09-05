/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.CompleteLattice

/-!
# Sums of measures

Given `μ : ι → Measure α`, we define `Measure.sum μ` as the measure which to a measurable set `s`
associates `∑' i, μ i s`.

## Tags

measure, sum
-/

public section

open Function Filter

namespace MeasureTheory.Measure

variable {α ι ι' : Type*} {mα : MeasurableSpace α} {s t : Set α} {μ : ι → Measure α}

/-- Sum of an indexed family of measures. -/
noncomputable def sum (μ : ι → Measure α) : Measure α :=
  (OuterMeasure.sum fun i => (μ i).toOuterMeasure).toMeasure <|
    le_trans (le_iInf fun _ => le_toOuterMeasure_caratheodory _)
      (OuterMeasure.le_sum_caratheodory _)

theorem le_sum_apply (μ : ι → Measure α) (s : Set α) : ∑' i, μ i s ≤ sum μ s := by
  grw [sum, ← le_toMeasure_apply]; rfl

@[simp]
theorem sum_apply (μ : ι → Measure α) (hs : MeasurableSet s) :
    sum μ s = ∑' i, μ i s :=
  toMeasure_apply _ _ hs

theorem sum_apply₀ (μ : ι → Measure α) (hs : NullMeasurableSet s (sum μ)) :
    sum μ s = ∑' i, μ i s := by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, t_meas, ht⟩
  calc
  sum μ s = sum μ t := measure_congr ht.symm
  _ = ∑' i, μ i t := sum_apply _ t_meas
  _ ≤ ∑' i, μ i s := ENNReal.tsum_le_tsum fun i ↦ measure_mono ts

/-! For the next theorem, the countability assumption is necessary. For a counterexample, consider
an uncountable space, with a distinguished point `x₀`, and the sigma-algebra made of countable sets
not containing `x₀`, and their complements. All points but `x₀` are measurable.
Consider the sum of the Dirac masses at points different from `x₀`, and `s = {x₀}`. For any Dirac
mass `δ_x`, we have `δ_x (x₀) = 0`, so `∑' x, δ_x (x₀) = 0`. On the other hand, the measure
`sum δ_x` gives mass one to each point different from `x₀`, so it gives infinite mass to any
measurable set containing `x₀` (as such a set is uncountable), and by outer regularity one gets
`sum δ_x {x₀} = ∞`.
-/
theorem sum_apply_of_countable [Countable ι] (μ : ι → Measure α) (s : Set α) :
    sum μ s = ∑' i, μ i s := by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases exists_measurable_superset_forall_eq μ s with ⟨t, hst, htm, ht⟩
  calc
  sum μ s ≤ sum μ t := measure_mono hst
  _ = ∑' i, μ i t := sum_apply _ htm
  _ = ∑' i, μ i s := by simp [ht]

theorem le_sum (μ : ι → Measure α) (i : ι) : μ i ≤ sum μ :=
  le_iff.2 fun s hs ↦ by grw [sum_apply μ hs, ← ENNReal.le_tsum i]

@[simp]
theorem sum_apply_eq_zero [Countable ι] :
    sum μ s = 0 ↔ ∀ i, μ i s = 0 := by
  simp [sum_apply_of_countable]

theorem sum_apply_eq_zero' (hs : MeasurableSet s) :
    sum μ s = 0 ↔ ∀ i, μ i s = 0 := by simp [hs]

@[simp] lemma sum_eq_zero : sum μ = 0 ↔ ∀ i, μ i = 0 := by
  simp +contextual [Measure.ext_iff, forall_comm (α := ι)]

@[simp]
lemma sum_zero : Measure.sum (fun (_ : ι) ↦ (0 : Measure α)) = 0 := by
  ext s hs
  simp [Measure.sum_apply _ hs]

theorem sum_sum (μ : ι → ι' → Measure α) :
    (sum fun n => sum (μ n)) = sum (fun (p : ι × ι') ↦ μ p.1 p.2) := by
  ext1 s hs
  simp [sum_apply _ hs, ENNReal.tsum_prod']

theorem sum_comm (μ : ι → ι' → Measure α) :
    (sum fun n => sum (μ n)) = sum fun m => sum fun n => μ n m := by
  ext1 s hs
  simp_rw [sum_apply _ hs]
  rw [ENNReal.tsum_comm]

theorem ae_sum_iff [Countable ι] {p : α → Prop} :
    (∀ᵐ x ∂sum μ, p x) ↔ ∀ i, ∀ᵐ x ∂μ i, p x :=
  sum_apply_eq_zero

theorem ae_sum_iff' {p : α → Prop} (h : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂sum μ, p x) ↔ ∀ i, ∀ᵐ x ∂μ i, p x :=
  sum_apply_eq_zero' h.compl

@[simp]
theorem sum_fintype [Fintype ι] (μ : ι → Measure α) : sum μ = ∑ i, μ i := by
  ext1 s hs
  simp only [sum_apply, finsetSum_apply, hs, tsum_fintype]

theorem sum_coe_finset (s : Finset ι) (μ : ι → Measure α) :
    (sum fun i : s => μ i) = ∑ i ∈ s, μ i := by rw [sum_fintype, Finset.sum_coe_sort s μ]

@[simp]
theorem ae_sum_eq [Countable ι] (μ : ι → Measure α) : ae (sum μ) = ⨆ i, ae (μ i) :=
  Filter.ext fun _ => ae_sum_iff.trans mem_iSup.symm

theorem sum_bool (μ : Bool → Measure α) : sum μ = μ true + μ false := by
  rw [sum_fintype, Fintype.sum_bool]

theorem sum_cond (μ ν : Measure α) : (sum fun b => cond b μ ν) = μ + ν :=
  sum_bool _

@[simp]
theorem sum_of_isEmpty [IsEmpty ι] (μ : ι → Measure α) : sum μ = 0 := by
  rw [← measure_univ_eq_zero, sum_apply _ MeasurableSet.univ, tsum_empty]

theorem sum_add_sum_compl (s : Set ι) (μ : ι → Measure α) :
    ((sum fun i : s => μ i) + sum fun i : ↥sᶜ => μ i) = sum μ := by
  ext1 t ht
  simp only [add_apply, sum_apply _ ht]
  exact ENNReal.summable.tsum_add_tsum_compl (f := fun i => μ i t) ENNReal.summable

theorem sum_congr {μ ν : ℕ → Measure α} (h : ∀ n, μ n = ν n) : sum μ = sum ν :=
  congr_arg sum (funext h)

theorem sum_add_sum (μ ν : ι → Measure α) : sum μ + sum ν = sum fun n => μ n + ν n := by
  ext1 s hs
  simp only [add_apply, sum_apply _ hs,
    ENNReal.summable.tsum_add ENNReal.summable]

@[simp] lemma sum_comp_equiv (e : ι' ≃ ι) (μ : ι → Measure α) :
    sum (μ ∘ e) = sum μ := by
  ext s hs
  simpa [hs, sum_apply] using e.tsum_eq (fun n ↦ μ n s)

@[simp] lemma sum_extend_zero {f : ι → ι'} (hf : Injective f) (μ : ι → Measure α) :
    sum (Function.extend f μ 0) = sum μ := by
  ext s hs
  simp [*, Function.apply_extend (fun μ : Measure α ↦ μ s)]

end MeasureTheory.Measure
