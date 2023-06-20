/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

! This file was ported from Lean 3 source module probability.martingale.optional_stopping
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic

/-! # Optional stopping theorem (fair game theorem)

The optional stopping theorem states that an adapted integrable process `f` is a submartingale if
and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`.

This file also contains Doob's maximal inequality: given a non-negative submartingale `f`, for all
`ε : ℝ≥0`, we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f* n ω = max_{k ≤ n}, f k ω`.

### Main results

* `measure_theory.submartingale_iff_expected_stopped_value_mono`: the optional stopping theorem.
* `measure_theory.submartingale.stopped_process`: the stopped process of a submartingale with
  respect to a stopping time is a submartingale.
* `measure_theory.maximal_ineq`: Doob's maximal inequality.

 -/


open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type _} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
  {τ π : Ω → ℕ}

-- We may generalize the below lemma to functions taking value in a `normed_lattice_add_comm_group`.
-- Similarly, generalize `(super/)submartingale.set_integral_le`.
/-- Given a submartingale `f` and bounded stopping times `τ` and `π` such that `τ ≤ π`, the
expectation of `stopped_value f τ` is less than or equal to the expectation of `stopped_value f π`.
This is the forward direction of the optional stopping theorem. -/
theorem Submartingale.expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢]
    (hf : Submartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) (hπ : IsStoppingTime 𝒢 π) (hle : τ ≤ π)
    {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) : μ[stoppedValue f τ] ≤ μ[stoppedValue f π] := by
  rw [← sub_nonneg, ← integral_sub', stopped_value_sub_eq_sum' hle hbdd]
  · simp only [Finset.sum_apply]
    have : ∀ i, measurable_set[𝒢 i] {ω : Ω | τ ω ≤ i ∧ i < π ω} := by
      intro i
      refine' (hτ i).inter _
      convert (hπ i).compl
      ext x
      simpa
    rw [integral_finset_sum]
    · refine' Finset.sum_nonneg fun i hi => _
      rw [integral_indicator (𝒢.le _ _ (this _)), integral_sub', sub_nonneg]
      · exact hf.set_integral_le (Nat.le_succ i) (this _)
      · exact (hf.integrable _).IntegrableOn
      · exact (hf.integrable _).IntegrableOn
    intro i hi
    exact
      integrable.indicator (integrable.sub (hf.integrable _) (hf.integrable _)) (𝒢.le _ _ (this _))
  · exact hf.integrable_stopped_value hπ hbdd
  · exact hf.integrable_stopped_value hτ fun ω => le_trans (hle ω) (hbdd ω)
#align measure_theory.submartingale.expected_stopped_value_mono MeasureTheory.Submartingale.expected_stoppedValue_mono

/-- The converse direction of the optional stopping theorem, i.e. an adapted integrable process `f`
is a submartingale if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
theorem submartingale_of_expected_stoppedValue_mono [IsFiniteMeasure μ] (hadp : Adapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ)
    (hf :
      ∀ τ π : Ω → ℕ,
        IsStoppingTime 𝒢 τ →
          IsStoppingTime 𝒢 π →
            τ ≤ π → (∃ N, ∀ ω, π ω ≤ N) → μ[stoppedValue f τ] ≤ μ[stoppedValue f π]) :
    Submartingale f 𝒢 μ := by
  refine' submartingale_of_set_integral_le hadp hint fun i j hij s hs => _
  classical
  specialize
    hf (s.piecewise (fun _ => i) fun _ => j) _ (is_stopping_time_piecewise_const hij hs)
      (is_stopping_time_const 𝒢 j) (fun x => (ite_le_sup _ _ _).trans (max_eq_right hij).le)
      ⟨j, fun x => le_rfl⟩
  rwa [stopped_value_const, stopped_value_piecewise_const,
    integral_piecewise (𝒢.le _ _ hs) (hint _).IntegrableOn (hint _).IntegrableOn, ←
    integral_add_compl (𝒢.le _ _ hs) (hint j), add_le_add_iff_right] at hf 
#align measure_theory.submartingale_of_expected_stopped_value_mono MeasureTheory.submartingale_of_expected_stoppedValue_mono

/-- **The optional stopping theorem** (fair game theorem): an adapted integrable process `f`
is a submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
theorem submartingale_iff_expected_stoppedValue_mono [IsFiniteMeasure μ] (hadp : Adapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) :
    Submartingale f 𝒢 μ ↔
      ∀ τ π : Ω → ℕ,
        IsStoppingTime 𝒢 τ →
          IsStoppingTime 𝒢 π →
            τ ≤ π → (∃ N, ∀ x, π x ≤ N) → μ[stoppedValue f τ] ≤ μ[stoppedValue f π] :=
  ⟨fun hf _ _ hτ hπ hle ⟨N, hN⟩ => hf.expected_stoppedValue_mono hτ hπ hle hN,
    submartingale_of_expected_stoppedValue_mono hadp hint⟩
#align measure_theory.submartingale_iff_expected_stopped_value_mono MeasureTheory.submartingale_iff_expected_stoppedValue_mono

/-- The stopped process of a submartingale with respect to a stopping time is a submartingale. -/
@[protected]
theorem Submartingale.stoppedProcess [IsFiniteMeasure μ] (h : Submartingale f 𝒢 μ)
    (hτ : IsStoppingTime 𝒢 τ) : Submartingale (stoppedProcess f τ) 𝒢 μ := by
  rw [submartingale_iff_expected_stopped_value_mono]
  · intro σ π hσ hπ hσ_le_π hπ_bdd
    simp_rw [stopped_value_stopped_process]
    obtain ⟨n, hπ_le_n⟩ := hπ_bdd
    exact
      h.expected_stopped_value_mono (hσ.min hτ) (hπ.min hτ) (fun ω => min_le_min (hσ_le_π ω) le_rfl)
        fun ω => (min_le_left _ _).trans (hπ_le_n ω)
  · exact adapted.stopped_process_of_discrete h.adapted hτ
  ·
    exact fun i =>
      h.integrable_stopped_value ((is_stopping_time_const _ i).min hτ) fun ω => min_le_left _ _
#align measure_theory.submartingale.stopped_process MeasureTheory.Submartingale.stoppedProcess

section Maximal

open Finset

theorem smul_le_stoppedValue_hitting [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) {ε : ℝ≥0}
    (n : ℕ) :
    ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ fun k => f k ω} ≤
      ENNReal.ofReal
        (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ fun k => f k ω},
          stoppedValue f (hitting f {y : ℝ | ↑ε ≤ y} 0 n) ω ∂μ) := by
  have hn : Set.Icc 0 n = {k | k ≤ n} := by ext x; simp
  have :
    ∀ ω,
      ((ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ fun k => f k ω) →
        (ε : ℝ) ≤ stopped_value f (hitting f {y : ℝ | ↑ε ≤ y} 0 n) ω := by
    intro x hx
    simp_rw [le_sup'_iff, mem_range, Nat.lt_succ_iff] at hx 
    refine' stopped_value_hitting_mem _
    simp only [Set.mem_setOf_eq, exists_prop, hn]
    exact
      let ⟨j, hj₁, hj₂⟩ := hx
      ⟨j, hj₁, hj₂⟩
  have h :=
    set_integral_ge_of_const_le
      (measurableSet_le measurable_const
        (Finset.measurable_range_sup'' fun n _ =>
          (hsub.strongly_measurable n).Measurable.le (𝒢.le n)))
      (measure_ne_top _ _) this
      (integrable.integrable_on
        (hsub.integrable_stopped_value (hitting_is_stopping_time hsub.adapted measurableSet_Ici)
          hitting_le))
  rw [ENNReal.le_ofReal_iff_toReal_le, ENNReal.toReal_smul]
  · exact h
  · exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · exact le_trans (mul_nonneg ε.coe_nonneg ENNReal.toReal_nonneg) h
#align measure_theory.smul_le_stopped_value_hitting MeasureTheory.smul_le_stoppedValue_hitting

/-- **Doob's maximal inequality**: Given a non-negative submartingale `f`, for all `ε : ℝ≥0`,
we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f* n ω = max_{k ≤ n}, f k ω`.

In some literature, the Doob's maximal inequality refers to what we call Doob's Lp inequality
(which is a corollary of this lemma and will be proved in an upcomming PR). -/
theorem maximal_ineq [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : ℝ≥0}
    (n : ℕ) :
    ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ fun k => f k ω} ≤
      ENNReal.ofReal
        (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ fun k => f k ω},
          f n ω ∂μ) := by
  suffices
    ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ fun k => f k ω} +
        ENNReal.ofReal
          (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_succ fun k => f k ω) < ε}, f n ω ∂μ) ≤
      ENNReal.ofReal (μ[f n]) by
    have hadd :
      ENNReal.ofReal (∫ ω, f n ω ∂μ) =
        ENNReal.ofReal
            (∫ ω in {ω | ↑ε ≤ (range (n + 1)).sup' nonempty_range_succ fun k => f k ω}, f n ω ∂μ) +
          ENNReal.ofReal
            (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_succ fun k => f k ω) < ↑ε},
              f n ω ∂μ) := by
      rw [← ENNReal.ofReal_add, ← integral_union]
      · conv_lhs => rw [← integral_univ]
        convert rfl
        ext ω
        change (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ) ↔ _
        simp only [le_or_lt, true_iff_iff]
      · rw [disjoint_iff_inf_le]
        rintro ω ⟨hω₁ : _ ≤ _, hω₂ : _ < _⟩
        exact (not_le.2 hω₂) hω₁
      ·
        exact
          measurableSet_lt
            (Finset.measurable_range_sup'' fun n _ =>
              (hsub.strongly_measurable n).Measurable.le (𝒢.le n))
            measurable_const
      exacts [(hsub.integrable _).IntegrableOn, (hsub.integrable _).IntegrableOn,
        integral_nonneg (hnonneg _), integral_nonneg (hnonneg _)]
    rwa [hadd, ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top] at this 
  calc
    ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ fun k => f k ω} +
          ENNReal.ofReal
            (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_succ fun k => f k ω) < ε}, f n ω ∂μ) ≤
        ENNReal.ofReal
            (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ fun k => f k ω},
              stopped_value f (hitting f {y : ℝ | ↑ε ≤ y} 0 n) ω ∂μ) +
          ENNReal.ofReal
            (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_succ fun k => f k ω) < ε},
              stopped_value f (hitting f {y : ℝ | ↑ε ≤ y} 0 n) ω ∂μ) := by
      refine'
        add_le_add (smul_le_stopped_value_hitting hsub _)
          (ENNReal.ofReal_le_ofReal
            (set_integral_mono_on (hsub.integrable n).IntegrableOn
              (integrable.integrable_on
                (hsub.integrable_stopped_value
                  (hitting_is_stopping_time hsub.adapted measurableSet_Ici) hitting_le))
              (measurableSet_lt
                (Finset.measurable_range_sup'' fun n _ =>
                  (hsub.strongly_measurable n).Measurable.le (𝒢.le n))
                measurable_const)
              _))
      intro ω hω
      rw [Set.mem_setOf_eq] at hω 
      have : hitting f {y : ℝ | ↑ε ≤ y} 0 n ω = n := by
        simp only [hitting, Set.mem_setOf_eq, exists_prop, Pi.coe_nat, Nat.cast_id,
          ite_eq_right_iff, forall_exists_index, and_imp]
        intro m hm hεm
        exact
          False.elim
            ((not_le.2 hω) ((le_sup'_iff _).2 ⟨m, mem_range.2 (Nat.lt_succ_of_le hm.2), hεm⟩))
      simp_rw [stopped_value, this]
    _ = ENNReal.ofReal (∫ ω, stopped_value f (hitting f {y : ℝ | ↑ε ≤ y} 0 n) ω ∂μ) := by
      rw [← ENNReal.ofReal_add, ← integral_union]
      · conv_rhs => rw [← integral_univ]
        convert rfl
        ext ω
        change _ ↔ (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ)
        simp only [le_or_lt, iff_true_iff]
      · rw [disjoint_iff_inf_le]
        rintro ω ⟨hω₁ : _ ≤ _, hω₂ : _ < _⟩
        exact (not_le.2 hω₂) hω₁
      ·
        exact
          measurableSet_lt
            (Finset.measurable_range_sup'' fun n _ =>
              (hsub.strongly_measurable n).Measurable.le (𝒢.le n))
            measurable_const
      ·
        exact
          integrable.integrable_on
            (hsub.integrable_stopped_value (hitting_is_stopping_time hsub.adapted measurableSet_Ici)
              hitting_le)
      ·
        exact
          integrable.integrable_on
            (hsub.integrable_stopped_value (hitting_is_stopping_time hsub.adapted measurableSet_Ici)
              hitting_le)
      exacts [integral_nonneg fun x => hnonneg _ _, integral_nonneg fun x => hnonneg _ _]
    _ ≤ ENNReal.ofReal (μ[f n]) := by
      refine' ENNReal.ofReal_le_ofReal _
      rw [← stopped_value_const f n]
      exact
        hsub.expected_stopped_value_mono (hitting_is_stopping_time hsub.adapted measurableSet_Ici)
          (is_stopping_time_const _ _) (fun ω => hitting_le ω) (fun ω => le_rfl : ∀ ω, n ≤ n)
#align measure_theory.maximal_ineq MeasureTheory.maximal_ineq

end Maximal

end MeasureTheory

