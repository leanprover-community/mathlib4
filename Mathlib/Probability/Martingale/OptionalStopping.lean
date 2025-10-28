/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
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

* `MeasureTheory.submartingale_iff_expected_stoppedValue_mono`: the optional stopping theorem.
* `MeasureTheory.Submartingale.stoppedProcess`: the stopped process of a submartingale with
  respect to a stopping time is a submartingale.
* `MeasureTheory.maximal_ineq`: Doob's maximal inequality.

-/


open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
  {τ π : Ω → ℕ∞}

-- We may generalize the below lemma to functions taking value in a `NormedLatticeAddCommGroup`.
-- Similarly, generalize `(Super/Sub)martingale.setIntegral_le`.
/-- Given a submartingale `f` and bounded stopping times `τ` and `π` such that `τ ≤ π`, the
expectation of `stoppedValue f τ` is less than or equal to the expectation of `stoppedValue f π`.
This is the forward direction of the optional stopping theorem. -/
theorem Submartingale.expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢]
    (hf : Submartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) (hπ : IsStoppingTime 𝒢 π) (hle : τ ≤ π)
    {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) : μ[stoppedValue f τ] ≤ μ[stoppedValue f π] := by
  rw [← sub_nonneg, ← integral_sub', stoppedValue_sub_eq_sum' hle hbdd]
  · simp only [Finset.sum_apply]
    have : ∀ i, MeasurableSet[𝒢 i] {ω : Ω | τ ω ≤ i ∧ i < π ω} := by
      intro i
      refine (hτ i).inter ?_
      convert (hπ i).compl using 1
      ext x
      simp; rfl
    rw [integral_finset_sum]
    · refine Finset.sum_nonneg fun i _ => ?_
      rw [integral_indicator (𝒢.le _ _ (this _)), integral_sub', sub_nonneg]
      · exact hf.setIntegral_le (Nat.le_succ i) (this _)
      · exact (hf.integrable _).integrableOn
      · exact (hf.integrable _).integrableOn
    intro i _
    exact Integrable.indicator (Integrable.sub (hf.integrable _) (hf.integrable _))
      (𝒢.le _ _ (this _))
  · exact hf.integrable_stoppedValue hπ hbdd
  · exact hf.integrable_stoppedValue hτ fun ω => le_trans (hle ω) (hbdd ω)

/-- The converse direction of the optional stopping theorem, i.e. an adapted integrable process `f`
is a submartingale if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
theorem submartingale_of_expected_stoppedValue_mono [IsFiniteMeasure μ] (hadp : Adapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ τ π : Ω → ℕ∞, IsStoppingTime 𝒢 τ → IsStoppingTime 𝒢 π →
      τ ≤ π → (∃ N : ℕ, ∀ ω, π ω ≤ N) → μ[stoppedValue f τ] ≤ μ[stoppedValue f π]) :
    Submartingale f 𝒢 μ := by
  refine submartingale_of_setIntegral_le hadp hint fun i j hij s hs => ?_
  classical
  specialize hf (s.piecewise (fun _ => i) fun _ => j) _ (isStoppingTime_piecewise_const hij hs)
    (isStoppingTime_const 𝒢 j) ?_
    ⟨j, fun _ => le_rfl⟩
  · intro ω
    simp only [Set.piecewise, ENat.some_eq_coe]
    split_ifs with hω
    · exact mod_cast hij
    · norm_cast
  · rwa [stoppedValue_const, ← ENat.some_eq_coe, stoppedValue_piecewise_const,
      integral_piecewise (𝒢.le _ _ hs) (hint _).integrableOn (hint _).integrableOn, ←
      integral_add_compl (𝒢.le _ _ hs) (hint j), add_le_add_iff_right] at hf

/-- **The optional stopping theorem** (fair game theorem): an adapted integrable process `f`
is a submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
theorem submartingale_iff_expected_stoppedValue_mono [IsFiniteMeasure μ] (hadp : Adapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) :
    Submartingale f 𝒢 μ ↔ ∀ τ π : Ω → ℕ∞, IsStoppingTime 𝒢 τ → IsStoppingTime 𝒢 π →
      τ ≤ π → (∃ N : ℕ, ∀ x, π x ≤ N) → μ[stoppedValue f τ] ≤ μ[stoppedValue f π] :=
  ⟨fun hf _ _ hτ hπ hle ⟨_, hN⟩ => hf.expected_stoppedValue_mono hτ hπ hle hN,
    submartingale_of_expected_stoppedValue_mono hadp hint⟩

/-- The stopped process of a submartingale with respect to a stopping time is a submartingale. -/
protected theorem Submartingale.stoppedProcess [IsFiniteMeasure μ] (h : Submartingale f 𝒢 μ)
    (hτ : IsStoppingTime 𝒢 τ) : Submartingale (stoppedProcess f τ) 𝒢 μ := by
  rw [submartingale_iff_expected_stoppedValue_mono]
  · intro σ π hσ hπ hσ_le_π hπ_bdd
    simp_rw [stoppedValue_stoppedProcess]
    obtain ⟨n, hπ_le_n⟩ := hπ_bdd
    have hπ_top ω : π ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hπ_le_n ω)
    have hσ_top ω : σ ω ≠ ⊤ := ne_top_of_le_ne_top (hπ_top ω) (hσ_le_π ω)
    simp only [ne_eq, hσ_top, not_false_eq_true, ↓reduceIte, hπ_top, ge_iff_le]
    exact h.expected_stoppedValue_mono (hσ.min hτ) (hπ.min hτ)
      (fun ω => min_le_min (hσ_le_π ω) le_rfl) fun ω => (min_le_left _ _).trans (hπ_le_n ω)
  · exact Adapted.stoppedProcess_of_discrete h.adapted hτ
  · exact fun i =>
      h.integrable_stoppedValue ((isStoppingTime_const _ i).min hτ) fun ω => min_le_left _ _

section Maximal

open Finset

theorem smul_le_stoppedValue_hittingBtwn [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) {ε : ℝ≥0}
    (n : ℕ) : ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
    ENNReal.ofReal
      (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
      stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ↑ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
  have hn : Set.Icc 0 n = {k | k ≤ n} := by ext x; simp
  have : ∀ ω, ((ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) →
      (ε : ℝ) ≤ stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ↑ε ≤ y} 0 n ω : ℕ)) ω := by
    intro x hx
    simp_rw [le_sup'_iff, mem_range, Nat.lt_succ_iff] at hx
    refine stoppedValue_hittingBtwn_mem ?_
    simp only [Set.mem_setOf_eq, hn]
    exact
      let ⟨j, hj₁, hj₂⟩ := hx
      ⟨j, hj₁, hj₂⟩
  have h := setIntegral_ge_of_const_le (measurableSet_le measurable_const
    (Finset.measurable_range_sup'' fun n _ => (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)))
      (measure_ne_top _ _) this (Integrable.integrableOn (hsub.integrable_stoppedValue
        (hittingBtwn_isStoppingTime hsub.adapted measurableSet_Ici)
        (by simpa using hittingBtwn_le)))
  rw [ENNReal.le_ofReal_iff_toReal_le, ENNReal.toReal_smul]
  · exact h
  · exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · exact le_trans (mul_nonneg ε.coe_nonneg ENNReal.toReal_nonneg) h

@[deprecated (since := "2025-10-25")] alias smul_le_stoppedValue_hitting :=
  smul_le_stoppedValue_hittingBtwn

/-- **Doob's maximal inequality**: Given a non-negative submartingale `f`, for all `ε : ℝ≥0`,
we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f* n ω = max_{k ≤ n}, f k ω`.

In some literature, the Doob's maximal inequality refers to what we call Doob's Lp inequality
(which is a corollary of this lemma and will be proved in an upcoming PR). -/
theorem maximal_ineq [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : ℝ≥0}
    (n : ℕ) : ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
    ENNReal.ofReal
      (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
        f n ω ∂μ) := by
  suffices ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} +
      ENNReal.ofReal
        (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
          f n ω ∂μ) ≤
      ENNReal.ofReal (μ[f n]) by
    have hadd : ENNReal.ofReal (∫ ω, f n ω ∂μ) =
      ENNReal.ofReal
        (∫ ω in {ω | ↑ε ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}, f n ω ∂μ) +
      ENNReal.ofReal
        (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ↑ε},
          f n ω ∂μ) := by
      rw [← ENNReal.ofReal_add, ← setIntegral_union]
      · rw [← setIntegral_univ]
        convert rfl
        ext ω
        change (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ) ↔ _
        simp only [le_or_gt, Set.mem_univ]
      · rw [disjoint_iff_inf_le]
        rintro ω ⟨hω₁, hω₂⟩
        change (ε : ℝ) ≤ _ at hω₁
        change _ < (ε : ℝ) at hω₂
        exact (not_le.2 hω₂) hω₁
      · exact measurableSet_lt (Finset.measurable_range_sup'' fun n _ =>
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)) measurable_const
      exacts [(hsub.integrable _).integrableOn, (hsub.integrable _).integrableOn,
        integral_nonneg (hnonneg _), integral_nonneg (hnonneg _)]
    rwa [hadd, ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top] at this
  calc
    ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} +
        ENNReal.ofReal
          (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
            f n ω ∂μ) ≤
        ENNReal.ofReal
          (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
            stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ↑ε ≤ y} 0 n ω : ℕ)) ω ∂μ) +
        ENNReal.ofReal
          (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
            stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ↑ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
      gcongr with ω hω
      · exact smul_le_stoppedValue_hittingBtwn hsub n
      · exact (hsub.integrable n).integrableOn
      · refine Integrable.integrableOn ?_
        refine hsub.integrable_stoppedValue ?_ (by simpa using hittingBtwn_le)
        exact hittingBtwn_isStoppingTime hsub.adapted measurableSet_Ici
      · exact nullMeasurableSet_lt (Finset.measurable_range_sup'' fun n _ ↦
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)).aemeasurable aemeasurable_const
      rw [Set.mem_setOf_eq] at hω
      have : hittingBtwn f {y : ℝ | ↑ε ≤ y} 0 n ω = n := by
        classical simp only [hittingBtwn, Set.mem_setOf_eq,
          ite_eq_right_iff, forall_exists_index, and_imp]
        intro m hm hεm
        exact False.elim
          ((not_le.2 hω) ((le_sup'_iff _).2 ⟨m, mem_range.2 (Nat.lt_succ_of_le hm.2), hεm⟩))
      simp only [stoppedValue, this, ge_iff_le]
      refine le_of_eq ?_
      congr
    _ = ENNReal.ofReal
        (∫ ω, stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ↑ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
      rw [← ENNReal.ofReal_add, ← setIntegral_union]
      · rw [← setIntegral_univ (μ := μ)]
        convert rfl
        ext ω
        change _ ↔ (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ)
        simp only [le_or_gt, Set.mem_univ]
      · rw [disjoint_iff_inf_le]
        rintro ω ⟨hω₁, hω₂⟩
        change (ε : ℝ) ≤ _ at hω₁
        change _ < (ε : ℝ) at hω₂
        exact (not_le.2 hω₂) hω₁
      · exact measurableSet_lt (Finset.measurable_range_sup'' fun n _ =>
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)) measurable_const
      · exact Integrable.integrableOn (hsub.integrable_stoppedValue
          (hittingBtwn_isStoppingTime hsub.adapted measurableSet_Ici)
          (by simpa using hittingBtwn_le))
      · exact Integrable.integrableOn (hsub.integrable_stoppedValue
          (hittingBtwn_isStoppingTime hsub.adapted measurableSet_Ici)
          (by simpa using hittingBtwn_le))
      exacts [integral_nonneg fun x => hnonneg _ _, integral_nonneg fun x => hnonneg _ _]
    _ ≤ ENNReal.ofReal (μ[f n]) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← stoppedValue_const f n]
      refine hsub.expected_stoppedValue_mono
        (hittingBtwn_isStoppingTime hsub.adapted measurableSet_Ici)
        (isStoppingTime_const _ _) (fun ω ↦ ?_) (fun _ => mod_cast le_rfl)
      simp [hittingBtwn_le]

end Maximal

end MeasureTheory
