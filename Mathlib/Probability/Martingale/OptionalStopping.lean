/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Notation
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Moments.Variance

/-! # Optional stopping theorem (fair game theorem)

The optional stopping theorem states that a strongly adapted integrable process `f` is a
submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`.

This file also contains Doob's maximal inequality: given a non-negative submartingale `f`, for all
`ε : ℝ≥0`, we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f * n ω = max_{k ≤ n}, f k ω`.

### Main results

* `MeasureTheory.submartingale_iff_expected_stoppedValue_mono`: the optional stopping theorem.
* `MeasureTheory.Submartingale.stoppedProcess`: the stopped process of a submartingale with
  respect to a stopping time is a submartingale.
* `MeasureTheory.maximal_ineq`: Doob's maximal inequality.

-/

public section


open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
  {τ π : Ω → ℕ∞}

/-- Given a submartingale `f` and bounded stopping times `τ` and `π` such that `τ ≤ π`, the
expectation of `stoppedValue f τ` is less than or equal to the expectation of `stoppedValue f π`.
This is the forward direction of the optional stopping theorem. -/
theorem Submartingale.expected_stoppedValue_mono {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [PartialOrder E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] [ClosedIciTopology E] [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → E}
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

set_option backward.isDefEq.respectTransparency false in
/-- The converse direction of the optional stopping theorem, i.e. a strongly adapted integrable
process `f` is a submartingale if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
theorem submartingale_of_expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢]
    (hadp : StronglyAdapted 𝒢 f)
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

/-- **The optional stopping theorem** (fair game theorem): a strongly adapted integrable process `f`
is a submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
theorem submartingale_iff_expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢]
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ) :
    Submartingale f 𝒢 μ ↔ ∀ τ π : Ω → ℕ∞, IsStoppingTime 𝒢 τ → IsStoppingTime 𝒢 π →
      τ ≤ π → (∃ N : ℕ, ∀ x, π x ≤ N) → μ[stoppedValue f τ] ≤ μ[stoppedValue f π] :=
  ⟨fun hf _ _ hτ hπ hle ⟨_, hN⟩ => hf.expected_stoppedValue_mono hτ hπ hle hN,
    submartingale_of_expected_stoppedValue_mono hadp hint⟩

set_option backward.isDefEq.respectTransparency false in
/-- The stopped process of a submartingale with respect to a stopping time is a submartingale. -/
protected theorem Submartingale.stoppedProcess [SigmaFiniteFiltration μ 𝒢]
    (h : Submartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) :
    Submartingale (stoppedProcess f τ) 𝒢 μ := by
  rw [submartingale_iff_expected_stoppedValue_mono]
  · intro σ π hσ hπ hσ_le_π hπ_bdd
    simp_rw [stoppedValue_stoppedProcess]
    obtain ⟨n, hπ_le_n⟩ := hπ_bdd
    have hπ_top ω : π ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hπ_le_n ω)
    have hσ_top ω : σ ω ≠ ⊤ := ne_top_of_le_ne_top (hπ_top ω) (hσ_le_π ω)
    simp only [ne_eq, hσ_top, not_false_eq_true, ↓reduceIte, hπ_top, ge_iff_le]
    exact h.expected_stoppedValue_mono (hσ.min hτ) (hπ.min hτ)
      (fun ω => min_le_min (hσ_le_π ω) le_rfl) fun ω => (min_le_left _ _).trans (hπ_le_n ω)
  · exact StronglyAdapted.stoppedProcess_of_discrete h.stronglyAdapted hτ
  · exact fun i =>
      h.integrable_stoppedValue ((isStoppingTime_const _ i).min hτ) fun ω => min_le_left _ _

section Maximal

open Finset

set_option backward.isDefEq.respectTransparency false in
theorem smul_le_stoppedValue_hittingBtwn [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) {ε : ℝ≥0}
    (n : ℕ) : ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
    ENNReal.ofReal
      (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
      stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
  have : ∀ ω, ((ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) →
      (ε : ℝ) ≤ stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω := by
    intro x hx
    simp_rw [le_sup'_iff, mem_range, Nat.lt_succ_iff] at hx
    refine stoppedValue_hittingBtwn_mem ?_
    simp only [Set.mem_Icc, zero_le, true_and, Set.mem_setOf_eq]
    exact
      let ⟨j, hj₁, hj₂⟩ := hx
      ⟨j, hj₁, hj₂⟩
  have h := setIntegral_ge_of_const_le_real (measurableSet_le measurable_const
    (measurable_range_sup'' fun n _ => (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)))
      (measure_ne_top _ _) this (Integrable.integrableOn (hsub.integrable_stoppedValue
        (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
        (mod_cast hittingBtwn_le)))
  rw [ENNReal.le_ofReal_iff_toReal_le, ENNReal.toReal_smul]
  · exact h
  · exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · exact le_trans (mul_nonneg ε.coe_nonneg ENNReal.toReal_nonneg) h

@[deprecated (since := "2025-10-25")] alias smul_le_stoppedValue_hitting :=
  smul_le_stoppedValue_hittingBtwn

set_option backward.isDefEq.respectTransparency false in
/-- **Doob's maximal inequality**: Given a non-negative submartingale `f`, for all `ε : ℝ≥0`,
we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f* n ω = max_{k ≤ n}, f k ω`.

In some literature, the Doob's maximal inequality refers to what we call Doob's Lp inequality
(which is a corollary of this lemma and will be proved in an upcoming PR). -/
theorem maximal_ineq [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : ℝ≥0}
    (n : ℕ) : ε * μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
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
        (∫ ω in {ω | ε ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}, f n ω ∂μ) +
      ENNReal.ofReal
        (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
          f n ω ∂μ) := by
      rw [← ENNReal.ofReal_add, ← setIntegral_union]
      · rw [← setIntegral_univ]
        convert rfl
        ext ω
        change (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ) ↔ _
        simp only [le_or_gt, Set.mem_univ]
      · grind
      · exact measurableSet_lt (measurable_range_sup'' fun n _ =>
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)) measurable_const
      exacts [(hsub.integrable _).integrableOn, (hsub.integrable _).integrableOn,
        integral_nonneg (hnonneg _), integral_nonneg (hnonneg _)]
    rwa [hadd, ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top] at this
  calc
    _ ≤ ENNReal.ofReal
          (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
            stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) +
        ENNReal.ofReal
          (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
            stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
      gcongr with ω hω
      · exact smul_le_stoppedValue_hittingBtwn hsub n
      · exact (hsub.integrable n).integrableOn
      · refine Integrable.integrableOn ?_
        refine hsub.integrable_stoppedValue ?_ (fun ω ↦ mod_cast hittingBtwn_le ω)
        exact hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
      · exact nullMeasurableSet_lt (measurable_range_sup'' fun n _ ↦
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)).aemeasurable aemeasurable_const
      rw [Set.mem_setOf_eq] at hω
      have : hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω = n := by
        simp only [hittingBtwn, Set.mem_setOf_eq, ite_eq_right_iff, forall_exists_index, and_imp]
        intro m hm hεm
        exact False.elim
          ((not_le.2 hω) ((le_sup'_iff _).2 ⟨m, mem_range.2 (Nat.lt_succ_of_le hm.2), hεm⟩))
      simp only [stoppedValue, this, ge_iff_le]
      refine le_of_eq ?_
      congr
    _ = ENNReal.ofReal
        (∫ ω, stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
      rw [← ENNReal.ofReal_add, ← setIntegral_union]
      · rw [← setIntegral_univ (μ := μ)]
        convert rfl
        ext ω
        change _ ↔ (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ)
        simp only [le_or_gt, Set.mem_univ]
      · grind
      · exact measurableSet_lt (measurable_range_sup'' fun n _ =>
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)) measurable_const
      · exact Integrable.integrableOn (hsub.integrable_stoppedValue
          (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
          (fun ω ↦ mod_cast hittingBtwn_le ω))
      · exact Integrable.integrableOn (hsub.integrable_stoppedValue
          (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
          (fun ω ↦ mod_cast hittingBtwn_le ω))
      exacts [integral_nonneg fun x => hnonneg _ _, integral_nonneg fun x => hnonneg _ _]
    _ ≤ ENNReal.ofReal (μ[f n]) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← stoppedValue_const f n]
      refine hsub.expected_stoppedValue_mono
        (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
        (isStoppingTime_const _ _) (fun ω ↦ ?_) (fun _ => mod_cast le_rfl)
      simp [hittingBtwn_le]

end Maximal



section Kolmogorov

open ProbabilityTheory Finset

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ m0}
variable {M : ℕ → Ω → ℝ}

lemma square_submartingale_of_martingale (hM : Martingale M ℱ μ) (hL2 : ∀ n, MemLp (M n) 2 μ) :
    Submartingale (fun n ω => (M n ω) ^ 2) ℱ μ := by
  refine MeasureTheory.submartingale_nat ?hadp ?hint ?hstep
  · intro n
    simpa using (hM.stronglyAdapted n).pow 2
  · intro n
    exact MemLp.integrable_sq (hL2 n)
  · intro n
    have hcv : condVar (ℱ n) (M (n + 1)) μ
        =ᵐ[μ] μ[(M (n + 1)) ^ 2 | ℱ n] - (M n) ^ 2 := by
      have h1 := ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp
            (μ := μ) (m := ℱ n) (X := M (n + 1)) (hm := ℱ.le n) (hX := hL2 (n + 1))
      have h2 : μ[M (n + 1) | ℱ n] =ᶠ[ae μ] M n := by
        simpa using hM.condExp_ae_eq (Nat.le_succ n)
      filter_upwards [h1, h2] with ω h1ω h2ω
      simp [h1ω, h2ω]
    have hnonneg : 0 ≤ᵐ[μ] μ[(M (n + 1)) ^ 2 | ℱ n] - (M n) ^ 2 := by
      filter_upwards [ProbabilityTheory.ae_nonneg_condVar (μ := μ) (m := ℱ n) (X := M (n + 1)),
        hcv] with ω hω₁ hω₂
      simpa [hω₂] using hω₁
    filter_upwards [hnonneg] with ω hω
    exact sub_nonneg.mp (by simpa using hω)

/-- Martingale form of Kolmogorov's inequality. -/
theorem kolmogorov_ineq_martingale_sq (hM : Martingale M ℱ μ)
    (hL2 : ∀ n, MemLp (M n) 2 μ) (ε : NNReal) (n : ℕ) :
    ε ^ 2 * μ {ω | ε ^ 2 ≤ (range (n + 1)).sup' nonempty_range_add_one (fun k => (M k ω) ^ 2)}
    ≤ ENNReal.ofReal (∫ ω, (M n ω) ^ 2 ∂μ) := by
  let G : ℕ → Ω → ℝ := fun k ω => (M k ω) ^ 2
  have hGsub : Submartingale G ℱ μ := square_submartingale_of_martingale (μ := μ) (ℱ := ℱ) hM hL2
  have hGnonneg : 0 ≤ G := fun k ω ↦ sq_nonneg (M k ω)
  have hdoob := MeasureTheory.maximal_ineq (μ := μ) (f := G) hGsub hGnonneg (ε := ε ^ 2) n
  refine le_trans hdoob ?_
  apply ENNReal.ofReal_le_ofReal
  have hmono : ∫ ω in {ω | ε ^ 2 ≤ (range (n + 1)).sup' (by simp) (fun k => G k ω)}, G n ω ∂μ
      ≤ ∫ ω, G n ω ∂μ := by
    exact setIntegral_le_integral (s := {ω | ε ^ 2 ≤ (range (n + 1)).sup'
      (nonempty_range_add_one) (fun k => G k ω)}) (hfi := hGsub.integrable n)
      (hf := Filter.Eventually.of_forall fun ω => hGnonneg n ω)
  simpa [G] using hmono

theorem kolmogorov_ineq_wiki_version (hM : Martingale M ℱ μ)
    (hL2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) (ε : NNReal) (hmean : μ[M n] = 0) :
    ε ^ 2 * μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one (fun k => |M k ω|)}
    ≤ ENNReal.ofReal (Var[M n; μ]) := by
  set A : Set Ω := {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one (fun k => |M k ω|)}
  set B : Set Ω := {ω | (ε : ℝ) ^ 2 ≤ (range (n + 1)).sup' nonempty_range_add_one
    (fun k => (M k ω) ^ 2)}
  have hAB : A ⊆ B := by
    intro ω hω
    rcases (le_sup'_iff nonempty_range_add_one (f := fun k => |M k ω|) (a := (ε : ℝ))).mp hω
      with ⟨k, hk, hkω⟩
    exact le_trans (by rwa [sq_le_sq, NNReal.abs_eq ε]) (le_sup' (f := fun j => (M j ω) ^ 2) hk)
  calc
    _ ≤ ε ^ 2 * μ B := mul_le_mul_right (measure_mono hAB) (ε ^ 2)
    _ ≤ ENNReal.ofReal (∫ ω, (M n ω) ^ 2 ∂μ) := by
      simpa [A, B] using kolmogorov_ineq_martingale_sq (μ := μ) (ℱ := ℱ) (M := M) hM hL2 ε n
    _ = ENNReal.ofReal (Var[M n; μ]) := by
      rw [← variance_of_integral_eq_zero (MemLp.aemeasurable (hL2 n)) hmean]

end Kolmogorov

end MeasureTheory
