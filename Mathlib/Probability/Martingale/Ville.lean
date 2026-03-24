/-
Copyright (c) 2026 Wei Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Lin
-/
module
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.MeasureTheory.Integral.IntegrableOn
/-!
# Ville's supermartingale inequality

This file proves Ville's inequality for nonnegative supermartingales.

## Main results

* \MeasureTheory.Supermartingale.measureReal_le_div\: basic Ville inequality.
* \MeasureTheory.Supermartingale.measureReal_sup_le_div\: supremum version.

## References

* Ville, J. (1939). Etude critique de la notion de collectif.
* Howard et al. (2021). Time-uniform confidence sequences. Ann. Statist.
-/

set_option linter.privateModule false
set_option linter.style.whitespace false

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

/-- The expected value of a nonneg supermartingale is nonincreasing. -/
theorem Supermartingale.integral_le
    (hf : Supermartingale f ℱ μ) [IsFiniteMeasure μ]
    {i j : ℕ} (hij : i ≤ j) :
    ∫ ω, f j ω ∂μ ≤ ∫ ω, f i ω ∂μ := by
  have h_ae : μ[f j | ℱ i] ≤ᵐ[μ] f i := hf.2.1 i j hij
  have h_eq : ∫ ω, μ[f j | ℱ i] ω ∂μ = ∫ ω, f j ω ∂μ :=
    integral_condExp (ℱ.le i)
  calc ∫ ω, f j ω ∂μ
      = ∫ ω, μ[f j | ℱ i] ω ∂μ := h_eq.symm
    _ ≤ ∫ ω, f i ω ∂μ :=
        integral_mono_ae integrable_condExp (hf.2.2 i) h_ae

/-- Expected value of a stopped nonneg supermartingale is bounded by E[f 0]. -/
theorem Supermartingale.integral_stoppedValue_le
    (hf : Supermartingale f ℱ μ) [SigmaFiniteFiltration μ ℱ]
    [IsFiniteMeasure μ]
    (hnn : ∀ n ω, 0 ≤ f n ω)
    {τ : Ω → ℕ∞} (hτ : IsStoppingTime ℱ τ)
    {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue f τ ω ∂μ ≤ ∫ ω, f 0 ω ∂μ := by
  have hsub : Submartingale (-f) ℱ μ := hf.neg
  have key := hsub.expected_stoppedValue_mono
    (isStoppingTime_const ℱ 0) hτ
    (fun _ => bot_le) hbdd
  simp only [stoppedValue_const] at key
  have h_neg : ∀ ω, stoppedValue ((-f) : ℕ → Ω → ℝ) τ ω =
      -(stoppedValue f τ ω) :=
    fun ω => by simp [stoppedValue, Pi.neg_apply]
  simp_rw [h_neg] at key
  simp only [integral_neg, Pi.neg_apply, neg_le_neg_iff] at key
  exact key

/-- Ville inequality: mu{f_n >= lam} <= E[f_0] / lam. -/
theorem Supermartingale.measureReal_le_div
    (hf : Supermartingale f ℱ μ) [SigmaFiniteFiltration μ ℱ]
    [IsFiniteMeasure μ]
    (hnn : ∀ n ω, 0 ≤ f n ω)
    {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    μ.real {ω | lam ≤ f n ω} ≤ (∫ ω, f 0 ω ∂μ) / lam := by
  have h_markov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (hnn n)) (hf.2.2 n) lam
  have h_mono := hf.integral_le (Nat.zero_le n)
  rw [le_div_iff₀ hlam, mul_comm]; linarith

/-- Ville inequality for all n. -/
theorem Supermartingale.measureReal_le_div_forall
    (hf : Supermartingale f ℱ μ) [SigmaFiniteFiltration μ ℱ]
    [IsFiniteMeasure μ]
    (hnn : ∀ n ω, 0 ≤ f n ω)
    {lam : ℝ} (hlam : 0 < lam) :
    ∀ n, μ.real {ω | lam ≤ f n ω} ≤ (∫ ω, f 0 ω ∂μ) / lam :=
  fun n => hf.measureReal_le_div hnn hlam n

/-- Ville supremum version: mu{exists n, f_n >= lam} <= E[f_0] / lam. -/
theorem Supermartingale.measureReal_sup_le_div
    (hf : Supermartingale f ℱ μ) [SigmaFiniteFiltration μ ℱ]
    [IsFiniteMeasure μ]
    (hnn : ∀ n ω, 0 ≤ f n ω)
    {lam : ℝ} (hlam : 0 < lam) :
    μ.real {ω | ∃ n, lam ≤ f n ω} ≤ (∫ ω, f 0 ω ∂μ) / lam := by
  have hnn_ae : ∀ n, 0 ≤ᵐ[μ] f n := fun n => ae_of_all μ (hnn n)
  have hI0 : 0 ≤ (∫ ω, f 0 ω ∂μ) / lam :=
    div_nonneg (integral_nonneg (hnn 0)) hlam.le
  -- A n = ⋃_{i≤n} {f_i ≥ λ} is monotone with union = {exists n, f_n ≥ λ}
  let A : ℕ → Set Ω := fun n => ⋃ i ≤ n, {ω | lam ≤ f i ω}
  have hmono : Monotone A := by
    intro a b hab ω hω
    simp only [A, Set.mem_iUnion, Set.mem_setOf_eq] at hω ⊢
    obtain ⟨i, hia, hfi⟩ := hω
    exact ⟨i, hia.trans hab, hfi⟩
  have hAeq : ((⋃ n, A n) = {ω | ∃ n, lam ≤ f n ω}) := by
    ext ω; simp only [A, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, i, _, hfi⟩; exact ⟨i, hfi⟩
    · rintro ⟨n, hfn⟩; exact ⟨n, n, le_refl n, hfn⟩
  -- Key bound: μ.real(A n) ≤ E[f_0]/λ for each n
  -- Proof: let τ = hitting time of {y | lam ≤ y} in [0,n]
  have hAbound : ∀ n, μ.real (A n) ≤ (∫ ω, f 0 ω ∂μ) / lam := by
    intro n
    -- τ = hitting time of {y | lam ≤ y} in [0,n], coerced to ℕ∞
    set τ : Ω → ℕ∞ := fun ω => (hittingBtwn (ι := ℕ) f {y | lam ≤ y} 0 n ω : ℕ) with hτdef
    have hτst : IsStoppingTime ℱ τ :=
      hf.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
    have hτbdd : ∀ ω, τ ω ≤ ↑n := fun ω => by
      simp only [hτdef]
      exact WithTop.coe_le_coe.mpr
        (hittingBtwn_le (u := f) (s := {y | lam ≤ y}) (n := 0) (m := n) ω)
    have h_on_A : ∀ ω ∈ A n, lam ≤ stoppedValue f τ ω := by
      intro ω hω
      simp only [A, Set.mem_iUnion, Set.mem_setOf_eq] at hω
      obtain ⟨i, hi, hfi⟩ := hω
      exact stoppedValue_hittingBtwn_mem ⟨i, ⟨Nat.zero_le i, hi⟩, hfi⟩
    have hEτ : ∫ ω, stoppedValue f τ ω ∂μ ≤ ∫ ω, f 0 ω ∂μ :=
      hf.integral_stoppedValue_le hnn hτst hτbdd
    have hA_meas : MeasurableSet (A n) := by
      apply MeasurableSet.iUnion; intro i
      apply MeasurableSet.iUnion; intro _
      exact measurableSet_le measurable_const
        (hf.stronglyMeasurable i |>.measurable.mono (ℱ.le i) le_rfl)
    have hinteg : Integrable (stoppedValue f τ) μ := by
      have h := hf.neg.integrable_stoppedValue hτst hτbdd
      have heq : stoppedValue (-f) τ = -stoppedValue f τ := by
        ext ω; simp [stoppedValue, Pi.neg_apply]
      rw [heq] at h; simpa using h.neg
    have hkey : lam * μ.real (A n) ≤ ∫ ω, stoppedValue f τ ω ∂μ := by
      have hset := setIntegral_ge_of_const_le_real hA_meas (measure_ne_top μ _)
        h_on_A hinteg.integrableOn
      have hle : ∫ ω in A n, stoppedValue f τ ω ∂μ ≤
          ∫ ω, stoppedValue f τ ω ∂μ :=
        setIntegral_le_integral hinteg (ae_of_all μ (fun ω => hnn _ _))
      linarith
    -- lam * μ(A n) ≤ E[f_τ] ≤ E[f_0], so μ(A n) ≤ E[f_0]/lam
    have hchain : lam * μ.real (A n) ≤ ∫ ω, f 0 ω ∂μ := hkey.trans hEτ
    rw [le_div_iff₀ hlam]; linarith
  -- Combine: {exists n, f_n ≥ λ} = ⋃ A_n, μ(⋃ A_n) = sup μ(A_n) ≤ E[f_0]/λ
  rw [← hAeq, Measure.real, hmono.measure_iUnion]
  apply ENNReal.toReal_le_of_le_ofReal hI0
  apply iSup_le; intro n
  apply ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hI0 |>.mpr
  rw [← Measure.real]
  exact hAbound n

end MeasureTheory
