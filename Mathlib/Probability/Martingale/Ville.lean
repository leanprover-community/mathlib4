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

* `MeasureTheory.Supermartingale.measureReal_le_div`: basic Ville inequality.
  For a nonneg supermartingale `f`, `μ.real {ω | λ ≤ f n ω} ≤ (∫ ω, f 0 ω ∂μ) / λ`.
* `MeasureTheory.Supermartingale.measureReal_sup_le_div`: supremum version.
  `μ.real {ω | ∃ n, λ ≤ f n ω} ≤ (∫ ω, f 0 ω ∂μ) / λ`.

## References

* Ville, J. (1939). Étude critique de la notion de collectif.
* Howard, Ramdas, McAuliffe, Sekhon (2021). Time-uniform, nonparametric,
  nonasymptotic confidence sequences. Ann. Statist.
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

/-- Expected value of a stopped nonneg supermartingale is bounded by `𝔼[f 0]`. -/
theorem Supermartingale.integral_stoppedValue_le
    (hf : Supermartingale f ℱ μ) [SigmaFiniteFiltration μ ℱ]
    [IsFiniteMeasure μ]
    (hnn : ∀ n ω, 0 ≤ f n ω)
    {τ : Ω → ℕ∞} (hτ : IsStoppingTime ℱ τ)
    {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue f τ ω ∂μ ≤ ∫ ω, f 0 ω ∂μ := by
  sorry

/-- **Ville's inequality**: for a nonneg supermartingale `f` and `0 < λ`,
`μ.real {ω | λ ≤ f n ω} ≤ (𝔼[f 0]) / λ`. -/
theorem Supermartingale.measureReal_le_div
    (hf : Supermartingale f ℱ μ) [SigmaFiniteFiltration μ ℱ]
    [IsFiniteMeasure μ]
    (hnn : ∀ n ω, 0 ≤ f n ω)
    {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    μ.real {ω | lam ≤ f n ω} ≤ (∫ ω, f 0 ω ∂μ) / lam := by
  rw [le_div_iff₀ hlam]
  have hMarkov : lam * μ.real {x | lam ≤ f n x} ≤ ∫ x, f n x ∂μ :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all μ (hnn n)) (hf.2.2 n) lam
  calc μ.real {ω | lam ≤ f n ω} * lam
      = lam * μ.real {ω | lam ≤ f n ω} := mul_comm _ _
    _ ≤ ∫ ω, f n ω ∂μ := hMarkov
    _ ≤ ∫ ω, f 0 ω ∂μ := hf.integral_le (Nat.zero_le n)

/-- **Ville's inequality** (quantified over all `n`). -/
theorem Supermartingale.measureReal_le_div_forall
    (hf : Supermartingale f ℱ μ) [SigmaFiniteFiltration μ ℱ]
    [IsFiniteMeasure μ]
    (hnn : ∀ n ω, 0 ≤ f n ω)
    {lam : ℝ} (hlam : 0 < lam) :
    ∀ n, μ.real {ω | lam ≤ f n ω} ≤ (∫ ω, f 0 ω ∂μ) / lam :=
  fun n => hf.measureReal_le_div hnn hlam n

/-- **Ville's inequality (supremum version)**: for a nonneg supermartingale,
`μ.real {ω | ∃ n, λ ≤ f n ω} ≤ (𝔼[f 0]) / λ`.

Proof sketch:
1. Let `A_N = {ω | ∃ n ≤ N, f n ω ≥ λ}`. Then `A_N ↑ {ω | ∃ n, f n ω ≥ λ}`.
2. Define hitting time `τ_N`: first `n ≤ N` with `f n ω ≥ λ`, else `N`.
3. `τ_N` is a stopping time bounded by `N`.
4. On `A_N`, `f (τ_N ω) ω ≥ λ`, so `λ · μ A_N ≤ 𝔼[f_{τ_N}] ≤ 𝔼[f_0]`.
5. Monotone convergence: `μ A_N → μ {∃ n, ...}`. -/
theorem Supermartingale.measureReal_sup_le_div
    (hf : Supermartingale f ℱ μ) [SigmaFiniteFiltration μ ℱ]
    [IsFiniteMeasure μ]
    (hnn : ∀ n ω, 0 ≤ f n ω)
    {lam : ℝ} (hlam : 0 < lam) :
    μ.real {ω | ∃ n, lam ≤ f n ω} ≤ (∫ ω, f 0 ω ∂μ) / lam := by
  sorry

end MeasureTheory