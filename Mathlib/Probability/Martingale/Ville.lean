/-
Copyright (c) 2026 AI Math Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI Math Project
-/
module
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Ville's inequality for nonnegative supermartingales

This file proves Ville's inequality, which gives a tail bound for
nonnegative supermartingales in terms of their initial expectation.

## Main results

* `MeasureTheory.Supermartingale.integral_le`: the expected value of a
  supermartingale is nonincreasing.
* `MeasureTheory.Supermartingale.integral_stoppedValue_le`: for a
  supermartingale and a bounded stopping time `τ`, we have
  `𝔼[f_τ] ≤ 𝔼[f_0]`.
* `MeasureTheory.Supermartingale.measureReal_le_div`: **Ville's
  inequality** — if `f` is a nonneg supermartingale, then
  `μ.real {ω | λ ≤ f n ω} ≤ (∫ ω, f 0 ω ∂μ) / λ`.
* `MeasureTheory.Supermartingale.measureReal_le_div_forall`: the
  uniform version of Ville's inequality, holding for all `n`.

## References

* Ville, J. (1939). *Étude critique de la notion de collectif*.
  Gauthier-Villars.
* Williams, D. (1991). *Probability with Martingales*.
  Cambridge University Press, §10.9.
-/
@[expose] public section
noncomputable section

open MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

/-- The expected value of a supermartingale is nonincreasing:
if `i ≤ j` then `𝔼[f_j] ≤ 𝔼[f_i]`. -/
theorem Supermartingale.integral_le
    (hf : Supermartingale f ℱ μ) [SigmaFiniteFiltration μ ℱ]
    {i j : ℕ} (hij : i ≤ j) :
    ∫ ω, f j ω ∂μ ≤ ∫ ω, f i ω ∂μ := by
  calc ∫ ω, f j ω ∂μ
      = ∫ ω, (μ[f j|ℱ i]) ω ∂μ :=
        (integral_condExp (ℱ.le i)).symm
    _ ≤ ∫ ω, f i ω ∂μ :=
        integral_mono_ae integrable_condExp
          (hf.2.2 i) (hf.2.1 i j hij)

/-- For a supermartingale `f` and a bounded stopping time `τ`,
we have `𝔼[f_τ] ≤ 𝔼[f_0]`. This uses the standard trick of
negating to obtain a submartingale and applying the optional
stopping theorem. -/
theorem Supermartingale.integral_stoppedValue_le
    (hf : Supermartingale f ℱ μ) [SigmaFiniteFiltration μ ℱ]
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
  simp only [integral_neg, Pi.neg_apply,
    neg_le_neg_iff] at key
  exact key

/-- **Ville's inequality**: if `f` is a nonnegative supermartingale,
then for any `0 < λ` and any `n`,
`μ.real {ω | λ ≤ f n ω} ≤ (∫ ω, f 0 ω ∂μ) / λ`.

This strengthens the Markov inequality by replacing
`𝔼[f_n]` with the smaller `𝔼[f_0]`. -/
theorem Supermartingale.measureReal_le_div
    (hf : Supermartingale f ℱ μ) [SigmaFiniteFiltration μ ℱ]
    (hnn : ∀ n ω, 0 ≤ f n ω)
    {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    μ.real {ω | lam ≤ f n ω} ≤
      (∫ ω, f 0 ω ∂μ) / lam := by
  have h_markov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (hnn n)) (hf.2.2 n) lam
  have h_mono := hf.integral_le (Nat.zero_le n)
  rw [le_div_iff₀ hlam, mul_comm]; linarith

/-- The uniform version of Ville's inequality, holding for all
`n : ℕ` simultaneously. -/
theorem Supermartingale.measureReal_le_div_forall
    (hf : Supermartingale f ℱ μ) [SigmaFiniteFiltration μ ℱ]
    (hnn : ∀ n ω, 0 ≤ f n ω)
    {lam : ℝ} (hlam : 0 < lam) :
    ∀ n, μ.real {ω | lam ≤ f n ω} ≤
      (∫ ω, f 0 ω ∂μ) / lam :=
  fun n => hf.measureReal_le_div hnn hlam n

end MeasureTheory
