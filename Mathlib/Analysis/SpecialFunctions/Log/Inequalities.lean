import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Sharp Logarithm Inequalities for Concentration Arguments

Upper bounds on `Real.log (1 + ε)` and `Real.log (1 - ε)` used in chi-squared
Chernoff bounds for the Johnson–Lindenstrauss lemma.

## Main results

* `Real.log_one_add_le` : `log(1+ε) ≤ ε − ε²/4` for `ε ∈ (−1, 1]`
* `Real.log_one_sub_le` : `log(1−ε) ≤ −ε − ε²/4` for `ε ∈ [0, 1)`

Both bounds are tight enough to close the Chernoff exponent to `−mε²/8`
in the JL chi-squared tail (see `Contrib.Probability.Concentration.JohnsonLindenstrauss`).

## References

Dasgupta, S. and Gupta, A. (2003). An elementary proof of a theorem of Johnson
and Lindenstrauss. *Random Structures & Algorithms* 22(1), 60–65.

## Status

-- STAGING: pending Mathlib PR targeting Mathlib.Analysis.SpecialFunctions.Log.Inequalities
-- Retire this file once the PR is merged into Mathlib.
-/

namespace Real

/-- **Log upper bound**: `log(1+ε) ≤ ε − ε²/4` for `ε ∈ (−1, 1]`.

The proof defines `g(e) = e − e²/4 − log(1+e)`, notes `g(0) = 0`, and
uses the sign of `g'(e) = e(1−e)/(2(1+e))` to establish monotonicity on
each sign interval.

**STATUS:** staging for `Mathlib.Analysis.SpecialFunctions.Log.Inequalities`.
Retire once merged into Mathlib. -/
lemma log_one_add_le {ε : ℝ} (hε : -1 < ε) (hε1 : ε ≤ 1) :
    Real.log (1 + ε) ≤ ε - ε ^ 2 / 4 := by
  -- g(e) = e - e²/4 - log(1+e).  g(0)=0, g'(e)=e(1-e)/(2(1+e)).
  -- For e ≥ 0: g' ≥ 0 (nondecreasing from 0) → g(e) ≥ 0.
  -- For e < 0: g' < 0 on (ε,0) (antitone from ε to 0) → g(0)=0 ≤ g(ε).
  suffices h : 0 ≤ ε - ε ^ 2 / 4 - Real.log (1 + ε) by linarith
  set g := fun e : ℝ => e - e ^ 2 / 4 - Real.log (1 + e) with hg_def
  have hg0 : g 0 = 0 := by simp [hg_def]
  -- HasDerivAt for g at any e with 1+e > 0
  have hg_drv : ∀ e : ℝ, -1 < e →
      HasDerivAt g (e * (1 - e) / (2 * (1 + e))) e := fun e he => by
    have h1e : 0 < 1 + e := by linarith
    have hd1 : HasDerivAt (fun e => e) 1 e := hasDerivAt_id e
    have hd2 : HasDerivAt (fun e => e ^ 2 / 4) (2 * e / 4) e := by
      have h1 : HasDerivAt (fun e : ℝ => e ^ 2) (2 * e) e := by
        have h := hasDerivAt_pow 2 e
        simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
        exact h
      exact h1.div_const 4
    have hd3 : HasDerivAt (fun e => Real.log (1 + e)) (1 + e)⁻¹ e := by
      have h := (Real.hasDerivAt_log h1e.ne').comp e
        ((hasDerivAt_const e 1).add (hasDerivAt_id e))
      simpa [Function.comp, zero_add, mul_one] using h
    have hd := hd1.sub hd2 |>.sub hd3
    rwa [show 1 - 2 * e / 4 - (1 + e)⁻¹ = e * (1 - e) / (2 * (1 + e)) from by
      field_simp; ring] at hd
  by_cases hε_sign : 0 ≤ ε
  · -- Case ε ≥ 0: g nondecreasing on Icc 0 1 → g(ε) ≥ g(0) = 0
    have hmon : MonotoneOn g (Set.Icc 0 1) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
        (ContinuousOn.sub (ContinuousOn.sub continuous_id.continuousOn
          ((continuous_pow 2).div_const 4).continuousOn)
          (Real.continuousOn_log.comp (continuous_const.add continuous_id).continuousOn
            (fun e he => (show 0 < 1 + e by linarith [he.1]).ne')))
        (fun e he => by rw [interior_Icc] at he; exact (hg_drv e (by linarith [he.1])).hasDerivWithinAt)
        (fun e he => by
          rw [interior_Icc] at he
          exact div_nonneg (mul_nonneg he.1.le (by linarith [he.2])) (by linarith [he.1]))
    exact hg0 ▸ hmon (Set.left_mem_Icc.mpr (by norm_num)) (Set.mem_Icc.mpr ⟨hε_sign, hε1⟩) hε_sign
  · -- Case ε < 0: g antitone on Icc ε 0 → g(0)=0 ≤ g(ε)
    have hε_neg : ε < 0 := not_le.mp hε_sign
    have hamon : AntitoneOn g (Set.Icc ε 0) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc ε 0)
        (ContinuousOn.sub (ContinuousOn.sub continuous_id.continuousOn
          ((continuous_pow 2).div_const 4).continuousOn)
          (Real.continuousOn_log.comp (continuous_const.add continuous_id).continuousOn
            (fun e he => (show 0 < 1 + e by linarith [he.1, hε]).ne')))
        (fun e he => by rw [interior_Icc] at he; exact (hg_drv e (by linarith [he.1, hε])).hasDerivWithinAt)
        (fun e he => by
          rw [interior_Icc] at he
          exact div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg he.2.le (by linarith [he.2]))
            (by linarith [hε, he.1]))
    exact hg0 ▸ hamon (Set.left_mem_Icc.mpr hε_neg.le) (Set.right_mem_Icc.mpr hε_neg.le) hε_neg.le

/-- **Log upper bound**: `log(1−ε) ≤ −ε − ε²/4` for `ε ∈ [0, 1)`.

The proof defines `h(e) = −e − e²/4 − log(1−e)`, notes `h(0) = 0`, and
uses `h'(e) = e(1+e)/(2(1−e)) ≥ 0` to show `h` is nondecreasing on `[0, 1)`.

**STATUS:** staging for `Mathlib.Analysis.SpecialFunctions.Log.Inequalities`.
Retire once merged into Mathlib. -/
lemma log_one_sub_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Real.log (1 - ε) ≤ -ε - ε ^ 2 / 4 := by
  -- h(e) = -e - e²/4 - log(1-e).  h(0)=0, h'(e)=e(1+e)/(2(1-e)) ≥ 0.
  -- So h is nondecreasing on [0,1) → h(e) ≥ h(0) = 0.
  suffices h : 0 ≤ -ε - ε ^ 2 / 4 - Real.log (1 - ε) by linarith
  set h := fun e : ℝ => -e - e ^ 2 / 4 - Real.log (1 - e) with hh_def
  have hh0 : h 0 = 0 := by simp [hh_def]
  have hh_drv : ∀ e : ℝ, e < 1 →
      HasDerivAt h (e * (1 + e) / (2 * (1 - e))) e := fun e he => by
    have h1e : 0 < 1 - e := by linarith
    have hd1 : HasDerivAt (fun e => -e) (-1 : ℝ) e := (hasDerivAt_id e).neg
    have hd2 : HasDerivAt (fun e => e ^ 2 / 4) (2 * e / 4) e := by
      have h1 : HasDerivAt (fun e : ℝ => e ^ 2) (2 * e) e := by
        have h := hasDerivAt_pow 2 e
        simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
        exact h
      exact h1.div_const 4
    have hd3 : HasDerivAt (fun e => Real.log (1 - e)) (-(1 - e)⁻¹) e := by
      have h' := (Real.hasDerivAt_log h1e.ne').comp e
        ((hasDerivAt_const e 1).sub (hasDerivAt_id e))
      simpa [Function.comp, zero_sub, mul_neg, mul_one] using h'
    have hd := hd1.sub hd2 |>.sub hd3
    rwa [show -1 - 2 * e / 4 - -(1 - e)⁻¹ = e * (1 + e) / (2 * (1 - e)) from by
      field_simp; ring] at hd
  have hmon : MonotoneOn h (Set.Ico 0 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (ContinuousOn.sub (ContinuousOn.sub continuous_neg.continuousOn
        ((continuous_pow 2).div_const 4).continuousOn)
        (Real.continuousOn_log.comp (continuous_const.sub continuous_id).continuousOn
          (fun e he => (show 0 < 1 - e by linarith [he.2]).ne')))
      (fun e he => by rw [interior_Ico] at he; exact (hh_drv e he.2).hasDerivWithinAt)
      (fun e he => by
        rw [interior_Ico] at he
        exact div_nonneg (mul_nonneg he.1.le (by linarith [he.1])) (by linarith [he.2]))
  exact hh0 ▸ hmon (Set.left_mem_Ico.mpr (by linarith)) (Set.mem_Ico.mpr ⟨hε0, hε1⟩) hε0

end Real
