/-
Copyright (c) 2026 rytjy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rytjy
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic

/-!
# Wilson score interval

The Wilson score interval is the standard small-sample confidence interval for a
binomial proportion.  For `x` successes in `n` trials and critical value `z` it is
the interval with centre `(x + z²/2) / (n + z²)` and half-width
`z √(x(n−x)/n + z²/4) / (n + z²)`.

This file defines the centre and half-width, shows that the centre lies in `[0, 1]`,
that the endpoints are ordered, and that the sample proportion `x / n` always lies
inside the interval.

## Main results

* `wilsonCenter_mem_Icc`
* `wilsonLo_le_wilsonHi`, `wilsonHi_nonneg`, `wilsonLo_le_one`
* `wilson_contains`

## References

* E. B. Wilson, *Probable inference, the law of succession, and statistical
  inference*, J. Amer. Statist. Assoc. 22 (1927), 209–212.
-/

namespace ProbabilityTheory

/-- Wilson score interval centre for `x` successes in `n` trials, critical value `z`. -/
noncomputable def wilsonCenter (n x : ℕ) (z : ℝ) : ℝ :=
  ((x : ℝ) + z ^ 2 / 2) / ((n : ℝ) + z ^ 2)

/-- Wilson score interval half-width. -/
noncomputable def wilsonHalf (n x : ℕ) (z : ℝ) : ℝ :=
  z * Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) /
    ((n : ℝ) + z ^ 2)

/-- Lower endpoint of the Wilson score interval. -/
noncomputable def wilsonLo (n x : ℕ) (z : ℝ) : ℝ :=
  wilsonCenter n x z - wilsonHalf n x z

/-- Upper endpoint of the Wilson score interval. -/
noncomputable def wilsonHi (n x : ℕ) (z : ℝ) : ℝ :=
  wilsonCenter n x z + wilsonHalf n x z

theorem wilsonCenter_mem_Icc (n x : ℕ) (z : ℝ) (hx : x ≤ n) (hn : 0 < n) :
    0 ≤ wilsonCenter n x z ∧ wilsonCenter n x z ≤ 1 := by
  have hx' : (x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx
  have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · have hden : (0 : ℝ) < (n : ℝ) + z ^ 2 := by positivity
    rw [wilsonCenter, div_le_one hden]
    nlinarith

theorem wilsonHalf_nonneg (n x : ℕ) (z : ℝ) (hz : 0 ≤ z) (hx : x ≤ n) (hn : 0 < n) :
    0 ≤ wilsonHalf n x z := by
  have hx' : (x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hxn : (0 : ℝ) ≤ (n : ℝ) - (x : ℝ) := by linarith
  have hxz : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hprod : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) := mul_nonneg hxz hxn
  have hdiv : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) :=
    div_nonneg hprod (le_of_lt hn')
  have hz4 : (0 : ℝ) ≤ z ^ 2 / 4 := by positivity
  have hrad : (0 : ℝ) ≤
      (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4 := add_nonneg hdiv hz4
  have hsqrt : (0 : ℝ) ≤ Real.sqrt
      ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) := Real.sqrt_nonneg _
  have hmul : (0 : ℝ) ≤ z * Real.sqrt
      ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) := mul_nonneg hz hsqrt
  exact div_nonneg hmul (by positivity)

theorem wilsonLo_le_wilsonHi (n x : ℕ) (z : ℝ) (hz : 0 ≤ z) (hx : x ≤ n) (hn : 0 < n) :
    wilsonLo n x z ≤ wilsonHi n x z := by
  have h := wilsonHalf_nonneg n x z hz hx hn
  unfold wilsonLo wilsonHi
  linarith

theorem wilsonHi_nonneg (n x : ℕ) (z : ℝ) (hz : 0 ≤ z) (hx : x ≤ n) (hn : 0 < n) :
    0 ≤ wilsonHi n x z := by
  have hc := (wilsonCenter_mem_Icc n x z hx hn).1
  have h := wilsonHalf_nonneg n x z hz hx hn
  unfold wilsonHi
  linarith

theorem wilsonLo_le_one (n x : ℕ) (z : ℝ) (hz : 0 ≤ z) (hx : x ≤ n) (hn : 0 < n) :
    wilsonLo n x z ≤ 1 := by
  have hc := (wilsonCenter_mem_Icc n x z hx hn).2
  have h := wilsonHalf_nonneg n x z hz hx hn
  unfold wilsonLo
  linarith

theorem wilson_sq_gap (n x : ℕ) (z : ℝ) (hx : x ≤ n) (hn : 0 < n) :
    ((x : ℝ) / (n : ℝ) - wilsonCenter n x z) ^ 2 ≤ (wilsonHalf n x z) ^ 2 := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk : (0 : ℝ) < (n : ℝ) + z ^ 2 := by positivity
  have hx' : (x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hNp : (0 : ℝ) ≤ (n : ℝ) - (x : ℝ) := by linarith
  have hprod : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) := mul_nonneg hx0 hNp
  have hΔ : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4 := by
    have h1 : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) := div_nonneg hprod hN.le
    nlinarith [sq_nonneg z]
  have hleft : ((x : ℝ) / (n : ℝ) - wilsonCenter n x z) ^ 2
      = (z ^ 2 * ((x : ℝ) - (n : ℝ) / 2)) ^ 2 /
        ((n : ℝ) ^ 2 * ((n : ℝ) + z ^ 2) ^ 2) := by
    unfold wilsonCenter
    field_simp
    ring
  have hright : (wilsonHalf n x z) ^ 2
      = z ^ 2 * ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) /
        ((n : ℝ) + z ^ 2) ^ 2 := by
    unfold wilsonHalf
    rw [div_pow, mul_pow, Real.sq_sqrt hΔ]
  rw [hleft, hright]
  have hkey : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) * ((n : ℝ) + z ^ 2) :=
    mul_nonneg hprod hk.le
  field_simp
  nlinarith [hkey, hprod, sq_nonneg z]

/-- The sample proportion lies inside the Wilson score interval. -/
theorem wilson_contains (n x : ℕ) (z : ℝ) (hz : 0 ≤ z) (hx : x ≤ n) (hn : 0 < n) :
    wilsonLo n x z ≤ (x : ℝ) / (n : ℝ) ∧ (x : ℝ) / (n : ℝ) ≤ wilsonHi n x z := by
  have hsq := wilson_sq_gap n x z hx hn
  have hh := wilsonHalf_nonneg n x z hz hx hn
  have habs : |(x : ℝ) / (n : ℝ) - wilsonCenter n x z| ≤ wilsonHalf n x z :=
    abs_le_of_sq_le_sq hsq hh
  have hb := abs_le.mp habs
  constructor
  · unfold wilsonLo
    linarith [hb.1]
  · unfold wilsonHi
    linarith [hb.2]


/-- The lower Wilson endpoint is nonnegative: the interval never leaves `[0, 1]` below. -/
theorem wilsonLo_nonneg (n x : ℕ) (z : ℝ) (hx : x ≤ n) (hn : 0 < n) :
    0 ≤ wilsonLo n x z := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk : (0 : ℝ) < (n : ℝ) + z ^ 2 := by positivity
  have hx' : (x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hNp : (0 : ℝ) ≤ (n : ℝ) - (x : ℝ) := by linarith
  have hprod : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) := mul_nonneg hx0 hNp
  have hΔ : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4 := by
    have h1 : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) := div_nonneg hprod hN.le
    nlinarith [sq_nonneg z]
  have hsq : z ^ 2 * ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4)
      ≤ ((x : ℝ) + z ^ 2 / 2) ^ 2 := by
    have hkey : (0 : ℝ) ≤ (x : ℝ) ^ 2 * ((n : ℝ) + z ^ 2) :=
      mul_nonneg (sq_nonneg _) hk.le
    field_simp
    nlinarith [hkey]
  have hle : z * Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4)
      ≤ (x : ℝ) + z ^ 2 / 2 := by
    have hs : (z * Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4)) ^ 2
        ≤ ((x : ℝ) + z ^ 2 / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hΔ]
      exact hsq
    have habs := (sq_le_sq).mp hs
    rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at habs
  unfold wilsonLo wilsonCenter wilsonHalf
  exact div_nonneg (by linarith) hk.le

/-- The upper Wilson endpoint is at most one. -/
theorem wilsonHi_le_one (n x : ℕ) (z : ℝ) (hx : x ≤ n) (hn : 0 < n) :
    wilsonHi n x z ≤ 1 := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk : (0 : ℝ) < (n : ℝ) + z ^ 2 := by positivity
  have hx' : (x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hNp : (0 : ℝ) ≤ (n : ℝ) - (x : ℝ) := by linarith
  have hprod : (0 : ℝ) ≤ ((n : ℝ) - (x : ℝ)) * (x : ℝ) := mul_nonneg hNp hx0
  have hΔ : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4 := by
    have h1 : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) :=
      div_nonneg (mul_nonneg hx0 hNp) hN.le
    nlinarith [sq_nonneg z]
  have hsq : z ^ 2 * ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4)
      ≤ (((n : ℝ) - (x : ℝ)) + z ^ 2 / 2) ^ 2 := by
    have hkey : (0 : ℝ) ≤ ((n : ℝ) - (x : ℝ)) ^ 2 * ((n : ℝ) + z ^ 2) :=
      mul_nonneg (sq_nonneg _) hk.le
    field_simp
    nlinarith [hkey]
  have hle : z * Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4)
      ≤ ((n : ℝ) - (x : ℝ)) + z ^ 2 / 2 := by
    have hs : (z * Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4)) ^ 2
        ≤ (((n : ℝ) - (x : ℝ)) + z ^ 2 / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hΔ]
      exact hsq
    have habs := (sq_le_sq).mp hs
    rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at habs
  unfold wilsonHi wilsonCenter wilsonHalf
  rw [div_le_one hk]
  linarith

end ProbabilityTheory
