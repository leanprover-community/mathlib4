/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.PeakFunction

/-! # Euler's infinite product for the sine function

This file proves the infinite product formula

$$ \sin \pi z = \pi z \prod_{n = 1}^\infty \left(1 - \frac{z ^ 2}{n ^ 2}\right) $$

for any real or complex `z`. Our proof closely follows the article
[Salwinski, *Euler's Sine Product Formula: An Elementary Proof*][salwinski2018]: the basic strategy
is to prove a recurrence relation for the integrals `∫ x in 0..π/2, cos 2 z x * cos x ^ (2 * n)`,
generalising the arguments used to prove Wallis' limit formula for `π`.
-/

open scoped Real Topology

open Real Set Filter intervalIntegral MeasureTheory.MeasureSpace

namespace EulerSine

section IntegralRecursion

/-! ## Recursion formula for the integral of `cos (2 * z * x) * cos x ^ n`

We evaluate the integral of `cos (2 * z * x) * cos x ^ n`, for any complex `z` and even integers
`n`, via repeated integration by parts. -/


variable {z : ℂ} {n : ℕ}

theorem antideriv_cos_comp_const_mul (hz : z ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.sin (2 * z * y) / (2 * z)) (Complex.cos (2 * z * x)) x := by
  have a : HasDerivAt (fun y : ℂ => y * (2 * z)) _ x := hasDerivAt_mul_const _
  have b : HasDerivAt (Complex.sin ∘ fun y : ℂ => (y * (2 * z))) _ x :=
    HasDerivAt.comp (x : ℂ) (Complex.hasDerivAt_sin (x * (2 * z))) a
  have c := b.comp_ofReal.div_const (2 * z)
  field_simp at c; simp only [mul_rotate _ 2 z] at c
  exact c

theorem antideriv_sin_comp_const_mul (hz : z ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -Complex.cos (2 * z * y) / (2 * z)) (Complex.sin (2 * z * x)) x := by
  have a : HasDerivAt (fun y : ℂ => y * (2 * z)) _ x := hasDerivAt_mul_const _
  have b : HasDerivAt (Complex.cos ∘ fun y : ℂ => (y * (2 * z))) _ x :=
    HasDerivAt.comp (x : ℂ) (Complex.hasDerivAt_cos (x * (2 * z))) a
  have c := (b.comp_ofReal.div_const (2 * z)).fun_neg
  simp at c ⊢; field_simp at c ⊢; simp only [mul_rotate _ 2 z] at c
  exact c

theorem integral_cos_mul_cos_pow_aux (hn : 2 ≤ n) (hz : z ≠ 0) :
    (∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ n) =
      n / (2 * z) *
        ∫ x in (0 : ℝ)..π / 2, Complex.sin (2 * z * x) * sin x * (cos x : ℂ) ^ (n - 1) := by
  have der1 :
    ∀ x : ℝ,
      x ∈ uIcc 0 (π / 2) →
        HasDerivAt (fun y : ℝ => (cos y : ℂ) ^ n) (-n * sin x * (cos x : ℂ) ^ (n - 1)) x := by
    intro x _
    have b : HasDerivAt (fun y : ℝ => (cos y : ℂ)) (-sin x) x := by
      simpa using (hasDerivAt_cos x).ofReal_comp
    convert HasDerivAt.comp x (hasDerivAt_pow _ _) b using 1
    ring
  convert (config := { sameFun := true })
    integral_mul_deriv_eq_deriv_mul der1 (fun x _ => antideriv_cos_comp_const_mul hz x) _ _ using 2
  · ext1 x; rw [mul_comm]
  · rw [Complex.ofReal_zero, mul_zero, Complex.sin_zero, zero_div, mul_zero, sub_zero,
      cos_pi_div_two, Complex.ofReal_zero, zero_pow (by positivity : n ≠ 0), zero_mul, zero_sub,
      ← integral_neg, ← integral_const_mul]
    refine integral_congr fun x _ => ?_
    field_simp
  · apply Continuous.intervalIntegrable
    exact
      (continuous_const.mul (Complex.continuous_ofReal.comp continuous_sin)).mul
        ((Complex.continuous_ofReal.comp continuous_cos).pow (n - 1))
  · apply Continuous.intervalIntegrable
    exact Complex.continuous_cos.comp (continuous_const.mul Complex.continuous_ofReal)

theorem integral_sin_mul_sin_mul_cos_pow_eq (hn : 2 ≤ n) (hz : z ≠ 0) :
    (∫ x in (0 : ℝ)..π / 2, Complex.sin (2 * z * x) * sin x * (cos x : ℂ) ^ (n - 1)) =
      (n / (2 * z) * ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ n) -
        (n - 1) / (2 * z) *
          ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (n - 2) := by
  have der1 :
    ∀ x : ℝ,
      x ∈ uIcc 0 (π / 2) →
        HasDerivAt (fun y : ℝ => sin y * (cos y : ℂ) ^ (n - 1))
          ((cos x : ℂ) ^ n - (n - 1) * (sin x : ℂ) ^ 2 * (cos x : ℂ) ^ (n - 2)) x := by
    intro x _
    have c := HasDerivAt.comp (x : ℂ) (hasDerivAt_pow (n - 1) _) (Complex.hasDerivAt_cos x)
    convert ((Complex.hasDerivAt_sin x).fun_mul c).comp_ofReal using 1
    · ext1 y; simp only [Complex.ofReal_sin, Complex.ofReal_cos, Function.comp]
    · simp only [Complex.ofReal_cos, Complex.ofReal_sin]
      rw [mul_neg, mul_neg, ← sub_eq_add_neg, Function.comp_apply]
      congr 1
      · rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]
      · have : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
          rw [Nat.cast_sub (one_le_two.trans hn), Nat.cast_one]
        rw [Nat.sub_sub, this]
        ring
  convert
    integral_mul_deriv_eq_deriv_mul der1 (fun x _ => antideriv_sin_comp_const_mul hz x) _ _ using 1
  · refine integral_congr fun x _ => ?_
    ring_nf
  · -- now a tedious rearrangement of terms
    -- gather into a single integral, and deal with continuity subgoals:
    rw [sin_zero, cos_pi_div_two, Complex.ofReal_zero, zero_pow, zero_mul,
      mul_zero, zero_mul, zero_mul, sub_zero, zero_sub, ←
      integral_neg, ← integral_const_mul, ← integral_const_mul, ← integral_sub]
    rotate_left
    · apply Continuous.intervalIntegrable
      exact
        continuous_const.mul
          ((Complex.continuous_cos.comp (continuous_const.mul Complex.continuous_ofReal)).mul
            ((Complex.continuous_ofReal.comp continuous_cos).pow n))
    · apply Continuous.intervalIntegrable
      exact
        continuous_const.mul
          ((Complex.continuous_cos.comp (continuous_const.mul Complex.continuous_ofReal)).mul
            ((Complex.continuous_ofReal.comp continuous_cos).pow (n - 2)))
    · exact Nat.sub_ne_zero_of_lt hn
    refine integral_congr fun x _ => ?_
    dsimp only
    -- get rid of real trig functions and divisions by 2 * z:
    rw [Complex.ofReal_cos, Complex.ofReal_sin, Complex.sin_sq, ← mul_div_right_comm, ←
      mul_div_right_comm, ← sub_div, mul_div, ← neg_div]
    congr 1
    have : Complex.cos x ^ n = Complex.cos x ^ (n - 2) * Complex.cos x ^ 2 := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, pow_add]
    rw [this]
    ring
  · apply Continuous.intervalIntegrable
    exact
      ((Complex.continuous_ofReal.comp continuous_cos).pow n).sub
        ((continuous_const.mul ((Complex.continuous_ofReal.comp continuous_sin).pow 2)).mul
          ((Complex.continuous_ofReal.comp continuous_cos).pow (n - 2)))
  · apply Continuous.intervalIntegrable
    exact Complex.continuous_sin.comp (continuous_const.mul Complex.continuous_ofReal)

/-- Note this also holds for `z = 0`, but we do not need this case for `sin_pi_mul_eq`. -/
theorem integral_cos_mul_cos_pow (hn : 2 ≤ n) (hz : z ≠ 0) :
    (((1 : ℂ) - (4 : ℂ) * z ^ 2 / (n : ℂ) ^ 2) *
      ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ n) =
      (n - 1 : ℂ) / n *
        ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (n - 2) := by
  have nne : (n : ℂ) ≠ 0 := by
    contrapose! hn; rw [Nat.cast_eq_zero] at hn; rw [hn]; exact zero_lt_two
  have := integral_cos_mul_cos_pow_aux hn hz
  rw [integral_sin_mul_sin_mul_cos_pow_eq hn hz, sub_eq_neg_add, mul_add, ← sub_eq_iff_eq_add]
    at this
  convert congr_arg (fun u : ℂ => -u * (2 * z) ^ 2 / n ^ 2) this using 1 <;> field_simp; ring

/-- Note this also holds for `z = 0`, but we do not need this case for `sin_pi_mul_eq`. -/
theorem integral_cos_mul_cos_pow_even (n : ℕ) (hz : z ≠ 0) :
    (((1 : ℂ) - z ^ 2 / ((n : ℂ) + 1) ^ 2) *
        ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n + 2)) =
      (2 * n + 1 : ℂ) / (2 * n + 2) *
        ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n) := by
  convert integral_cos_mul_cos_pow (by omega : 2 ≤ 2 * n + 2) hz using 3
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_two]
    nth_rw 2 [← mul_one (2 : ℂ)]
    rw [← mul_add, mul_pow, ← div_div]
    ring
  · push_cast; ring
  · push_cast; ring

/-- Relate the integral `cos x ^ n` over `[0, π/2]` to the integral of `sin x ^ n` over `[0, π]`,
which is studied in `Data.Real.Pi.Wallis` and other places. -/
theorem integral_cos_pow_eq (n : ℕ) :
    (∫ x in (0 : ℝ)..π / 2, cos x ^ n) = 1 / 2 * ∫ x in (0 : ℝ)..π, sin x ^ n := by
  rw [mul_comm (1 / 2 : ℝ), ← div_eq_iff (one_div_ne_zero (two_ne_zero' ℝ)), ← div_mul, div_one,
    mul_two]
  have L : IntervalIntegrable _ volume 0 (π / 2) := (continuous_sin.pow n).intervalIntegrable _ _
  have R : IntervalIntegrable _ volume (π / 2) π := (continuous_sin.pow n).intervalIntegrable _ _
  rw [← integral_add_adjacent_intervals L R]
  congr 1
  · nth_rw 1 [(by ring : 0 = π / 2 - π / 2)]
    nth_rw 3 [(by ring : π / 2 = π / 2 - 0)]
    rw [← integral_comp_sub_left]
    refine integral_congr fun x _ => ?_
    rw [cos_pi_div_two_sub]
  · nth_rw 3 [(by ring : π = π / 2 + π / 2)]
    nth_rw 2 [(by ring : π / 2 = 0 + π / 2)]
    rw [← integral_comp_add_right]
    refine integral_congr fun x _ => ?_
    rw [sin_add_pi_div_two]

theorem integral_cos_pow_pos (n : ℕ) : 0 < ∫ x in (0 : ℝ)..π / 2, cos x ^ n :=
  (integral_cos_pow_eq n).symm ▸ mul_pos one_half_pos (integral_sin_pow_pos _)

/-- Finite form of Euler's sine product, with remainder term expressed as a ratio of cosine
integrals. -/
theorem sin_pi_mul_eq (z : ℂ) (n : ℕ) :
    Complex.sin (π * z) =
      ((π * z * ∏ j ∈ Finset.range n, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2)) *
          ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n)) /
        (∫ x in (0 : ℝ)..π / 2, cos x ^ (2 * n) : ℝ) := by
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp
  induction' n with n hn
  · simp_rw [mul_zero, pow_zero, mul_one, Finset.prod_range_zero, mul_one,
      integral_one, sub_zero]
    rw [integral_cos_mul_complex (mul_ne_zero two_ne_zero hz), Complex.ofReal_zero,
      mul_zero, Complex.sin_zero, zero_div, sub_zero,
      (by push_cast; field_simp : 2 * z * ↑(π / 2) = π * z)]
    simp [field]
  · rw [hn, Finset.prod_range_succ]
    set A := ∏ j ∈ Finset.range n, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2)
    set B := ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n)
    set C := ∫ x in (0 : ℝ)..π / 2, cos x ^ (2 * n)
    have aux' : 2 * n.succ = 2 * n + 2 := by rw [Nat.succ_eq_add_one, mul_add, mul_one]
    have : (∫ x in (0 : ℝ)..π / 2, cos x ^ (2 * n.succ)) = (2 * (n : ℝ) + 1) / (2 * n + 2) * C := by
      rw [integral_cos_pow_eq]
      dsimp only [C]
      rw [integral_cos_pow_eq, aux', integral_sin_pow, sin_zero, sin_pi, pow_succ',
        zero_mul, zero_mul, zero_mul, sub_zero, zero_div,
        zero_add, ← mul_assoc, ← mul_assoc, mul_comm (1 / 2 : ℝ) _, Nat.cast_mul, Nat.cast_ofNat]
    rw [this]
    change
      π * z * A * B / C =
        (π * z * (A * ((1 : ℂ) - z ^ 2 / ((n : ℂ) + 1) ^ 2)) *
            ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n.succ)) /
          ((2 * n + 1) / (2 * n + 2) * C : ℝ)
    have :
      (π * z * (A * ((1 : ℂ) - z ^ 2 / ((n : ℂ) + 1) ^ 2)) *
          ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n.succ)) =
        π * z * A *
          (((1 : ℂ) - z ^ 2 / (n.succ : ℂ) ^ 2) *
            ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n.succ)) := by
      nth_rw 2 [Nat.succ_eq_add_one]
      rw [Nat.cast_add_one]
      ring
    rw [this]
    suffices
      (((1 : ℂ) - z ^ 2 / (n.succ : ℂ) ^ 2) *
          ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n.succ)) =
        (2 * n + 1) / (2 * n + 2) * B by
      rw [this, Complex.ofReal_mul, Complex.ofReal_div]
      have : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (integral_cos_pow_pos _).ne'
      have : 2 * (n : ℂ) + 1 ≠ 0 := by
        convert (Nat.cast_add_one_ne_zero (2 * n) : (↑(2 * n) + 1 : ℂ) ≠ 0)
        simp
      have : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
      simp [field]
    convert integral_cos_mul_cos_pow_even n hz
    rw [Nat.cast_succ]

end IntegralRecursion

/-! ## Conclusion of the proof

The main theorem `Complex.tendsto_euler_sin_prod`, and its real variant
`Real.tendsto_euler_sin_prod`, now follow by combining `sin_pi_mul_eq` with a lemma
stating that the sequence of measures on `[0, π/2]` given by integration against `cos x ^ n`
(suitably normalised) tends to the Dirac measure at 0, as a special case of the general result
`tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`. -/


theorem tendsto_integral_cos_pow_mul_div {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 (π / 2))) :
    Tendsto
      (fun n : ℕ => (∫ x in (0 : ℝ)..π / 2, (cos x : ℂ) ^ n * f x) /
        (∫ x in (0 : ℝ)..π / 2, cos x ^ n : ℝ))
      atTop (𝓝 <| f 0) := by
  simp_rw [div_eq_inv_mul (α := ℂ), ← Complex.ofReal_inv, integral_of_le pi_div_two_pos.le,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← Complex.ofReal_pow, ← Complex.real_smul]
  have c_lt : ∀ y : ℝ, y ∈ Icc 0 (π / 2) → y ≠ 0 → cos y < cos 0 := fun y hy hy' =>
    cos_lt_cos_of_nonneg_of_le_pi_div_two (le_refl 0) hy.2 (lt_of_le_of_ne hy.1 hy'.symm)
  have c_nonneg : ∀ x : ℝ, x ∈ Icc 0 (π / 2) → 0 ≤ cos x := fun x hx =>
    cos_nonneg_of_mem_Icc ((Icc_subset_Icc_left (neg_nonpos_of_nonneg pi_div_two_pos.le)) hx)
  have c_zero_pos : 0 < cos 0 := by rw [cos_zero]; exact zero_lt_one
  have zero_mem : (0 : ℝ) ∈ closure (interior (Icc 0 (π / 2))) := by
    rw [interior_Icc, closure_Ioo pi_div_two_pos.ne, left_mem_Icc]
    exact pi_div_two_pos.le
  exact
    tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn isCompact_Icc
      continuousOn_cos c_lt c_nonneg c_zero_pos zero_mem hf

/-- Euler's infinite product formula for the complex sine function. -/
theorem _root_.Complex.tendsto_euler_sin_prod (z : ℂ) :
    Tendsto (fun n : ℕ => π * z * ∏ j ∈ Finset.range n, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2))
      atTop (𝓝 <| Complex.sin (π * z)) := by
  have A :
    Tendsto
      (fun n : ℕ =>
        ((π * z * ∏ j ∈ Finset.range n, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2)) *
            ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n)) /
          (∫ x in (0 : ℝ)..π / 2, cos x ^ (2 * n) : ℝ))
      atTop (𝓝 <| _) :=
    Tendsto.congr (fun n => sin_pi_mul_eq z n) tendsto_const_nhds
  have : 𝓝 (Complex.sin (π * z)) = 𝓝 (Complex.sin (π * z) * 1) := by rw [mul_one]
  simp_rw [this, mul_div_assoc] at A
  convert (tendsto_mul_iff_of_ne_zero _ one_ne_zero).mp A
  suffices Tendsto (fun n : ℕ =>
        (∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ n) /
          (∫ x in (0 : ℝ)..π / 2, cos x ^ n : ℝ)) atTop (𝓝 1) from
    this.comp (tendsto_id.const_mul_atTop' zero_lt_two)
  have : ContinuousOn (fun x : ℝ => Complex.cos (2 * z * x)) (Icc 0 (π / 2)) :=
    (Complex.continuous_cos.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  convert tendsto_integral_cos_pow_mul_div this using 1
  · ext1 n; congr 2 with x : 1; rw [mul_comm]
  · rw [Complex.ofReal_zero, mul_zero, Complex.cos_zero]

/-- Euler's infinite product formula for the real sine function. -/
theorem _root_.Real.tendsto_euler_sin_prod (x : ℝ) :
    Tendsto (fun n : ℕ => π * x * ∏ j ∈ Finset.range n, ((1 : ℝ) - x ^ 2 / ((j : ℝ) + 1) ^ 2))
      atTop (𝓝 <| sin (π * x)) := by
  convert (Complex.continuous_re.tendsto _).comp (Complex.tendsto_euler_sin_prod x) using 1
  · ext1 n
    rw [Function.comp_apply, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    suffices
      (∏ j ∈ Finset.range n, (1 - x ^ 2 / (j + 1) ^ 2) : ℂ) =
        (∏ j ∈ Finset.range n, (1 - x ^ 2 / (j + 1) ^ 2) : ℝ) by
      rw [this, Complex.ofReal_re]
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr (by rfl) fun n _ => ?_
    norm_cast
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_sin, Complex.ofReal_re]

end EulerSine
