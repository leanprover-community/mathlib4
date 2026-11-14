/-
Copyright (c) 2026 darkhipo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: darkhipo
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Quantitative decay of Fourier coefficients from strip analyticity

If `g : ℂ → ℂ` is holomorphic on the horizontal strip `{z | |z.im| < a}`, `T`-periodic
there, and bounded there by `M`, then the Fourier coefficients of the induced function
`f : AddCircle T → ℂ` (agreeing with `g` on the real axis) decay geometrically in the
frequency:

`‖fourierCoeff f k‖ ≤ M * exp (- 2 * π * a * |k| / T)`,

the classical Cauchy estimate for Fourier coefficients of functions analytic in a strip
(Katznelson, *An Introduction to Harmonic Analysis*; cf. Kahane, *Some Random Series of
Functions*, 2nd ed., 1985; Trefethen & Weideman, SIAM Rev. 56 (2014) for the numerical
corollary).

The route is elementary and avoids annulus/Laurent machinery: the integral of a periodic
holomorphic function over one period is invariant under vertical shifts within the strip
(`integral_eq_shift_of_periodic_of_differentiableOn`) — on the rectangle
`uIcc 0 T ×ℂ uIcc 0 s` the two vertical sides cancel by periodicity
(`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`).  Shifting the contour to
height `s` therefore scales the `k`-th coefficient by a factor of modulus
`exp (2 * π * k * s / T)` (`norm_fourierCoeff_le_of_shift`).  Optimizing over `|s| < a`
is an *endpoint passage* (`le_of_tendsto_of_tendsto`), not a substitution: `e ^ (k * s)`
is not bounded by its value at the strip edge at any interior `s`.

## Main declarations

* `integral_eq_shift_of_periodic_of_differentiableOn`: period integrals of a periodic
  holomorphic function are invariant under vertical shifts whose rectangle lies in the
  domain of holomorphy.
* `norm_fourierCoeff_le_of_shift`: the coefficient bound at a fixed vertical shift `s`.
* `norm_fourierCoeff_le_of_strip`: `‖fourierCoeff f k‖ ≤ M * exp (- 2 * π * a * |k| / T)`.
-/

open Complex intervalIntegral Real Filter

variable {T : ℝ} [hT : Fact (0 < T)]

/-- On `uIcc 0 s` the modulus is controlled by `|s|`. Auxiliary lemma. -/
private theorem abs_le_abs_of_mem_uIcc' {s y : ℝ} (hy : y ∈ Set.uIcc (0 : ℝ) s) :
    |y| ≤ |s| := by
  rcases le_total (0 : ℝ) s with h | h
  · rw [Set.uIcc_of_le h] at hy
    rw [abs_of_nonneg h]
    exact (abs_le).mpr ⟨by linarith [hy.1], hy.2⟩
  · rw [Set.uIcc_of_ge h] at hy
    rw [abs_of_nonpos h]
    exact (abs_le).mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- A value dominated by `c * exp (e * s)` at *every* interior point of `(-b, b)` is
dominated at the right endpoint: the endpoint is a limit, not a substitution. -/
private theorem le_mul_exp_of_forall_abs_lt {b c e C : ℝ} (hb : 0 < b)
    (h : ∀ s : ℝ, |s| < b → C ≤ c * Real.exp (e * s)) : C ≤ c * Real.exp (e * b) := by
  have htend : Filter.Tendsto (fun s : ℝ => c * Real.exp (e * s))
      (nhdsWithin b (Set.Iio b)) (nhds (c * Real.exp (e * b))) :=
    (ContinuousAt.tendsto (h := by fun_prop)).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto tendsto_const_nhds htend ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith : (-b : ℝ) < b))] with s hs1 hs2
  exact h s (by rw [abs_lt]; exact ⟨hs2, hs1⟩)

public section

omit hT in
/-- **Invariance of period integrals under vertical shifts.**  If `g` is holomorphic on
`U` and `T`-periodic there, then its integral along `[0, T]` is unchanged by shifting the
contour up (or down) by `s`, as long as the closed rectangle `uIcc 0 T ×ℂ uIcc 0 s` stays
inside `U`: Cauchy's theorem on the rectangle makes the two vertical sides cancel by
periodicity. -/
theorem integral_eq_shift_of_periodic_of_differentiableOn {g : ℂ → ℂ} {U : Set ℂ}
    (hg : DifferentiableOn ℂ g U) (hper : ∀ z ∈ U, g (z + T) = g z)
    {s : ℝ} (hs : Set.uIcc (0 : ℝ) T ×ℂ Set.uIcc (0 : ℝ) s ⊆ U) :
    ∫ x in (0 : ℝ)..T, g ((x : ℂ))
      = ∫ x in (0 : ℝ)..T, g ((x : ℂ) + (s : ℂ) * Complex.I) := by
  classical
  -- the closed rectangle of the shift sits in `U`, so `g` is holomorphic on it
  have hgrect : DifferentiableOn ℂ g (Set.uIcc (0 : ℝ) T ×ℂ Set.uIcc (0 : ℝ) s) := hg.mono hs
  -- Cauchy–Goursat on the rectangle with corners `0` and `T + s * I`
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g (0 : ℂ)
    ((T : ℂ) + (s : ℂ) * Complex.I) (by simpa using hgrect)
  have hrect' : (∫ x : ℝ in (0:ℝ)..T, g ((x:ℂ)))
      - (∫ x : ℝ in (0:ℝ)..T, g ((x:ℂ) + (s:ℂ) * Complex.I))
      + Complex.I • (∫ y : ℝ in (0:ℝ)..s, g ((T:ℂ) + (y:ℂ) * Complex.I))
      - Complex.I • (∫ y : ℝ in (0:ℝ)..s, g ((y:ℂ) * Complex.I)) = 0 := by
    simpa [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] using hrect
  -- the vertical sides coincide by periodicity
  have hvert : ∀ y ∈ Set.uIcc (0 : ℝ) s,
      g ((T : ℂ) + (y : ℂ) * Complex.I) = g ((y : ℂ) * Complex.I) := by
    intro y hy
    have hre : ((y : ℂ) * Complex.I).re = 0 := by simp
    have him : ((y : ℂ) * Complex.I).im = y := by simp
    have hyin : ((y : ℂ) * Complex.I) ∈ Set.uIcc (0 : ℝ) T ×ℂ Set.uIcc (0 : ℝ) s := by
      rw [Complex.mem_reProdIm, hre, him]
      exact ⟨Set.left_mem_uIcc, hy⟩
    rw [add_comm (T : ℂ) ((y : ℂ) * Complex.I)]
    exact hper ((y : ℂ) * Complex.I) (hs hyin)
  have hvert_int : ∫ y in (0 : ℝ)..s, g ((T : ℂ) + (y : ℂ) * Complex.I)
      = ∫ y in (0 : ℝ)..s, g ((y : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr (fun y hy => hvert y hy)
  rw [hvert_int] at hrect'
  linear_combination (norm := module) hrect'

/-- **The coefficient bound at a fixed shift.**  Under the strip hypotheses, shifting the
contour to height `s` scales the `k`-th Fourier coefficient by a factor of modulus
`exp (2 * π * k * s / T)`, so `‖fourierCoeff f k‖ ≤ M * exp (2 * π * k * s / T)` for
every `|s| < a`.  (The endpoint optimization over `s` is `norm_fourierCoeff_le_of_strip`.) -/
theorem norm_fourierCoeff_le_of_shift {f : AddCircle T → ℂ} {g : ℂ → ℂ} {M a : ℝ}
    (hg : DifferentiableOn ℂ g {z : ℂ | |z.im| < a})
    (hgb : ∀ z ∈ {z : ℂ | |z.im| < a}, ‖g z‖ ≤ M)
    (hper : ∀ z : ℂ, |z.im| < a → g (z + T) = g z)
    (hf : ∀ x : ℝ, f ((x : ℝ) : AddCircle T) = g ((x : ℂ)))
    {s : ℝ} (hs : |s| < a) (k : ℤ) :
    ‖fourierCoeff f k‖ ≤ M * Real.exp (2 * π * k * s / T) := by
  classical
  have hTne : (T : ℝ) ≠ 0 := hT.out.ne'
  have h1T : (0 : ℝ) ≤ 1 / T := one_div_nonneg.mpr hT.out.le
  -- the shifted integrand `H z = exp (2 * π * I * (-k) * z / T) * g z`
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, ∀ z : ℂ, H z =
      Complex.exp (2 * π * Complex.I * ((-k : ℤ) : ℂ) * z / (T : ℂ)) * g z :=
    ⟨fun z => Complex.exp (2 * π * Complex.I * ((-k : ℤ) : ℂ) * z / (T : ℂ)) * g z,
      fun _ => rfl⟩
  -- `H` is holomorphic on the strip and `T`-periodic there
  have hHdiff : DifferentiableOn ℂ H {z : ℂ | |z.im| < a} := by
    have hHfun : H = fun z : ℂ =>
        Complex.exp (2 * π * Complex.I * ((-k : ℤ) : ℂ) * z / (T : ℂ)) * g z := funext hH
    rw [hHfun]
    have hlin : Differentiable ℂ
        (fun z : ℂ => 2 * π * Complex.I * ((-k : ℤ) : ℂ) * z / (T : ℂ)) := by
      fun_prop
    exact hlin.cexp.differentiableOn.mul hg
  have hTne : (T : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hT.out
  have hHper : ∀ z ∈ {z : ℂ | |z.im| < a}, H (z + T) = H z := by
    intro z hz
    rw [hH (z + T), hper z hz, hH z]
    have hsplit : 2 * π * Complex.I * ((-k : ℤ) : ℂ) * (z + T) / (T : ℂ)
        = 2 * π * Complex.I * ((-k : ℤ) : ℂ) * z / (T : ℂ)
          + ((-k : ℤ) : ℂ) * (2 * π * Complex.I) := by
      field_simp
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  -- the shift rectangle stays in the strip
  have hsub : Set.uIcc (0 : ℝ) T ×ℂ Set.uIcc (0 : ℝ) s ⊆ {z : ℂ | |z.im| < a} := by
    intro z hz
    have h1 : |z.im| ≤ |s| := abs_le_abs_of_mem_uIcc' hz.2
    have h2 : |z.im| < a := by linarith [abs_nonneg s]
    exact h2
  -- shift the contour, then bound the shifted integrand pointwise
  have hshift := integral_eq_shift_of_periodic_of_differentiableOn hHdiff hHper hsub
  have hpoint : ∀ x : ℝ, ‖H ((x : ℂ) + (s : ℂ) * Complex.I)‖
      ≤ M * Real.exp (2 * π * k * s / T) := by
    intro x
    rw [hH ((x : ℂ) + (s : ℂ) * Complex.I), norm_mul]
    have hmem : ((x : ℂ) + (s : ℂ) * Complex.I) ∈ {z : ℂ | |z.im| < a} := by
      have him : ((x : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
      simp only [Set.mem_ofPred_eq, him]
      exact hs
    have hgbd := hgb _ hmem
    have hexp : ‖Complex.exp (2 * π * Complex.I * ((-k : ℤ) : ℂ)
        * ((x : ℂ) + (s : ℂ) * Complex.I) / (T : ℂ))‖ = Real.exp (2 * π * k * s / T) := by
      rw [Complex.norm_exp]
      congr 1
      have hdiv : ∀ w : ℂ, (w / (T : ℂ)).re = w.re / (T : ℝ) := by
        intro w
        rw [div_eq_inv_mul, Complex.mul_re, Complex.inv_re, Complex.inv_im]
        simp [Complex.normSq]
        field_simp
      have h2re : (2 : ℂ).re = 2 := by
        have h : (2 : ℂ) = ((2 : ℝ) : ℂ) := rfl
        rw [h, Complex.ofReal_re]
      have h2im : (2 : ℂ).im = 0 := by
        have h : (2 : ℂ) = ((2 : ℝ) : ℂ) := rfl
        rw [h, Complex.ofReal_im]
      rw [hdiv]
      push_cast [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im,
        Complex.intCast_re, Complex.intCast_im]
      rw [h2re, h2im]
      field_simp
      ring
    rw [hexp]
    refine (mul_le_mul_of_nonneg_left hgbd (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have hint : ‖∫ x in (0 : ℝ)..T, H ((x : ℂ) + (s : ℂ) * Complex.I)‖
      ≤ (M * Real.exp (2 * π * k * s / T)) * T := by
    have hb := norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T)
      (C := M * Real.exp (2 * π * k * s / T))
      (f := fun x : ℝ => H ((x : ℂ) + (s : ℂ) * Complex.I))
      (fun x _ => hpoint x)
    rwa [sub_zero, abs_of_pos hT.out] at hb
  -- assemble: `fourierCoeff f k = (1 / T) • ∫ H ↑x`
  have hcoeffeq : fourierCoeff f k = (1 / (T : ℝ)) • (∫ x in (0 : ℝ)..T, H ((x : ℂ))) := by
    have hcoeff := fourierCoeff_eq_intervalIntegral f k (0 : ℝ)
    rw [hcoeff, zero_add]
    have hinteg : ∀ x : ℝ, (fourier (-k) ((x : ℝ) : AddCircle T)) • f ((x : ℝ) : AddCircle T)
        = H ((x : ℂ)) := by
      intro x
      rw [fourier_coe_apply, hf, smul_eq_mul, ← hH]
    congr 1
    refine intervalIntegral.integral_congr ?_
    exact fun x _ => hinteg x
  rw [hcoeffeq, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hT.out)]
  rw [hshift]
  calc (1 / T : ℝ) * ‖∫ x in (0 : ℝ)..T, H ((x : ℂ) + (s : ℂ) * Complex.I)‖
      ≤ (1 / T : ℝ) * ((M * Real.exp (2 * π * k * s / T)) * T) :=
        mul_le_mul_of_nonneg_left hint h1T
    _ = M * Real.exp (2 * π * k * s / T) := by field_simp

/-- **Geometric decay of Fourier coefficients from strip analyticity.**  If `g` is
holomorphic on the strip `{z | |z.im| < a}`, bounded there by `M`, and `T`-periodic
there, and `f : AddCircle T → ℂ` agrees with `g` on the real axis, then

`‖fourierCoeff f k‖ ≤ M * exp (- 2 * π * a * |k| / T)`.

The constant `M` is the strip supremum, taken as a hypothesis.  At `T = 2 * π` the decay
rate per unit frequency is `exp (- a)`. -/
theorem norm_fourierCoeff_le_of_strip {f : AddCircle T → ℂ} {g : ℂ → ℂ} {M a : ℝ}
    (ha : 0 < a)
    (hg : DifferentiableOn ℂ g {z : ℂ | |z.im| < a})
    (hgb : ∀ z ∈ {z : ℂ | |z.im| < a}, ‖g z‖ ≤ M)
    (hper : ∀ z : ℂ, |z.im| < a → g (z + T) = g z)
    (hf : ∀ x : ℝ, f ((x : ℝ) : AddCircle T) = g ((x : ℂ)))
    (k : ℤ) :
    ‖fourierCoeff f k‖ ≤ M * Real.exp (-(2 * π * a / T) * |(k : ℝ)|) := by
  have hbound : ∀ s : ℝ, |s| < a → ‖fourierCoeff f k‖ ≤ M * Real.exp ((2 * π * k / T) * s) := by
    intro s hsb
    have hb := norm_fourierCoeff_le_of_shift hg hgb hper hf hsb k
    rwa [show (2 * π * k * s / T : ℝ) = (2 * π * k / T) * s from by ring] at hb
  rcases lt_trichotomy k 0 with hlt | heq | hgt
  · -- `k < 0`: shift towards `+ a`
    have hkr : |(k : ℝ)| = -(k : ℝ) := by
      have hkneg : (k : ℝ) < 0 := by exact_mod_cast hlt
      rw [abs_of_neg hkneg]
    have hb := le_mul_exp_of_forall_abs_lt (b := a) (c := M) (e := 2 * π * k / T)
      (C := ‖fourierCoeff f k‖) ha hbound
    rw [hkr]
    have hex : (2 * π * k / T : ℝ) * a = -(2 * π * a / T) * -(k : ℝ) := by ring
    rw [hex] at hb
    exact hb
  · -- `k = 0`: shift by `s = 0`
    subst heq
    have hb := norm_fourierCoeff_le_of_shift hg hgb hper hf (s := (0 : ℝ)) (by simp [ha]) (0 : ℤ)
    simpa using hb
  · -- `k > 0`: shift towards `- a` via the substitution `s ↦ -s`
    have hkr : |(k : ℝ)| = (k : ℝ) := by
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hgt
      rw [abs_of_pos hkpos]
    have hsub' : ∀ s : ℝ, |s| < a → ‖fourierCoeff f k‖
        ≤ M * Real.exp ((-(2 * π * k / T)) * s) := by
      intro s hsb
      have hb := hbound (-s) (by rwa [abs_neg])
      rwa [mul_neg, ← neg_mul] at hb
    have hb := le_mul_exp_of_forall_abs_lt (b := a) (c := M) (e := -(2 * π * k / T))
      (C := ‖fourierCoeff f k‖) ha hsub'
    rw [hkr]
    have hex : (-(2 * π * k / T) : ℝ) * a = -(2 * π * a / T) * (k : ℝ) := by ring
    rw [hex] at hb
    exact hb

end
