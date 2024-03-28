/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.ZetaFunctions.KernelBounds
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-!
# Odd Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the analytic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`completedHurwitzZetaOdd a s = 1 / 2 * □ * ∑' n : ℤ, sgn (n + a) / |n + a| ^ s`

and

`completedSinZeta a s = □ * ∑' n : ℕ, sin (2 * π * a * n) / n ^ s`

where `□` denotes a Gamma factor. The term for `n = -a` in the first sum is understood as 0
if `a` is an integer, as is the term for `n = 0` in the second sum (for all `a`). Note that these
functions are differentiable everywhere, unlike their even counterparts which have poles.

Of course, we cannot *define* these functions by the above formulae (since existence of the
analytic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function.

## Main definitions and theorems

* `completedHurwitzZetaOdd`: the completed Hurwitz zeta function
* `completedSinZeta`: the completed cosine zeta function
* `differentiable_completedHurwitzZetaOdd` and `differentiable_completedSinZeta`:
  differentiability on `ℂ`
* `completedHurwitzZetaOdd_one_sub`: the functional equation
  `completedHurwitzZetaOdd a (1 - s) = completedSinZeta a s`
* [TODO] `completedHurwitzZetaOdd_eq_tsum_int` and `completedSinZeta_eq_tsum_nat`: relation between
  the zeta functions and corresponding Dirichlet series for `1 < re s`
-/

noncomputable section

open Complex hiding abs_of_nonneg
open Filter Topology Asymptotics Real Set MeasureTheory

section defs
/-!
## Definitions and elementary properties of kernels
-/

/-- Odd Hurwitz zeta kernel (function whose Mellin transform will be the odd part of the completed
Hurwitz zeta function). See `oddKernel_def` for the defining formula, and `hasSum_int_oddKernel`
for an expression as a sum over `ℤ`.
-/
@[irreducible] def oddKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun a : ℝ ↦ re (cexp (-π * a ^ 2 * x) *
    (jacobiTheta₂' (a * I * x) (I * x) / (2 * π * I) + a * jacobiTheta₂ (a * I * x) (I * x)))) 1 by
      intro a
      dsimp only
      rw [ofReal_add, ofReal_one, add_mul, one_mul, add_mul, jacobiTheta₂'_add_left',
        jacobiTheta₂_add_left']
      field_simp [pi_ne_zero]
      simp_rw [mul_add, mul_comm ((a : ℂ) + 1) _, ← mul_assoc, ← Complex.exp_add]
      ring_nf
      rw [I_sq]
      ring_nf).lift a

lemma oddKernel_def (a x : ℝ) : ↑(oddKernel ↑a x) = cexp (-π * a ^ 2 * x) *
    (jacobiTheta₂' (a * I * x) (I * x) / (2 * π * I) + a * jacobiTheta₂ (a * I * x) (I * x)) := by
  rw [oddKernel, Function.Periodic.lift_coe]
  simp only [neg_mul, re_eq_add_conj, map_mul, ← exp_conj, map_neg,
    conj_ofReal, map_pow, map_add, map_div₀, jacobiTheta₂'_conj, conj_I, mul_neg, neg_neg,
    jacobiTheta₂'_neg_left, map_ofNat, jacobiTheta₂_conj, jacobiTheta₂_neg_left]
  ring_nf

lemma hasSum_int_oddKernel (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℤ ↦ (n + a) * rexp (-π * (n + a) ^ 2 * x)) (oddKernel ↑a x) := by
  rw [← hasSum_ofReal, oddKernel_def a x]
  have h1 := hasSum_jacobiTheta₂_term (a * I * x) (by rwa [I_mul_im, ofReal_re] : 0 < im (I * x))
  have h2 := hasSum_jacobiTheta₂'_term (a * I * x) (by rwa [I_mul_im, ofReal_re] : 0 < im (I * x))
  convert ((h2.div_const (2 * π * I)).add (h1.mul_left ↑a)).mul_left _ using 2 with n
  rw [jacobiTheta₂'_term, mul_assoc (2 * π * I), mul_div_cancel_left₀, ← add_mul,
    ← mul_assoc, mul_comm _ (n + a : ℂ), mul_assoc (n + a : ℂ), jacobiTheta₂_term,
    ← Complex.exp_add]
  · push_cast
    ring_nf
    rw [I_sq]
    ring_nf
  · simpa only [mul_ne_zero_iff, ofReal_ne_zero] using ⟨⟨two_ne_zero, pi_ne_zero⟩, I_ne_zero⟩

lemma oddKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : oddKernel a x = 0 := by
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_eq_zero, oddKernel_def, jacobiTheta₂_undef, jacobiTheta₂'_undef, zero_div, zero_add,
    mul_zero, mul_zero] <;>
  rwa [I_mul_im, ofReal_re]

/-- Auxiliary function appearing in the functional equation for the odd Hurwitz zeta kernel, equal
to `∑ (n : ℕ), 2 * n * sin (2 * π * n * a) * exp (-π * n ^ 2 * x)`. See `hasSum_nat_sinKernel`
for the defining sum. -/
@[irreducible] def sinKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun ξ : ℝ ↦ re (jacobiTheta₂' ξ (I * x) / (-2 * π))) 1 by
    intro ξ; simp_rw [ofReal_add, ofReal_one, jacobiTheta₂'_add_left]).lift a

lemma sinKernel_def (a x : ℝ) : ↑(sinKernel ↑a x) = jacobiTheta₂' a (I * x) / (-2 * π) := by
  rw [sinKernel, Function.Periodic.lift_coe, re_eq_add_conj, map_div₀, jacobiTheta₂'_conj]
  simp_rw [map_mul, conj_I, conj_ofReal, map_neg, map_ofNat, neg_mul, neg_neg]
  ring

lemma hasSum_int_sinKernel (a : ℝ) {t : ℝ} (ht : 0 < t) : HasSum
    (fun n : ℤ ↦ -I * n * cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(sinKernel a t) := by
  rw [sinKernel_def]
  have := hasSum_jacobiTheta₂'_term a (by rwa [I_mul_im, ofReal_re])
  convert this.div_const _ using 2 with n
  rw [jacobiTheta₂'_term, jacobiTheta₂_term, ofReal_exp, mul_assoc (-I * n), ← Complex.exp_add]
  field_simp [pi_ne_zero]
  ring_nf
  rw [I_sq]
  ring_nf

lemma hasSum_nat_sinKernel (a : ℝ) {t : ℝ} (ht : 0 < t) : HasSum
    (fun n : ℕ ↦ 2 * n * Real.sin (2 * π * a * n) * rexp (-π * n ^ 2 * t))
    (sinKernel ↑a t) := by
  rw [← hasSum_ofReal]
  convert (hasSum_int_sinKernel a ht).sum_nat_of_sum_int using 2 with n
  · simp_rw [Int.cast_neg, neg_sq, mul_neg, ofReal_mul, Int.cast_ofNat, ofReal_nat_cast,
      ofReal_ofNat, ← add_mul, ofReal_sin, Complex.sin]
    push_cast
    ring_nf
  · simp

lemma sinKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : sinKernel a x = 0 := by
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_eq_zero, sinKernel_def, jacobiTheta₂'_undef, zero_div]
  rwa [I_mul_im, ofReal_re]

lemma oddKernel_neg (a : UnitAddCircle) (x : ℝ) :
    oddKernel (-a) x = -oddKernel a x := by
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_inj, ← QuotientAddGroup.mk_neg, oddKernel_def, ofReal_neg, ofReal_neg,
    oddKernel_def, neg_mul (a' : ℂ), neg_mul (a' : ℂ), neg_mul (a' * I),
    jacobiTheta₂_neg_left, jacobiTheta₂'_neg_left]
  ring_nf

lemma oddKernel_zero (x : ℝ) : oddKernel 0 x = 0 := by
  have := oddKernel_neg 0 x
  rwa [neg_zero, ← add_eq_zero_iff_eq_neg, ← two_mul, mul_eq_zero, eq_false_intro two_ne_zero,
    false_or] at this

lemma sinKernel_neg (a : UnitAddCircle) (x : ℝ) :
    sinKernel (-a) x = -sinKernel a x := by
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_inj, ← QuotientAddGroup.mk_neg, ofReal_neg, sinKernel_def, sinKernel_def, ofReal_neg,
    jacobiTheta₂'_neg_left, neg_div]

lemma sinKernel_zero (x : ℝ) : sinKernel 0 x = 0 := by
  have := sinKernel_neg 0 x
  rwa [neg_zero, ← add_eq_zero_iff_eq_neg, ← two_mul, mul_eq_zero, eq_false_intro two_ne_zero,
    false_or] at this

/-- The odd kernel is continuous on `Ioi 0`. -/
lemma continuousOn_oddKernel (a : UnitAddCircle) : ContinuousOn (oddKernel a) (Ioi 0) := by
  induction' a using QuotientAddGroup.induction_on' with a'
  change ContinuousOn (fun x ↦ re (oddKernel a' x : ℂ)) (Ioi 0)
  apply Complex.continuous_re.comp_continuousOn
  simp_rw [oddKernel_def a']
  refine fun x hx ↦ ((Continuous.continuousAt ?_).mul ?_).continuousWithinAt
  · exact Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal)
  · have hx' : 0 < im (I * x) := by rwa [I_mul_im, ofReal_re]
    have hf : Continuous fun u : ℝ ↦ (a' * I * u, I * u) := by continuity
    apply ContinuousAt.add
    · exact ((continuousAt_jacobiTheta₂' (a' * I * x) hx').comp
        (f := fun u : ℝ ↦ (a' * I * u, I * u)) hf.continuousAt).div_const _
    · exact continuousAt_const.mul <| (continuousAt_jacobiTheta₂ (a' * I * x) hx').comp
        (f := fun u : ℝ ↦ (a' * I * u, I * u)) hf.continuousAt

lemma continuousOn_sinKernel (a : UnitAddCircle) : ContinuousOn (sinKernel a) (Ioi 0) := by
  induction' a using QuotientAddGroup.induction_on' with a'
  change ContinuousOn (fun x ↦ re (sinKernel a' x : ℂ)) (Ioi 0)
  apply Complex.continuous_re.comp_continuousOn
  simp_rw [sinKernel_def]
  apply (ContinuousAt.continuousOn (fun x hx ↦ ?_)).div_const
  have h := continuousAt_jacobiTheta₂' a' (by rwa [I_mul_im, ofReal_re] : 0 < im (I * x))
  exact h.comp (f := fun u : ℝ ↦ ((a' : ℂ), I * u)) (continuous_prod_mk.mpr ⟨continuous_const,
    continuous_const.mul continuous_ofReal⟩).continuousAt

lemma oddKernel_functional_equation (a : UnitAddCircle) (x : ℝ) :
    oddKernel a x = 1 / x ^ (3 / 2 : ℝ) * sinKernel a (1 / x) := by
  -- first reduce to `0 < x`
  rcases le_or_lt x 0 with hx | hx
  · rw [oddKernel_undef _ hx, sinKernel_undef _ (one_div_nonpos.mpr hx), mul_zero]
  induction' a using QuotientAddGroup.induction_on' with a
  rw [← ofReal_inj, ofReal_mul, oddKernel_def, sinKernel_def, jacobiTheta₂'_functional_equation a]
  -- What remains is an annoyingly fiddly rearrangement. We use `generalize` to replace complicated
  -- subexpressions with abstract variables that `field_simp` and `ring_nf` can work with. The
  -- sticky point is that we need to be careful about branches of complex powers.
  --
  -- *First step*: get rid of the theta-functions themselves.
  have : -1 / (I * ↑(1 / x)) = I * x := by { push_cast; field_simp; ring_nf }
  rw [this]
  have : a / (I * ↑(1 / x)) = -(a * I * x) := by { push_cast; field_simp; ring_nf }
  rw [this, jacobiTheta₂_neg_left, jacobiTheta₂'_neg_left]
  generalize jacobiTheta₂ (↑a * I * ↑x) (I * ↑x) = J
  generalize jacobiTheta₂' (↑a * I * ↑x) (I * ↑x) = J'
  -- *Second step*: get rid of the complex exponential.
  have : -π * I * a ^ 2 / (I * ↑(1 / x)) = -π * a ^ 2 * x := by
    push_cast; field_simp; ring_nf; rw [I_sq]; ring_nf
  rw [this]
  generalize cexp (-π * a ^ 2 * x) = C
  -- *Third step*: rewrite all the powers in terms of `y = ↑(x ^ (1 / 2))`.
  generalize hy : (↑(x ^ (1 / 2 : ℝ)) : ℂ) = y
  have : ↑(1 / x ^ (3 / 2 : ℝ)) = 1 / y ^ 3 := by
    rw [← hy, ← ofReal_pow, ← rpow_mul_natCast hx.le]; norm_num
  rw [this]
  have : 1 / (-I * (I * ↑(1 / x))) ^ (1 / 2 : ℂ) = y := by
    rw [← hy]
    push_cast; field_simp; rw [one_div, one_div, inv_cpow, inv_inv, ofReal_cpow hx.le]; norm_num
    rw [arg_ofReal_of_nonneg hx.le]
    exact pi_pos.ne
  rw [this]
  have : ↑(1 / x) = 1 / y ^ 2 := by
    rw [← hy, one_div, one_div, ofReal_inv, inv_inj, ← ofReal_pow, ofReal_inj,
      ← rpow_mul_natCast hx.le]; norm_num
  rw [this]
  -- *Fourth step*: use `field_simp` and `ring_nf` (twice, because we first need to bring the
  -- powers of `I` together)
  have hy' : y ≠ 0 := by
    rw [← hy]; exact ofReal_ne_zero.mpr (rpow_pos_of_pos hx _).ne'
  field_simp [pi_ne_zero]
  ring_nf
  rw [(by norm_num : I ^ 3 = I ^ (2 + 1)), pow_add, I_sq]
  ring_nf
  -- *Fifth step*: breathe a sigh of relief and go to bed.

/-!
## Asymptotics as `t → ∞`
-/

/-- The function `sinKernel a` has exponential decay at `+∞`, for any `a`. -/
lemma isBigO_atTop_sinKernel (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (sinKernel a) (fun x ↦ Real.exp (-p * x)) := by
  induction' a using QuotientAddGroup.induction_on with a
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_one (le_refl 0)
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [HurwitzKernelBounds.F_nat, ← (hasSum_nat_sinKernel a ht).tsum_eq]
  apply tsum_of_norm_bounded (g := fun n ↦ 2 * HurwitzKernelBounds.f_nat 1 0 t n)
  · exact (HurwitzKernelBounds.summable_f_nat 1 0 ht).hasSum.mul_left _
  · intro n
    rw [norm_mul, norm_mul, norm_mul, norm_two, mul_assoc, mul_assoc,
      mul_le_mul_iff_of_pos_left two_pos, HurwitzKernelBounds.f_nat, pow_one, add_zero,
      norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs, Nat.abs_cast, ← mul_assoc,
      mul_le_mul_iff_of_pos_right (exp_pos _)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (abs_sin_le_one _)

/-- The function `oddKernel a` has exponential decay at `+∞`, for any `a`. -/
lemma isBigO_atTop_oddKernel (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (oddKernel a) (fun x ↦ Real.exp (-p * x)) := by
  obtain ⟨b, _, rfl⟩ := a.eq_coe_Ico
  let ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_one b
  refine ⟨p, hp, (Eventually.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simpa only [← (hasSum_int_oddKernel b ht).tsum_eq, Real.norm_eq_abs, HurwitzKernelBounds.F_int,
    HurwitzKernelBounds.f_int, pow_one, norm_mul, abs_of_nonneg (exp_pos _).le] using
    (norm_tsum_le_tsum_norm (hasSum_int_oddKernel b ht).summable.norm)

section FEPair
/-!
## Construction of a FE-pair
-/

/-- A `StrongFEPair` structure with `f = oddKernel a` and `g = sinKernel a`. -/
def hurwitzOddFEPair (a : UnitAddCircle) : StrongFEPair ℂ where
  f := ofReal' ∘ oddKernel a
  g := ofReal' ∘ sinKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_oddKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_sinKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 3 / 2
  hk := by norm_num
  hε := one_ne_zero
  f₀ := 0
  hf₀ := by rfl
  g₀ := 0
  hg₀ := by rfl
  hf_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_oddKernel a
    rw [← isBigO_norm_left] at hv' ⊢
    simp_rw [Function.comp_def, sub_zero, norm_real]
    exact hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  hg_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_sinKernel a
    rw [← isBigO_norm_left] at hv' ⊢
    simp_rw [Function.comp_def, sub_zero, norm_real]
    exact hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  h_feq x hx := by simp_rw [Function.comp_apply, one_mul, smul_eq_mul, ← ofReal_mul,
    oddKernel_functional_equation a, one_div x, one_div x⁻¹, inv_rpow (le_of_lt hx), one_div,
    inv_inv]

/-- The entire function of `s` which agrees with
`1 / 2 * Gamma ((s + 1) / 2) * π ^ (-(s + 1) / 2) * ∑' (n : ℤ), sgn (n + a) / |n + a| ^ s`
for `1 < re s`.
-/
def completedHurwitzZetaOdd (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzOddFEPair a).Λ ((s + 1) / 2)) / 2

lemma differentiable_completedHurwitzZetaOdd (a : UnitAddCircle) :
    Differentiable ℂ (completedHurwitzZetaOdd a) :=
  ((hurwitzOddFEPair a).differentiable_Λ.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2

/-- The entire function of `s` which agrees with
` Gamma ((s + 1) / 2) * π ^ (-(s + 1) / 2) * ∑' (n : ℕ), sin (2 * π * a * n) / n ^ s`
for `1 < re s`.
-/
def completedSinZeta (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzOddFEPair a).symm.Λ ((s + 1) / 2)) / 2

lemma differentiable_completedSinZeta (a : UnitAddCircle) :
    Differentiable ℂ (completedSinZeta a) :=
  ((hurwitzOddFEPair a).symm.differentiable_Λ.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2

/-!
## Parity and functional equations
-/

lemma completedHurwitzZetaOdd_neg (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaOdd (-a) s = -completedHurwitzZetaOdd a s := by
  simp only [completedHurwitzZetaOdd, StrongFEPair.Λ, hurwitzOddFEPair, mellin, Function.comp_def,
    oddKernel_neg, ofReal_neg, smul_neg]
  rw [integral_neg, neg_div]

lemma completedSinZeta_neg (a : UnitAddCircle) (s : ℂ) :
    completedSinZeta (-a) s = -completedSinZeta a s := by
  simp only [completedSinZeta, StrongFEPair.Λ, mellin, StrongFEPair.symm, WeakFEPair.symm,
    hurwitzOddFEPair, Function.comp_def, sinKernel_neg, ofReal_neg, smul_neg]
  rw [integral_neg, neg_div]

/-- Functional equation for the odd Hurwitz zeta function. -/
lemma completedHurwitzZetaOdd_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaOdd a (1 - s) = completedSinZeta a s := by
  erw [completedHurwitzZetaOdd, completedSinZeta,
    (by { push_cast; ring } : (1 - s + 1) / 2 = ↑(3 / 2 : ℝ) - (s + 1) / 2),
    (hurwitzOddFEPair a).functional_equation ((s + 1) / 2), one_smul]

/-- Functional equation for the odd Hurwitz zeta function (alternative form). -/
lemma completedSinZeta_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedSinZeta a (1 - s) = completedHurwitzZetaOdd a s := by
  rw [← completedHurwitzZetaOdd_one_sub, sub_sub_cancel]

/-!
## Relation to the Dirichlet series for `0 ≪ re s`
-/

/-- Formula for `completedSinZeta` as a Dirichlet series in the convergence range
(first version, with sum over `ℤ`). -/
lemma hasSum_int_completedSinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ Gammaℝ (s + 1) * (-I) * Int.sign n *
    cexp (2 * π * I * a * n) / (↑|n| : ℂ) ^ s / 2) (completedSinZeta a s) := by
  let c (n : ℤ) : ℂ := -I * cexp (2 * π * I * a * n) / 2
  have hc (n : ℤ) : ‖c n‖ = 1 / 2 := by
    simp_rw [c, (by { push_cast; ring } : 2 * π * I * a * n = ↑(2 * π * a * n) * I), norm_div,
      IsROrC.norm_ofNat, norm_mul, norm_neg, norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
  have hF t (ht : 0 < t) :
      HasSum (fun n ↦ c n * n * rexp (-π * n ^ 2 * t)) (sinKernel a t / 2) := by
    convert (hasSum_int_sinKernel a ht).div_const 2 using 2 with n
    ring_nf
  convert hasSum_mellin_pi_mul_sq' (zero_lt_one.trans hs) hF ?_ using 1
  · ext1 n
    rw [← Int.cast_abs, ofReal_int_cast]
    have : (Int.sign n : ℂ) = SignType.sign (n : ℝ) := by
      rcases lt_trichotomy 0 n with h | rfl | h
      · rw [Int.sign_eq_one_of_pos h, Int.cast_one, sign_pos (Int.cast_pos.mpr h), SignType.coe_one]
      · rw [Int.sign_zero, Int.cast_zero, Int.cast_zero, sign_zero, SignType.coe_zero]
      · rw [Int.sign_eq_neg_one_of_neg h, Int.cast_neg, Int.cast_one,
            sign_neg (Int.cast_lt_zero.mpr h), SignType.coe_neg_one]
    rw [this]
    ring_nf
  · rw [mellin_div_const]
    rfl
  · simp_rw [hc, div_right_comm]
    apply Summable.div_const
    apply Summable.of_nat_of_neg <;>
    · simp only [Int.cast_neg, abs_neg, Int.cast_ofNat, Nat.abs_cast]
      rwa [summable_one_div_nat_rpow]

/-- Formula for `completedSinZeta` as a Dirichlet series in the convergence range
(second version, with sum over `ℕ`). -/
lemma hasSum_nat_completedSinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ Gammaℝ (s + 1) * Real.sin (2 * π * a * n) / (n : ℂ) ^ s)
    (completedSinZeta a s) := by
  have := (hasSum_int_completedSinZeta a hs).sum_nat_of_sum_int
  simp_rw [Int.sign_zero, Int.cast_zero, mul_zero, zero_mul, zero_div, add_zero, abs_neg,
    Int.sign_neg, Nat.abs_cast, Int.cast_neg, Int.cast_ofNat, ← add_div] at this
  convert this using 2 with n
  rw [div_right_comm]
  rcases eq_or_ne n 0 with rfl | h
  · simp
  simp_rw [Int.sign_coe_nat_of_nonzero h, Int.cast_one, ofReal_sin, Complex.sin]
  cancel_denoms
  ring_nf

/-- Formula for `completedHurwitzZetaOdd` as a Dirichlet series in the convergence range. -/
lemma hasSum_int_completedHurwitzZetaOdd (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ Gammaℝ (s + 1) * SignType.sign (n + a) / (↑|n + a| : ℂ) ^ s / 2)
    (completedHurwitzZetaOdd a s) := by
  let r (n : ℤ) : ℝ := n + a
  let c (n : ℤ) : ℂ := 1 / 2
  have hF t (ht : 0 < t) : HasSum (fun n ↦ c n * r n * rexp (-π * (r n) ^ 2 * t))
      (oddKernel a t / 2) := by
    convert (hasSum_ofReal.mpr (hasSum_int_oddKernel a ht)).div_const 2 using 2 with n
    simp only [r, c]
    push_cast
    ring_nf
  convert hasSum_mellin_pi_mul_sq' (zero_lt_one.trans hs) hF ?_ using 1
  · ext1 n
    ring_nf
  · rw [mellin_div_const]
    rfl
  · simp_rw [c, ← mul_one_div ‖_‖]
    apply Summable.mul_left
    rwa [summable_one_div_int_add_rpow]

/-!
## Non-completed zeta functions
-/

/-- The odd part of the Hurwitz zeta function, i.e. the meromorphic function of `s` which agrees
with `1 / 2 * ∑' (n : ℤ), sign (n + a) / |n + a| ^ s` for `1 < re s`-/
noncomputable def hurwitzZetaOdd (a : UnitAddCircle) (s : ℂ) :=
  completedHurwitzZetaOdd a s / Gammaℝ (s + 1)

lemma hurwitzZetaOdd_neg (a : UnitAddCircle) (s : ℂ) :
    hurwitzZetaOdd (-a) s = -hurwitzZetaOdd a s := by
  simp_rw [hurwitzZetaOdd, completedHurwitzZetaOdd_neg, neg_div]

/-- The odd Hurwitz zeta function is differentiable everywhere. -/
lemma differentiable_hurwitzZetaOdd (a : UnitAddCircle) :
    Differentiable ℂ (hurwitzZetaOdd a) :=
  (differentiable_completedHurwitzZetaOdd a).mul <| differentiable_Gammaℝ_inv.comp <|
    differentiable_id.add <| differentiable_const _

/-- The sine zeta function, i.e. the meromorphic function of `s` which agrees
with `∑' (n : ℕ), sin (2 * π * a * n) / n ^ s` for `1 < re s`. -/
noncomputable def sinZeta (a : UnitAddCircle) (s : ℂ) :=
  completedSinZeta a s / Gammaℝ (s + 1)

lemma sinZeta_neg (a : UnitAddCircle) (s : ℂ) :
    sinZeta (-a) s = -sinZeta a s := by
  simp_rw [sinZeta, completedSinZeta_neg, neg_div]

/-- The sine zeta function is differentiable everywhere. -/
lemma differentiableAt_sinZeta (a : UnitAddCircle) :
    Differentiable ℂ (sinZeta a) :=
  (differentiable_completedSinZeta a).mul <| differentiable_Gammaℝ_inv.comp <|
    differentiable_id.add <| differentiable_const _

/-- Formula for `hurwitzZetaOdd` as a Dirichlet series in the convergence range (sum over `ℤ`). -/
lemma hasSum_int_hurwitzZetaOdd (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ SignType.sign (n + a) / (↑|n + a| : ℂ) ^ s / 2) (hurwitzZetaOdd a s) := by
  rw [hurwitzZetaOdd]
  convert (hasSum_int_completedHurwitzZetaOdd a hs).div_const (Gammaℝ (s + 1)) using 2 with n
  simp_rw [div_right_comm _ _ (Gammaℝ _)]
  rw [mul_div_cancel_left₀ _ (Gammaℝ_ne_zero_of_re_pos ?_)]
  rw [add_re, one_re]
  positivity

/-- Formula for `hurwitzZetaOdd` as a Dirichlet series in the convergence range, with sum over `ℕ`
(version with absolute values) -/
lemma hasSum_nat_hurwitzZetaOdd (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ (SignType.sign (n + a) / (↑|n + a| : ℂ) ^ s
      - SignType.sign (n + 1 - a) / (↑|n + 1 - a| : ℂ) ^ s) / 2) (hurwitzZetaOdd a s) := by
  convert (hasSum_int_hurwitzZetaOdd a hs).nat_add_neg_add_one using 2 with n
  rw [Int.cast_neg, Int.cast_add, Int.cast_one, sub_div, sub_eq_add_neg, Int.cast_ofNat]
  have : -(n + 1) + a = -(n + 1 - a) := by { push_cast; ring_nf }
  rw [this, Left.sign_neg, abs_neg, SignType.coe_neg, neg_div, neg_div]

/-- Formula for `hurwitzZetaOdd` as a Dirichlet series in the convergence range, with sum over `ℕ`
(version without absolute values, assuming `a ∈ Icc 0 1`) -/
lemma hasSum_nat_hurwitzZetaOdd_of_mem_Icc {a : ℝ} (ha : a ∈ Icc 0 1) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ (1 / (n + a : ℂ) ^ s - 1 / (n + 1 - a : ℂ) ^ s) / 2)
    (hurwitzZetaOdd a s) := by
  convert (hasSum_nat_hurwitzZetaOdd a hs) using 2 with n
  suffices ∀ (b : ℝ) (_ : 0 ≤ b), SignType.sign (n + b) / (↑|n + b| : ℂ) ^ s = 1 / (n + b) ^ s by
    simp only [add_sub_assoc, this a ha.1, this (1 - a) (sub_nonneg.mpr ha.2), push_cast]
  intro b hb
  rw [abs_of_nonneg (by positivity), (by simp : (n : ℂ) + b = ↑(n + b))]
  rcases lt_or_eq_of_le (by positivity : 0 ≤ n + b) with hb | hb
  · rw [sign_pos hb, SignType.coe_one]
  · rw [← hb, ofReal_zero, zero_cpow ((not_lt.mpr zero_le_one) ∘ (zero_re ▸ · ▸ hs)),
      div_zero, div_zero]

/-- Formula for `cosZeta` as a Dirichlet series in the convergence range, with sum over `ℤ`. -/
lemma hasSum_int_sinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ -I * Int.sign n * cexp (2 * π * I * a * n) / ↑|n| ^ s / 2)
    (sinZeta a s) := by
  rw [sinZeta]
  convert (hasSum_int_completedSinZeta a hs).div_const (Gammaℝ (s + 1)) using 2 with n
  simp_rw [mul_assoc, div_right_comm _ _ (Gammaℝ _)]
  rw [mul_div_cancel_left₀ _ (Gammaℝ_ne_zero_of_re_pos (?_ : 0 < (s + 1).re))]
  rw [add_re, one_re]
  positivity

/-- Formula for `cosZeta` as a Dirichlet series in the convergence range, with sum over `ℕ`. -/
lemma hasSum_nat_sinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ Real.sin (2 * π * a * n) / (n : ℂ) ^ s) (sinZeta a s) := by
  have hs' : s ≠ 0 := (fun h ↦ (not_lt.mpr zero_le_one) ((zero_re ▸ h ▸ hs)))
  have := (hasSum_int_sinZeta a hs).sum_nat_of_sum_int
  simp_rw [abs_neg, Int.sign_neg, Int.cast_neg, Nat.abs_cast, Int.cast_ofNat, mul_neg,
    abs_zero, Int.cast_zero, zero_cpow hs', div_zero, zero_div, add_zero] at this
  simp_rw [push_cast, Complex.sin]
  convert this using 2 with n
  rcases ne_or_eq n 0 with h | rfl
  · simp only [Int.sign_coe_nat_of_nonzero h, Int.cast_one]
    ring_nf
  · simp only [Nat.cast_zero, Int.sign_zero, Int.cast_zero]
    ring_nf

/-- The trivial zeroes of the odd Hurwitz zeta function. -/
theorem hurwitzZetaOdd_neg_two_mul_nat_sub_one (a : UnitAddCircle) (n : ℕ) :
    hurwitzZetaOdd a (-2 * n - 1) = 0 := by
  rw [hurwitzZetaOdd, Gammaℝ_eq_zero_iff.mpr ⟨n, by rw [neg_mul, sub_add_cancel]⟩, div_zero]

/-- The trivial zeroes of the sine zeta function. -/
theorem sinZeta_neg_two_mul_nat_sub_one (a : UnitAddCircle) (n : ℕ) :
    sinZeta a (-2 * n - 1) = 0 := by
  rw [sinZeta, Gammaℝ_eq_zero_iff.mpr ⟨n, by rw [neg_mul, sub_add_cancel]⟩, div_zero]

/-- If `s` is not in `-ℕ`, then `hurwitzZetaOdd a (1 - s)` is an explicit multiple of
`sinZeta s`. -/
lemma hurwitzZetaOdd_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -n) :
    hurwitzZetaOdd a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * sin (π * s / 2) * sinZeta a s := by
  change hurwitzZetaOdd a (1 - s) = Gammaℂ s * sin (π * s / 2) * sinZeta a s
  rw [hurwitzZetaOdd, (by ring : 1 - s + 1 = 2 - s), div_eq_mul_inv, inv_Gammaℝ_two_sub hs,
    completedHurwitzZetaOdd_one_sub, sinZeta]
  ring_nf

/-- If `s` is not in `-ℕ`, then `hurwitzZetaOdd a (1 - s)` is an explicit multiple of
`sinZeta s`. -/
lemma sinZeta_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -n) :
    sinZeta a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * sin (π * s / 2) * hurwitzZetaOdd a s := by
  change sinZeta a (1 - s) = Gammaℂ s * sin (π * s / 2) * hurwitzZetaOdd a s
  rw [sinZeta, (by ring : 1 - s + 1 = 2 - s), div_eq_mul_inv, inv_Gammaℝ_two_sub hs,
    ← completedHurwitzZetaOdd_one_sub, ← sub_add, sub_self, zero_add, hurwitzZetaOdd]
  ring_nf
