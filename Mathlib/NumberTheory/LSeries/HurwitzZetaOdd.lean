/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Odd Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the analytic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`hurwitzZetaOdd a s = 1 / 2 * ∑' n : ℤ, sgn (n + a) / |n + a| ^ s`

and

`sinZeta a s = ∑' n : ℕ, sin (2 * π * a * n) / n ^ s`.

The term for `n = -a` in the first sum is understood as 0 if `a` is an integer, as is the term for
`n = 0` in the second sum (for all `a`). Note that these functions are differentiable everywhere,
unlike their even counterparts which have poles.

Of course, we cannot *define* these functions by the above formulae (since existence of the
analytic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function.

## Main definitions and theorems

* `completedHurwitzZetaOdd`: the completed Hurwitz zeta function
* `completedSinZeta`: the completed sine zeta function
* `differentiable_completedHurwitzZetaOdd` and `differentiable_completedSinZeta`:
  differentiability on `ℂ`
* `completedHurwitzZetaOdd_one_sub`: the functional equation
  `completedHurwitzZetaOdd a (1 - s) = completedSinZeta a s`
* `hasSum_int_hurwitzZetaOdd` and `hasSum_nat_sinZeta`: relation between
  the zeta functions and corresponding Dirichlet series for `1 < re s`
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

open Complex
open CharZero Filter Topology Asymptotics Real Set MeasureTheory
open scoped ComplexConjugate

namespace HurwitzZeta

section kernel_defs
/-!
## Definitions and elementary properties of kernels
-/

/-- Variant of `jacobiTheta₂'` which we introduce to simplify some formulae. -/
def jacobiTheta₂'' (z τ : ℂ) : ℂ :=
  cexp (π * I * z ^ 2 * τ) * (jacobiTheta₂' (z * τ) τ / (2 * π * I) + z * jacobiTheta₂ (z * τ) τ)

lemma jacobiTheta₂''_conj (z τ : ℂ) :
    conj (jacobiTheta₂'' z τ) = jacobiTheta₂'' (conj z) (-conj τ) := by
  simp [jacobiTheta₂'', jacobiTheta₂'_conj, jacobiTheta₂_conj, ← exp_conj, map_ofNat, div_neg,
    neg_div, jacobiTheta₂'_neg_left]

/-- Restatement of `jacobiTheta₂'_add_left'`: the function `jacobiTheta₂''` is 1-periodic in `z`. -/
lemma jacobiTheta₂''_add_left (z τ : ℂ) : jacobiTheta₂'' (z + 1) τ = jacobiTheta₂'' z τ := by
  simp only [jacobiTheta₂'', add_mul z 1, one_mul, jacobiTheta₂'_add_left', jacobiTheta₂_add_left']
  generalize jacobiTheta₂ (z * τ) τ = J
  generalize jacobiTheta₂' (z * τ) τ = J'
  -- clear denominator
  simp_rw [div_add' _ _ _ two_pi_I_ne_zero, ← mul_div_assoc]
  refine congr_arg (· / (2 * π * I)) ?_
  -- get all exponential terms to left
  rw [mul_left_comm _ (cexp _), ← mul_add, mul_assoc (cexp _), ← mul_add, ← mul_assoc (cexp _),
    ← Complex.exp_add]
  congrm (cexp ?_ * ?_) <;> ring

lemma jacobiTheta₂''_neg_left (z τ : ℂ) : jacobiTheta₂'' (-z) τ = -jacobiTheta₂'' z τ := by
  simp [jacobiTheta₂'', jacobiTheta₂'_neg_left, neg_div, -neg_add_rev, ← neg_add]

lemma jacobiTheta₂'_functional_equation' (z τ : ℂ) :
    jacobiTheta₂' z τ = (-2 * π) / (-I * τ) ^ (3 / 2 : ℂ) * jacobiTheta₂'' z (-1 / τ) := by
  rcases eq_or_ne τ 0 with rfl | hτ
  · rw [jacobiTheta₂'_undef _ (by simp), mul_zero, zero_cpow (by simp), div_zero, zero_mul]
  have aux1 : (-2 * π : ℂ) / (2 * π * I) = I := by
    rw [div_eq_iff two_pi_I_ne_zero, mul_comm I, mul_assoc _ I I, I_mul_I, neg_mul, mul_neg,
      mul_one]
  rw [jacobiTheta₂'_functional_equation, ← mul_one_div _ τ, mul_right_comm _ (cexp _),
    (by rw [cpow_one, ← div_div, div_self (neg_ne_zero.mpr I_ne_zero)] :
      1 / τ = -I / (-I * τ) ^ (1 : ℂ)), div_mul_div_comm,
    ← cpow_add _ _ (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ), ← div_mul_eq_mul_div,
    (by norm_num : (1 / 2 + 1 : ℂ) = 3 / 2), mul_assoc (1 / _), mul_assoc (1 / _),
    ← mul_one_div (-2 * π : ℂ), mul_comm _ (1 / _), mul_assoc (1 / _)]
  congr 1
  rw [jacobiTheta₂'', div_add' _ _ _ two_pi_I_ne_zero, ← mul_div_assoc, ← mul_div_assoc,
    ← div_mul_eq_mul_div (-2 * π : ℂ), mul_assoc, aux1, mul_div z (-1), mul_neg_one, neg_div τ z,
    jacobiTheta₂_neg_left, jacobiTheta₂'_neg_left, neg_mul, ← mul_neg, ← mul_neg,
    mul_div, mul_neg_one, neg_div, neg_mul, neg_mul, neg_div]
  congr 2
  rw [neg_sub, ← sub_eq_neg_add, mul_comm _ (_ * I), ← mul_assoc]

/-- Odd Hurwitz zeta kernel (function whose Mellin transform will be the odd part of the completed
Hurwitz zeta function). See `oddKernel_def` for the defining formula, and `hasSum_int_oddKernel`
for an expression as a sum over `ℤ`.
-/
@[irreducible] def oddKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun a : ℝ ↦ re (jacobiTheta₂'' a (I * x))) 1 by
    simp [jacobiTheta₂''_add_left]).lift a

lemma oddKernel_def (a x : ℝ) : ↑(oddKernel a x) = jacobiTheta₂'' a (I * x) := by
  simp [oddKernel, ← conj_eq_iff_re, jacobiTheta₂''_conj]

lemma oddKernel_def' (a x : ℝ) : ↑(oddKernel ↑a x) = cexp (-π * a ^ 2 * x) *
    (jacobiTheta₂' (a * I * x) (I * x) / (2 * π * I) + a * jacobiTheta₂ (a * I * x) (I * x)) := by
  rw [oddKernel_def, jacobiTheta₂'', ← mul_assoc ↑a I x,
    (by ring : ↑π * I * ↑a ^ 2 * (I * ↑x) = I ^ 2 * ↑π * ↑a ^ 2 * x), I_sq, neg_one_mul]

lemma oddKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : oddKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  rw [← ofReal_eq_zero, oddKernel_def', jacobiTheta₂_undef, jacobiTheta₂'_undef, zero_div, zero_add,
    mul_zero, mul_zero] <;>
  simpa

/-- Auxiliary function appearing in the functional equation for the odd Hurwitz zeta kernel, equal
to `∑ (n : ℕ), 2 * n * sin (2 * π * n * a) * exp (-π * n ^ 2 * x)`. See `hasSum_nat_sinKernel`
for the defining sum. -/
@[irreducible] def sinKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun ξ : ℝ ↦ re (jacobiTheta₂' ξ (I * x) / (-2 * π))) 1 by
    simp [jacobiTheta₂'_add_left]).lift a

lemma sinKernel_def (a x : ℝ) : ↑(sinKernel ↑a x) = jacobiTheta₂' a (I * x) / (-2 * π) := by
  simp [sinKernel, re_eq_add_conj, jacobiTheta₂'_conj, map_ofNat]

lemma sinKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : sinKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H a => rw [← ofReal_eq_zero, sinKernel_def, jacobiTheta₂'_undef _ (by simpa), zero_div]

lemma oddKernel_neg (a : UnitAddCircle) (x : ℝ) : oddKernel (-a) x = -oddKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, oddKernel_def, jacobiTheta₂''_neg_left]

@[simp] lemma oddKernel_zero (x : ℝ) : oddKernel 0 x = 0 := by
  simpa using oddKernel_neg 0 x

lemma sinKernel_neg (a : UnitAddCircle) (x : ℝ) :
    sinKernel (-a) x = -sinKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, sinKernel_def, jacobiTheta₂'_neg_left,
      neg_div]

@[simp] lemma sinKernel_zero (x : ℝ) : sinKernel 0 x = 0 := by
  simpa using sinKernel_neg 0 x

/-- The odd kernel is continuous on `Ioi 0`. -/
lemma continuousOn_oddKernel (a : UnitAddCircle) : ContinuousOn (oddKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  suffices ContinuousOn (fun x ↦ (oddKernel a x : ℂ)) (Ioi 0) from
    (continuous_re.comp_continuousOn this).congr fun a _ ↦ (ofReal_re _).symm
  simp_rw [oddKernel_def' a]
  refine fun x hx ↦ ((Continuous.continuousAt ?_).mul ?_).continuousWithinAt
  · fun_prop
  · have hf : Continuous fun u : ℝ ↦ (a * I * u, I * u) := by fun_prop
    apply ContinuousAt.add
    · exact ((continuousAt_jacobiTheta₂' (a * I * x) (by rwa [I_mul_im, ofReal_re])).comp
        (f := fun u : ℝ ↦ (a * I * u, I * u)) hf.continuousAt).div_const _
    · exact continuousAt_const.mul <| (continuousAt_jacobiTheta₂ (a * I * x)
        (by rwa [I_mul_im, ofReal_re])).comp (f := fun u : ℝ ↦ (a * I * u, I * u)) hf.continuousAt

lemma continuousOn_sinKernel (a : UnitAddCircle) : ContinuousOn (sinKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  suffices ContinuousOn (fun x ↦ (sinKernel a x : ℂ)) (Ioi 0) from
    (continuous_re.comp_continuousOn this).congr fun a _ ↦ (ofReal_re _).symm
  simp_rw [sinKernel_def]
  apply (continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)).div_const
  have h := continuousAt_jacobiTheta₂' a (by rwa [I_mul_im, ofReal_re])
  fun_prop

lemma oddKernel_functional_equation (a : UnitAddCircle) (x : ℝ) :
    oddKernel a x = 1 / x ^ (3 / 2 : ℝ) * sinKernel a (1 / x) := by
  -- first reduce to `0 < x`
  rcases le_or_gt x 0 with hx | hx
  · rw [oddKernel_undef _ hx, sinKernel_undef _ (one_div_nonpos.mpr hx), mul_zero]
  induction a using QuotientAddGroup.induction_on with | H a =>
  have h1 : -1 / (I * ↑(1 / x)) = I * x := by rw [one_div, ofReal_inv, mul_comm, ← div_div,
    div_inv_eq_mul, div_eq_mul_inv, inv_I, mul_neg, neg_one_mul, neg_mul, neg_neg, mul_comm]
  have h2 : (-I * (I * ↑(1 / x))) = 1 / x := by
    rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul, ofReal_div, ofReal_one]
  have h3 : (x : ℂ) ^ (3 / 2 : ℂ) ≠ 0 := by
    simp only [Ne, cpow_eq_zero_iff, ofReal_eq_zero, hx.ne', false_and, not_false_eq_true]
  have h4 : arg x ≠ π := by rw [arg_ofReal_of_nonneg hx.le]; exact pi_ne_zero.symm
  rw [← ofReal_inj, oddKernel_def, ofReal_mul, sinKernel_def, jacobiTheta₂'_functional_equation',
    h1, h2]
  generalize jacobiTheta₂'' a (I * ↑x) = J
  rw [one_div (x : ℂ), inv_cpow _ _ h4, div_inv_eq_mul, one_div, ofReal_inv, ofReal_cpow hx.le,
    ofReal_div, ofReal_ofNat, ofReal_ofNat, ← mul_div_assoc _ _ (-2 * π : ℂ),
    eq_div_iff <| mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (ofReal_ne_zero.mpr pi_ne_zero),
    ← div_eq_inv_mul, eq_div_iff h3, mul_comm J _, mul_right_comm]

end kernel_defs

section sum_formulas

/-!
## Formulae for the kernels as sums
-/

lemma hasSum_int_oddKernel (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℤ ↦ (n + a) * rexp (-π * (n + a) ^ 2 * x)) (oddKernel ↑a x) := by
  rw [← hasSum_ofReal, oddKernel_def' a x]
  have h1 := hasSum_jacobiTheta₂_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
  have h2 := hasSum_jacobiTheta₂'_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
  refine (((h2.div_const (2 * π * I)).add (h1.mul_left ↑a)).mul_left
    (cexp (-π * a ^ 2 * x))).congr_fun (fun n ↦ ?_)
  rw [jacobiTheta₂'_term, mul_assoc (2 * π * I), mul_div_cancel_left₀ _ two_pi_I_ne_zero, ← add_mul,
    mul_left_comm, jacobiTheta₂_term, ← Complex.exp_add]
  push_cast
  simp only [← mul_assoc, ← add_mul]
  congrm _ * cexp (?_ * x)
  simp only [mul_right_comm _ I, add_mul, mul_assoc _ I, I_mul_I]
  ring_nf

lemma hasSum_int_sinKernel (a : ℝ) {t : ℝ} (ht : 0 < t) : HasSum
    (fun n : ℤ ↦ -I * n * cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(sinKernel a t) := by
  have h : -2 * (π : ℂ) ≠ (0 : ℂ) := by
    simp only [neg_mul, ne_eq, neg_eq_zero, mul_eq_zero,
      OfNat.ofNat_ne_zero, ofReal_eq_zero, pi_ne_zero, or_self, not_false_eq_true]
  rw [sinKernel_def]
  refine ((hasSum_jacobiTheta₂'_term a
    (by rwa [I_mul_im, ofReal_re])).div_const _).congr_fun fun n ↦ ?_
  rw [jacobiTheta₂'_term, jacobiTheta₂_term, ofReal_exp, mul_assoc (-I * n), ← Complex.exp_add,
    eq_div_iff h, ofReal_mul, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_intCast,
    mul_comm _ (-2 * π : ℂ), ← mul_assoc]
  congrm ?_ * cexp (?_ + ?_)
  · simp [mul_assoc]
  · exact mul_right_comm (2 * π * I) a n
  · simp [← mul_assoc, mul_comm _ I]

lemma hasSum_nat_sinKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ 2 * n * Real.sin (2 * π * a * n) * rexp (-π * n ^ 2 * t))
    (sinKernel ↑a t) := by
  rw [← hasSum_ofReal]
  have := (hasSum_int_sinKernel a ht).nat_add_neg
  simp only [Int.cast_zero, zero_mul, mul_zero, add_zero] at this
  refine this.congr_fun fun n ↦ ?_
  simp_rw [Int.cast_neg, neg_sq, mul_neg, ofReal_mul, Int.cast_natCast, ofReal_natCast,
      ofReal_ofNat, ← add_mul, ofReal_sin, Complex.sin]
  push_cast
  congr 1
  rw [← mul_div_assoc, ← div_mul_eq_mul_div, ← div_mul_eq_mul_div, div_self two_ne_zero, one_mul,
    neg_mul, neg_mul, neg_neg, mul_comm _ I, ← mul_assoc, mul_comm _ I, neg_mul,
    ← sub_eq_neg_add, mul_sub]
  congr 3 <;> ring

end sum_formulas

section asymp
/-!
## Asymptotics of the kernels as `t → ∞`
-/

/-- The function `oddKernel a` has exponential decay at `+∞`, for any `a`. -/
lemma isBigO_atTop_oddKernel (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (oddKernel a) (fun x ↦ Real.exp (-p * x)) := by
  induction a using QuotientAddGroup.induction_on with | H b =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_one b
  refine ⟨p, hp, (Eventually.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simpa [← (hasSum_int_oddKernel b ht).tsum_eq, HurwitzKernelBounds.F_int,
    HurwitzKernelBounds.f_int, abs_of_nonneg (exp_pos _).le] using
    norm_tsum_le_tsum_norm (hasSum_int_oddKernel b ht).summable.norm

/-- The function `sinKernel a` has exponential decay at `+∞`, for any `a`. -/
lemma isBigO_atTop_sinKernel (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (sinKernel a) (fun x ↦ Real.exp (-p * x)) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
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

end asymp

section FEPair
/-!
## Construction of an FE-pair
-/

/-- A `StrongFEPair` structure with `f = oddKernel a` and `g = sinKernel a`. -/
@[simps]
def hurwitzOddFEPair (a : UnitAddCircle) : StrongFEPair ℂ where
  f := ofReal ∘ oddKernel a
  g := ofReal ∘ sinKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_oddKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_sinKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 3 / 2
  hk := by norm_num
  ε := 1
  hε := one_ne_zero
  f₀ := 0
  hf₀ := rfl
  g₀ := 0
  hg₀ := rfl
  hf_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_oddKernel a
    rw [← isBigO_norm_left] at hv' ⊢
    simpa using hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  hg_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_sinKernel a
    rw [← isBigO_norm_left] at hv' ⊢
    simpa using hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  h_feq x hx := by simp [← ofReal_mul, oddKernel_functional_equation a, inv_rpow (le_of_lt hx)]

end FEPair

/-!
## Definition of the completed odd Hurwitz zeta function
-/

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
  simp [completedHurwitzZetaOdd, StrongFEPair.Λ, hurwitzOddFEPair, mellin, oddKernel_neg,
    integral_neg, neg_div]

lemma completedSinZeta_neg (a : UnitAddCircle) (s : ℂ) :
    completedSinZeta (-a) s = -completedSinZeta a s := by
  simp [completedSinZeta, StrongFEPair.Λ, mellin, StrongFEPair.symm, WeakFEPair.symm,
    hurwitzOddFEPair, sinKernel_neg, integral_neg, neg_div]

/-- Functional equation for the odd Hurwitz zeta function. -/
theorem completedHurwitzZetaOdd_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaOdd a (1 - s) = completedSinZeta a s := by
  rw [completedHurwitzZetaOdd, completedSinZeta,
    (by { push_cast; ring } : (1 - s + 1) / 2 = ↑(3 / 2 : ℝ) - (s + 1) / 2),
    ← hurwitzOddFEPair_k, (hurwitzOddFEPair a).functional_equation ((s + 1) / 2),
    hurwitzOddFEPair_ε, one_smul]

/-- Functional equation for the odd Hurwitz zeta function (alternative form). -/
lemma completedSinZeta_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedSinZeta a (1 - s) = completedHurwitzZetaOdd a s := by
  simp [← completedHurwitzZetaOdd_one_sub]

/-!
## Relation to the Dirichlet series for `1 < re s`
-/

/-- Formula for `completedSinZeta` as a Dirichlet series in the convergence range
(first version, with sum over `ℤ`). -/
lemma hasSum_int_completedSinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ Gammaℝ (s + 1) * (-I) * Int.sign n *
    cexp (2 * π * I * a * n) / (↑|n| : ℂ) ^ s / 2) (completedSinZeta a s) := by
  let c (n : ℤ) : ℂ := -I * cexp (2 * π * I * a * n) / 2
  have hc (n : ℤ) : ‖c n‖ = 1 / 2 := by
    simp_rw [c, (by { push_cast; ring } : 2 * π * I * a * n = ↑(2 * π * a * n) * I), norm_div,
      RCLike.norm_ofNat, norm_mul, norm_neg, norm_I, one_mul, norm_exp_ofReal_mul_I]
  have hF t (ht : 0 < t) :
      HasSum (fun n ↦ c n * n * rexp (-π * n ^ 2 * t)) (sinKernel a t / 2) := by
    refine ((hasSum_int_sinKernel a ht).div_const 2).congr_fun fun n ↦ ?_
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_right_comm (-I)]
  have h_sum : Summable fun i ↦ ‖c i‖ / |↑i| ^ s.re := by
    simp_rw [hc, div_right_comm]
    apply Summable.div_const
    apply Summable.of_nat_of_neg <;>
    simpa
  refine (mellin_div_const .. ▸ hasSum_mellin_pi_mul_sq' (zero_lt_one.trans hs) hF h_sum).congr_fun
    fun n ↦ ?_
  simp [Int.sign_eq_sign, ← Int.cast_abs] -- non-terminal simp OK when `ring` follows
  ring

/-- Formula for `completedSinZeta` as a Dirichlet series in the convergence range
(second version, with sum over `ℕ`). -/
lemma hasSum_nat_completedSinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ Gammaℝ (s + 1) * Real.sin (2 * π * a * n) / (n : ℂ) ^ s)
    (completedSinZeta a s) := by
  have := (hasSum_int_completedSinZeta a hs).nat_add_neg
  simp_rw [Int.sign_zero, Int.cast_zero, mul_zero, zero_mul, zero_div, add_zero, abs_neg,
    Int.sign_neg, Nat.abs_cast, Int.cast_neg, Int.cast_natCast, ← add_div] at this
  refine this.congr_fun fun n ↦ ?_
  rw [div_right_comm]
  rcases eq_or_ne n 0 with rfl | h
  · simp
  simp_rw [Int.sign_natCast_of_ne_zero h, Int.cast_one, ofReal_sin, Complex.sin]
  simp only [← mul_div_assoc, push_cast, mul_assoc (Gammaℝ _), ← mul_add]
  congr 3
  rw [mul_one, mul_neg_one, neg_neg, neg_mul I, ← sub_eq_neg_add, ← mul_sub, mul_comm,
    mul_neg, neg_mul]
  congr 3 <;> ring

/-- Formula for `completedHurwitzZetaOdd` as a Dirichlet series in the convergence range. -/
lemma hasSum_int_completedHurwitzZetaOdd (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ Gammaℝ (s + 1) * SignType.sign (n + a) / (↑|n + a| : ℂ) ^ s / 2)
    (completedHurwitzZetaOdd a s) := by
  let r (n : ℤ) : ℝ := n + a
  let c (n : ℤ) : ℂ := 1 / 2
  have hF t (ht : 0 < t) : HasSum (fun n ↦ c n * r n * rexp (-π * (r n) ^ 2 * t))
      (oddKernel a t / 2) := by
    refine ((hasSum_ofReal.mpr (hasSum_int_oddKernel a ht)).div_const 2).congr_fun fun n ↦ ?_
    simp [r, c, push_cast, div_mul_eq_mul_div, -one_div]
  have h_sum : Summable fun i ↦ ‖c i‖ / |r i| ^ s.re := by
    simp_rw [c, ← mul_one_div ‖_‖]
    apply Summable.mul_left
    rwa [summable_one_div_int_add_rpow]
  have := mellin_div_const .. ▸ hasSum_mellin_pi_mul_sq' (zero_lt_one.trans hs) hF h_sum
  refine this.congr_fun fun n ↦ ?_
  simp only [r, c, mul_one_div, div_mul_eq_mul_div, div_right_comm]

/-!
## Non-completed zeta functions
-/

/-- The odd part of the Hurwitz zeta function, i.e. the meromorphic function of `s` which agrees
with `1 / 2 * ∑' (n : ℤ), sign (n + a) / |n + a| ^ s` for `1 < re s` -/
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
theorem hasSum_int_hurwitzZetaOdd (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ SignType.sign (n + a) / (↑|n + a| : ℂ) ^ s / 2) (hurwitzZetaOdd a s) := by
  refine ((hasSum_int_completedHurwitzZetaOdd a hs).div_const (Gammaℝ _)).congr_fun fun n ↦ ?_
  have : 0 < re (s + 1) := by rw [add_re, one_re]; positivity
  simp [div_right_comm _ _ (Gammaℝ _), mul_div_cancel_left₀ _ (Gammaℝ_ne_zero_of_re_pos this)]

/-- Formula for `hurwitzZetaOdd` as a Dirichlet series in the convergence range, with sum over `ℕ`
(version with absolute values) -/
lemma hasSum_nat_hurwitzZetaOdd (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ (SignType.sign (n + a) / (↑|n + a| : ℂ) ^ s
      - SignType.sign (n + 1 - a) / (↑|n + 1 - a| : ℂ) ^ s) / 2) (hurwitzZetaOdd a s) := by
  refine (hasSum_int_hurwitzZetaOdd a hs).nat_add_neg_add_one.congr_fun fun n ↦ ?_
  rw [Int.cast_neg, Int.cast_add, Int.cast_one, sub_div, sub_eq_add_neg, Int.cast_natCast]
  have : -(n + 1) + a = -(n + 1 - a) := by ring_nf
  rw [this, Left.sign_neg, abs_neg, SignType.coe_neg, neg_div, neg_div]

/-- Formula for `hurwitzZetaOdd` as a Dirichlet series in the convergence range, with sum over `ℕ`
(version without absolute values, assuming `a ∈ Icc 0 1`) -/
lemma hasSum_nat_hurwitzZetaOdd_of_mem_Icc {a : ℝ} (ha : a ∈ Icc 0 1) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ (1 / (n + a : ℂ) ^ s - 1 / (n + 1 - a : ℂ) ^ s) / 2)
    (hurwitzZetaOdd a s) := by
  refine (hasSum_nat_hurwitzZetaOdd a hs).congr_fun fun n ↦ ?_
  suffices ∀ b : ℝ, 0 ≤ b → SignType.sign (n + b) / (↑|n + b| : ℂ) ^ s = 1 / (n + b) ^ s by
    simp only [add_sub_assoc, this a ha.1, this (1 - a) (sub_nonneg.mpr ha.2), push_cast]
  intro b hb
  rw [abs_of_nonneg (by positivity), (by simp : (n : ℂ) + b = ↑(n + b))]
  rcases lt_or_eq_of_le (by positivity : 0 ≤ n + b) with hb | hb
  · simp [sign_pos hb]
  · rw [← hb, ofReal_zero, zero_cpow ((not_lt.mpr zero_le_one) ∘ (zero_re ▸ · ▸ hs)),
      div_zero, div_zero]

/-- Formula for `sinZeta` as a Dirichlet series in the convergence range, with sum over `ℤ`. -/
theorem hasSum_int_sinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ -I * n.sign * cexp (2 * π * I * a * n) / ↑|n| ^ s / 2) (sinZeta a s) := by
  rw [sinZeta]
  refine ((hasSum_int_completedSinZeta a hs).div_const (Gammaℝ (s + 1))).congr_fun fun n ↦ ?_
  have : 0 < re (s + 1) := by rw [add_re, one_re]; positivity
  simp only [mul_assoc, div_right_comm _ _ (Gammaℝ _),
    mul_div_cancel_left₀ _ (Gammaℝ_ne_zero_of_re_pos this)]

/-- Formula for `sinZeta` as a Dirichlet series in the convergence range, with sum over `ℕ`. -/
lemma hasSum_nat_sinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ Real.sin (2 * π * a * n) / (n : ℂ) ^ s) (sinZeta a s) := by
  have := (hasSum_int_sinZeta a hs).nat_add_neg
  simp_rw [abs_neg, Int.sign_neg, Int.cast_neg, Nat.abs_cast, Int.cast_natCast, mul_neg, abs_zero,
    Int.cast_zero, zero_cpow (ne_zero_of_one_lt_re hs), div_zero, zero_div, add_zero] at this
  simp_rw [push_cast, Complex.sin]
  refine this.congr_fun fun n ↦ ?_
  rcases ne_or_eq n 0 with h | rfl
  · simp only [neg_mul, sub_mul, div_right_comm _ (2 : ℂ), Int.sign_natCast_of_ne_zero h,
      Int.cast_one, mul_one, mul_comm I, neg_neg, ← add_div, ← sub_eq_neg_add]
    congr 5 <;> ring
  · simp

/-- Reformulation of `hasSum_nat_sinZeta` using `LSeriesHasSum`. -/
lemma LSeriesHasSum_sin (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    LSeriesHasSum (Real.sin <| 2 * π * a * ·) s (sinZeta a s) :=
  (hasSum_nat_sinZeta a hs).congr_fun (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)

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
  rw [← Gammaℂ, hurwitzZetaOdd, (by ring : 1 - s + 1 = 2 - s), div_eq_mul_inv,
    inv_Gammaℝ_two_sub hs, completedHurwitzZetaOdd_one_sub, sinZeta, ← div_eq_mul_inv,
    ← mul_div_assoc, ← mul_div_assoc, mul_comm]

/-- If `s` is not in `-ℕ`, then `sinZeta a (1 - s)` is an explicit multiple of
`hurwitzZetaOdd s`. -/
lemma sinZeta_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -n) :
    sinZeta a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * sin (π * s / 2) * hurwitzZetaOdd a s := by
  rw [← Gammaℂ, sinZeta, (by ring : 1 - s + 1 = 2 - s), div_eq_mul_inv, inv_Gammaℝ_two_sub hs,
    completedSinZeta_one_sub, hurwitzZetaOdd, ← div_eq_mul_inv, ← mul_div_assoc, ← mul_div_assoc,
    mul_comm]

end HurwitzZeta
