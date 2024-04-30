/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds

/-!
# Even Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the meromorphic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`completedHurwitzZetaEven a s = 1 / 2 * □ * ∑' n : ℤ, 1 / |n + a| ^ s`

and

`completedCosZeta a s = □ * ∑' n : ℕ, cos (2 * π * a * n) / |n| ^ s`

where `□` denotes a Gamma factor. Note that the term for `n = -a` in the first sum is omitted
if `a` is an integer, and the term for `n = 0` is omitted in the second sum (always).

Of course, we cannot *define* these functions by the above formulae (since existence of the
meromorphic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function. We also define modified versions with a subscript `0`
which are entire functions differing from the above by multiples of `1 / s` and `1 / (1 - s)`.

## Main definitions and theorems

* `completedHurwitzZetaEven`: the completed Hurwitz zeta function
* `completedCosZeta`: the completed cosine zeta function
* `differentiableAt_completedHurwitzZetaEven` and `differentiableAt_completedCosZeta`:
  differentiability away from `s = 0` and `s = 1`
* `completedHurwitzZetaEven_one_sub`: the functional equation
  `completedHurwitzZetaEven a (1 - s) = completedCosZeta a s`
* `completedHurwitzZetaEven_eq_tsum_int` and `completedCosZeta_eq_tsum_nat`: relation between the
  zeta functions and corresponding Dirichlet series for `1 < re s`
-/
noncomputable section

open Complex Filter Topology Asymptotics Real Set Classical MeasureTheory

section kernel_defs
/-!
## Definitions and elementary properties of kernels
-/

/-- Even Hurwitz zeta kernel (function whose Mellin transform will be the even part of the
completed Hurwit zeta function). See `evenKernel_def` for the defining formula, and
`hasSum_int_evenKernel` for an expression as a sum over `ℤ`. -/
@[irreducible] def evenKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic
    (fun ξ : ℝ ↦ rexp (-π * ξ ^ 2 * x) * re (jacobiTheta₂ (ξ * I * x) (I * x))) 1 by
      intro ξ
      simp only [ofReal_add, ofReal_one, add_mul, one_mul, jacobiTheta₂_add_left']
      have : cexp (-↑π * I * ((I * ↑x) + 2 * (↑ξ * I * ↑x))) = rexp (π * (x + 2 * ξ * x)) := by
        ring_nf
        simp only [I_sq, mul_neg, mul_one, neg_mul, neg_neg, sub_neg_eq_add, ofReal_exp, ofReal_add,
          ofReal_mul, ofReal_ofNat]
      rw [this, re_ofReal_mul, ← mul_assoc, ← Real.exp_add]
      congr
      ring).lift a

lemma evenKernel_def (a x : ℝ) :
    ↑(evenKernel ↑a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x) := by
  unfold evenKernel
  simp only [neg_mul, Function.Periodic.lift_coe, ofReal_mul, ofReal_exp, ofReal_neg, ofReal_pow,
    re_eq_add_conj, jacobiTheta₂_conj, map_mul, conj_ofReal, conj_I, mul_neg, neg_neg,
    jacobiTheta₂_neg_left, ← mul_two, mul_div_cancel_right₀ _ (two_ne_zero' ℂ)]

/-- For `x ≤ 0` the defining sum diverges, so the kernel is 0. -/
lemma evenKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : evenKernel a x = 0 := by
  have : (I * ↑x).im ≤ 0 := by rwa [I_mul_im, ofReal_re]
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_inj, evenKernel_def, jacobiTheta₂_undef _ this, mul_zero, ofReal_zero]

/-- Cosine Hurwitz zeta kernel. See `cosKernel_def` for the defining formula, and
`hasSum_int_cosKernel` for expression as a sum. -/
@[irreducible] def cosKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun ξ : ℝ ↦ re (jacobiTheta₂ ξ (I * x))) 1 by
    intro ξ; simp_rw [ofReal_add, ofReal_one, jacobiTheta₂_add_left]).lift a

lemma cosKernel_def (a x : ℝ) : ↑(cosKernel ↑a x) = jacobiTheta₂ a (I * x) := by
  unfold cosKernel
  simp only [Function.Periodic.lift_coe, re_eq_add_conj, jacobiTheta₂_conj, conj_ofReal, map_mul,
    conj_I, neg_mul, neg_neg, ← mul_two, mul_div_cancel_right₀ _ (two_ne_zero' ℂ)]

lemma cosKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : cosKernel a x = 0 := by
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_inj, cosKernel_def, jacobiTheta₂_undef, ofReal_zero]
  rwa [I_mul_im, ofReal_re]

/-- For `a = 0`, both kernels agree. -/
lemma evenKernel_eq_cosKernel_of_zero : evenKernel 0 = cosKernel 0 := by
  ext1 x
  simp only [← QuotientAddGroup.mk_zero, ← ofReal_inj, evenKernel_def, ofReal_zero, sq, mul_zero,
    zero_mul, Complex.exp_zero, one_mul, cosKernel_def]

lemma evenKernel_neg (a : UnitAddCircle) (x : ℝ) : evenKernel (-a) x = evenKernel a x := by
  induction' a using QuotientAddGroup.induction_on' with a'
  simp only [← QuotientAddGroup.mk_neg, ← ofReal_inj, evenKernel_def, ofReal_neg, neg_sq, neg_mul,
    jacobiTheta₂_neg_left]

lemma cosKernel_neg (a : UnitAddCircle) (x : ℝ) : cosKernel (-a) x = cosKernel a x := by
  induction' a using QuotientAddGroup.induction_on' with a'
  simp only [← QuotientAddGroup.mk_neg, ← ofReal_inj, cosKernel_def, ofReal_neg,
    jacobiTheta₂_neg_left]

lemma continuousOn_evenKernel (a : UnitAddCircle) : ContinuousOn (evenKernel a) (Ioi 0) := by
  induction' a using QuotientAddGroup.induction_on' with a'
  apply continuous_re.comp_continuousOn (f := fun x ↦ (evenKernel a' x : ℂ))
  simp only [evenKernel_def a']
  refine ContinuousAt.continuousOn (fun x hx ↦ ((Continuous.continuousAt ?_).mul ?_))
  · exact Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal)
  · have h := continuousAt_jacobiTheta₂ (a' * I * x) (?_ : 0 < im (I * x))
    · exact h.comp (f := fun u : ℝ ↦ (a' * I * u, I * u)) (by fun_prop)
    · rwa [mul_im, I_re, I_im, zero_mul, one_mul, zero_add, ofReal_re]

lemma continuousOn_cosKernel (a : UnitAddCircle) : ContinuousOn (cosKernel a) (Ioi 0) := by
  induction' a using QuotientAddGroup.induction_on' with a'
  apply continuous_re.comp_continuousOn (f := fun x ↦ (cosKernel a' x : ℂ))
  simp only [cosKernel_def]
  refine ContinuousAt.continuousOn (fun x hx ↦ ?_)
  have : 0 < im (I * x) := by rwa [mul_im, I_re, I_im, zero_mul, one_mul, zero_add, ofReal_re]
  exact (continuousAt_jacobiTheta₂ a' this).comp (f := fun u : ℝ ↦ (_, I * u)) (by fun_prop)

lemma evenKernel_functional_equation (a : UnitAddCircle) (x : ℝ) :
    evenKernel a x = 1 / x ^ (1 / 2 : ℝ) * cosKernel a (1 / x) := by
  rcases le_or_lt x 0 with hx | hx
  · rw [evenKernel_undef _ hx, cosKernel_undef, mul_zero]
    exact div_nonpos_of_nonneg_of_nonpos zero_le_one hx
  induction' a using QuotientAddGroup.induction_on' with a
  rw [← ofReal_inj, ofReal_mul, evenKernel_def, cosKernel_def, jacobiTheta₂_functional_equation]
  have h1 : I * ↑(1 / x) = -1 / (I * x) := by
    push_cast
    rw [← div_div, mul_one_div, div_I, neg_one_mul, neg_neg]
  have hx' : I * x ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  have h2 : a * I * x / (I * x) = a := by
    rw [div_eq_iff hx']
    ring
  have h3 : 1 / (-I * (I * x)) ^ (1 / 2 : ℂ) = 1 / ↑(x ^ (1 / 2 : ℝ)) := by
    rw [neg_mul, ← mul_assoc, I_mul_I, neg_one_mul, neg_neg,ofReal_cpow hx.le, ofReal_div,
      ofReal_one, ofReal_ofNat]
  have h4 : -π * I * (a * I * x) ^ 2 / (I * x) = - (-π * a ^ 2 * x) := by
    rw [mul_pow, mul_pow, I_sq, div_eq_iff hx']
    ring
  rw [h1, h2, h3, h4, ← mul_assoc, mul_comm (cexp _), mul_assoc _ (cexp _) (cexp _),
    ← Complex.exp_add, neg_add_self, Complex.exp_zero, mul_one, ofReal_div, ofReal_one]

end kernel_defs

section asymp

/-!
## Formulae for the kernels as sums
-/

lemma hasSum_int_evenKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ rexp (-π * (n + a) ^ 2 * t)) (evenKernel a t) := by
  rw [← hasSum_ofReal, evenKernel_def]
  have (n : ℤ) : ↑(rexp (-π * (↑n + a) ^ 2 * t)) =
      cexp (-↑π * ↑a ^ 2 * ↑t) * jacobiTheta₂_term n (↑a * I * ↑t) (I * ↑t) := by
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    push_cast
    congr
    ring_nf
    simp only [I_sq, mul_neg, neg_mul, mul_one]
  simp only [this]
  exact (hasSum_jacobiTheta₂_term _ (by rwa [I_mul_im, ofReal_re])).mul_left _

lemma hasSum_int_cosKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(cosKernel a t) := by
  rw [cosKernel_def a t]
  have (n : ℤ) : cexp (2 * ↑π * I * ↑a * ↑n) * ↑(rexp (-π * ↑n ^ 2 * t)) =
      jacobiTheta₂_term n (↑a) (I * ↑t) := by
    rw [jacobiTheta₂_term, ofReal_exp, ← Complex.exp_add]
    push_cast
    ring_nf
    simp only [I_sq, mul_neg, neg_mul, mul_one, sub_eq_add_neg]
  simp only [this]
  exact hasSum_jacobiTheta₂_term a (by rwa [I_mul_im, ofReal_re] : 0 < im (I * t))

/-- Modified version of `hasSum_int_evenKernel` omitting the constant term at `∞`. -/
lemma hasSum_int_evenKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ if n + a = 0 then 0 else rexp (-π * (n + a) ^ 2 * t))
    (evenKernel a t - if (a : UnitAddCircle) = 0 then 1 else 0) := by
  simp_rw [AddCircle.coe_eq_zero_iff, zsmul_one]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    simp_rw [← Int.cast_add, Int.cast_eq_zero, add_eq_zero_iff_eq_neg]
    simpa only [Int.cast_add, neg_mul, Int.cast_neg, add_left_neg, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, zero_mul, Real.exp_zero]
      using hasSum_ite_sub_hasSum (hasSum_int_evenKernel (k : ℝ) ht) (-k)
  · suffices ∀ (n : ℤ), n + a ≠ 0 by simpa [this] using hasSum_int_evenKernel a ht
    contrapose! h
    let ⟨n, hn⟩ := h
    exact ⟨-n, by rwa [Int.cast_neg, neg_eq_iff_add_eq_zero]⟩

lemma hasSum_int_cosKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ if n = 0 then 0 else cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t))
    (↑(cosKernel a t) - 1) := by
  simpa using hasSum_ite_sub_hasSum (hasSum_int_cosKernel a ht) 0

lemma hasSum_nat_cosKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ 2 * Real.cos (2 * π * a * (n + 1)) * rexp (-π * (n + 1) ^ 2 * t))
    (cosKernel a t - 1) := by
  rw [← hasSum_ofReal, ofReal_sub, ofReal_one]
  have := (hasSum_int_cosKernel a ht).sum_nat_of_sum_int
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Nat.cast_zero, neg_zero, Int.cast_zero, zero_pow two_ne_zero,
    mul_zero, zero_mul, Complex.exp_zero, Real.exp_zero, ofReal_one, mul_one, Int.cast_neg,
    Int.cast_natCast, neg_sq, ← add_mul, add_sub_assoc, ← sub_sub, sub_self, zero_sub,
    ← sub_eq_add_neg, mul_neg] at this
  refine this.congr_fun <| funext fun n ↦ ?_
  push_cast
  rw [Complex.cos, mul_div_cancel₀ _ two_ne_zero]
  congr 3 <;> ring

/-!
## Asymptotics of the kernels as `t → ∞`
-/

/-- The function `evenKernel a - L` has exponential decay at `+∞`, where `L = 1` if
`a = 0` and `L = 0` otherwise. -/
lemma isBigO_atTop_evenKernel_sub (a : UnitAddCircle) : ∃ p : ℝ, 0 < p ∧
    (evenKernel a · - (if a = 0 then 1 else 0)) =O[atTop] (rexp <| -p * ·) := by
  obtain ⟨b, _, rfl⟩ := a.eq_coe_Ico
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub b
  refine ⟨p, hp, (EventuallyEq.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [← (hasSum_int_evenKernel b ht).tsum_eq, HurwitzKernelBounds.F_int,
    HurwitzKernelBounds.f_int, pow_zero, one_mul, Function.Periodic.lift_coe]

/-- The function `cosKernel a - 1` has exponential decay at `+∞`, for any `a`. -/
lemma isBigO_atTop_cosKernel_sub (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (cosKernel a · - 1) (fun x ↦ Real.exp (-p * x)) := by
  induction' a using QuotientAddGroup.induction_on with a
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_zero_sub zero_le_one
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  simp only [eq_false_intro one_ne_zero, if_false, sub_zero]
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [← (hasSum_nat_cosKernel₀ a ht).tsum_eq, HurwitzKernelBounds.F_nat]
  apply tsum_of_norm_bounded ((HurwitzKernelBounds.summable_f_nat 0 1 ht).hasSum.mul_left 2)
  intro n
  rw [norm_mul, norm_mul, norm_two, mul_assoc, mul_le_mul_iff_of_pos_left two_pos,
    norm_of_nonneg (exp_pos _).le, HurwitzKernelBounds.f_nat, pow_zero, one_mul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (exp_pos _).le (abs_cos_le_one _)

end asymp

section FEPair
/-!
## Construction of a FE-pair
-/

/-- A `WeakFEPair` structure with `f = evenKernel a` and `g = cosKernel a`. -/
def hurwitzEvenFEPair (a : UnitAddCircle) : WeakFEPair ℂ where
  f := ofReal' ∘ evenKernel a
  g := ofReal' ∘ cosKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_evenKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_cosKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hk := one_half_pos
  hε := one_ne_zero
  f₀ := if a = 0 then 1 else 0
  hf_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_evenKernel_sub a
    rw [← isBigO_norm_left] at hv' ⊢
    conv at hv' =>
      enter [2, x]; rw [← norm_real, ofReal_sub, apply_ite ((↑) : ℝ → ℂ), ofReal_one, ofReal_zero]
    exact hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  g₀ := 1
  hg_top r := by
    obtain ⟨p, hp, hp'⟩ := isBigO_atTop_cosKernel_sub a
    rw [← isBigO_norm_left] at hp' ⊢
    have (x : ℝ) : ‖(ofReal' ∘ cosKernel a) x - 1‖ = ‖cosKernel a x - 1‖ := by
      rw [← norm_real, ofReal_sub, ofReal_one, Function.comp_apply]
    simp only [this]
    exact hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp _).isBigO
  h_feq x hx := by
    simp_rw [Function.comp_apply, one_mul, smul_eq_mul, ← ofReal_mul,
      evenKernel_functional_equation, one_div x, one_div x⁻¹, inv_rpow (le_of_lt hx),
      one_div, inv_inv]

lemma hurwitzEvenFEPair_zero_symm :
    (hurwitzEvenFEPair 0).symm = hurwitzEvenFEPair 0 := by
  unfold hurwitzEvenFEPair WeakFEPair.symm
  congr 1 <;> simp only [evenKernel_eq_cosKernel_of_zero, inv_one, if_true]

lemma hurwitzEvenFEPair_neg (a : UnitAddCircle) : hurwitzEvenFEPair (-a) = hurwitzEvenFEPair a := by
  unfold hurwitzEvenFEPair
  congr 1 <;> simp only [Function.comp_def, evenKernel_neg, cosKernel_neg, neg_eq_zero]

/-!
## Definition of the completed even Hurwitz zeta function
-/

/--
The meromorphic function of `s` which agrees with
`1 / 2 * Gamma (s / 2) * π ^ (-s / 2) * ∑' (n : ℤ), 1 / |n + a| ^ s` for `1 < re s`.
-/
def completedHurwitzZetaEven (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).Λ (s / 2)) / 2

/-- The entire function differing from `completedHurwitzZetaEven a s` by a linear combination of
`1 / s` and `1 / (1 - s)`. -/
def completedHurwitzZetaEven₀ (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).Λ₀ (s / 2)) / 2

lemma completedHurwitzZetaEven_eq (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven a s =
    completedHurwitzZetaEven₀ a s - (if a = 0 then 1 else 0) / s - 1 / (1 - s) := by
  rw [completedHurwitzZetaEven, WeakFEPair.Λ, sub_div, sub_div]
  congr 1
  · change completedHurwitzZetaEven₀ a s - (1 / (s / 2)) • (if a = 0 then 1 else 0) / 2 =
      completedHurwitzZetaEven₀ a s - (if a = 0 then 1 else 0) / s
    rw [smul_eq_mul, mul_comm, mul_div_assoc, div_div, div_mul_cancel₀ _ two_ne_zero, mul_one_div]
  · change (1 / (↑(1 / 2 : ℝ) - s / 2)) • 1 / 2 = 1 / (1 - s)
    push_cast
    rw [smul_eq_mul, mul_one, ← sub_div, div_div, div_mul_cancel₀ _ two_ne_zero]

/--
The meromorphic function of `s` which agrees with
`Gamma (s / 2) * π ^ (-s / 2) * ∑' n : ℕ, cos (2 * π * a * n) / n ^ s` for `1 < re s`.
-/
def completedCosZeta (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).symm.Λ (s / 2)) / 2

/-- The entire function differing from `completedCosZeta a s` by a linear combination of
`1 / s` and `1 / (1 - s)`. -/
def completedCosZeta₀ (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).symm.Λ₀ (s / 2)) / 2

lemma completedCosZeta_eq (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta a s =
    completedCosZeta₀ a s - 1 / s - (if a = 0 then 1 else 0) / (1 - s) := by
  rw [completedCosZeta, WeakFEPair.Λ, sub_div, sub_div]
  congr 1
  · rw [completedCosZeta₀, WeakFEPair.symm, hurwitzEvenFEPair, smul_eq_mul, mul_one, div_div,
      div_mul_cancel₀ _ (two_ne_zero' ℂ)]
  · simp_rw [WeakFEPair.symm, hurwitzEvenFEPair, push_cast, inv_one, smul_eq_mul,
      mul_comm _ (if _ then _ else _), mul_div_assoc, div_div, ← sub_div,
      div_mul_cancel₀ _ (two_ne_zero' ℂ), mul_one_div]

/-!
## Parity and functional equations
-/

lemma completedHurwitzZetaEven_neg (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven (-a) s = completedHurwitzZetaEven a s := by
  simp only [completedHurwitzZetaEven, hurwitzEvenFEPair_neg]

lemma completedHurwitzZetaEven₀_neg (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven₀ (-a) s = completedHurwitzZetaEven₀ a s := by
  simp only [completedHurwitzZetaEven₀, hurwitzEvenFEPair_neg]

lemma completedCosZeta_neg (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta (-a) s = completedCosZeta a s := by
  simp only [completedCosZeta, hurwitzEvenFEPair_neg]

lemma completedCosZeta₀_neg (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta₀ (-a) s = completedCosZeta₀ a s := by
  simp only [completedCosZeta₀, hurwitzEvenFEPair_neg]

/-- Functional equation for the even Hurwitz zeta function. -/
lemma completedHurwitzZetaEven_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven a (1 - s) = completedCosZeta a s := by
  rw [completedHurwitzZetaEven, completedCosZeta, sub_div,
    (by norm_num : (1 / 2 : ℂ) = ↑(1 / 2 : ℝ)),
    (by rfl : (1 / 2 : ℝ) = (hurwitzEvenFEPair a).k),
    (hurwitzEvenFEPair a).functional_equation (s / 2),
    (by rfl : (hurwitzEvenFEPair a).ε = 1),
    one_smul]

/-- Functional equation for the even Hurwitz zeta function with poles removed. -/
lemma completedHurwitzZetaEven₀_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven₀ a (1 - s) = completedCosZeta₀ a s := by
  rw [completedHurwitzZetaEven₀, completedCosZeta₀, sub_div,
    (by norm_num : (1 / 2 : ℂ) = ↑(1 / 2 : ℝ)),
    (by rfl : (1 / 2 : ℝ) = (hurwitzEvenFEPair a).k),
    (hurwitzEvenFEPair a).functional_equation₀ (s / 2),
    (by rfl : (hurwitzEvenFEPair a).ε = 1),
    one_smul]

/-- Functional equation for the even Hurwitz zeta function (alternative form). -/
lemma completedCosZeta_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta a (1 - s) = completedHurwitzZetaEven a s := by
  rw [← completedHurwitzZetaEven_one_sub, sub_sub_cancel]

/-- Functional equation for the even Hurwitz zeta function with poles removed (alternative form). -/
lemma completedCosZeta₀_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta₀ a (1 - s) = completedHurwitzZetaEven₀ a s := by
  rw [← completedHurwitzZetaEven₀_one_sub, sub_sub_cancel]

end FEPair
