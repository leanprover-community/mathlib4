/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Even Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the meromorphic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`hurwitzZetaEven a s = 1 / 2 * ∑' n : ℤ, 1 / |n + a| ^ s`

and

`cosZeta a s = ∑' n : ℕ, cos (2 * π * a * n) / |n| ^ s`.

Note that the term for `n = -a` in the first sum is omitted if `a` is an integer, and the term for
`n = 0` is omitted in the second sum (always).

Of course, we cannot *define* these functions by the above formulae (since existence of the
meromorphic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function.

We also define completed versions of these functions with nicer functional equations (satisfying
`completedHurwitzZetaEven a s = Gammaℝ s * hurwitzZetaEven a s`, and similarly for `cosZeta`); and
modified versions with a subscript `0`, which are entire functions differing from the above by
multiples of `1 / s` and `1 / (1 - s)`.

## Main definitions and theorems
* `hurwitzZetaEven` and `cosZeta`: the zeta functions
* `completedHurwitzZetaEven` and `completedCosZeta`: completed variants
* `differentiableAt_hurwitzZetaEven` and `differentiableAt_cosZeta`:
  differentiability away from `s = 1`
* `completedHurwitzZetaEven_one_sub`: the functional equation
  `completedHurwitzZetaEven a (1 - s) = completedCosZeta a s`
* `hasSum_int_hurwitzZetaEven` and `hasSum_nat_cosZeta`: relation between the zeta functions and
  the corresponding Dirichlet series for `1 < re s`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section
noncomputable section

open Complex Filter Topology Asymptotics Real Set MeasureTheory

namespace HurwitzZeta

section kernel_defs
/-!
## Definitions and elementary properties of kernels
-/

/-- Even Hurwitz zeta kernel (function whose Mellin transform will be the even part of the
completed Hurwitz zeta function). See `evenKernel_def` for the defining formula, and
`hasSum_int_evenKernel` for an expression as a sum over `ℤ`. -/
@[irreducible] def evenKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic
    (fun ξ : ℝ ↦ rexp (-π * ξ ^ 2 * x) * re (jacobiTheta₂ (ξ * I * x) (I * x))) 1 by
      intro ξ
      simp only [ofReal_add, ofReal_one, add_mul, one_mul, jacobiTheta₂_add_left']
      have : cexp (-↑π * I * ((I * ↑x) + 2 * (↑ξ * I * ↑x))) = rexp (π * (x + 2 * ξ * x)) := by
        ring_nf
        simp [I_sq]
      rw [this, re_ofReal_mul, ← mul_assoc, ← Real.exp_add]
      congr
      ring).lift a

lemma evenKernel_def (a x : ℝ) :
    ↑(evenKernel ↑a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x) := by
  simp [evenKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
    mul_div_cancel_right₀ _ (two_ne_zero' ℂ)]

/-- For `x ≤ 0` the defining sum diverges, so the kernel is 0. -/
lemma evenKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : evenKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H a' => simp [← ofReal_inj, evenKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im ≤ 0)]

/-- Cosine Hurwitz zeta kernel. See `cosKernel_def` for the defining formula, and
`hasSum_int_cosKernel` for expression as a sum. -/
@[irreducible] def cosKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun ξ : ℝ ↦ re (jacobiTheta₂ ξ (I * x))) 1 by
    intro ξ; simp [jacobiTheta₂_add_left]).lift a

lemma cosKernel_def (a x : ℝ) : ↑(cosKernel ↑a x) = jacobiTheta₂ a (I * x) := by
  simp [cosKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
    mul_div_cancel_right₀ _ (two_ne_zero' ℂ)]

lemma cosKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : cosKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← ofReal_inj, cosKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im ≤ 0)]

/-- For `a = 0`, both kernels agree. -/
lemma evenKernel_eq_cosKernel_of_zero : evenKernel 0 = cosKernel 0 := by
  ext1 x
  simp [← QuotientAddGroup.mk_zero, ← ofReal_inj, evenKernel_def, cosKernel_def]

@[simp]
lemma evenKernel_neg (a : UnitAddCircle) (x : ℝ) : evenKernel (-a) x = evenKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← QuotientAddGroup.mk_neg, ← ofReal_inj, evenKernel_def, jacobiTheta₂_neg_left]

@[simp]
lemma cosKernel_neg (a : UnitAddCircle) (x : ℝ) : cosKernel (-a) x = cosKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← QuotientAddGroup.mk_neg, ← ofReal_inj, cosKernel_def]

lemma continuousOn_evenKernel (a : UnitAddCircle) : ContinuousOn (evenKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  apply continuous_re.comp_continuousOn (f := fun x ↦ (evenKernel a' x : ℂ))
  simp only [evenKernel_def]
  refine continuousOn_of_forall_continuousAt (fun x hx ↦ .mul (by fun_prop) ?_)
  exact (continuousAt_jacobiTheta₂ (a' * I * x) <| by simpa).comp
    (f := fun u : ℝ ↦ (a' * I * u, I * u)) (by fun_prop)

lemma continuousOn_cosKernel (a : UnitAddCircle) : ContinuousOn (cosKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  apply continuous_re.comp_continuousOn (f := fun x ↦ (cosKernel a' x : ℂ))
  simp only [cosKernel_def]
  refine continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)
  exact (continuousAt_jacobiTheta₂ a' <| by simpa).comp
    (f := fun u : ℝ ↦ ((a' : ℂ), I * u)) (by fun_prop)

lemma evenKernel_functional_equation (a : UnitAddCircle) (x : ℝ) :
    evenKernel a x = 1 / x ^ (1 / 2 : ℝ) * cosKernel a (1 / x) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [evenKernel_undef _ hx, cosKernel_undef, mul_zero]
    exact div_nonpos_of_nonneg_of_nonpos zero_le_one hx
  induction a using QuotientAddGroup.induction_on with | H a =>
  rw [← ofReal_inj, ofReal_mul, evenKernel_def, cosKernel_def, jacobiTheta₂_functional_equation]
  have h1 : I * ↑(1 / x) = -1 / (I * x) := by
    push_cast
    rw [← div_div, mul_one_div, div_I, neg_one_mul, neg_neg]
  have hx' : I * x ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  have h2 : a * I * x / (I * x) = a := by
    rw [div_eq_iff hx']
    ring
  have h3 : 1 / (-I * (I * x)) ^ (1 / 2 : ℂ) = 1 / ↑(x ^ (1 / 2 : ℝ)) := by
    rw [neg_mul, ← mul_assoc, I_mul_I, neg_one_mul, neg_neg, ofReal_cpow hx.le, ofReal_div,
      ofReal_one, ofReal_ofNat]
  have h4 : -π * I * (a * I * x) ^ 2 / (I * x) = - (-π * a ^ 2 * x) := by
    rw [mul_pow, mul_pow, I_sq, div_eq_iff hx']
    ring
  rw [h1, h2, h3, h4, ← mul_assoc, mul_comm (cexp _), mul_assoc _ (cexp _) (cexp _),
    ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one, ofReal_div, ofReal_one]

end kernel_defs

section asymp

/-!
## Formulae for the kernels as sums
-/

lemma hasSum_int_evenKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ rexp (-π * (n + a) ^ 2 * t)) (evenKernel a t) := by
  rw [← hasSum_ofReal, evenKernel_def]
  have (n : ℤ) : cexp (-(π * (n + a) ^ 2 * t)) = cexp (-(π * a ^ 2 * t)) *
      jacobiTheta₂_term n (a * I * t) (I * t) := by
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    grind [I_sq]
  simpa [this] using (hasSum_jacobiTheta₂_term _ (by simpa)).mul_left _

lemma hasSum_int_cosKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(cosKernel a t) := by
  rw [cosKernel_def a t]
  have (n : ℤ) : cexp (2 * π * I * a * n) * cexp (-(π * n ^ 2 * t)) =
      jacobiTheta₂_term n a (I * ↑t) := by
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    ring_nf
    simp [sub_eq_add_neg]
  simpa [this] using hasSum_jacobiTheta₂_term _ (by simpa)

/-- Modified version of `hasSum_int_evenKernel` omitting the constant term at `∞`. -/
lemma hasSum_int_evenKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ if n + a = 0 then 0 else rexp (-π * (n + a) ^ 2 * t))
    (evenKernel a t - if (a : UnitAddCircle) = 0 then 1 else 0) := by
  haveI := Classical.propDecidable -- speed up instance search for `if / then / else`
  simp_rw [AddCircle.coe_eq_zero_iff, zsmul_one]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    simpa [← Int.cast_add, add_eq_zero_iff_eq_neg]
      using hasSum_ite_sub_hasSum (hasSum_int_evenKernel (k : ℝ) ht) (-k)
  · suffices ∀ (n : ℤ), n + a ≠ 0 by simpa [this] using hasSum_int_evenKernel a ht
    contrapose! h
    let ⟨n, hn⟩ := h
    exact ⟨-n, by simpa [neg_eq_iff_add_eq_zero]⟩

lemma hasSum_int_cosKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ if n = 0 then 0 else cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t))
    (↑(cosKernel a t) - 1) := by
  simpa using hasSum_ite_sub_hasSum (hasSum_int_cosKernel a ht) 0

lemma hasSum_nat_cosKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ 2 * Real.cos (2 * π * a * (n + 1)) * rexp (-π * (n + 1) ^ 2 * t))
    (cosKernel a t - 1) := by
  rw [← hasSum_ofReal, ofReal_sub, ofReal_one]
  have := (hasSum_int_cosKernel a ht).nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Nat.cast_zero, neg_zero, Int.cast_zero, zero_pow two_ne_zero,
    mul_zero, zero_mul, Complex.exp_zero, Real.exp_zero, ofReal_one, mul_one, Int.cast_neg,
    Int.cast_natCast, neg_sq, ← add_mul, add_sub_assoc, ← sub_sub, sub_self, zero_sub,
    ← sub_eq_add_neg, mul_neg] at this
  refine this.congr_fun fun n ↦ ?_
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
  induction a using QuotientAddGroup.induction_on with | H b =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub b
  refine ⟨p, hp, (EventuallyEq.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t h
  simp [← (hasSum_int_evenKernel b h).tsum_eq, HurwitzKernelBounds.F_int, HurwitzKernelBounds.f_int]

/-- The function `cosKernel a - 1` has exponential decay at `+∞`, for any `a`. -/
lemma isBigO_atTop_cosKernel_sub (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (cosKernel a · - 1) (fun x ↦ Real.exp (-p * x)) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_zero_sub zero_le_one
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [eq_false_intro one_ne_zero, if_false, sub_zero,
    ← (hasSum_nat_cosKernel₀ a ht).tsum_eq, HurwitzKernelBounds.F_nat]
  apply tsum_of_norm_bounded ((HurwitzKernelBounds.summable_f_nat 0 1 ht).hasSum.mul_left 2)
  intro n
  rw [norm_mul, norm_mul, norm_two, mul_assoc, mul_le_mul_iff_of_pos_left two_pos,
    norm_of_nonneg (exp_pos _).le, HurwitzKernelBounds.f_nat, pow_zero, one_mul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (exp_pos _).le (abs_cos_le_one _)

end asymp

section FEPair
/-!
## Construction of an FE-pair
-/

/-- A `WeakFEPair` structure with `f = evenKernel a` and `g = cosKernel a`. -/
def hurwitzEvenFEPair (a : UnitAddCircle) : WeakFEPair ℂ where
  f := ofReal ∘ evenKernel a
  g := ofReal ∘ cosKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_evenKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_cosKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 1 / 2
  hk := one_half_pos
  ε := 1
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
    simpa using isBigO_ofReal_left.mpr <| hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO
  h_feq x hx := by simp [← ofReal_mul, evenKernel_functional_equation, inv_rpow (le_of_lt hx)]

@[simp]
lemma hurwitzEvenFEPair_zero_symm :
    (hurwitzEvenFEPair 0).symm = hurwitzEvenFEPair 0 := by
  unfold hurwitzEvenFEPair WeakFEPair.symm
  congr 1 <;> simp [evenKernel_eq_cosKernel_of_zero]

@[simp]
lemma hurwitzEvenFEPair_neg (a : UnitAddCircle) : hurwitzEvenFEPair (-a) = hurwitzEvenFEPair a := by
  unfold hurwitzEvenFEPair
  congr 1 <;> simp [Function.comp_def]

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

@[simp]
lemma completedHurwitzZetaEven_neg (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven (-a) s = completedHurwitzZetaEven a s := by
  simp [completedHurwitzZetaEven]

@[simp]
lemma completedHurwitzZetaEven₀_neg (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven₀ (-a) s = completedHurwitzZetaEven₀ a s := by
  simp [completedHurwitzZetaEven₀]

@[simp]
lemma completedCosZeta_neg (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta (-a) s = completedCosZeta a s := by
  simp [completedCosZeta]

@[simp]
lemma completedCosZeta₀_neg (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta₀ (-a) s = completedCosZeta₀ a s := by
  simp [completedCosZeta₀]

/-- Functional equation for the even Hurwitz zeta function. -/
lemma completedHurwitzZetaEven_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven a (1 - s) = completedCosZeta a s := by
  rw [completedHurwitzZetaEven, completedCosZeta, sub_div,
    (by simp : (1 / 2 : ℂ) = ↑(1 / 2 : ℝ)),
    (by rfl : (1 / 2 : ℝ) = (hurwitzEvenFEPair a).k),
    (hurwitzEvenFEPair a).functional_equation (s / 2),
    (by rfl : (hurwitzEvenFEPair a).ε = 1),
    one_smul]

/-- Functional equation for the even Hurwitz zeta function with poles removed. -/
lemma completedHurwitzZetaEven₀_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven₀ a (1 - s) = completedCosZeta₀ a s := by
  rw [completedHurwitzZetaEven₀, completedCosZeta₀, sub_div,
    (by simp : (1 / 2 : ℂ) = ↑(1 / 2 : ℝ)),
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

/-!
## Differentiability and residues
-/

section FEPair

/--
The even Hurwitz completed zeta is differentiable away from `s = 0` and `s = 1` (and also at
`s = 0` if `a ≠ 0`)
-/
lemma differentiableAt_completedHurwitzZetaEven
    (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 0 ∨ a ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ (completedHurwitzZetaEven a) s := by
  refine (((hurwitzEvenFEPair a).differentiableAt_Λ ?_ (Or.inl ?_)).comp s
      (differentiableAt_id.div_const _)).div_const _
  · rcases hs with h | h <;>
    simp [hurwitzEvenFEPair, h]
  · change s / 2 ≠ ↑(1 / 2 : ℝ)
    rw [ofReal_div, ofReal_one, ofReal_ofNat]
    exact hs' ∘ (div_left_inj' two_ne_zero).mp

lemma differentiable_completedHurwitzZetaEven₀ (a : UnitAddCircle) :
    Differentiable ℂ (completedHurwitzZetaEven₀ a) :=
  ((hurwitzEvenFEPair a).differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

/-- The difference of two completed even Hurwitz zeta functions is differentiable at `s = 1`. -/
lemma differentiableAt_one_completedHurwitzZetaEven_sub_completedHurwitzZetaEven
    (a b : UnitAddCircle) :
    DifferentiableAt ℂ (fun s ↦ completedHurwitzZetaEven a s - completedHurwitzZetaEven b s) 1 := by
  have (s : _) : completedHurwitzZetaEven a s - completedHurwitzZetaEven b s =
      completedHurwitzZetaEven₀ a s - completedHurwitzZetaEven₀ b s -
      ((if a = 0 then 1 else 0) - (if b = 0 then 1 else 0)) / s := by
    simp_rw [completedHurwitzZetaEven_eq, sub_div]
    abel
  rw [funext this]
  refine .sub ?_ <| (differentiable_const _ _).div (differentiable_id _) one_ne_zero
  apply DifferentiableAt.sub <;> apply differentiable_completedHurwitzZetaEven₀

lemma differentiableAt_completedCosZeta
    (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1 ∨ a ≠ 0) :
    DifferentiableAt ℂ (completedCosZeta a) s := by
  refine (((hurwitzEvenFEPair a).symm.differentiableAt_Λ (Or.inl ?_) ?_).comp s
      (differentiableAt_id.div_const _)).div_const _
  · exact div_ne_zero_iff.mpr ⟨hs, two_ne_zero⟩
  · change s / 2 ≠ ↑(1 / 2 : ℝ) ∨ (if a = 0 then 1 else 0) = 0
    refine Or.imp (fun h ↦ ?_) (fun ha ↦ ?_) hs'
    · simpa [push_cast] using h ∘ (div_left_inj' two_ne_zero).mp
    · simpa

lemma differentiable_completedCosZeta₀ (a : UnitAddCircle) :
    Differentiable ℂ (completedCosZeta₀ a) :=
  ((hurwitzEvenFEPair a).symm.differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

private lemma tendsto_div_two_punctured_nhds (a : ℂ) :
    Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] a) (𝓝[≠] (a / 2)) :=
  le_of_eq ((Homeomorph.mulRight₀ _ (inv_ne_zero (two_ne_zero' ℂ))).map_punctured_nhds_eq a)

/-- The residue of `completedHurwitzZetaEven a s` at `s = 1` is equal to `1`. -/
lemma completedHurwitzZetaEven_residue_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ (s - 1) * completedHurwitzZetaEven a s) (𝓝[≠] 1) (𝓝 1) := by
  have h1 : Tendsto (fun s : ℂ ↦ (s - ↑(1 / 2 : ℝ)) * _) (𝓝[≠] ↑(1 / 2 : ℝ))
    (𝓝 ((1 : ℂ) * (1 : ℂ))) := (hurwitzEvenFEPair a).Λ_residue_k
  simp only [push_cast, one_mul] at h1
  refine (h1.comp <| tendsto_div_two_punctured_nhds 1).congr (fun s ↦ ?_)
  rw [completedHurwitzZetaEven, Function.comp_apply, ← sub_div, div_mul_eq_mul_div, mul_div_assoc]

/-- The residue of `completedHurwitzZetaEven a s` at `s = 0` is equal to `-1` if `a = 0`, and `0`
otherwise. -/
lemma completedHurwitzZetaEven_residue_zero (a : UnitAddCircle) :
    Tendsto (fun s ↦ s * completedHurwitzZetaEven a s) (𝓝[≠] 0) (𝓝 (if a = 0 then -1 else 0)) := by
  have h1 : Tendsto (fun s : ℂ ↦ s * _) (𝓝[≠] 0)
    (𝓝 (-(if a = 0 then 1 else 0))) := (hurwitzEvenFEPair a).Λ_residue_zero
  have : -(if a = 0 then (1 : ℂ) else 0) = (if a = 0 then -1 else 0) := by { split_ifs <;> simp }
  simp only [this, push_cast] at h1
  refine (h1.comp <| zero_div (2 : ℂ) ▸ (tendsto_div_two_punctured_nhds 0)).congr (fun s ↦ ?_)
  simp [completedHurwitzZetaEven, div_mul_eq_mul_div, mul_div_assoc]

lemma completedCosZeta_residue_zero (a : UnitAddCircle) :
    Tendsto (fun s ↦ s * completedCosZeta a s) (𝓝[≠] 0) (𝓝 (-1)) := by
  have h1 : Tendsto (fun s : ℂ ↦ s * _) (𝓝[≠] 0)
    (𝓝 (-1)) := (hurwitzEvenFEPair a).symm.Λ_residue_zero
  refine (h1.comp <| zero_div (2 : ℂ) ▸ (tendsto_div_two_punctured_nhds 0)).congr (fun s ↦ ?_)
  simp [completedCosZeta, div_mul_eq_mul_div, mul_div_assoc]

end FEPair

/-!
## Relation to the Dirichlet series for `1 < re s`
-/

/-- Formula for `completedCosZeta` as a Dirichlet series in the convergence range
(first version, with sum over `ℤ`). -/
lemma hasSum_int_completedCosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ Gammaℝ s * cexp (2 * π * I * a * n) / (↑|n| : ℂ) ^ s / 2)
    (completedCosZeta a s) := by
  let c (n : ℤ) : ℂ := cexp (2 * π * I * a * n) / 2
  have hF t (ht : 0 < t) : HasSum (fun n : ℤ ↦ if n = 0 then 0 else c n * rexp (-π * n ^ 2 * t))
      ((cosKernel a t - 1) / 2) := by
    refine ((hasSum_int_cosKernel₀ a ht).div_const 2).congr_fun fun n ↦ ?_
    split_ifs <;> simp [c, div_mul_eq_mul_div]
  simp only [← Int.cast_eq_zero (α := ℝ)] at hF
  rw [show completedCosZeta a s = mellin (fun t ↦ (cosKernel a t - 1 : ℂ) / 2) (s / 2) by
    rw [mellin_div_const, completedCosZeta]
    congr 1
    refine ((hurwitzEvenFEPair a).symm.hasMellin (?_ : 1 / 2 < (s / 2).re)).2.symm
    rwa [div_ofNat_re, div_lt_div_iff_of_pos_right two_pos]]
  refine (hasSum_mellin_pi_mul_sq (zero_lt_one.trans hs) hF ?_).congr_fun fun n ↦ ?_
  · apply (((summable_one_div_int_add_rpow 0 s.re).mpr hs).div_const 2).of_norm_bounded
    intro i
    simp only [c, (by { push_cast; ring } : 2 * π * I * a * i = ↑(2 * π * a * i) * I), norm_div,
      RCLike.norm_ofNat, Complex.norm_exp_ofReal_mul_I, add_zero, norm_one,
      norm_of_nonneg (by positivity : 0 ≤ |(i : ℝ)| ^ s.re), div_right_comm, le_rfl]
  · simp [c, ← Int.cast_abs, div_right_comm, mul_div_assoc]

/-- Formula for `completedCosZeta` as a Dirichlet series in the convergence range
(second version, with sum over `ℕ`). -/
lemma hasSum_nat_completedCosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ if n = 0 then 0 else Gammaℝ s * Real.cos (2 * π * a * n) / (n : ℂ) ^ s)
    (completedCosZeta a s) := by
  have aux : ((|0| : ℤ) : ℂ) ^ s = 0 := by
    rw [abs_zero, Int.cast_zero, zero_cpow (ne_zero_of_one_lt_re hs)]
  have hint := (hasSum_int_completedCosZeta a hs).nat_add_neg
  rw [aux, div_zero, zero_div, add_zero] at hint
  refine hint.congr_fun fun n ↦ ?_
  split_ifs with h
  · simp only [h, Nat.cast_zero, aux, div_zero, zero_div, neg_zero, zero_add]
  · simp only [ofReal_cos, ofReal_mul, ofReal_ofNat, ofReal_natCast, Complex.cos,
      show 2 * π * a * n * I = 2 * π * I * a * n by ring, neg_mul, mul_div_assoc,
      div_right_comm _ (2 : ℂ), Int.cast_natCast, Nat.abs_cast, Int.cast_neg, mul_neg, abs_neg, ←
      mul_add, ← add_div]

/-- Formula for `completedHurwitzZetaEven` as a Dirichlet series in the convergence range. -/
lemma hasSum_int_completedHurwitzZetaEven (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ Gammaℝ s / (↑|n + a| : ℂ) ^ s / 2) (completedHurwitzZetaEven a s) := by
  have hF (t : ℝ) (ht : 0 < t) : HasSum (fun n : ℤ ↦ if n + a = 0 then 0
      else (1 / 2 : ℂ) * rexp (-π * (n + a) ^ 2 * t))
      ((evenKernel a t - (if (a : UnitAddCircle) = 0 then 1 else 0 : ℝ)) / 2) := by
    refine (ofReal_sub .. ▸ (hasSum_ofReal.mpr (hasSum_int_evenKernel₀ a ht)).div_const
      2).congr_fun fun n ↦ ?_
    split_ifs
    · rw [ofReal_zero, zero_div]
    · rw [mul_comm, mul_one_div]
  rw [show completedHurwitzZetaEven a s = mellin (fun t ↦ ((evenKernel (↑a) t : ℂ) -
        ↑(if (a : UnitAddCircle) = 0 then 1 else 0 : ℝ)) / 2) (s / 2) by
    simp_rw [mellin_div_const, apply_ite ofReal, ofReal_one, ofReal_zero]
    refine congr_arg (· / 2) ((hurwitzEvenFEPair a).hasMellin (?_ : 1 / 2 < (s / 2).re)).2.symm
    rwa [div_ofNat_re, div_lt_div_iff_of_pos_right two_pos]]
  refine (hasSum_mellin_pi_mul_sq (zero_lt_one.trans hs) hF ?_).congr_fun fun n ↦ ?_
  · simp_rw [← mul_one_div ‖_‖]
    apply Summable.mul_left
    rwa [summable_one_div_int_add_rpow]
  · rw [mul_one_div, div_right_comm]

/-!
## The un-completed even Hurwitz zeta
-/

/-- Technical lemma which will give us differentiability of Hurwitz zeta at `s = 0`. -/
lemma differentiableAt_update_of_residue
    {Λ : ℂ → ℂ} (hf : ∀ (s : ℂ) (_ : s ≠ 0) (_ : s ≠ 1), DifferentiableAt ℂ Λ s)
    {L : ℂ} (h_lim : Tendsto (fun s ↦ s * Λ s) (𝓝[≠] 0) (𝓝 L)) (s : ℂ) (hs' : s ≠ 1) :
    DifferentiableAt ℂ (Function.update (fun s ↦ Λ s / Gammaℝ s) 0 (L / 2)) s := by
  have claim (t) (ht : t ≠ 0) (ht' : t ≠ 1) : DifferentiableAt ℂ (fun u : ℂ ↦ Λ u / Gammaℝ u) t :=
    (hf t ht ht').mul differentiable_Gammaℝ_inv.differentiableAt
  have claim2 : Tendsto (fun s : ℂ ↦ Λ s / Gammaℝ s) (𝓝[≠] 0) (𝓝 <| L / 2) := by
    refine Tendsto.congr' ?_ (h_lim.div Gammaℝ_residue_zero two_ne_zero)
    filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 0)
    rw [Pi.div_apply, ← div_div, mul_div_cancel_left₀ _ hs]
  rcases ne_or_eq s 0 with hs | rfl
  · -- Easy case : `s ≠ 0`
    refine (claim s hs hs').congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with x hx
    simp [Function.update_of_ne hx]
  · -- Hard case : `s = 0`
    simp_rw [← claim2.limUnder_eq]
    have S_nhds : {(1 : ℂ)}ᶜ ∈ 𝓝 (0 : ℂ) := isOpen_compl_singleton.mem_nhds hs'
    refine ((Complex.differentiableOn_update_limUnder_of_isLittleO S_nhds
      (fun t ht ↦ (claim t ht.2 ht.1).differentiableWithinAt) ?_) 0 hs').differentiableAt S_nhds
    simp only [Gammaℝ, zero_div, div_zero, Complex.Gamma_zero, mul_zero, sub_zero]
    -- Remains to show completed zeta is `o (s ^ (-1))` near 0.
    refine (isBigO_const_of_tendsto claim2 <| one_ne_zero' ℂ).trans_isLittleO ?_
    rw [isLittleO_iff_tendsto']
    · exact Tendsto.congr (fun x ↦ by rw [← one_div, one_div_one_div]) nhdsWithin_le_nhds
    · exact eventually_of_mem self_mem_nhdsWithin fun x hx hx' ↦ (hx <| inv_eq_zero.mp hx').elim

/-- The even part of the Hurwitz zeta function, i.e. the meromorphic function of `s` which agrees
with `1 / 2 * ∑' (n : ℤ), 1 / |n + a| ^ s` for `1 < re s` -/
noncomputable def hurwitzZetaEven (a : UnitAddCircle) :=
  Function.update (fun s ↦ completedHurwitzZetaEven a s / Gammaℝ s)
  0 (if a = 0 then -1 / 2 else 0)

lemma hurwitzZetaEven_def_of_ne_or_ne {a : UnitAddCircle} {s : ℂ} (h : a ≠ 0 ∨ s ≠ 0) :
    hurwitzZetaEven a s = completedHurwitzZetaEven a s / Gammaℝ s := by
  rw [hurwitzZetaEven]
  rcases ne_or_eq s 0 with h' | rfl
  · rw [Function.update_of_ne h']
  · simpa [Gammaℝ] using h

lemma hurwitzZetaEven_apply_zero (a : UnitAddCircle) :
    hurwitzZetaEven a 0 = if a = 0 then -1 / 2 else 0 :=
  Function.update_self ..

lemma hurwitzZetaEven_neg (a : UnitAddCircle) (s : ℂ) :
    hurwitzZetaEven (-a) s = hurwitzZetaEven a s := by
  simp [hurwitzZetaEven]

/-- The trivial zeroes of the even Hurwitz zeta function. -/
theorem hurwitzZetaEven_neg_two_mul_nat_add_one (a : UnitAddCircle) (n : ℕ) :
    hurwitzZetaEven a (-2 * (n + 1)) = 0 := by
  have : (-2 : ℂ) * (n + 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [hurwitzZetaEven, Function.update_of_ne this, Gammaℝ_eq_zero_iff.mpr ⟨n + 1, by simp⟩,
    div_zero]

/-- The Hurwitz zeta function is differentiable everywhere except at `s = 1`. This is true
even in the delicate case `a = 0` and `s = 0` (where the completed zeta has a pole, but this is
cancelled out by the Gamma factor). -/
lemma differentiableAt_hurwitzZetaEven (a : UnitAddCircle) {s : ℂ} (hs' : s ≠ 1) :
    DifferentiableAt ℂ (hurwitzZetaEven a) s := by
  have := differentiableAt_update_of_residue
    (fun t ht ht' ↦ differentiableAt_completedHurwitzZetaEven a (Or.inl ht) ht')
    (completedHurwitzZetaEven_residue_zero a) s hs'
  simp_rw [div_eq_mul_inv, ite_mul, zero_mul, ← div_eq_mul_inv] at this
  exact this

lemma hurwitzZetaEven_residue_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ (s - 1) * hurwitzZetaEven a s) (𝓝[≠] 1) (𝓝 1) := by
  have : Tendsto (fun s ↦ (s - 1) * completedHurwitzZetaEven a s / Gammaℝ s) (𝓝[≠] 1) (𝓝 1) := by
    simpa only [Gammaℝ_one, inv_one, mul_one] using (completedHurwitzZetaEven_residue_one a).mul
      <| (differentiable_Gammaℝ_inv.continuous.tendsto _).mono_left nhdsWithin_le_nhds
  refine this.congr' ?_
  filter_upwards [eventually_ne_nhdsWithin one_ne_zero] with s hs
  simp [hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs), mul_div_assoc]

lemma differentiableAt_hurwitzZetaEven_sub_one_div (a : UnitAddCircle) :
    DifferentiableAt ℂ (fun s ↦ hurwitzZetaEven a s - 1 / (s - 1) / Gammaℝ s) 1 := by
  suffices DifferentiableAt ℂ
      (fun s ↦ completedHurwitzZetaEven a s / Gammaℝ s - 1 / (s - 1) / Gammaℝ s) 1 by
    apply this.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds one_ne_zero] with x hx
    rw [hurwitzZetaEven, Function.update_of_ne hx]
  simp_rw [← sub_div, div_eq_mul_inv _ (Gammaℝ _)]
  refine DifferentiableAt.mul ?_ differentiable_Gammaℝ_inv.differentiableAt
  simp_rw [completedHurwitzZetaEven_eq, sub_sub, add_assoc]
  conv => enter [2, s, 2]; rw [← neg_sub, div_neg, neg_add_cancel, add_zero]
  exact (differentiable_completedHurwitzZetaEven₀ a _).sub
    <| (differentiableAt_const _).div differentiableAt_id one_ne_zero

/-- Expression for `hurwitzZetaEven a 1` as a limit. (Mathematically `hurwitzZetaEven a 1` is
undefined, but our construction assigns some value to it; this lemma is mostly of interest for
determining what that value is). -/
lemma tendsto_hurwitzZetaEven_sub_one_div_nhds_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ hurwitzZetaEven a s - 1 / (s - 1) / Gammaℝ s) (𝓝 1)
    (𝓝 (hurwitzZetaEven a 1)) := by
  simpa using (differentiableAt_hurwitzZetaEven_sub_one_div a).continuousAt.tendsto

lemma differentiable_hurwitzZetaEven_sub_hurwitzZetaEven (a b : UnitAddCircle) :
    Differentiable ℂ (fun s ↦ hurwitzZetaEven a s - hurwitzZetaEven b s) := by
  intro z
  rcases ne_or_eq z 1 with hz | rfl
  · exact (differentiableAt_hurwitzZetaEven a hz).sub (differentiableAt_hurwitzZetaEven b hz)
  · convert (differentiableAt_hurwitzZetaEven_sub_one_div a).fun_sub
      (differentiableAt_hurwitzZetaEven_sub_one_div b) using 2 with s
    abel

/--
Formula for `hurwitzZetaEven` as a Dirichlet series in the convergence range, with sum over `ℤ`.
-/
lemma hasSum_int_hurwitzZetaEven (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ 1 / (↑|n + a| : ℂ) ^ s / 2) (hurwitzZetaEven a s) := by
  rw [hurwitzZetaEven, Function.update_of_ne (ne_zero_of_one_lt_re hs)]
  have := (hasSum_int_completedHurwitzZetaEven a hs).div_const (Gammaℝ s)
  exact this.congr_fun fun n ↦ by simp only [div_right_comm _ _ (Gammaℝ _),
    div_self (Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs))]

/-- Formula for `hurwitzZetaEven` as a Dirichlet series in the convergence range, with sum over `ℕ`
(version with absolute values) -/
lemma hasSum_nat_hurwitzZetaEven (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ (1 / (↑|n + a| : ℂ) ^ s + 1 / (↑|n + 1 - a| : ℂ) ^ s) / 2)
    (hurwitzZetaEven a s) := by
  refine (hasSum_int_hurwitzZetaEven a hs).nat_add_neg_add_one.congr_fun fun n ↦ ?_
  simp [← abs_neg (n + 1 - a), -neg_sub, neg_sub', add_div]

/-- Formula for `hurwitzZetaEven` as a Dirichlet series in the convergence range, with sum over `ℕ`
(version without absolute values, assuming `a ∈ Icc 0 1`) -/
lemma hasSum_nat_hurwitzZetaEven_of_mem_Icc {a : ℝ} (ha : a ∈ Icc 0 1) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ (1 / (n + a : ℂ) ^ s + 1 / (n + 1 - a : ℂ) ^ s) / 2)
    (hurwitzZetaEven a s) := by
  refine (hasSum_nat_hurwitzZetaEven a hs).congr_fun fun n ↦ ?_
  congr 2 <;>
  rw [abs_of_nonneg (by linarith [ha.1, ha.2])] <;>
  simp

/-!
## The un-completed cosine zeta
-/

/-- The cosine zeta function, i.e. the meromorphic function of `s` which agrees
with `∑' (n : ℕ), cos (2 * π * a * n) / n ^ s` for `1 < re s`. -/
noncomputable def cosZeta (a : UnitAddCircle) :=
  Function.update (fun s : ℂ ↦ completedCosZeta a s / Gammaℝ s) 0 (-1 / 2)

lemma cosZeta_apply_zero (a : UnitAddCircle) : cosZeta a 0 = -1 / 2 :=
  Function.update_self ..

lemma cosZeta_neg (a : UnitAddCircle) (s : ℂ) :
    cosZeta (-a) s = cosZeta a s := by
  simp [cosZeta]

/-- The trivial zeroes of the cosine zeta function. -/
theorem cosZeta_neg_two_mul_nat_add_one (a : UnitAddCircle) (n : ℕ) :
    cosZeta a (-2 * (n + 1)) = 0 := by
  have : (-2 : ℂ) * (n + 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [cosZeta, Function.update_of_ne this,
    Gammaℝ_eq_zero_iff.mpr ⟨n + 1, by rw [neg_mul, Nat.cast_add_one]⟩, div_zero]

/-- The cosine zeta function is differentiable everywhere, except at `s = 1` if `a = 0`. -/
lemma differentiableAt_cosZeta (a : UnitAddCircle) {s : ℂ} (hs' : s ≠ 1 ∨ a ≠ 0) :
    DifferentiableAt ℂ (cosZeta a) s := by
  rcases ne_or_eq s 1 with hs' | rfl
  · exact differentiableAt_update_of_residue (fun _ ht ht' ↦
      differentiableAt_completedCosZeta a ht (Or.inl ht')) (completedCosZeta_residue_zero a) s hs'
  · apply ((differentiableAt_completedCosZeta a one_ne_zero hs').fun_mul
      (differentiable_Gammaℝ_inv.differentiableAt)).congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds one_ne_zero] with x hx
    rw [cosZeta, Function.update_of_ne hx, div_eq_mul_inv]

/-- If `a ≠ 0` then the cosine zeta function is entire. -/
lemma differentiable_cosZeta_of_ne_zero {a : UnitAddCircle} (ha : a ≠ 0) :
    Differentiable ℂ (cosZeta a) :=
  fun _ ↦ differentiableAt_cosZeta a (Or.inr ha)

/-- Formula for `cosZeta` as a Dirichlet series in the convergence range, with sum over `ℤ`. -/
lemma hasSum_int_cosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ cexp (2 * π * I * a * n) / ↑|n| ^ s / 2) (cosZeta a s) := by
  rw [cosZeta, Function.update_of_ne (ne_zero_of_one_lt_re hs)]
  refine ((hasSum_int_completedCosZeta a hs).div_const (Gammaℝ s)).congr_fun fun n ↦ ?_
  rw [mul_div_assoc _ (cexp _), div_right_comm _ (2 : ℂ),
    mul_div_cancel_left₀ _ (Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs))]

/-- Formula for `cosZeta` as a Dirichlet series in the convergence range, with sum over `ℕ`. -/
lemma hasSum_nat_cosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ Real.cos (2 * π * a * n) / (n : ℂ) ^ s) (cosZeta a s) := by
  have := (hasSum_int_cosZeta a hs).nat_add_neg
  simp_rw [abs_neg, Int.cast_neg, Nat.abs_cast, Int.cast_natCast, mul_neg, abs_zero, Int.cast_zero,
    zero_cpow (ne_zero_of_one_lt_re hs), div_zero, zero_div, add_zero, ← add_div,
    div_right_comm _ _ (2 : ℂ)] at this
  simp_rw [push_cast, Complex.cos, neg_mul]
  exact this.congr_fun fun n ↦ by rw [show 2 * π * a * n * I = 2 * π * I * a * n by ring]

/-- Reformulation of `hasSum_nat_cosZeta` using `LSeriesHasSum`. -/
lemma LSeriesHasSum_cos (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    LSeriesHasSum (Real.cos <| 2 * π * a * ·) s (cosZeta a s) :=
  (hasSum_nat_cosZeta a hs).congr_fun (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)

/-!
## Functional equations for the un-completed zetas
-/

/-- If `s` is not in `-ℕ`, and either `a ≠ 0` or `s ≠ 1`, then
`hurwitzZetaEven a (1 - s)` is an explicit multiple of `cosZeta s`. -/
lemma hurwitzZetaEven_one_sub (a : UnitAddCircle) {s : ℂ}
    (hs : ∀ (n : ℕ), s ≠ -n) (hs' : a ≠ 0 ∨ s ≠ 1) :
    hurwitzZetaEven a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * cosZeta a s := by
  have : hurwitzZetaEven a (1 - s) = completedHurwitzZetaEven a (1 - s) * (Gammaℝ (1 - s))⁻¹ := by
    rw [hurwitzZetaEven_def_of_ne_or_ne, div_eq_mul_inv]
    simpa [sub_eq_zero, eq_comm (a := s)] using hs'
  rw [this, completedHurwitzZetaEven_one_sub, inv_Gammaℝ_one_sub hs, cosZeta,
    Function.update_of_ne (by simpa using hs 0), ← Gammaℂ]
  generalize Gammaℂ s * cos (π * s / 2) = A -- speeds up ring_nf call
  ring_nf

/-- If `s` is not of the form `1 - n` for `n ∈ ℕ`, then `cosZeta a (1 - s)` is an explicit
multiple of `hurwitzZetaEven s`. -/
lemma cosZeta_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ 1 - n) :
    cosZeta a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * hurwitzZetaEven a s := by
  rw [← Gammaℂ]
  have : cosZeta a (1 - s) = completedCosZeta a (1 - s) * (Gammaℝ (1 - s))⁻¹ := by
    rw [cosZeta, Function.update_of_ne, div_eq_mul_inv]
    simpa [sub_eq_zero] using (hs 0).symm
  rw [this, completedCosZeta_one_sub, inv_Gammaℝ_one_sub (fun n ↦ by simpa using hs (n + 1)),
    hurwitzZetaEven_def_of_ne_or_ne (Or.inr (by simpa using hs 1))]
  generalize Gammaℂ s * cos (π * s / 2) = A -- speeds up ring_nf call
  ring_nf

end HurwitzZeta
