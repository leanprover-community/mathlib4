/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The Gamma function

This file defines the `Γ` function (of a real or complex variable `s`). We define this by Euler's
integral `Γ(s) = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` in the range where this integral converges
(i.e., for `0 < s` in the real case, and `0 < re s` in the complex case).

We show that this integral satisfies `Γ(1) = 1` and `Γ(s + 1) = s * Γ(s)`; hence we can define
`Γ(s)` for all `s` as the unique function satisfying this recurrence and agreeing with Euler's
integral in the convergence range. (If `s = -n` for `n ∈ ℕ`, then the function is undefined, and we
set it to be `0` by convention.)

## Gamma function: main statements (complex case)

* `Complex.Gamma`: the `Γ` function (of a complex variable).
* `Complex.Gamma_eq_integral`: for `0 < re s`, `Γ(s)` agrees with Euler's integral.
* `Complex.Gamma_add_one`: for all `s : ℂ` with `s ≠ 0`, we have `Γ (s + 1) = s Γ(s)`.
* `Complex.Gamma_nat_eq_factorial`: for all `n : ℕ` we have `Γ (n + 1) = n!`.

## Gamma function: main statements (real case)

* `Real.Gamma`: the `Γ` function (of a real variable).
* Real counterparts of all the properties of the complex Gamma function listed above:
  `Real.Gamma_eq_integral`, `Real.Gamma_add_one`, `Real.Gamma_nat_eq_factorial`.

## Tags

Gamma
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


noncomputable section


open Filter intervalIntegral Set Real MeasureTheory Asymptotics

open scoped Nat Topology ComplexConjugate

namespace Real

/-- Asymptotic bound for the `Γ` function integrand. -/
theorem Gamma_integrand_isLittleO (s : ℝ) :
    (fun x : ℝ => exp (-x) * x ^ s) =o[atTop] fun x : ℝ => exp (-(1 / 2) * x) := by
  refine isLittleO_of_tendsto (fun x hx => ?_) ?_
  · exfalso; exact (exp_pos (-(1 / 2) * x)).ne' hx
  have : (fun x : ℝ => exp (-x) * x ^ s / exp (-(1 / 2) * x)) =
      (fun x : ℝ => exp (1 / 2 * x) / x ^ s)⁻¹ := by
    ext1 x
    simp [field, ← exp_nsmul, exp_neg]
  rw [this]
  exact (tendsto_exp_mul_div_rpow_atTop s (1 / 2) one_half_pos).inv_tendsto_atTop

/-- The Euler integral for the `Γ` function converges for positive real `s`. -/
theorem GammaIntegral_convergent {s : ℝ} (h : 0 < s) :
    IntegrableOn (fun x : ℝ => exp (-x) * x ^ (s - 1)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrableOn_union]
  constructor
  · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    refine IntegrableOn.continuousOn_mul continuousOn_id.neg.rexp ?_ isCompact_Icc
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp ?_
    exact intervalIntegrable_rpow' (by linarith)
  · refine integrable_of_isBigO_exp_neg one_half_pos ?_ (Gamma_integrand_isLittleO _).isBigO
    exact continuousOn_id.neg.rexp.mul (continuousOn_id.rpow_const (by grind))

end Real

namespace Complex

/- Technical note: In defining the Gamma integrand exp (-x) * x ^ (s - 1) for s complex, we have to
make a choice between ↑(Real.exp (-x)), Complex.exp (↑(-x)), and Complex.exp (-↑x), all of which are
equal but not definitionally so. We use the first of these throughout. -/
/-- The integral defining the `Γ` function converges for complex `s` with `0 < re s`.

This is proved by reduction to the real case. -/
theorem GammaIntegral_convergent {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) := by
  constructor
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply (continuous_ofReal.comp continuous_neg.rexp).continuousOn.mul
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have : ContinuousAt (fun x : ℂ => x ^ (s - 1)) ↑x :=
      continuousAt_cpow_const <| ofReal_mem_slitPlane.2 hx
    exact ContinuousAt.comp this continuous_ofReal.continuousAt
  · rw [← hasFiniteIntegral_norm_iff]
    refine HasFiniteIntegral.congr (Real.GammaIntegral_convergent hs).2 ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with x hx
    rw [norm_mul, Complex.norm_of_nonneg <| le_of_lt <| exp_pos <| -x,
      norm_cpow_eq_rpow_re_of_pos hx _]
    simp

/-- Euler's integral for the `Γ` function (of a complex variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `Complex.GammaIntegral_convergent` for a proof of the convergence of the integral for
`0 < re s`. -/
def GammaIntegral (s : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), ↑(-x).exp * ↑x ^ (s - 1)

set_option backward.isDefEq.respectTransparency false in
theorem GammaIntegral_conj (s : ℂ) : GammaIntegral (conj s) = conj (GammaIntegral s) := by
  rw [GammaIntegral, GammaIntegral, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  dsimp only
  rw [map_mul, conj_ofReal, cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), ← exp_conj, map_mul,
    ← ofReal_log (le_of_lt hx), conj_ofReal, map_sub, map_one]

theorem GammaIntegral_ofReal (s : ℝ) :
    GammaIntegral ↑s = ↑(∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ (s - 1)) := by
  have : ∀ r : ℝ, Complex.ofReal r = @RCLike.ofReal ℂ _ r := fun r => rfl
  rw [GammaIntegral]
  conv_rhs => rw [this, ← _root_.integral_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx; dsimp only
  conv_rhs => rw [← this]
  rw [ofReal_mul, ofReal_cpow (mem_Ioi.mp hx).le]
  simp

@[simp]
theorem GammaIntegral_one : GammaIntegral 1 = 1 := by
  simpa only [← ofReal_one, GammaIntegral_ofReal, ofReal_inj, sub_self, rpow_zero,
    mul_one] using integral_exp_neg_Ioi_zero

end Complex

/-! Now we establish the recurrence relation `Γ(s + 1) = s * Γ(s)` using integration by parts. -/


namespace Complex

section GammaRecurrence

/-- The indefinite version of the `Γ` function, `Γ(s, X) = ∫ x ∈ 0..X, exp(-x) x ^ (s - 1)`. -/
def partialGamma (s : ℂ) (X : ℝ) : ℂ :=
  ∫ x in 0..X, (-x).exp * x ^ (s - 1)

theorem tendsto_partialGamma {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun X : ℝ => partialGamma s X) atTop (𝓝 <| GammaIntegral s) :=
  intervalIntegral_tendsto_integral_Ioi 0 (GammaIntegral_convergent hs) tendsto_id

private theorem Gamma_integrand_intervalIntegrable (s : ℂ) {X : ℝ} (hs : 0 < s.re) (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) volume 0 X := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX]
  exact IntegrableOn.mono_set (GammaIntegral_convergent hs) Ioc_subset_Ioi_self

private theorem Gamma_integrand_deriv_integrable_A {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => -((-x).exp * x ^ s) : ℝ → ℂ) volume 0 X := by
  convert (Gamma_integrand_intervalIntegrable (s + 1) _ hX).neg
  · simp only [ofReal_exp, ofReal_neg, add_sub_cancel_right]; rfl
  · simp only [add_re, one_re]; linarith

private theorem Gamma_integrand_deriv_integrable_B {s : ℂ} (hs : 0 < s.re) {Y : ℝ} (hY : 0 ≤ Y) :
    IntervalIntegrable (fun x : ℝ => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) volume 0 Y := by
  have : (fun x => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) =
      (fun x => s * ((-x).exp * x ^ (s - 1)) : ℝ → ℂ) := by ext1; ring
  rw [this, intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
  constructor
  · refine (continuousOn_const.mul ?_).aestronglyMeasurable measurableSet_Ioc
    apply (continuous_ofReal.comp continuous_neg.rexp).continuousOn.mul
    apply continuousOn_of_forall_continuousAt
    intro x hx
    refine (?_ : ContinuousAt (fun x : ℂ => x ^ (s - 1)) _).comp continuous_ofReal.continuousAt
    exact continuousAt_cpow_const <| ofReal_mem_slitPlane.2 hx.1
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_mul]
  refine (((Real.GammaIntegral_convergent hs).mono_set
    Ioc_subset_Ioi_self).hasFiniteIntegral.congr ?_).const_mul _
  rw [EventuallyEq, ae_restrict_iff']
  · filter_upwards with x hx
    rw [Complex.norm_of_nonneg (exp_pos _).le, norm_cpow_eq_rpow_re_of_pos hx.1]
    simp
  · exact measurableSet_Ioc

set_option backward.isDefEq.respectTransparency false in
/-- The recurrence relation for the indefinite version of the `Γ` function. -/
theorem partialGamma_add_one {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 0 ≤ X) :
    partialGamma (s + 1) X = s * partialGamma s X - (-X).exp * X ^ s := by
  rw [partialGamma, partialGamma, add_sub_cancel_right]
  have F_der_I : ∀ x : ℝ, x ∈ Ioo 0 X → HasDerivAt (fun x => (-x).exp * x ^ s : ℝ → ℂ)
      (-((-x).exp * x ^ s) + (-x).exp * (s * x ^ (s - 1))) x := by
    intro x hx
    have d1 : HasDerivAt (fun y : ℝ => (-y).exp) (-(-x).exp) x := by
      simpa using (hasDerivAt_neg x).exp
    have d2 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * x ^ (s - 1)) x := by
      have t := @HasDerivAt.cpow_const _ _ _ s (hasDerivAt_id ↑x) ?_
      · simpa only [mul_one] using t.comp_ofReal
      · exact ofReal_mem_slitPlane.2 hx.1
    simpa only [ofReal_neg, neg_mul] using d1.ofReal_comp.mul d2
  have cont := (continuous_ofReal.comp continuous_neg.rexp).mul (continuous_ofReal_cpow_const hs)
  have der_ible :=
    (Gamma_integrand_deriv_integrable_A hs hX).add (Gamma_integrand_deriv_integrable_B hs hX)
  have int_eval := integral_eq_sub_of_hasDerivAt_of_le hX cont.continuousOn F_der_I der_ible
  -- We are basically done here but manipulating the output into the right form is fiddly.
  apply_fun fun x : ℂ => -x at int_eval
  rw [intervalIntegral.integral_add (Gamma_integrand_deriv_integrable_A hs hX)
      (Gamma_integrand_deriv_integrable_B hs hX),
    intervalIntegral.integral_neg, neg_add, neg_neg] at int_eval
  rw [eq_sub_of_add_eq int_eval, sub_neg_eq_add, neg_sub, add_comm, add_sub]
  have hn : s ≠ 0 := by contrapose! hs; rw [hs, zero_re]
  simp only [Pi.mul_apply, Function.comp_apply, ofReal_zero, zero_cpow hn, mul_zero, add_zero,
    ← intervalIntegral.integral_const_mul]
  congr with x
  ring

/-- The recurrence relation for the `Γ` integral. -/
theorem GammaIntegral_add_one {s : ℂ} (hs : 0 < s.re) :
    GammaIntegral (s + 1) = s * GammaIntegral s := by
  suffices Tendsto (s + 1).partialGamma atTop (𝓝 <| s * GammaIntegral s) by
    refine tendsto_nhds_unique ?_ this
    apply tendsto_partialGamma; rw [add_re, one_re]; linarith
  have : (fun X : ℝ => s * partialGamma s X - X ^ s * (-X).exp) =ᶠ[atTop]
      (s + 1).partialGamma := by
    apply eventuallyEq_of_mem (Ici_mem_atTop (0 : ℝ))
    intro X hX
    rw [partialGamma_add_one hs (mem_Ici.mp hX)]
    ring_nf
  refine Tendsto.congr' this ?_
  suffices Tendsto (fun X => -X ^ s * (-X).exp : ℝ → ℂ) atTop (𝓝 0) by
    simpa using Tendsto.add (Tendsto.const_mul s (tendsto_partialGamma hs)) this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have :
      (fun e : ℝ => ‖-(e : ℂ) ^ s * (-e).exp‖) =ᶠ[atTop] fun e : ℝ => e ^ s.re * (-1 * e).exp := by
    refine eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_
    intro x hx; dsimp only
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hx,
      Complex.norm_of_nonneg (exp_pos (-x)).le, neg_mul, one_mul]
  exact (tendsto_congr' this).mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ zero_lt_one)

end GammaRecurrence

/-! Now we define `Γ(s)` on the whole complex plane, by recursion. -/


section GammaDef

/-- The `n`th function in this family is `Γ(s)` if `-n < s.re`, and junk otherwise. -/
noncomputable def GammaAux : ℕ → ℂ → ℂ
  | 0 => GammaIntegral
  | n + 1 => fun s : ℂ => GammaAux n (s + 1) / s

theorem GammaAux_recurrence1 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
    GammaAux n s = GammaAux n (s + 1) / s := by
  induction n generalizing s with
  | zero =>
    simp only [CharP.cast_eq_zero, Left.neg_neg_iff] at h1
    dsimp only [GammaAux]; rw [GammaIntegral_add_one h1]
    rw [mul_comm, mul_div_cancel_right₀]; contrapose! h1; rw [h1]
    simp
  | succ n hn =>
    dsimp only [GammaAux]
    have hh1 : -(s + 1).re < n := by
      rw [Nat.cast_add, Nat.cast_one] at h1
      rw [add_re, one_re]; linarith
    rw [← hn (s + 1) hh1]

theorem GammaAux_recurrence2 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
    GammaAux n s = GammaAux (n + 1) s := by
  rcases n with - | n
  · simp only [CharP.cast_eq_zero, Left.neg_neg_iff] at h1
    dsimp only [GammaAux]
    rw [GammaIntegral_add_one h1, mul_div_cancel_left₀]
    rintro rfl
    rw [zero_re] at h1
    exact h1.false
  · dsimp only [GammaAux]
    have : GammaAux n (s + 1 + 1) / (s + 1) = GammaAux n (s + 1) := by
      have hh1 : -(s + 1).re < n := by
        rw [Nat.cast_add, Nat.cast_one] at h1
        rw [add_re, one_re]; linarith
      rw [GammaAux_recurrence1 (s + 1) n hh1]
    rw [this]

/-- The `Γ` function (of a complex variable `s`). -/
@[pp_nodot]
irreducible_def Gamma (s : ℂ) : ℂ :=
  GammaAux ⌊1 - s.re⌋₊ s

theorem Gamma_eq_GammaAux (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) : Gamma s = GammaAux n s := by
  have u : ∀ k : ℕ, GammaAux (⌊1 - s.re⌋₊ + k) s = Gamma s := fun k ↦ by
    induction k with
    | zero => simp [Gamma_def]
    | succ k hk =>
      rw [← hk, ← add_assoc]
      refine (GammaAux_recurrence2 s (⌊1 - s.re⌋₊ + k) ?_).symm
      rw [Nat.cast_add]
      have i0 := Nat.sub_one_lt_floor (1 - s.re)
      simp only [sub_sub_cancel_left] at i0
      refine lt_add_of_lt_of_nonneg i0 ?_
      rw [← Nat.cast_zero, Nat.cast_le]; exact Nat.zero_le k
  convert (u <| n - ⌊1 - s.re⌋₊).symm; rw [Nat.add_sub_of_le]
  by_cases h : 0 ≤ 1 - s.re
  · apply Nat.le_of_lt_succ
    exact_mod_cast lt_of_le_of_lt (Nat.floor_le h) (by linarith : 1 - s.re < n + 1)
  · rw [Nat.floor_of_nonpos]
    · lia
    · linarith

/-- The recurrence relation for the `Γ` function. -/
theorem Gamma_add_one (s : ℂ) (h2 : s ≠ 0) : Gamma (s + 1) = s * Gamma s := by
  let n := ⌊1 - s.re⌋₊
  have t1 : -s.re < n := by simpa only [sub_sub_cancel_left] using Nat.sub_one_lt_floor (1 - s.re)
  have t2 : -(s + 1).re < n := by rw [add_re, one_re]; linarith
  rw [Gamma_eq_GammaAux s n t1, Gamma_eq_GammaAux (s + 1) n t2, GammaAux_recurrence1 s n t1]
  field

theorem Gamma_eq_integral {s : ℂ} (hs : 0 < s.re) : Gamma s = GammaIntegral s :=
  Gamma_eq_GammaAux s 0 (by norm_cast; linarith)

@[simp]
theorem Gamma_one : Gamma 1 = 1 := by rw [Gamma_eq_integral] <;> simp

theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n + 1) = n ! := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Gamma_add_one n.succ <| Nat.cast_ne_zero.mpr <| Nat.succ_ne_zero n]
    simp only [Nat.cast_succ, Nat.factorial_succ, Nat.cast_mul]
    congr

@[simp]
theorem Gamma_ofNat_eq_factorial (n : ℕ) [(n + 1).AtLeastTwo] :
    Gamma (ofNat(n + 1) : ℂ) = n ! :=
  mod_cast Gamma_nat_eq_factorial (n : ℕ)

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
@[simp]
theorem Gamma_zero : Gamma 0 = 0 := by
  simp_rw [Gamma_def, zero_re, sub_zero, Nat.floor_one, GammaAux, div_zero]

/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value 0. -/
theorem Gamma_neg_nat_eq_zero (n : ℕ) : Gamma (-n) = 0 := by
  induction n with
  | zero => rw [Nat.cast_zero, neg_zero, Gamma_zero]
  | succ n IH =>
    have A : -(n.succ : ℂ) ≠ 0 := by
      rw [neg_ne_zero, Nat.cast_ne_zero]
      apply Nat.succ_ne_zero
    have : -(n : ℂ) = -↑n.succ + 1 := by simp
    rw [this, Gamma_add_one _ A] at IH
    contrapose! IH
    exact mul_ne_zero A IH

theorem Gamma_conj (s : ℂ) : Gamma (conj s) = conj (Gamma s) := by
  suffices ∀ (n : ℕ) (s : ℂ), GammaAux n (conj s) = conj (GammaAux n s) by
    simp [Gamma_def, this]
  intro n
  induction n with
  | zero => rw [GammaAux]; exact GammaIntegral_conj
  | succ n IH =>
    intro s
    rw [GammaAux]
    dsimp only
    rw [div_eq_mul_inv _ s, map_mul, conj_inv, ← div_eq_mul_inv]
    suffices conj s + 1 = conj (s + 1) by rw [this, IH]
    rw [map_add, map_one]

set_option backward.isDefEq.respectTransparency false in
/-- Expresses the integral over `Ioi 0` of `t ^ (a - 1) * exp (-(r * t))` in terms of the Gamma
function, for complex `a`. -/
lemma integral_cpow_mul_exp_neg_mul_Ioi {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    ∫ (t : ℝ) in Ioi 0, t ^ (a - 1) * exp (-(r * t)) = (1 / r) ^ a * Gamma a := by
  have aux : (1 / r : ℂ) ^ a = 1 / r * (1 / r) ^ (a - 1) := by
    nth_rewrite 2 [← cpow_one (1 / r : ℂ)]
    rw [← cpow_add _ _ (one_div_ne_zero <| ofReal_ne_zero.mpr hr.ne'), add_sub_cancel]
  calc
    _ = ∫ (t : ℝ) in Ioi 0, (1 / r) ^ (a - 1) * (r * t) ^ (a - 1) * exp (-(r * t)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ ?_)
      rw [mem_Ioi] at hx
      rw [mul_cpow_ofReal_nonneg hr.le hx.le, ← mul_assoc, one_div, ← ofReal_inv,
        ← mul_cpow_ofReal_nonneg (inv_pos.mpr hr).le hr.le, ← ofReal_mul r⁻¹,
        inv_mul_cancel₀ hr.ne', ofReal_one, one_cpow, one_mul]
    _ = 1 / r * ∫ (t : ℝ) in Ioi 0, (1 / r) ^ (a - 1) * t ^ (a - 1) * exp (-t) := by
      simp_rw [← ofReal_mul]
      rw [integral_comp_mul_left_Ioi (fun x ↦ _ * x ^ (a - 1) * exp (-x)) _ hr, mul_zero,
        real_smul, ← one_div, ofReal_div, ofReal_one]
    _ = 1 / r * (1 / r : ℂ) ^ (a - 1) * (∫ (t : ℝ) in Ioi 0, t ^ (a - 1) * exp (-t)) := by
      simp_rw [← MeasureTheory.integral_const_mul, mul_assoc]
    _ = (1 / r) ^ a * Gamma a := by
      rw [aux, Gamma_eq_integral ha]
      congr 2 with x
      rw [ofReal_exp, ofReal_neg, mul_comm]

end GammaDef

end Complex

namespace Real

/-- The `Γ` function (of a real variable `s`). -/
@[pp_nodot]
def Gamma (s : ℝ) : ℝ :=
  (Complex.Gamma s).re

set_option backward.isDefEq.respectTransparency false in
theorem Gamma_eq_integral {s : ℝ} (hs : 0 < s) :
    Gamma s = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1) := by
  rw [Gamma, Complex.Gamma_eq_integral (by rwa [Complex.ofReal_re] : 0 < Complex.re s)]
  dsimp only [Complex.GammaIntegral]
  simp_rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
  suffices ∫ x : ℝ in Ioi 0, ↑(exp (-x)) * (x : ℂ) ^ ((s - 1 : ℝ) : ℂ) =
      ∫ x : ℝ in Ioi 0, ((exp (-x) * x ^ (s - 1) : ℝ) : ℂ) by
    have cc : ∀ r : ℝ, Complex.ofReal r = @RCLike.ofReal ℂ _ r := fun r => rfl
    conv_lhs => rw [this]; enter [1, 2, x]; rw [cc]
    rw [_root_.integral_ofReal, ← cc, Complex.ofReal_re]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  push_cast
  rw [Complex.ofReal_cpow (le_of_lt hx)]
  push_cast; rfl

theorem Gamma_add_one {s : ℝ} (hs : s ≠ 0) : Gamma (s + 1) = s * Gamma s := by
  simp_rw [Gamma]
  rw [Complex.ofReal_add, Complex.ofReal_one, Complex.Gamma_add_one, Complex.re_ofReal_mul]
  rwa [Complex.ofReal_ne_zero]

@[simp]
theorem Gamma_one : Gamma 1 = 1 := by
  rw [Gamma, Complex.ofReal_one, Complex.Gamma_one, Complex.one_re]

theorem _root_.Complex.Gamma_ofReal (s : ℝ) : Complex.Gamma (s : ℂ) = Gamma s := by
  rw [Gamma, eq_comm, ← Complex.conj_eq_iff_re, ← Complex.Gamma_conj, Complex.conj_ofReal]

theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n + 1) = n ! := by
  rw [Gamma, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.Gamma_nat_eq_factorial, ← Complex.ofReal_natCast, Complex.ofReal_re]

@[simp]
theorem Gamma_ofNat_eq_factorial (n : ℕ) [(n + 1).AtLeastTwo] :
    Gamma (ofNat(n + 1) : ℝ) = n ! :=
  mod_cast Gamma_nat_eq_factorial (n : ℕ)

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
@[simp]
theorem Gamma_zero : Gamma 0 = 0 := by
  simpa only [← Complex.ofReal_zero, Complex.Gamma_ofReal, Complex.ofReal_inj] using
    Complex.Gamma_zero

/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value `0`.
-/
theorem Gamma_neg_nat_eq_zero (n : ℕ) : Gamma (-n) = 0 := by
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.Gamma_ofReal,
    Complex.ofReal_eq_zero] using Complex.Gamma_neg_nat_eq_zero n

theorem Gamma_pos_of_pos {s : ℝ} (hs : 0 < s) : 0 < Gamma s := by
  rw [Gamma_eq_integral hs]
  have : (Function.support fun x : ℝ => exp (-x) * x ^ (s - 1)) ∩ Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro x hx
    rw [Function.mem_support]
    exact mul_ne_zero (exp_pos _).ne' (rpow_pos_of_pos hx _).ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [this, volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
  · refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
    exact fun x hx => (mul_pos (exp_pos _) (rpow_pos_of_pos hx _)).le
  · exact GammaIntegral_convergent hs

theorem Gamma_nonneg_of_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ Gamma s := by
  obtain rfl | h := eq_or_lt_of_le hs
  · rw [Gamma_zero]
  · exact (Gamma_pos_of_pos h).le

open Complex in
/-- Expresses the integral over `Ioi 0` of `t ^ (a - 1) * exp (-(r * t))`, for positive real `r`,
in terms of the Gamma function. -/
lemma integral_rpow_mul_exp_neg_mul_Ioi {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ t : ℝ in Ioi 0, t ^ (a - 1) * exp (-(r * t)) = (1 / r) ^ a * Gamma a := by
  rw [← ofReal_inj, ofReal_mul, ← Gamma_ofReal, ofReal_cpow (by positivity), ofReal_div]
  convert integral_cpow_mul_exp_neg_mul_Ioi (by rwa [ofReal_re] : 0 < (a : ℂ).re) hr
  refine integral_ofReal.symm.trans <| setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ ?_)
  norm_cast
  simp_rw [← ofReal_cpow ht.le, RCLike.ofReal_mul, coe_algebraMap]

open Lean.Meta Qq Mathlib.Meta.Positivity in
/-- The `positivity` extension which identifies expressions of the form `Gamma a`. -/
@[positivity Gamma (_ : ℝ)]
meta def _root_.Mathlib.Meta.Positivity.evalGamma : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Gamma $a) =>
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa =>
      assertInstancesCommute
      pure (.positive q(Gamma_pos_of_pos $pa))
    | .nonnegative pa =>
      assertInstancesCommute
      pure (.nonnegative q(Gamma_nonneg_of_nonneg $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Gamma application"

/-- The Gamma function does not vanish on `ℝ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
theorem Gamma_ne_zero {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : Gamma s ≠ 0 := by
  suffices ∀ {n : ℕ}, -(n : ℝ) < s → Gamma s ≠ 0 by
    apply this
    swap
    · exact ⌊-s⌋₊ + 1
    rw [neg_lt, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  intro n
  induction n generalizing s with
  | zero =>
    intro hs
    refine (Gamma_pos_of_pos ?_).ne'
    rwa [Nat.cast_zero, neg_zero] at hs
  | succ _ n_ih =>
    intro hs'
    have : Gamma (s + 1) ≠ 0 := by
      apply n_ih
      · intro m
        specialize hs (1 + m)
        contrapose hs
        rw [← eq_sub_iff_add_eq] at hs
        rw [hs]
        push_cast
        ring
      · rw [Nat.cast_add, Nat.cast_one, neg_add] at hs'
        linarith
    rw [Gamma_add_one, mul_ne_zero_iff] at this
    · exact this.2
    · simpa using hs 0

theorem Gamma_eq_zero_iff (s : ℝ) : Gamma s = 0 ↔ ∃ m : ℕ, s = -m :=
  ⟨by contrapose!; exact Gamma_ne_zero, by rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m⟩

end Real
