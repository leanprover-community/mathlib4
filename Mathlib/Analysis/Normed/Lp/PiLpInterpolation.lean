/-
Copyright (c) 2026 Jan Bernlöhr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan Bernlöhr
-/
module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Normed.Lp.PiLpDual

import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Sharp interpolation for finite complex matrices

Endpoint bounds for the bilinear pairing of a finite matrix interpolate with the geometric
constant `M₀ ^ (1 - t) * M₁ ^ t`. All input and test exponents in the bilinear theorem are finite.
The proof uses entire phase/magnitude power families and Hadamard's three-lines theorem.

Conjugate norm detection then turns the scalar pairing estimate into an operator estimate.
The constants do not depend on the cardinalities of the input and output index types.
-/

public section

noncomputable section

open Complex WithLp
open scoped ENNReal

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private def powerCurve (a w : ℂ) : ℂ :=
  if a = 0 then 0 else (a / (‖a‖ : ℂ)) * exp (w * (Real.log ‖a‖ : ℂ))

private lemma powerCurve_one (a : ℂ) : powerCurve a 1 = a := by
  by_cases ha : a = 0
  · simp [powerCurve, ha]
  · simp only [powerCurve, ite_eq_right ha, one_mul, ← Complex.ofReal_exp,
      Real.exp_log (norm_pos_iff.mpr ha)]
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha))

private lemma differentiable_powerCurve (a : ℂ) : Differentiable ℂ (powerCurve a) := by
  unfold powerCurve
  split_ifs
  · exact differentiable_const _
  · exact differentiable_const _ |>.mul ((differentiable_id.mul_const _).cexp)

private lemma norm_powerCurve (a w : ℂ) (hw : 0 < w.re) :
    ‖powerCurve a w‖ = ‖a‖ ^ w.re := by
  by_cases ha : a = 0
  · simp [powerCurve, ha, hw.ne']
  · simp only [powerCurve, ite_eq_right ha, norm_mul, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a), div_self (norm_ne_zero_iff.mpr ha),
      one_mul, Complex.norm_exp, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    rw [Real.rpow_def_of_pos (norm_pos_iff.mpr ha)]
    congr 1
    ring

private def weight (r p₀ p₁ : ℝ) (z : ℂ) : ℂ :=
  (r : ℂ) * ((1 - z) / (p₀ : ℂ) + z / (p₁ : ℂ))

private lemma weight_re (r p₀ p₁ : ℝ) (z : ℂ) :
    (weight r p₀ p₁ z).re = r * ((1 - z.re) / p₀ + z.re / p₁) := by
  simp only [weight, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    add_re, div_ofReal_re, sub_re, one_re]

private lemma differentiable_weight (r p₀ p₁ : ℝ) : Differentiable ℂ (weight r p₀ p₁) :=
  differentiable_const _ |>.mul
    (((differentiable_const _).sub differentiable_id).div_const _ |>.add
      (differentiable_id.div_const _))

private lemma weight_re_pos {r p₀ p₁ : ℝ} (hr : 0 < r) (h₀ : 0 < p₀) (h₁ : 0 < p₁)
    {z : ℂ} (hz₀ : 0 ≤ z.re) (hz₁ : z.re ≤ 1) : 0 < (weight r p₀ p₁ z).re := by
  rw [weight_re]
  apply mul_pos hr
  rcases eq_or_lt_of_le hz₀ with hz | hz
  · rw [← hz]
    positivity
  · exact add_pos_of_nonneg_of_pos (div_nonneg (by linarith) h₀.le) (div_pos hz h₁)

private lemma weight_at {r p₀ p₁ t : ℝ}
    (h : r * ((1 - t) / p₀ + t / p₁) = 1) : weight r p₀ p₁ (t : ℂ) = 1 := by
  unfold weight
  exact_mod_cast h

private lemma norm_power_le_one {p r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hp : 0 < p.toReal) (hr : 0 < r.toReal) (a : ι → ℂ)
    (ha : ‖toLp r a‖ ≤ 1) {w : ℂ} (hw : w.re = r.toReal / p.toReal) :
    ‖toLp p (fun i ↦ powerCurve (a i) w)‖ ≤ 1 := by
  have hpos : 0 < w.re := by rw [hw]; exact div_pos hr hp
  have hsum : (∑ i, ‖a i‖ ^ r.toReal) ≤ 1 := by
    have h := Real.rpow_le_one (norm_nonneg (toLp r a)) ha hr.le
    rw [PiLp.norm_eq_sum hr,
      ← Real.rpow_mul (Finset.sum_nonneg (fun _ _ ↦ by positivity)),
      one_div_mul_cancel hr.ne', Real.rpow_one] at h
    exact h
  rw [PiLp.norm_eq_sum hp]
  simp_rw [norm_powerCurve _ _ hpos, ← Real.rpow_mul (norm_nonneg _), hw,
    div_mul_cancel₀ _ hp.ne']
  exact Real.rpow_le_one (Finset.sum_nonneg (fun _ _ ↦ by positivity)) hsum (by positivity)

private lemma norm_power_apply_le_one {r : ℝ≥0∞} [Fact (1 ≤ r)] (a : ι → ℂ)
    (ha : ‖toLp r a‖ ≤ 1) {w : ℂ} (hw : 0 < w.re) (i : ι) :
    ‖powerCurve (a i) w‖ ≤ 1 := by
  rw [norm_powerCurve _ _ hw]
  exact Real.rpow_le_one (norm_nonneg _)
    ((PiLp.norm_apply_le (toLp r a) i).trans ha) hw.le

private def pairing (M : Matrix κ ι ℂ) (a : ι → ℂ) (b : κ → ℂ) : ℂ :=
  ∑ j, (M *ᵥ a) j * b j

private lemma pairing_smul (M : Matrix κ ι ℂ) (a : ι → ℂ) (b : κ → ℂ) (c d : ℂ) :
    pairing M (c • a) (d • b) = c * d * pairing M a b := by
  simp only [pairing, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma norm_pairing_interpolate_unit
    {p₀ p₁ q₀ q₁ r s : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ r)] [Fact (1 ≤ s)]
    (hp₀ : 0 < p₀.toReal) (hp₁ : 0 < p₁.toReal)
    (hq₀ : 0 < q₀.toReal) (hq₁ : 0 < q₁.toReal)
    (hr : 0 < r.toReal) (hs : 0 < s.toReal)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hrt : r.toReal * ((1 - t) / p₀.toReal + t / p₁.toReal) = 1)
    (hst : s.toReal * ((1 - t) / q₀.toReal + t / q₁.toReal) = 1)
    (M : Matrix κ ι ℂ) {B₀ B₁ : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ∀ (a : ι → ℂ) (b : κ → ℂ), ‖pairing M a b‖ ≤ B₀ * ‖toLp p₀ a‖ * ‖toLp q₀ b‖)
    (h₁ : ∀ (a : ι → ℂ) (b : κ → ℂ), ‖pairing M a b‖ ≤ B₁ * ‖toLp p₁ a‖ * ‖toLp q₁ b‖)
    (a : ι → ℂ) (b : κ → ℂ) (ha : ‖toLp r a‖ ≤ 1) (hb : ‖toLp s b‖ ≤ 1) :
    ‖pairing M a b‖ ≤ B₀ ^ (1 - t) * B₁ ^ t := by
  let A := fun z i ↦ powerCurve (a i) (weight r.toReal p₀.toReal p₁.toReal z)
  let B := fun z j ↦ powerCurve (b j) (weight s.toReal q₀.toReal q₁.toReal z)
  let F := fun z ↦ pairing M (A z) (B z)
  have hd : Differentiable ℂ F := by
    simp only [F, pairing, mulVec, dotProduct, Finset.sum_mul]
    apply Differentiable.fun_sum
    intro j _
    apply Differentiable.fun_sum
    intro i _
    exact (((differentiable_powerCurve (a i)).comp (differentiable_weight _ _ _)).const_mul
      (M j i)).mul ((differentiable_powerCurve (b j)).comp (differentiable_weight _ _ _))
  have hbound : BddAbove ((norm ∘ F) '' HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨∑ j, ∑ i, ‖M j i‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simp only [Function.comp_apply, F, pairing, mulVec, dotProduct, Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul, norm_mul]
    calc
      _ ≤ ‖M j i‖ * 1 * 1 := by
        gcongr
        · exact norm_power_apply_le_one a ha (weight_re_pos hr hp₀ hp₁ hz.1 hz.2) i
        · exact norm_power_apply_le_one b hb (weight_re_pos hs hq₀ hq₁ hz.1 hz.2) j
      _ = _ := by ring
  have he₀ (z : ℂ) (hz : z.re = 0) : ‖F z‖ ≤ B₀ := by
    have hA : ‖toLp p₀ (A z)‖ ≤ 1 :=
      norm_power_le_one hp₀ hr a ha (by rw [weight_re, hz]; ring)
    have hB : ‖toLp q₀ (B z)‖ ≤ 1 :=
      norm_power_le_one hq₀ hs b hb (by rw [weight_re, hz]; ring)
    exact (h₀ (A z) (B z)).trans (by
      calc
        _ ≤ B₀ * 1 * 1 := by gcongr
        _ = B₀ := by ring)
  have he₁ (z : ℂ) (hz : z.re = 1) : ‖F z‖ ≤ B₁ := by
    have hA : ‖toLp p₁ (A z)‖ ≤ 1 :=
      norm_power_le_one hp₁ hr a ha (by rw [weight_re, hz]; ring)
    have hB : ‖toLp q₁ (B z)‖ ≤ 1 :=
      norm_power_le_one hq₁ hs b hb (by rw [weight_re, hz]; ring)
    exact (h₁ (A z) (B z)).trans (by
      calc
        _ ≤ B₁ * 1 * 1 := by gcongr
        _ = B₁ := by ring)
  have hthree := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' F
    (z := (t : ℂ)) ⟨ht₀, ht₁⟩ hd.diffContOnCl hbound he₀ he₁
  have ht : F (t : ℂ) = pairing M a b := by
    dsimp [F, A, B]
    rw [weight_at hrt, weight_at hst]
    simp only [powerCurve_one]
  rwa [ht, ofReal_re] at hthree

/-- Sharp interpolation of bilinear matrix estimates at finite input and test exponents.

The intermediate exponents satisfy affine reciprocal relations. The geometric bound is
independent of the dimensions of the matrix, and zero endpoint bounds are allowed. -/
theorem norm_sum_mulVec_interpolate
    {p₀ p₁ q₀ q₁ r s : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ r)] [Fact (1 ≤ s)]
    (hp₀ : 0 < p₀.toReal) (hp₁ : 0 < p₁.toReal)
    (hq₀ : 0 < q₀.toReal) (hq₁ : 0 < q₁.toReal)
    (hr : 0 < r.toReal) (hs : 0 < s.toReal)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hrt : r.toReal * ((1 - t) / p₀.toReal + t / p₁.toReal) = 1)
    (hst : s.toReal * ((1 - t) / q₀.toReal + t / q₁.toReal) = 1)
    (M : Matrix κ ι ℂ) {B₀ B₁ : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ∀ (a : ι → ℂ) (b : κ → ℂ), ‖∑ j, (M *ᵥ a) j * b j‖ ≤ B₀ * ‖toLp p₀ a‖ * ‖toLp q₀ b‖)
    (h₁ : ∀ (a : ι → ℂ) (b : κ → ℂ), ‖∑ j, (M *ᵥ a) j * b j‖ ≤ B₁ * ‖toLp p₁ a‖ * ‖toLp q₁ b‖)
    (a : ι → ℂ) (b : κ → ℂ) :
    ‖∑ j, (M *ᵥ a) j * b j‖ ≤
      (B₀ ^ (1 - t) * B₁ ^ t) * ‖toLp r a‖ * ‖toLp s b‖ := by
  change ‖pairing M a b‖ ≤ _
  by_cases ha : a = 0
  · simp [ha, pairing]
  by_cases hb : b = 0
  · simp [hb, pairing]
  have han : 0 < ‖toLp r a‖ := norm_pos_iff.mpr (fun h ↦ ha (congrArg ofLp h))
  have hbn : 0 < ‖toLp s b‖ := norm_pos_iff.mpr (fun h ↦ hb (congrArg ofLp h))
  let c : ℂ := (‖toLp r a‖ : ℂ)⁻¹
  let d : ℂ := (‖toLp s b‖ : ℂ)⁻¹
  have hc : ‖c‖ = ‖toLp r a‖⁻¹ := by simp [c, norm_inv]
  have hd : ‖d‖ = ‖toLp s b‖⁻¹ := by simp [d, norm_inv]
  have hna : ‖toLp r (c • a)‖ ≤ 1 := by
    change ‖c • toLp r a‖ ≤ 1
    rw [norm_smul, hc, inv_mul_cancel₀ han.ne']
  have hnb : ‖toLp s (d • b)‖ ≤ 1 := by
    change ‖d • toLp s b‖ ≤ 1
    rw [norm_smul, hd, inv_mul_cancel₀ hbn.ne']
  have h := norm_pairing_interpolate_unit hp₀ hp₁ hq₀ hq₁ hr hs ht₀ ht₁ hrt hst
    M hB₀ hB₁ h₀ h₁ (c • a) (d • b) hna hnb
  rw [pairing_smul, norm_mul, norm_mul, hc, hd] at h
  have h' := mul_le_mul_of_nonneg_left h (mul_nonneg han.le hbn.le)
  have he : (‖toLp r a‖ * ‖toLp s b‖) *
      (‖toLp r a‖⁻¹ * ‖toLp s b‖⁻¹ * ‖pairing M a b‖) = ‖pairing M a b‖ := by
    field_simp
  rw [he] at h'
  nlinarith only [h']

private lemma inv_toReal_conjExponent {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    p.conjExponent.toReal⁻¹ = 1 - p.toReal⁻¹ := by
  have h := congrArg ENNReal.toReal
    (ENNReal.HolderConjugate.inv_add_inv_eq_one p p.conjExponent)
  rw [ENNReal.toReal_add (by simp [ENNReal.HolderConjugate.ne_zero p p.conjExponent])
    (by simp [ENNReal.HolderConjugate.ne_zero p.conjExponent p]),
    ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_one] at h
  linarith

/-- Sharp interpolation of finite complex matrix operator bounds.

The input exponents are finite. The output exponents are strictly greater than one and may
be infinite; `∞.toReal⁻¹ = 0` gives the usual reciprocal convention in the output relation.
The estimate follows by applying conjugate norm detection to the interpolated pairing. -/
theorem norm_mulVec_interpolate
    {p₀ p₁ q₀ q₁ r s : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ r)] [Fact (1 ≤ s)]
    (hp₀ : 0 < p₀.toReal) (hp₁ : 0 < p₁.toReal) (hr : 0 < r.toReal)
    (hq₀ : 1 < q₀) (hq₁ : 1 < q₁) (hs : 1 < s)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hrt : r.toReal * ((1 - t) / p₀.toReal + t / p₁.toReal) = 1)
    (hst : s.toReal⁻¹ = (1 - t) / q₀.toReal + t / q₁.toReal)
    (M : Matrix κ ι ℂ) {B₀ B₁ : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ∀ a : ι → ℂ, ‖toLp q₀ (M *ᵥ a)‖ ≤ B₀ * ‖toLp p₀ a‖)
    (h₁ : ∀ a : ι → ℂ, ‖toLp q₁ (M *ᵥ a)‖ ≤ B₁ * ‖toLp p₁ a‖)
    (a : ι → ℂ) :
    ‖toLp s (M *ᵥ a)‖ ≤ (B₀ ^ (1 - t) * B₁ ^ t) * ‖toLp r a‖ := by
  let : Fact (1 ≤ q₀.conjExponent) :=
    ⟨ENNReal.HolderConjugate.one_le q₀.conjExponent q₀⟩
  let : Fact (1 ≤ q₁.conjExponent) :=
    ⟨ENNReal.HolderConjugate.one_le q₁.conjExponent q₁⟩
  let : Fact (1 ≤ s.conjExponent) :=
    ⟨ENNReal.HolderConjugate.one_le s.conjExponent s⟩
  have hc {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) : 0 < p.conjExponent.toReal :=
    ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p.conjExponent p)
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp).ne
  have hst' : s.conjExponent.toReal *
      ((1 - t) / q₀.conjExponent.toReal + t / q₁.conjExponent.toReal) = 1 := by
    have he : (1 - t) / q₀.conjExponent.toReal + t / q₁.conjExponent.toReal =
        s.conjExponent.toReal⁻¹ := by
      simp only [div_eq_mul_inv, inv_toReal_conjExponent]
      rw [hst]
      ring
    rw [he, mul_inv_cancel₀ (hc hs).ne']
  apply PiLp.norm_le_of_forall_sum_mul_le (q := s.conjExponent)
  intro b hb
  have h₀' (a : ι → ℂ) (b : κ → ℂ) :
      ‖∑ j, (M *ᵥ a) j * b j‖ ≤ B₀ * ‖toLp p₀ a‖ * ‖toLp q₀.conjExponent b‖ :=
    (PiLp.norm_sum_mul_le (toLp q₀ (M *ᵥ a)) (toLp q₀.conjExponent b)).trans
      (mul_le_mul_of_nonneg_right (h₀ a) (norm_nonneg _))
  have h₁' (a : ι → ℂ) (b : κ → ℂ) :
      ‖∑ j, (M *ᵥ a) j * b j‖ ≤ B₁ * ‖toLp p₁ a‖ * ‖toLp q₁.conjExponent b‖ :=
    (PiLp.norm_sum_mul_le (toLp q₁ (M *ᵥ a)) (toLp q₁.conjExponent b)).trans
      (mul_le_mul_of_nonneg_right (h₁ a) (norm_nonneg _))
  have h := norm_sum_mulVec_interpolate hp₀ hp₁ (hc hq₀) (hc hq₁) hr (hc hs)
    ht₀ ht₁ hrt hst' M hB₀ hB₁ h₀' h₁' a (ofLp b)
  exact h.trans (by
    change _ * ‖b‖ ≤ _
    calc
      _ ≤ (B₀ ^ (1 - t) * B₁ ^ t) * ‖toLp r a‖ * 1 := by gcongr
      _ = _ := mul_one _)

end Matrix
