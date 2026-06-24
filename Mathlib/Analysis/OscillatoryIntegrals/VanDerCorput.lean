/-
Copyright (c) 2025 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos, Manasa Praveen
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Cases

/-!
# Van der Corput's lemma

We prove van der Corput's lemma for oscillatory integrals of the first kind
in one real variable, following Stein.

## Main definitions

* `Oscillatory.VanDerCorput.c`: the constant `5 * 2 ^ (k - 1) - 2` appearing in the bound.

## Main statements

* `Oscillatory.norm_integral_exp_mul_I_le_of_order_one`:
  Vector-valued amplitude, first order case
* `Oscillatory.norm_integral_exp_mul_I_le_of_order_one'`:
  Scalar constant amplitude version, first order case
* `Oscillatory.norm_integral_exp_mul_I_le_of_order_ge_two`:
  Vector-valued amplitude, higher-order case
* `Oscillatory.norm_integral_exp_mul_I_le_of_order_ge_two'`:
  Scalar constant amplitude version, higher-order case

## Notes

Following the standard argument, we first prove the constant amplitude cases
and then extend to arbitrary amplitudes.

## References

* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality and Oscillatory
  Integrals*, Ch. VIII.1, Prop. 2, pp. 332–334.

-/

@[expose] public section

namespace Oscillatory

open Set Complex Real Function intervalIntegral Interval
open scoped ComplexConjugate

namespace VanDerCorput

/-- The constant appearing in van der Corput's lemma. Note: `c 0` is a junk value. -/
protected abbrev c (k : ℕ) : ℝ := 5 * 2 ^ (k - 1) - 2

open VanDerCorput (c)

protected theorem c_rec {k : ℕ} (hk : k ≠ 0) : c (k + 1) = 2 * c k + 2 := by
  simp only [c, add_tsub_cancel_right]
  conv_lhs => rw [show k = (k - 1) + 1 by lia]
  ring

protected theorem c_pos : ∀ k : ℕ, 0 < c k
| 0 => by norm_num
| 1 => by norm_num
| k + 2 => by rw [VanDerCorput.c_rec (by lia)]; positivity [VanDerCorput.c_pos (k + 1)]

end VanDerCorput

open VanDerCorput (c c_pos c_rec)

variable {a b : ℝ} {L : ℝ}
variable {φ : ℝ → ℝ}
variable {k : ℕ}

/-- Auxiliary lemma used in the higher-order proof -/
private theorem exists_le_abs_of_le_derivWithin
    {L : ℝ} (hL : 0 < L) (hφ : ContDiffOn ℝ 1 φ [[a, b]])
    (h : ∀ x ∈ [[a, b]], L ≤ derivWithin φ [[a, b]] x) :
    ∃ c ∈ [[a, b]], ∀ x ∈ [[a, b]], L * |x - c| ≤ |φ x| := by
  obtain (rfl | hab) := eq_or_ne a b
  · simp
  have hφ' := hφ.continuousOn
  have hmvt : ∀ x ∈ [[a, b]], ∀ y ∈ [[a, b]], x ≤ y → L * (y - x) ≤ φ y - φ x := by
    suffices hg : MonotoneOn (fun x ↦ φ x - L * x) [[a, b]] by
      intro x hx y hy hxy; linarith only [hg hx hy hxy]
    have := (hφ.differentiableOn one_ne_zero).mono interior_subset
    refine monotoneOn_of_deriv_nonneg (convex_uIcc ..) (by fun_prop) (by fun_prop) fun x hx ↦ ?_
    have hdx := this.differentiableAt <| isOpen_interior.mem_nhds hx
    have hx' := interior_subset hx
    rw [deriv_fun_sub hdx (by fun_prop), deriv_const_mul L differentiableAt_fun_id,
      deriv_id'', ← hdx.derivWithin (uniqueDiffOn_uIcc hab x hx')]
    simpa using h x hx'
  have hmon : MonotoneOn φ [[a, b]] := fun x hx y hy hxy ↦
    le_add_neg_iff_le.mp <| le_trans (by positivity) <| hmvt _ hx _ hy hxy
  have hmin : min a b ∈ [[a, b]] := ⟨le_rfl, min_le_max⟩
  have hmax : max a b ∈ [[a, b]] := ⟨min_le_max, le_rfl⟩
  -- If `φ` is non-neg. at left endpoint, take `c` to be left endpoint
  rcases le_or_gt 0 (φ (min a b)) with hm | hm
  · refine ⟨min a b, hmin, fun x hx ↦ ?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1), abs_of_nonneg (le_trans hm <| hmon hmin hx hx.1)]
    linarith [hmvt _ hmin _ hx hx.1, hx.1]
  -- If `φ` is non-pos. at right endpoint, take `c` to be right endpoint
  rcases le_or_gt (φ (max a b)) 0 with hM | hM
  · refine ⟨max a b, hmax, fun x hx ↦ ?_⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2), abs_of_nonpos (le_trans (hmon hx hmax hx.2) hM)]
    linarith [hmvt _ hx _ hmax hx.2, hx.2]
  -- Otherwise, `φ` has a zero. Take `c` so that `φ c = 0`
  have h0 : 0 ∈ [[φ (min a b), φ (max a b)]] := by grind [uIcc_of_le <| le_of_lt <| lt_trans hm hM]
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc
    (hφ.continuousOn.mono (uIcc_subset_uIcc hmin hmax)) h0
  have hc' := uIcc_subset_uIcc hmin hmax hc
  refine ⟨c, hc', fun x hx ↦ ?_⟩
  rcases le_or_gt c x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonneg (by linarith only [hmon hc' hx h, hfc])]
    linarith only [hmvt _ hc' _ hx h, hfc]
  · rw [abs_of_neg (sub_neg.mpr h), abs_of_nonpos (by linarith only [hmon hx hc' h.le, h, hfc])]
    linarith only [hmvt _ hx _ hc' h.le, hfc]

/-- Auxiliary lemma: If the second derivative is bounded from below,
then the first derivative is monotone. -/
private theorem monotoneOn_derivWithin_of_le_iteratedDerivWithin_two
    {L : ℝ} (hab : a ≠ b) (hL : 0 < L) (hφc : ContDiffOn ℝ 2 φ [[a, b]])
    (hφ : ∀ x ∈ [[a, b]], L ≤ iteratedDerivWithin 2 φ [[a, b]] x) :
    MonotoneOn (derivWithin φ [[a, b]]) [[a, b]] := by
  have hud := uniqueDiffOn_uIcc hab
  have hC1 := contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin hud |>.mp hφc |>.2
  suffices MonotoneOn (iteratedDerivWithin 1 φ [[a, b]]) [[a, b]] from
    fun x hx y hy hxy ↦ by simpa [iteratedDerivWithin_one] using this hx hy hxy
  refine monotoneOn_of_deriv_nonneg (convex_uIcc (r := a) (s := b)) hC1.continuousOn
    ((hC1.differentiableOn (by norm_num)).mono interior_subset) fun x hx ↦ ?_
  have hx' := interior_subset hx
  have hda := ((hC1.differentiableOn (by norm_num)) x hx').differentiableAt
    (Filter.mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset)
  rw [← hda.derivWithin (hud x hx'), ← iteratedDerivWithin_succ]
  exact le_trans hL.le <| hφ x hx'

section SpecialCase

/-- **Van der Corput's lemma**. Special case of `norm_integral_exp_mul_I_le_of_order_one`
  where the amplitude function is constant and scalar. -/
theorem norm_integral_exp_mul_I_le_of_order_one'
    (hφ : ContDiffOn ℝ 2 φ [[a, b]]) (h : ∀ x ∈ [[a, b]], L ≤ |derivWithin φ [[a, b]] x|)
    (hφ'_mono : MonotoneOn (derivWithin φ [[a, b]]) [[a, b]]) (hL : 0 < L) :
    ‖∫ x in a..b, exp (φ x * I)‖ ≤ c 1 * L⁻¹ := by
  wlog! hab : a ≠ b
  · simp only [hab, integral_same, norm_zero]; positivity
  have hud := uniqueDiffOn_uIcc hab
  /- `φ` is smooth of order `2` on `[[a, b]]`, hence continuous there, and its derivative within
  `[[a, b]]`, denoted by `φ'`, is continuous on `[[a, b]]`. -/
  have _ := hφ.continuousOn
  let φ' := fun x ↦ derivWithin φ [[a, b]] x
  have hasDerivAt_φ : ∀ x ∈ [[a, b]], HasDerivWithinAt φ (φ' x) [[a, b]] x := fun x hx ↦
    ((hφ.contDiffWithinAt hx).differentiableWithinAt (by norm_num)).hasDerivWithinAt
  have hφ'_cont := hφ.continuousOn_derivWithin hud (by norm_num)
  /- Since `[[a, b]]` is connected and `L ≤ |φ'|` on `[[a, b]]`, either `φ' ≥ L` or `φ' ≤ -L`
  everywhere on this set, so `L ≤ ‖φ' x‖` for all `x ∈ [[a, b]]`. The second derivative of `φ`,
  denoted `φ''`, is also continuous on `[[a, b]]`. -/
  have h' := isPreconnected_uIcc.forall_le_or_forall_le_of_forall_le_abs hL hφ'_cont h
  have hφ'_norm {x : ℝ} (hx : x ∈ [[a, b]]) : L ≤ ‖φ' x‖ := by simpa using h x hx
  let φ'' := fun x ↦ derivWithin φ' [[a, b]] x
  have hasDerivAt_φ' : ∀ x ∈ [[a, b]], HasDerivWithinAt φ' (φ'' x) [[a, b]] x :=
    fun x hx ↦ (hφ.contDiffWithinAt hx).derivWithin (m := 1) hud (by norm_num) hx |>
      fun h ↦ (h.differentiableWithinAt <| by norm_num).hasDerivWithinAt
  have hφ''_cont : ContinuousOn φ'' [[a, b]] := by
    simpa [φ'', iteratedDerivWithin_succ, iteratedDerivWithin_one] using
      hφ.continuousOn_iteratedDerivWithin (m := 2) (by norm_num) hud
  /- The rough idea is just to integrate by parts to gain the factor `L⁻¹`, where we
  express the integrand `exp (φ x * I)` as `u * v'` with `u := (φ' x * I)⁻¹` and
  `v' := φ' x * I * exp (φ x * I)`. -/
  let u := fun x ↦ (φ' x * I)⁻¹
  let v := fun x ↦ exp (φ x * I)
  let u' := fun x ↦ (φ'' x) * I / (φ' x) ^ 2
  let v' := fun x ↦ φ' x * I * exp (φ x * I)
  /- These help automation to succeed later -/
  have hφ'_nz {x : ℝ} (hx : x ∈ [[a, b]]) : φ' x ≠ 0 := by grind
  have hnz1 {x : ℝ} (hx : x ∈ [[a, b]]) : φ' x * I ≠ 0 := by simp [hφ'_nz hx]
  have hnz2 {x : ℝ} (hx : x ∈ [[a, b]]) : ((φ' x) ^ 2 : ℂ) ≠ 0 := by simp [hφ'_nz hx]
  /- The derivatives of `u` and `v` are `u'` and `v'`, respectively. -/
  have hasDerivAt_u : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x := fun x hx ↦ by
    convert! HasDerivWithinAt.inv (.mul (.ofReal_comp <| hasDerivAt_φ' _ hx)
        (hasDerivWithinAt_const _ _ I)) (hnz1 hx) using 1
    simp [mul_pow, u']
  have hasDerivAt_v : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x := fun x hx ↦ by
    convert! HasDerivWithinAt.cexp (.mul (.ofReal_comp <| hasDerivAt_φ _ hx)
      (hasDerivWithinAt_const _ _ I)) using 1
    simp [v']; ring
  have h1 : ∫ x in a..b, exp (φ x * I) = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
    suffices h'' : ∀ x ∈ [[a, b]], exp (φ x * I) = u x * v' x by
      rw [integral_congr h'']
      refine integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt hasDerivAt_u hasDerivAt_v ?_ ?_
        <;> exact ContinuousOn.intervalIntegrable (by fun_prop)
    grind only
  -- The boundary terms are each bounded by `L⁻¹`
  have h2 {x : ℝ} (hx : x ∈ [[a, b]]) : ‖u x * v x‖ ≤ L⁻¹ := by
    simpa [u, v, field, hL.trans_le (h x hx), φ'] using h x hx
  /- We want to estimate the integral `∫ x in a..b, u' x * v x`. We first recognize that
  `‖u' x‖` is the derivative of `fun y ↦ -(φ' y)⁻¹` evaluated at `x`. -/
  have hasDerivAt_φ'_int : ∀ x ∈ uIoo a b, HasDerivWithinAt (fun x ↦ -(φ' x)⁻¹)
      (φ'' x / (φ' x) ^ 2) (Ioi x) x := fun x hx ↦ by
    have hx' := uIoo_subset_uIcc_self hx
    have := hasDerivAt_φ' x hx' |>.mono uIoo_subset_uIcc_self |>.hasDerivAt (isOpen_Ioo.mem_nhds hx)
    simpa [neg_div] using! this.inv (hφ'_nz hx') |>.neg.hasDerivWithinAt
  have hnorm_u'_eq : ∀ x ∈ [[a, b]], ‖u' x‖ = φ'' x / (φ' x) ^ 2 := fun x hx ↦ by
    simp_all [u', φ'', φ', hφ'_mono.derivWithin_nonneg (x := x)]
  /- This is the key estimate, independent of `a, b`. We realize the integrand as the derivative of
  `fun x ↦ (φ' x)⁻¹` and apply the fundamental theorem of calculus. Since `|φ'| ≥ L > 0` and `φ'`
  is continuous (therefore always positive or always negative), `|(φ' b)⁻¹ - (φ' a)⁻¹| ≤ L⁻¹`. -/
  have h3 : ‖∫ x in a..b, u' x * v x‖ ≤ L⁻¹ := calc
    ‖∫ x in a..b, u' x * v x‖ ≤ |∫ x in a..b, ‖u' x * v x‖| := norm_integral_le_abs_integral_norm
    _ = |∫ x in a..b, φ'' x / (φ' x) ^ 2| := by simp [v, integral_congr hnorm_u'_eq]
    _ = |(φ' b)⁻¹ - (φ' a)⁻¹| := by
      rw [integral_eq_sub_of_hasDeriv_right ?cont hasDerivAt_φ'_int ?int]
      case int => exact ContinuousOn.intervalIntegrable <| by fun_prop (discharger := grind)
      case cont => fun_prop (discharger := grind)
      grind
    _ ≤ L⁻¹ := by
      /- To get the right constant, want `≤ L⁻¹`, not `2 * L⁻¹` here,
      so we can't just use the triangle inequality. -/
      suffices hrange : (∀ x ∈ [[a, b]], (φ' x)⁻¹ ≤ L⁻¹ ∧ 0 ≤ (φ' x)⁻¹) ∨
          (∀ x ∈ [[a, b]], (φ' x)⁻¹ ≤ 0 ∧ -L⁻¹ ≤ (φ' x)⁻¹) by
        rcases hrange with h | h <;> grind [h a left_mem_uIcc, h b right_mem_uIcc]
      refine h'.imp ?_ ?_ <;> refine forall₂_imp fun x hx hφL ↦ ?_
      · have : 0 < φ' x := by linarith only [hL, hφL]
        field_simp
        simpa using hφL
      · have : (φ' x)⁻¹ < 0 := by rw [inv_neg'']; linarith only [hL, hφL]
        exact ⟨this.le, by rwa [neg_le, neg_inv, inv_le_inv₀ (by simpa) ‹_›]⟩
  calc
    _ ≤ ‖∫ x in a..b, u' x * v x‖ + ‖u b * v b - u a * v a‖ := by
      rw [h1, sub_eq_neg_add]
      conv_rhs => rw [← norm_neg]
      exact norm_add_le ..
    _ ≤ L⁻¹ + 2 * L⁻¹ := by
      gcongr
      apply le_trans (norm_sub_le ..) (by linarith only [h2 left_mem_uIcc, h2 right_mem_uIcc])
    _ = _ := by ring

/-- **Van der Corput's lemma**. Special case of `norm_integral_exp_mul_I_le_of_order_ge_two`
  where the amplitude function is constant and scalar. -/
theorem norm_integral_exp_mul_I_le_of_order_ge_two' {k : ℕ} (hk : 2 ≤ k)
    (hφc : ContDiffOn ℝ k φ [[a, b]])
    (hφ : ∀ x ∈ [[a, b]], L ≤ |iteratedDerivWithin k φ [[a, b]] x|) (hL : 0 < L) :
    ‖∫ x in a..b, exp (φ x * I)‖ ≤ c k * L ^ (-(1 : ℝ) / k) := by
  wlog! hab : a < b generalizing a b
  · rcases hab.eq_or_lt with rfl | hba
    · rw [integral_same, norm_zero]
      have := c_pos k; positivity
    · convert this (by rwa [uIcc_comm]) (by rwa [uIcc_comm]) hba using 1
      rw [integral_symm, norm_neg]
  revert hk hL
  /- The idea is induction on the order `k`.
  If `k = 2` we use the order one theorem and show the monotonicity condition. -/
  induction k generalizing a b L φ with
  | zero => intro hk; contradiction
  | succ k ih =>
  intro hk hL
  have hφc' := hφc.continuousOn_iteratedDerivWithin (m := k + 1) (by rfl) (uniqueDiffOn_uIcc hab.ne)
  wlog hφ' : ∀ x ∈ [[a, b]], L ≤ iteratedDerivWithin (k + 1) φ [[a, b]] x generalizing φ L
  · rcases isPreconnected_uIcc.forall_le_or_forall_le_of_forall_le_abs hL hφc' hφ with _ | hφ'
    · contradiction
    convert! this (φ := -φ) hφc.neg (by simpa) hL ?_
        (fun x hx ↦ by rw [iteratedDerivWithin_neg]; linarith only [hφ' x hx]) using 1
    · simp [← conj_exp_ofReal_mul_I, intervalIntegral_conj]
    · convert hφc'.neg using 2
      exact funext <| fun x ↦ iteratedDerivWithin_neg _
  /- Main idea: split the integral into three pieces: `[a, d - δ]`, `[d - δ, d + δ]`, `[d + δ, b]`
  `δ` is small and carefully chosen, `d` is argmin of `|φ^(k) x|`,
  so that `δ`-far from `d` we have a good lower bound on `|φ^(k) x|` which allows us
  to use the inductive hypothesis (or the order one theorem). -/
  let δ := L ^ (-(1 : ℝ) / (k + 1))
  obtain ⟨d, hd, hd'⟩ := exists_le_abs_of_le_derivWithin (L := L) (hL := hL)
    ((contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin
      <| uniqueDiffOn_uIcc hab.ne).mp hφc |>.2)
    (by rwa [iteratedDerivWithin_succ] at hφ')
  let c₁ := max a (d - δ)
  let c₂ := min b (d + δ)
  have hδ_pos : 0 < δ := by positivity
  have ⟨had, hdb⟩ : a ≤ d ∧ d ≤ b := by rwa [uIcc_of_le hab.le] at hd
  have hδ : |c₂ - c₁| ≤ 2 * δ := by
    grind [max_le had (sub_le_self d hδ_pos.le), le_min hdb (le_add_of_nonneg_right hδ_pos.le)]
  have hc₁_mem : c₁ ∈ [[a, b]] := ⟨le_trans (min_le_left a b) (le_max_left a (d - δ)),
     max_le (le_max_left a b) (le_trans (sub_le_self d hδ_pos.le) hd.2)⟩
  have hc₂_mem : c₂ ∈ [[a, b]] :=
    ⟨le_min (min_le_right a b) (le_trans hd.1 (le_add_of_nonneg_right hδ_pos.le)),
     le_trans (min_le_left b (d + δ)) (le_max_right a b)⟩
  have hud := uniqueDiffOn_uIcc hab.ne
  replace hk : 1 ≤ k := by omega
  -- This is the main estimate for the outer two pieces, unified to avoid duplication.
  have haux {α β : ℝ} (hαβ' : α ≤ β) (hαβ : [[α, β]] ⊆ [[a, b]])
      (hest : α ≠ β → ∀ x ∈ [[α, β]], L * δ ≤ |iteratedDerivWithin k φ [[a, b]] x|) :
      ‖∫ x in α..β, exp (φ x * I)‖ ≤ c k * (L * δ) ^ (-(1 : ℝ) / k) := by
    by_cases hαβ_ne : α = β
    · simp only [hαβ_ne, integral_same, norm_zero]; have := c_pos k; positivity
    have hud_αβ := uniqueDiffOn_uIcc hαβ_ne
    have deriv_eq (x : ℝ) (hx : x ∈ [[α, β]]) :
        iteratedDerivWithin k φ [[α, β]] x = iteratedDerivWithin k φ [[a, b]] x := by
      simp only [iteratedDerivWithin]; congr 1
      exact iteratedFDerivWithin_subset hαβ hud_αβ hud (hφc.of_le (by norm_cast; omega)) hx
    have hψ_bd (x : ℝ) (hx : x ∈ [[α, β]]) : L * δ ≤ |iteratedDerivWithin k φ [[α, β]] x| := by
      simpa [deriv_eq x hx] using hest hαβ_ne x hx
    rcases eq_or_lt_of_le hk with rfl | hk'
    · -- This is the `k = 1` case: use the order one theorem
      have deq1 : ∀ z ∈ [[α, β]], derivWithin φ [[α, β]] z = derivWithin φ [[a, b]] z :=
        fun z hz ↦ by simpa only [iteratedDerivWithin_one] using deriv_eq z hz
      have hmono : MonotoneOn (derivWithin φ [[α, β]]) [[α, β]] := fun x hx y hy hxy ↦ by
        rw [deq1 x hx, deq1 y hy]
        exact monotoneOn_derivWithin_of_le_iteratedDerivWithin_two
          hab.ne hL hφc hφ' (hαβ hx) (hαβ hy) hxy
      calc _ ≤ c 1 * (L * δ)⁻¹ := norm_integral_exp_mul_I_le_of_order_one'
              (hφc.mono hαβ)
              (fun x hx ↦ by simpa only [iteratedDerivWithin_one] using hψ_bd x hx)
              hmono (by positivity)
        _ = _ := by norm_num [rpow_neg_one]
    · -- This is the `k ≥ 2` case: use inductive hypothesis
      have hψc : ContDiffOn ℝ (k : ℕ∞) φ [[α, β]] := (hφc.mono hαβ).of_le (by norm_cast; simp)
      simpa [mul_comm] using ih hψc hψ_bd (lt_of_le_of_ne hαβ' hαβ_ne) hk' (by positivity)
  -- The derivative estimate `hest` needed by `haux` holds if interval is `δ`-far from `d`.
  have hest_sub {α β : ℝ} (hαβ : [[α, β]] ⊆ [[a, b]])
      (hle : ∀ x ∈ [[α, β]], δ ≤ |x - d|) :
      ∀ x ∈ [[α, β]], L * δ ≤ |iteratedDerivWithin k φ [[a, b]] x| := fun x hx ↦ by
    have h1 : L * |x - d| ≤ |iteratedDerivWithin k φ [[a, b]] x| := by simpa using hd' x (hαβ hx)
    exact le_trans (by have := hle x hx; gcongr) h1
  -- Show that the outer two intervals are `δ`-far from `d`
  have hac₁_est : a ≠ c₁ → ∀ x ∈ [[a, c₁]], δ ≤ |x - d| := fun hne x hx ↦ by
    rw [uIcc_of_le (le_max_left a (d - δ))] at hx
    have : a < d - δ := by by_contra! hle; exact hne (max_eq_left hle).symm
    rw [abs_sub_comm, abs_of_nonneg (by linarith only [hδ_pos, hx.2, max_eq_right this.le])]
    linarith [hx.2, (max_eq_right this.le : c₁ = d - δ)]
  have hc₂b_est : c₂ ≠ b → ∀ x ∈ [[c₂, b]], δ ≤ |x - d| := fun hne x hx ↦ by
    rw [uIcc_of_le (min_le_left b (d + δ))] at hx
    have : d + δ < b := by by_contra! hle; exact hne (min_eq_left hle)
    rw [abs_of_nonneg (by linarith only [hδ_pos, hx.1, min_eq_right this.le])]
    linarith only [hδ_pos, hx.1, min_eq_right this.le]
  -- Finally, split the integral into three pieces
  have hf : ContinuousOn (fun x ↦ exp (φ x * I)) [[a, b]] := by have := hφc.continuousOn; fun_prop
  have hac₁ := uIcc_subset_uIcc left_mem_uIcc hc₁_mem
  have hc₂b := uIcc_subset_uIcc hc₂_mem right_mem_uIcc
  rw [← integral_add_adjacent_intervals (hf.mono hac₁ |>.intervalIntegrable)
          (hf.mono (uIcc_subset_uIcc hc₁_mem right_mem_uIcc) |>.intervalIntegrable),
    ← integral_add_adjacent_intervals (hf.mono (uIcc_subset_uIcc hc₁_mem hc₂_mem)
          |>.intervalIntegrable) (hf.mono hc₂b |>.intervalIntegrable)]
  -- Now apply the triangle inequality and estimate the outer two pieces by `haux`
  calc
    _ ≤ ‖∫ x in a..c₁, exp (φ x * I)‖ + ‖∫ x in c₁..c₂, exp (φ x * I)‖ +
        ‖∫ x in c₂..b, exp (φ x * I)‖ := by grind only [add_assoc, norm_add_le]
    _ ≤ c k * (L * δ) ^ (-(1 : ℝ) / k) + 2 * δ + c k * (L * δ) ^ (-(1 : ℝ) / k) := by
      gcongr
      · exact haux (le_max_left ..) hac₁ fun hne ↦ hest_sub hac₁ (hac₁_est hne)
      · exact le_trans (norm_integral_le_of_norm_le_const fun x _ ↦
          le_of_eq <| norm_exp_ofReal_mul_I _) (by simpa using hδ)
      · exact haux (min_le_left ..) hc₂b fun hne ↦ hest_sub hc₂b (hc₂b_est hne)
    _ = _ := by
      have _ : (L * δ) ^ (-(1 : ℝ) / k) = δ := by
        rw [mul_rpow (by positivity) (by positivity), ← rpow_mul (by positivity),
          ← rpow_add (by positivity)]
        congr; field_simp; simp
      grind only [c_rec <|ne_zero_of_lt hk]

end SpecialCase

section GeneralCase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [IsScalarTower ℝ ℂ E]
variable {ψ : ℝ → E}

/-- Auxiliary lemma for proving vector-valued amplitude versions of Van der Corput's lemma
from constant amplitude versions. -/
private theorem norm_integral_exp_mul_I_smul_le_of_norm_integral_exp_mul_I {A : ℝ} (hA : 0 < A)
    (hest : ∀ y ∈ [[a, b]], ‖∫ x in a..y, exp (φ x * I)‖ ≤ A)
    (hφ_cont : ContinuousOn φ [[a, b]]) (hψ : ContDiffOn ℝ 1 ψ [[a, b]]) :
    ‖∫ x in a..b, exp (φ x * I) • ψ x‖ ≤
      A * (‖ψ b‖ + |∫ x in a..b, ‖derivWithin ψ [[a, b]] x‖|) := by
  by_cases hab : a = b
  · simp only [hab, integral_same, norm_zero, Std.le_refl, uIcc_of_le, Icc_self, abs_zero,
    add_zero]; positivity
  have hψ'_cont := hψ.continuousOn_derivWithin (uniqueDiffOn_uIcc hab) (by norm_num)
  let F := fun x ↦ ∫ t in a..x, exp (φ t * I)
  let F' := fun x ↦ exp (φ x * I)
  let ψ' := fun x ↦ derivWithin ψ [[a, b]] x
  have hasDeriv_ψ := fun x (hx : x ∈ [[a, b]]) ↦
    (hψ.contDiffWithinAt hx).differentiableWithinAt (by norm_num) |>.hasDerivWithinAt
  have cont_F' : ContinuousOn F' [[a, b]] := by fun_prop
  have hasDeriv_F : ∀ x ∈ [[a, b]], HasDerivWithinAt F (F' x) [[a, b]] x := fun x hx ↦ by
    have := FTCFilter.nhdsUIcc (h := ⟨hx⟩)
    apply integral_hasDerivWithinAt_right (t := [[a, b]])
    · exact cont_F'.mono (uIcc_subset_uIcc_left hx) |>.intervalIntegrable
    · exact cont_F'.stronglyMeasurableAtFilter_nhdsWithin measurableSet_uIcc _
    · exact cont_F'.continuousWithinAt hx
  have h1 : ∫ x in a..b, F x • ψ' x = F b • ψ b - F a • ψ a - ∫ x in a..b, F' x • ψ x := by
    apply integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt hasDeriv_F hasDeriv_ψ
      <;> { apply ContinuousOn.intervalIntegrable; fun_prop }
  -- The main point is to integrate by parts to reduce to the constant amplitude case.
  calc
    _ = ‖F b • ψ b - F a • ψ a - ∫ x in a..b, F x • ψ' x‖ := by simp only [h1, sub_sub_cancel, F']
    _ ≤ ‖F b‖ * ‖ψ b‖ + |∫ x in a..b, A * ‖ψ' x‖| := by
      rw [show F a = 0 from integral_same, zero_smul, sub_zero]
      apply le_trans <| norm_sub_le ..
      refine add_le_add (le_of_eq <| norm_smul ..) <| norm_integral_le_abs_of_norm_le ?est ?int
      case int => apply ContinuousOn.intervalIntegrable; fun_prop
      case est => apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
                  intro x hx; rw [norm_smul]; gcongr
                  exact hest _ <| uIoc_subset_uIcc hx
    _ ≤ A * ‖ψ b‖ + A * |∫ x in a..b, ‖ψ' x‖| := by
      gcongr
      · exact hest _ right_mem_uIcc
      · simp [integral_const_mul, abs_of_pos hA]
    _ = _ := by ring

/-- **Van der Corput's lemma** for vector-valued amplitude functions, first order case.
For second and higher order see `norm_integral_exp_mul_I_le_of_order_ge_two`. -/
theorem norm_integral_exp_mul_I_le_of_order_one
    (hφ : ContDiffOn ℝ 2 φ [[a, b]]) (hψ : ContDiffOn ℝ 1 ψ [[a, b]])
    (h : ∀ x ∈ [[a, b]], L ≤ |derivWithin φ [[a, b]] x|)
    (hφ'_mono : MonotoneOn (derivWithin φ [[a, b]]) [[a, b]])
    (hL : 0 < L) :
    ‖∫ x in a..b, exp (φ x * I) • ψ x‖ ≤
      c 1 * L⁻¹ *
        (‖ψ b‖ + |∫ x in a..b, ‖derivWithin ψ [[a, b]] x‖|) := by
  refine norm_integral_exp_mul_I_smul_le_of_norm_integral_exp_mul_I
    (by positivity) ?_ hφ.continuousOn hψ
  intro x hx
  wlog hxa : x ≠ a
  · simp only [not_not.mp hxa, integral_same, norm_zero]; positivity
  have hsubset := uIcc_subset_uIcc_left hx
  have haux : ∀ y ∈ [[a, x]], derivWithin φ [[a, x]] y = derivWithin φ [[a, b]] y := by
    intro y hy
    refine ((hφ.contDiffWithinAt <| hsubset hy).differentiableWithinAt
      (by norm_num)).hasDerivWithinAt |>.mono hsubset |>.derivWithin ?_
    exact uniqueDiffOn_uIcc hxa.symm _ hy
  exact norm_integral_exp_mul_I_le_of_order_one' (hφ.mono hsubset)
    (fun y hy ↦ haux y hy ▸ h y (hsubset hy))
    ((hφ'_mono.mono hsubset).congr <| fun y hy ↦ (haux y hy).symm) hL

/-- **Van der Corput's lemma** for vector-valued amplitude functions, case `k ≥ 2`.
For `k = 1` see `norm_integral_exp_mul_I_le_of_order_one`. -/
theorem norm_integral_exp_mul_I_le_of_order_ge_two {k : ℕ} (hk : 2 ≤ k)
    (hφ : ContDiffOn ℝ k φ [[a, b]]) (hψ : ContDiffOn ℝ 1 ψ [[a, b]])
    (h : ∀ x ∈ [[a, b]], L ≤ |iteratedDerivWithin k φ [[a, b]] x|)
    (hL : 0 < L) :
    ‖∫ x in a..b, exp (φ x * I) • ψ x‖ ≤
      c k * L ^ ((-1 : ℝ) / k) *
        (‖ψ b‖ + |∫ x in a..b, ‖derivWithin ψ [[a, b]] x‖|) := by
  refine norm_integral_exp_mul_I_smul_le_of_norm_integral_exp_mul_I
    (by have := c_pos k; positivity) ?_ hφ.continuousOn hψ
  intro x hx
  have hsubset := uIcc_subset_uIcc_left hx
  wlog hxa : x ≠ a
  · rw [not_not.mp hxa, integral_same, norm_zero]; have := c_pos k; positivity
  have hud_ax := uniqueDiffOn_uIcc (Ne.symm hxa)
  have hab : a ≠ b := by rintro rfl; exact hxa (mem_singleton_iff.mp (by simpa using hx))
  refine norm_integral_exp_mul_I_le_of_order_ge_two' hk (hφ.mono hsubset)
    (fun y hy ↦ ?deriv_est) hL
  rw [show iteratedDerivWithin k φ [[a, x]] y = iteratedDerivWithin k φ [[a, b]] y by
    simp only [iteratedDerivWithin]; congr 1
    exact iteratedFDerivWithin_subset hsubset hud_ax (uniqueDiffOn_uIcc hab)
      (hφ.of_le (by norm_cast)) hy]
  exact h y (hsubset hy)

end GeneralCase

end Oscillatory
