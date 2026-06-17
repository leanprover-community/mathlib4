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

open Set Complex NNReal Function intervalIntegral Interval
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

/-- Auxiliary: If `f` is continuous on `[a, b]` and `|f x| ≥ L > 0` for all `x ∈ [a, b]`,
  then either `f x ≥ L` for all `x ∈ [a, b]` or `f x ≤ -L` for all `x ∈ [a, b]`. -/
private theorem forall_le_or_forall_le_of_forall_le_abs {a b : ℝ}
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hfcont : ContinuousOn f [[a, b]])
    (hf : ∀ x ∈ [[a, b]], L ≤ |f x|) :
    (∀ x ∈ [[a, b]], L ≤ f x) ∨ (∀ x ∈ [[a, b]], L ≤ -f x) := by
  obtain (h | h) := isPreconnected_uIcc.mapsTo_Ioi_or_Iio (b := (0 : ℝ)) hfcont
    (fun x hx h ↦ not_le_of_gt hL <| by simpa [h] using hf x hx)
  all_goals grind [MapsTo]

/-- Auxiliary lemma used in the higher-order proof -/
private theorem exists_le_abs_of_le_derivWithin
    {L : ℝ} (hL : 0 < L) (hφ : ContDiffOn ℝ 1 φ [[a, b]])
    (h : ∀ x ∈ [[a, b]], L ≤ derivWithin φ [[a, b]] x) :
    ∃ c ∈ [[a, b]], ∀ x ∈ [[a, b]], L * |x - c| ≤ |φ x| := by
  by_cases hab : a = b
  · exact ⟨a, left_mem_uIcc, fun x hx ↦ by
      subst hab; rw [uIcc_self] at hx; simp [mem_singleton_iff.mp hx]⟩
  wlog hL1 : L = 1 generalizing φ L
  · obtain ⟨c, hc, hc'⟩ := this (L := 1) (φ := L⁻¹ • φ) (by norm_num) (hφ.const_smul L⁻¹)
      (fun x hx ↦ by
        have : 1 ≤ L⁻¹ * derivWithin φ [[a, b]] x := by field_simp [hL.ne']; linarith [h x hx]
        simpa [smul_eq_mul, derivWithin_const_smul_field] using this) rfl
    refine ⟨c, hc, fun x hx ↦ ?_⟩
    calc
      L * |x - c| ≤ L * |(L⁻¹ • φ) x| := mul_le_mul_of_nonneg_left (by simpa using hc' x hx) hL.le
      _ = |φ x| := by simp [smul_eq_mul, abs_mul, abs_inv, abs_of_pos hL, hL.ne']
  subst hL1
  have hφ' := hφ.continuousOn
  have hφ'' := hφ.differentiableOn one_ne_zero
  have hud : UniqueDiffOn ℝ [[a, b]] := uniqueDiffOn_Icc (min_lt_max.mpr hab)
  have hmvt : ∀ x ∈ [[a, b]], ∀ y ∈ [[a, b]], x ≤ y → y - x ≤ φ y - φ x := by
    suffices hg : MonotoneOn (fun x ↦ φ x - x) [[a, b]] by
      intro x hx y hy hxy; linarith only [hg hx hy hxy]
    have := hφ''.mono interior_subset
    refine monotoneOn_of_deriv_nonneg (convex_uIcc ..) (by fun_prop) (by fun_prop) fun x hx ↦ ?_
    have hdx := this.differentiableAt <| isOpen_interior.mem_nhds hx
    have hx' := interior_subset hx
    rw [deriv_fun_sub hdx (by fun_prop), deriv_id'', ← hdx.derivWithin (hud x hx')]
    linarith only [h x hx']
  have hmin_mem : min a b ∈ [[a, b]] := ⟨le_rfl, min_le_max⟩
  have hmax_mem : max a b ∈ [[a, b]] := ⟨min_le_max, le_rfl⟩
  -- Three cases according to whether `φ` has a zero, or is pos./neg. everywhere.
  -- Note `c` is just the argmin of `|φ x|`.
  rcases le_or_gt 0 (φ (min a b)) with hmin | hmin
  · refine ⟨min a b, hmin_mem, fun x hx ↦ ?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1),
      abs_of_nonneg (le_trans hmin (by linarith only [hmvt _ hmin_mem _ hx hx.1, hx.1]))]
    linarith [hmvt _ hmin_mem _ hx hx.1, hx.1]
  · rcases le_or_gt (φ (max a b)) 0 with hmax | hmax
    · refine ⟨max a b, hmax_mem, fun x hx ↦ ?_⟩
      rw [abs_of_nonpos (sub_nonpos.mpr hx.2),
        abs_of_nonpos (le_trans (by linarith only [hmvt _ hx _ hmax_mem hx.2, hx.2]) hmax)]
      linarith [hmvt _ hx _ hmax_mem hx.2, hx.2]
    · have h0 : (0 : ℝ) ∈ [[φ (min a b), φ (max a b)]] := by
        rw [uIcc_of_le <| le_of_lt <| lt_trans hmin hmax]
        exact ⟨hmin.le, hmax.le⟩
      obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc
        (hφ.continuousOn.mono (uIcc_subset_uIcc hmin_mem hmax_mem)) h0
      have hc' : c ∈ [[a, b]] := uIcc_subset_uIcc hmin_mem hmax_mem hc
      refine ⟨c, hc', fun x hx ↦ ?_⟩
      rw [(show |φ x| = |φ x - φ c| by rw [hfc, sub_zero])]
      rcases le_or_gt c x with hle | hlt
      · rw [abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonneg
          (by linarith only [hmvt _ hc' _ hx hle, hle])]
        linarith only [hmvt _ hc' _ hx hle]
      · rw [abs_of_neg (sub_neg.mpr hlt), abs_of_nonpos
          (by linarith only [hmvt _ hx _ hc' hlt.le, hlt])]
        linarith only [hmvt _ hx _ hc' hlt.le]

section SpecialCase

/-- **Van der Corput's lemma**. Special case of `norm_integral_exp_mul_I_le_of_order_one`
  where the amplitude function is constant and scalar. -/
theorem norm_integral_exp_mul_I_le_of_order_one'
    (hφ : ContDiffOn ℝ 2 φ [[a, b]]) (h : ∀ x ∈ [[a, b]], L ≤ |derivWithin φ [[a, b]] x|)
    (hφ'_mono : MonotoneOn (derivWithin φ [[a, b]]) [[a, b]]) (hL : 0 < L) :
    ‖∫ x in a..b, exp (φ x * I)‖ ≤ c 1 * L⁻¹ := by
  wlog! hab : a ≠ b
  · simp only [hab, integral_same, norm_zero]; positivity
  have hud_ab : UniqueDiffOn ℝ [[a, b]] := uniqueDiffOn_Icc <| min_lt_max.mpr hab
  have := hφ.continuousOn
  let φ' := fun x ↦ derivWithin φ [[a, b]] x
  have hasDerivAt_φ : ∀ x ∈ [[a, b]], HasDerivWithinAt φ (φ' x) [[a, b]] x :=
    fun x hx ↦ ((hφ.contDiffWithinAt hx).differentiableWithinAt
      (by norm_num)).hasDerivWithinAt
  have hφ'_cont := hφ.continuousOn_derivWithin hud_ab (by norm_num)
  have h' := forall_le_or_forall_le_of_forall_le_abs hL hφ'_cont h
  let φ'' := fun x ↦ derivWithin φ' [[a, b]] x
  have hasDerivAt_φ' : ∀ x ∈ [[a, b]], HasDerivWithinAt φ' (φ'' x) [[a, b]] x :=
    fun x hx ↦ (hφ.contDiffWithinAt hx).derivWithin (m := 1) hud_ab (by norm_num) hx |>
      fun h ↦ (h.differentiableWithinAt <| by norm_num).hasDerivWithinAt
  have hφ''_cont : ContinuousOn φ'' [[a, b]] := by
    simpa [φ'', iteratedDerivWithin_succ, iteratedDerivWithin_one] using
      hφ.continuousOn_iteratedDerivWithin (m := 2) (by norm_num) hud_ab
  -- The rough idea is just to integrate by parts to gain the factor `L⁻¹`.
  let u := fun x ↦ 1 / (φ' x * I)
  let v := fun x ↦ exp (φ x * I)
  let u' := fun x ↦ (φ'' x) * I / (φ' x) ^ 2
  let v' := fun x ↦ φ' x * I * exp (φ x * I)
  have hφ'_nz {x : ℝ} (hx : x ∈ [[a, b]]) : φ' x ≠ 0 := by
    rcases h' with h' | h' <;> linarith only [h' x hx, hL]
  have hnz1 {x : ℝ} (hx : x ∈ [[a, b]]) : φ' x * I ≠ 0 := by simp [hφ'_nz hx]
  have hnz2 {x : ℝ} (hx : x ∈ [[a, b]]) : ((φ' x) ^ 2 : ℂ) ≠ 0 := by simp [hφ'_nz hx]
  have hφ'_norm {x : ℝ} (hx : x ∈ [[a, b]]) : L ≤ ‖φ' x‖ := by
    simpa [φ', Real.norm_eq_abs] using h x hx
  have hasDerivAt_u : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x := by
    intro x hx
    convert HasDerivWithinAt.div (hasDerivWithinAt_const _ _ (1 : ℂ))
      (.mul (.ofReal_comp <| hasDerivAt_φ' _ hx)
        (hasDerivWithinAt_const _ _ I)) (hnz1 hx) using 1
    · rfl
    · funext; simp [u]
    · have hφ0 : (φ' x : ℂ) ≠ 0 := by exact_mod_cast hφ'_nz hx
      simp [u']
      field_simp
      simp [I_sq]
  have hasDerivAt_v : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x := by
    intro x hx
    convert HasDerivWithinAt.cexp (.mul (.ofReal_comp <| hasDerivAt_φ _ hx)
      (hasDerivWithinAt_const _ _ I)) using 1
    · simp [v]
    · simp [v']; ring
  have h1 : ∫ x in a..b, exp (φ x * I) = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
    suffices h'' : ∀ x ∈ [[a, b]], exp (φ x * I) = u x * v' x by
      rw [integral_congr h'']
      refine integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt hasDerivAt_u hasDerivAt_v ?_ ?_
        <;> exact ContinuousOn.intervalIntegrable (by fun_prop (discharger := assumption))
    grind only
  -- The boundary terms are each bounded by `L⁻¹`
  have h2 {x : ℝ} (hx : x ∈ [[a, b]]) : ‖u x * v x‖ ≤ L⁻¹ := by
    simp only [u, v, norm_mul, norm_div, norm_one]
    norm_cast
    rw [norm_exp_ofReal_mul_I]
    have := norm_ne_zero_iff.mpr <| hφ'_nz hx
    field_simp [φ', h x hx]
    have := hφ'_norm hx
    rwa [norm_I, mul_one]
  -- We want to estimate the integral on RHS of `h1` **uniformly** in `a, b`.
  -- The idea is to use FTC and monotonicity. We require some groundwork first.
  have hasDerivAt_φ'_int : ∀ x ∈ uIoo a b, HasDerivWithinAt (fun x ↦ -1 / φ' x)
      (φ'' x / (φ' x) ^ 2) (Ioi x) x := by
    intro x hx
    have hx' := uIoo_subset_uIcc_self hx
    have := ((hasDerivAt_φ' x hx').mono uIoo_subset_uIcc_self).hasDerivAt <| isOpen_Ioo.mem_nhds hx
    convert HasDerivWithinAt.div (hasDerivWithinAt_const _ _ (-1)) this.hasDerivWithinAt ?_ using 1
    · rfl
    · rfl
    · funext; simp
    · simp
    · exact hφ'_nz hx'
  have hnorm_u'_eq : ∀ x ∈ [[a, b]], ‖u' x‖ = φ'' x / (φ' x) ^ 2 := by
    intro x hx
    simp only [Complex.norm_div, Complex.norm_mul, norm_real,
      Real.norm_eq_abs, norm_I, mul_one, norm_pow, sq_abs, u']
    rw [abs_of_nonneg <| hφ'_mono.derivWithin_nonneg (x := x)]
  have hv {x : ℝ} : ‖v x‖ = 1 := by simp [v]
  -- This is the key estimate, independent of `a, b`.
  have h3 : ‖∫ x in a..b, u' x * v x‖ ≤ L⁻¹ := by
    apply le_trans norm_integral_le_abs_integral_norm
    simp_rw [norm_mul, hv, mul_one]
    -- Discover integral of a derivative and use FTC.
    rw [integral_congr hnorm_u'_eq, integral_eq_sub_of_hasDeriv_right ?_ hasDerivAt_φ'_int]
    · -- To get the right constant, want `≤ L⁻¹`, not `2 * L⁻¹` here,
      -- so we can't just use the triangle inequality.
      have : |-1 / φ' b - -1 / φ' a| = |1 / φ' b - 1 / φ' a| := by
        rw [neg_div, neg_div, sub_neg_eq_add, add_comm, ← sub_eq_add_neg, abs_sub_comm]
      rw [this]
      have hrange : (∀ x ∈ [[a, b]], 1 / φ' x ≤ L⁻¹ ∧ 0 ≤ 1 / φ' x) ∨
                (∀ x ∈ [[a, b]], 1 / φ' x ≤ 0 ∧ -L⁻¹ ≤ (1 / φ' x)) := by
        rcases h' with hpos | hneg
        · left
          intro x hx
          have hposx := hpos x hx
          have : 0 < φ' x := by linarith only [hL, hposx]
          constructor <;> field_simp
          · assumption
          · simp
        · right
          intro x hx
          have hnegx := hneg x hx
          constructor
          · exact one_div_nonpos.mpr (by linarith only [hnegx, hL])
          · simpa [one_div_neg] using (neg_le_neg <| one_div_le_one_div_of_le hL hnegx)
      rcases hrange with hrange | hrange <;>
        have ha := hrange a left_mem_uIcc <;>
        have hb := hrange b right_mem_uIcc <;>
        rw [abs_le] <;> constructor <;> linarith only [ha, hb]
    · apply ContinuousOn.intervalIntegrable
      fun_prop (discharger := try { exact fun x hx ↦ by have := hφ'_nz hx; positivity })
    · fun_prop (discharger := exact fun x hx ↦ by have := hφ'_nz hx; positivity)
  calc
    _ ≤ ‖∫ x in a..b, u' x * v x‖ + ‖u b * v b - u a * v a‖ := by
      rw [h1, sub_eq_neg_add]
      nth_rewrite 2 [← norm_neg]
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
  -- The idea is induction on the order `k`.
  -- If `k = 2` we use the order one theorem and show the monotonicity condition.
  induction k generalizing a b L φ with
  | zero => intro hk; contradiction
  | succ k ih =>
  intro hk hL
  have hφc' := hφc.continuousOn_iteratedDerivWithin (m := k + 1) (by rfl)
    (uniqueDiffOn_Icc <| min_lt_max.mpr hab.ne)
  wlog hφ' : ∀ x ∈ [[a, b]], L ≤ iteratedDerivWithin (k + 1) φ [[a, b]] x
      generalizing φ L
  · rcases forall_le_or_forall_le_of_forall_le_abs hL hφc' hφ with _ | hφ'
    · contradiction
    convert this (φ := -φ) hφc.neg ?_ hL ?_
        (fun x hx ↦ by rw [iteratedDerivWithin_neg]; linarith only [hφ' x hx]) using 1
    · simp_rw [Pi.neg_apply, ofReal_neg, neg_mul, ← conj_exp_ofReal_mul_I,
        intervalIntegral_conj, norm_conj]
    · simpa
    · convert hφc'.neg using 2
      exact iteratedDerivWithin_neg _
  clear hφ
  -- Main idea: split the integral into three pieces: `[a, d - δ]`, `[d - δ, d + δ]`, `[d + δ, b]`
  -- `δ` is small and carefully chosen, `d` is argmin of `|φ^(k) x|`,
  -- so that `δ`-away from `d` we have a good lower bound on `|φ^(k) x|` which allows us
  -- to use the inductive hypothesis (or the order one theorem).
  let δ := L ^ (-(1 : ℝ) / (k + 1))
  obtain ⟨d, hd, hd'⟩ := exists_le_abs_of_le_derivWithin (L := L) (hL := hL)
    ((contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin
      <| uniqueDiffOn_Icc <| min_lt_max.mpr hab.ne).mp hφc |>.2)
    (by rwa [iteratedDerivWithin_succ] at hφ')
  let c₁ := max a (d - δ)
  let c₂ := min b (d + δ)
  rw [min_eq_left_of_lt hab, max_eq_right_of_lt hab] at hd'
  have hδ_pos : (0 : ℝ) < δ := by positivity
  have ⟨had, hdb⟩ : a ≤ d ∧ d ≤ b := by rwa [uIcc_of_le hab.le] at hd
  have hδ : |c₂ - c₁| ≤ 2 * δ := by
    have h1 : c₁ ≤ d := max_le had (sub_le_self d hδ_pos.le)
    have h2 : d ≤ c₂ := le_min hdb (le_add_of_nonneg_right hδ_pos.le)
    rw [abs_of_nonneg (by linarith only [h1, h2])]
    linarith only [min_le_right b (d + δ), le_max_right a (d - δ)]
  have hc₁_mem : c₁ ∈ [[a, b]] :=
    ⟨le_trans (min_le_left a b) (le_max_left a (d - δ)),
     max_le (le_max_left a b) (le_trans (sub_le_self d hδ_pos.le) hd.2)⟩
  have hc₂_mem : c₂ ∈ [[a, b]] :=
    ⟨le_min (min_le_right a b) (le_trans hd.1 (le_add_of_nonneg_right hδ_pos.le)),
     le_trans (min_le_left b (d + δ)) (le_max_right a b)⟩
  have hac₁ : [[a, c₁]] ⊆ [[a, b]] := uIcc_subset_uIcc left_mem_uIcc hc₁_mem
  have hc₁b : [[c₁, b]] ⊆ [[a, b]] := uIcc_subset_uIcc hc₁_mem right_mem_uIcc
  have hc₁c₂ : [[c₁, c₂]] ⊆ [[a, b]] := uIcc_subset_uIcc hc₁_mem hc₂_mem
  have hc₂b : [[c₂, b]] ⊆ [[a, b]] := uIcc_subset_uIcc hc₂_mem right_mem_uIcc
  have hud_ab : UniqueDiffOn ℝ [[a, b]] := uniqueDiffOn_Icc <| min_lt_max.mpr hab.ne
  replace hk : 1 ≤ k := by omega
  -- If `k = 1` we will need the monotonicity condition of the order one theorem.
  have hmono_ab (hk : k = 1) : MonotoneOn (derivWithin φ [[a, b]]) [[a, b]] := by
    subst hk
    have hC1 := contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin hud_ab |>.mp hφc |>.2
    suffices MonotoneOn (iteratedDerivWithin 1 φ [[a, b]]) [[a, b]] by
      exact fun x hx y hy hxy ↦ by simpa [iteratedDerivWithin_one] using this hx hy hxy
    apply monotoneOn_of_deriv_nonneg (convex_uIcc (r := a) (s := b)) hC1.continuousOn
      ((hC1.differentiableOn (by norm_num)).mono interior_subset)
    intro x hx
    have hx' := interior_subset hx
    have hda := ((hC1.differentiableOn (by norm_num)) x hx').differentiableAt
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset)
    rw [← hda.derivWithin (hud_ab x hx'), ← iteratedDerivWithin_succ]
    exact le_trans hL.le <| hφ' x hx'
  -- This is the main estimate for the outer two pieces, unified to avoid duplication.
  have haux {α β : ℝ} (hαβ : [[α, β]] ⊆ [[a, b]])
      (hest : α ≠ β → ∀ x ∈ [[α, β]], L * δ ≤ |iteratedDerivWithin k φ [[a, b]] x|) :
      ‖∫ x in α..β, exp (φ x * I)‖ ≤ c k * (L * δ) ^ (-(1 : ℝ) / k) := by
    by_cases hαβ' : α = β
    · simp only [hαβ', integral_same, norm_zero]; have := c_pos k; positivity
    have hud_αβ := uniqueDiffOn_Icc (min_lt_max.mpr hαβ')
    have deriv_eq (x : ℝ) (hx : x ∈ [[α, β]]) :
        iteratedDerivWithin k φ [[α, β]] x = iteratedDerivWithin k φ [[a, b]] x := by
      simp only [iteratedDerivWithin]; congr 1
      exact iteratedFDerivWithin_subset hαβ hud_αβ hud_ab (hφc.of_le (by norm_cast; omega)) hx
    have hψ_bd (x : ℝ) (hx : x ∈ [[α, β]]) :
        L * δ ≤ |iteratedDerivWithin k φ [[α, β]] x| := by
      simpa [deriv_eq x hx] using hest hαβ' x hx
    rcases eq_or_lt_of_le hk with rfl | hk'
    · -- This is the `k = 1` case: use the order one theorem
      have deq1 : ∀ z ∈ [[α, β]], derivWithin φ [[α, β]] z = derivWithin φ [[a, b]] z :=
        fun z hz ↦ by simpa only [iteratedDerivWithin_one] using deriv_eq z hz
      have hmono : MonotoneOn (derivWithin φ [[α, β]]) [[α, β]] := by
        intro x hx y hy hxy
        rw [deq1 x hx, deq1 y hy]
        exact hmono_ab rfl (hαβ hx) (hαβ hy) hxy
      calc _ ≤ c 1 * (L * δ)⁻¹ := norm_integral_exp_mul_I_le_of_order_one'
              (hφc.mono hαβ)
              (fun x hx ↦ by
                simpa only [iteratedDerivWithin_one]
                    using hψ_bd x hx)
              hmono (by positivity)
        _ = _ := by norm_num [Real.rpow_neg_one]
    · -- This is the `k ≥ 2` case: use inductive hypothesis
      have hψc : ContDiffOn ℝ (k : ℕ∞) φ [[α, β]] :=
        (hφc.mono hαβ).of_le (by exact_mod_cast Nat.le_succ k)
      rcases lt_or_gt_of_ne hαβ' with hlt | hlt
      · simpa [mul_comm] using ih hψc hψ_bd hlt hk' (by positivity)
      · rw [integral_symm, norm_neg]
        simpa [mul_comm] using ih (by rwa [uIcc_comm]) (by rwa [uIcc_comm]) hlt hk' (by positivity)
  -- Auxiliaries for verifying the hypothesis of `haux`.
  have hest_sub {α β : ℝ} (hαβ : [[α, β]] ⊆ [[a, b]])
      (hle : ∀ x ∈ [[α, β]], δ ≤ |x - d|) :
      ∀ x ∈ [[α, β]], L * δ ≤ |iteratedDerivWithin k φ [[a, b]] x| := by
    intro x hx
    have h1 : δ ≤ |x - d| := hle x hx
    have h2 : L * |x - d| ≤ |iteratedDerivWithin k φ [[a, b]] x| :=
      by simpa [uIcc_of_le hab.le] using hd' x (hαβ hx)
    exact le_trans (by gcongr) h2
  have hφcont : ContinuousOn φ [[a, b]] := hφc.continuousOn
  have hf : ContinuousOn (fun x : ℝ ↦ exp (φ x * I)) [[a, b]] := by fun_prop [hφcont]
  have hLδ : (L * δ) ^ (-(1 : ℝ) / k) = δ := by
    simp only [δ]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
      ← Real.rpow_add (by positivity)]
    congr
    field_simp
    simp
  have hac₁_est : a ≠ c₁ → ∀ x ∈ [[a, c₁]], δ ≤ |x - d| := by
    intro hne x hx
    rw [uIcc_of_le (le_max_left a (d - δ))] at hx
    have : a < d - δ := by by_contra! hle; exact hne (max_eq_left hle).symm
    rw [abs_sub_comm, abs_of_nonneg (by linarith only [hδ_pos, hx.2, max_eq_right this.le])]
    linarith [hx.2, (max_eq_right this.le : c₁ = d - δ)]
  have hc₂b_est : c₂ ≠ b → ∀ x ∈ [[c₂, b]], δ ≤ |x - d| := by
    intro hne x hx
    rw [uIcc_of_le (min_le_left b (d + δ))] at hx
    have : d + δ < b := by by_contra! hle; exact hne (min_eq_left hle)
    rw [abs_of_nonneg (by linarith only [hδ_pos, hx.1, min_eq_right this.le])]
    linarith only [hδ_pos, hx.1, min_eq_right this.le]
  -- Finally we are ready to put the pieces together
  rw [← integral_add_adjacent_intervals (b := c₁)
    (ContinuousOn.intervalIntegrable <| ContinuousOn.mono hf hac₁)
    (ContinuousOn.intervalIntegrable <| ContinuousOn.mono hf hc₁b),
    ← integral_add_adjacent_intervals (a := c₁) (b := c₂)
    (ContinuousOn.intervalIntegrable <| ContinuousOn.mono hf hc₁c₂)
    (ContinuousOn.intervalIntegrable <| ContinuousOn.mono hf hc₂b)]
  calc
    _ ≤ ‖∫ x in a..c₁, exp (φ x * I)‖ + ‖∫ x in c₁..c₂, exp (φ x * I)‖ +
        ‖∫ x in c₂..b, exp (φ x * I)‖ := by
      apply le_trans <| norm_add_le ..
      rw [add_assoc]
      gcongr
      exact norm_add_le ..
    _ ≤ c k * (L * δ) ^ (-(1 : ℝ) / k) + 2 * δ + c k * (L * δ) ^ (-(1 : ℝ) / k) := by
      gcongr
      · exact haux hac₁ fun hne ↦ hest_sub hac₁ (hac₁_est hne)
      · apply le_trans (norm_integral_le_of_norm_le_const fun x _ ↦ by
          exact le_of_eq <| norm_exp_ofReal_mul_I _)
        simpa using hδ
      · exact haux hc₂b fun hne ↦ hest_sub hc₂b (hc₂b_est hne)
    _ = _ := by
      push_cast
      rw [hLδ, show L ^ (-(1 : ℝ) / (↑k + 1)) = δ by rfl, c_rec <|ne_zero_of_lt hk]
      ring

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
  have hψ'_cont := hψ.continuousOn_derivWithin (uniqueDiffOn_Icc <| min_lt_max.mpr hab)
    (by norm_num)
  let F := fun x ↦ ∫ t in a..x, exp (φ t * I)
  let F' := fun x ↦ exp (φ x * I)
  let ψ' := fun x ↦ derivWithin ψ [[a, b]] x
  have hasDeriv_ψ := fun x (hx : x ∈ [[a, b]]) ↦
    (hψ.contDiffWithinAt hx).differentiableWithinAt (by norm_num) |>.hasDerivWithinAt
  have cont_F' : ContinuousOn F' [[a, b]] := by fun_prop
  have hasDeriv_F : ∀ x ∈ [[a, b]], HasDerivWithinAt F (F' x) [[a, b]] x := by
    intro x hx
    have := FTCFilter.nhdsUIcc (h := ⟨hx⟩)
    apply integral_hasDerivWithinAt_right (t := [[a, b]])
    · exact ContinuousOn.intervalIntegrable <| ContinuousOn.mono cont_F'
        <| uIcc_subset_uIcc_left hx
    · apply ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin cont_F' measurableSet_uIcc
    · exact ContinuousOn.continuousWithinAt cont_F' hx
  have h1 : ∫ x in a..b, F x • ψ' x = F b • ψ b - F a • ψ a - ∫ x in a..b, F' x • ψ x := by
    apply integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt hasDeriv_F hasDeriv_ψ
      <;> { apply ContinuousOn.intervalIntegrable; fun_prop }
  -- The main point is to integrate by parts to reduce to the constant amplitude case.
  calc
    _ = ‖F b • ψ b - F a • ψ a - ∫ x in a..b, F x • ψ' x‖ := by simp only [h1, sub_sub_cancel, F']
    _ ≤ ‖F b‖ * ‖ψ b‖ + |∫ x in a..b, A * ‖ψ' x‖| := by
      rw [show F a = 0 from integral_same, zero_smul, sub_zero]
      apply le_trans <| norm_sub_le ..
      apply add_le_add (le_of_eq <| norm_smul ..)
      apply norm_integral_le_abs_of_norm_le
      · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
        intro x hx; rw [norm_smul]; gcongr
        exact hest _ <| uIoc_subset_uIcc hx
      · apply ContinuousOn.intervalIntegrable; fun_prop
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
    have := uniqueDiffOn_Icc (min_lt_max.mpr hxa.symm) _ hy
    exact ((hφ.contDiffWithinAt <| hsubset hy).differentiableWithinAt
      (by norm_num)).hasDerivWithinAt |>.mono hsubset |>.derivWithin this
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
  have hud_ax : UniqueDiffOn ℝ [[a, x]] := uniqueDiffOn_Icc (min_lt_max.mpr (Ne.symm hxa))
  have hab : a ≠ b := by rintro rfl; exact hxa (mem_singleton_iff.mp (by simpa using hx))
  refine norm_integral_exp_mul_I_le_of_order_ge_two' hk (hφ.mono hsubset)
    (fun y hy ↦ ?deriv_est) hL
  rw [show iteratedDerivWithin k φ [[a, x]] y = iteratedDerivWithin k φ [[a, b]] y by
    simp only [iteratedDerivWithin]; congr 1
    exact iteratedFDerivWithin_subset hsubset hud_ax
      (uniqueDiffOn_Icc (min_lt_max.mpr hab))
      (hφ.of_le (by norm_cast)) hy]
  exact h y (hsubset hy)

end GeneralCase

end Oscillatory
