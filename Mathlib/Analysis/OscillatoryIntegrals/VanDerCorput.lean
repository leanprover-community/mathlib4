/-
Copyright (c) 2025 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos, Manasa Praveen
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

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
  Scalar version, first order case
* `Oscillatory.norm_integral_exp_mul_I_le_of_order_ge_two`:
  Vector-valued amplitude, higher-order case
* `Oscillatory.norm_integral_exp_mul_I_le_of_order_ge_two'`:
  Scalar version, higher-order case

## References

* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality and Oscillatory
  Integrals*, Ch. VIII.1, Prop. 2, pp. 332–334.

-/

@[expose] public section

namespace Oscillatory

open Set Complex NNReal Function
open intervalIntegral Interval

namespace VanDerCorput

/-- The constant appearing in van der Corput's lemma. -/
abbrev c (k : ℕ) : ℝ := 5 * 2 ^ (k - 1) - 2

theorem c_pos (k : ℕ) : 0 < c k := by
  induction k with
  | zero => norm_num
  | succ k hk =>
    norm_num
    have h : (2 ^ k : ℝ) ≥ 1 := by exact_mod_cast Nat.one_le_pow k 2 (by norm_num)
    have := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ (5 : ℝ))
    exact lt_of_lt_of_le (by norm_num : (2 : ℝ) < 5 * 1) this

theorem c_rec {k : ℕ} (hk : 1 ≤ k) : 2 * c k + 2 = c (k + 1) := by
  simp only [c, add_tsub_cancel_right]
  conv_rhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  ring

end VanDerCorput

open VanDerCorput

variable {a b : ℝ} {L : ℝ}
variable {φ : ℝ → ℝ}
variable {k : ℕ}

/-- Auxiliary: If `f` is continuous on `[a, b]` and `|f x| ≥ 1` for all `x ∈ [a, b]`, then either
`f x ≥ 1` for all `x ∈ [a, b]` or `f x ≤ -1` for all `x ∈ [a, b]`. -/
private theorem forall_le_or_forall_le_of_forall_le_abs {a b : ℝ}
    {f : ℝ → ℝ} (hfcont : ContinuousOn f [[a, b]])
    (hf : ∀ x ∈ [[a, b]], 1 ≤ |f x|) :
    (∀ x ∈ [[a, b]], 1 ≤ f x) ∨ (∀ x ∈ [[a, b]], f x ≤ -1) := by
  rcases isPreconnected_uIcc.mapsTo_Ioi_or_Iio (b := (0 : ℝ)) hfcont
      (fun x hx h ↦ zero_lt_one.not_ge <| by simpa [h] using hf x hx) with hp | hn
  · left; intro x hx
    simpa [abs_of_nonneg (show 0 ≤ f x from (hp hx).le)] using hf x hx
  · right; intro x hx
    simpa [le_neg, abs_of_nonpos (show f x ≤ 0 from (hn hx).le)] using hf x hx

/-- Auxiliary lemma used in the higher-order proof -/
private theorem exists_le_abs_of_le_derivWithin
    (hφ : ContDiffOn ℝ 1 φ [[a, b]]) (h : ∀ x ∈ [[a, b]], 1 ≤ derivWithin φ [[a, b]] x) :
    ∃ c ∈ [[a, b]], ∀ x ∈ [[a, b]], |x - c| ≤ |φ x| := by
  by_cases hab : a = b
  · exact ⟨a, left_mem_uIcc, fun x hx ↦ by
      subst hab; rw [uIcc_self] at hx; simp [mem_singleton_iff.mp hx]⟩
  have hud : UniqueDiffOn ℝ [[a, b]] := uniqueDiffOn_Icc (min_lt_max.mpr hab)
  have hmvt : ∀ x ∈ [[a, b]], ∀ y ∈ [[a, b]], x ≤ y → y - x ≤ φ y - φ x := by
    have hg : MonotoneOn (fun x ↦ φ x - x) [[a, b]] := by
      apply monotoneOn_of_deriv_nonneg (convex_uIcc (r := a) (s := b))
        (hφ.continuousOn.sub continuousOn_id)
        ((hφ.differentiableOn (by norm_num)).sub differentiableOn_id |>.mono interior_subset)
      intro x hx
      have hx' := interior_subset hx
      have hda : DifferentiableAt ℝ φ x :=
        ((hφ.differentiableOn (by norm_num)) x hx').differentiableAt
          (Filter.mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset)
      change 0 ≤ deriv (φ - id) x
      rw [deriv_sub hda differentiableAt_id, deriv_id', ← hda.derivWithin (hud x hx')]
      linarith only [h x hx']
    intro x hx y hy hxy; linarith only [hg hx hy hxy]
  have hmin_mem : min a b ∈ [[a, b]] := ⟨le_rfl, min_le_max⟩
  have hmax_mem : max a b ∈ [[a, b]] := ⟨min_le_max, le_rfl⟩
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
    (hφ : ContDiffOn ℝ 2 φ [[a, b]]) (h : ∀ x ∈ [[a, b]], 1 ≤ |derivWithin φ [[a, b]] x|)
    (hφ'_mono : MonotoneOn (derivWithin φ [[a, b]]) [[a, b]])
    (hL : L ≠ 0) :
    ‖∫ x in a..b, exp (L * φ x * I)‖ ≤ c 1 * |L|⁻¹ := by
  wlog! hab : a ≠ b
  · simp only [hab, integral_same, norm_zero]; positivity
  have hud_ab : UniqueDiffOn ℝ [[a, b]] := uniqueDiffOn_Icc <| min_lt_max.mpr hab
  have := hφ.continuousOn
  let φ' := fun x ↦ derivWithin φ [[a, b]] x
  have hasDerivAt_φ : ∀ x ∈ [[a, b]], HasDerivWithinAt φ (φ' x) [[a, b]] x :=
    fun x hx ↦ ((hφ.contDiffWithinAt hx).differentiableWithinAt
      (by norm_num)).hasDerivWithinAt
  have hφ'_cont := hφ.continuousOn_derivWithin hud_ab (by norm_num)
  have h' := forall_le_or_forall_le_of_forall_le_abs hφ'_cont h
  let φ'' := fun x ↦ derivWithin φ' [[a, b]] x
  have hasDerivAt_φ' : ∀ x ∈ [[a, b]], HasDerivWithinAt φ' (φ'' x) [[a, b]] x :=
    fun x hx ↦ (hφ.contDiffWithinAt hx).derivWithin (m := 1) hud_ab (by norm_num) hx |>
      fun h ↦ (h.differentiableWithinAt <| by norm_num).hasDerivWithinAt
  have hφ''_cont : ContinuousOn φ'' [[a, b]] := by
    simpa [φ'', iteratedDerivWithin_succ, iteratedDerivWithin_one] using
      hφ.continuousOn_iteratedDerivWithin (m := 2) (by norm_num) hud_ab
  let u := fun x ↦ 1 / (L * φ' x * I)
  let v := fun x ↦ exp (L * φ x * I)
  let u' := fun x ↦ (φ'' x) * I / (L * (φ' x) ^ 2)
  let v' := fun x ↦ L * φ' x * I * exp (L * φ x * I)
  have hφ'_nz {x : ℝ} (hx : x ∈ [[a, b]]) : φ' x ≠ 0 := by
    rcases h' with h' | h' <;> linarith only [h' x hx]
  have hnz1 {x : ℝ} (hx : x ∈ [[a, b]]) : L * φ' x * I ≠ 0 := by simp [hL, hφ'_nz hx]
  have hnz2 {x : ℝ} (hx : x ∈ [[a, b]]) : (L : ℂ) * (φ' x) ^ 2 ≠ 0 := by simp [hL, hφ'_nz hx]
  have hasDerivAt_u : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x := by
    intro x hx
    convert HasDerivWithinAt.div (hasDerivWithinAt_const ..)
      (.mul (.mul (hasDerivWithinAt_const ..)
        (.ofReal_comp <| hasDerivAt_φ' _ hx))
        (hasDerivWithinAt_const ..)) (hnz1 hx) using 1
    simp only [Pi.mul_apply, zero_mul, zero_add, mul_zero, add_zero, one_mul, zero_sub, mul_pow,
      I_sq, mul_neg, mul_one, neg_div_neg_eq, u']
    have := hφ'_nz hx
    have : ofReal L ^ 2 * (φ' x) ^ 2 ≠ 0 := by norm_cast; positivity
    field_simp
  have hasDerivAt_v : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x := by
    intro x hx
    convert HasDerivWithinAt.cexp (.mul (.mul (hasDerivWithinAt_const ..)
      (.ofReal_comp <| hasDerivAt_φ _ hx)) (hasDerivWithinAt_const ..)) using 1
    simp [v']; ring
  have h1 : ∫ x in a..b, exp (L * φ x * I) = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
    suffices h'' : ∀ x ∈ [[a, b]], exp (L * φ x * I) = u x * v' x by
      rw [integral_congr h'']
      refine integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
        hasDerivAt_u hasDerivAt_v ?intu ?intv
      case intu => exact ContinuousOn.intervalIntegrable (by fun_prop (discharger := assumption))
      case intv => exact ContinuousOn.intervalIntegrable (by fun_prop)
    grind only
  have h2 {x : ℝ} (hx : x ∈ [[a, b]]) : ‖u x * v x‖ ≤ |L|⁻¹ := by
    simp only [u, v, norm_mul, norm_div, norm_one]
    norm_cast
    rw [norm_exp_ofReal_mul_I]
    have hφ'_norm : 1 ≤ ‖φ' x‖ := by simpa [φ', Real.norm_eq_abs] using h x hx
    refine le_of_mul_le_mul_left ?_ (lt_of_lt_of_le zero_lt_one hφ'_norm)
    field_simp [φ', h x hx]
    simpa [Real.norm_eq_abs, norm_I] using le_mul_of_one_le_left (abs_nonneg L) hφ'_norm
  have hasDerivAt_φ'_int : ∀ x ∈ uIoo a b,
      HasDerivWithinAt (fun x ↦ -1 / φ' x)
        (φ'' x / (φ' x) ^ 2) (Ioi x) x := by
    intro x hx
    have hx' := uIoo_subset_uIcc_self hx
    have := ((hasDerivAt_φ' x hx').mono uIoo_subset_uIcc_self).hasDerivAt <| isOpen_Ioo.mem_nhds hx
    convert HasDerivWithinAt.div (hasDerivWithinAt_const ..) this.hasDerivWithinAt ?_ using 1
    · simp
    · exact hφ'_nz hx'
  have hnorm_u'_eq : ∀ x ∈ [[a, b]], ‖u' x‖ = φ'' x / (φ' x) ^ 2 * |L|⁻¹ := by
    intro x hx
    simp only [Complex.norm_div, Complex.norm_mul, norm_real,
      Real.norm_eq_abs, norm_I, mul_one, norm_pow, sq_abs, u']
    rw [abs_of_nonneg <| hφ'_mono.derivWithin_nonneg (x := x), mul_comm |L|]
    have : φ' x ^ 2 * L ≠ 0 := by have := hφ'_nz hx; positivity
    field_simp; rfl
  have hv {x : ℝ} : ‖v x‖ = 1 := by simpa [v] using norm_exp_ofReal_mul_I (L * φ x)
  have h3 : ‖∫ x in a..b, u' x * v x‖ ≤ |L|⁻¹ := by
    apply le_trans norm_integral_le_abs_integral_norm
    simp_rw [norm_mul, hv, mul_one]
    rw [integral_congr hnorm_u'_eq, integral_mul_const]
    rw [integral_eq_sub_of_hasDeriv_right ?_ hasDerivAt_φ'_int]
    · rw [abs_mul, abs_of_pos (show 0 < |L|⁻¹ by positivity)]
      refine le_of_mul_le_mul_right ?_ (show 0 < |L| by positivity)
      rw [mul_assoc, inv_mul_cancel₀ (by positivity), mul_one, neg_div, neg_div, sub_neg_eq_add]
      have hrange :
          (∀ x ∈ [[a, b]], -1 ≤ -(1 / φ' x) ∧ -(1 / φ' x) ≤ 0) ∨
          (∀ x ∈ [[a, b]], 0 ≤ -(1 / φ' x) ∧ -(1 / φ' x) ≤ 1) := by
        rcases h' with hpos | hneg
        · left
          intro x hx
          have hnonneg := div_nonneg zero_le_one (le_trans zero_le_one <| hpos x hx)
          have hle := (one_div_le (lt_of_lt_of_le zero_lt_one <| hpos x hx) zero_lt_one).mpr
            (by simpa using hpos x hx)
          constructor <;> linarith only [hnonneg, hle]
        · right
          intro x hx
          have hnonpos := div_nonpos_iff.mpr
            (Or.inl ⟨zero_le_one, le_trans (hneg x hx) neg_one_lt_zero.le⟩)
          have hle : -(1 / φ' x) ≤ 1 := by
            simpa only [← neg_div] using div_le_one_of_ge (hneg x hx)
              <| le_trans (hneg x hx) <| le_of_lt neg_one_lt_zero
          constructor <;> linarith [hnonpos, hle]
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
    _ ≤ |L|⁻¹ + 2 * |L|⁻¹ := by
      gcongr
      apply le_trans (norm_sub_le ..) (by linarith only [h2 left_mem_uIcc, h2 right_mem_uIcc])
    _ = _ := by ring

/-- **Van der Corput's lemma**. Special case of `norm_integral_exp_mul_I_le_of_order_ge_two`
  where the amplitude function is constant and scalar. -/
theorem norm_integral_exp_mul_I_le_of_order_ge_two' {k : ℕ} (hk : 2 ≤ k)
    (hφc : ContDiffOn ℝ k φ [[a, b]])
    (hφ : ∀ x ∈ [[a, b]], 1 ≤ |iteratedDerivWithin k φ [[a, b]] x|)
    (hL : L ≠ 0) :
    ‖∫ x in a..b, exp (L * φ x * I)‖ ≤ c k * |L| ^ (-(1 : ℝ) / k) := by
  wlog! hab : a < b generalizing a b
  · rcases hab.eq_or_lt with rfl | hba
    · rw [integral_same, norm_zero]; have := c_pos k; positivity
    · convert this (by rwa [uIcc_comm]) (by rwa [uIcc_comm]) hba using 1
      rw [integral_symm, norm_neg]
  revert hk hL
  induction k generalizing a b L φ with
  | zero => intro hk; contradiction
  | succ k ih =>
  intro hk hL
  have hφc' := hφc.continuousOn_iteratedDerivWithin (m := k + 1) (by rfl)
    (uniqueDiffOn_Icc <| min_lt_max.mpr hab.ne)
  wlog hφ' : ∀ x ∈ [[a, b]], 1 ≤ iteratedDerivWithin (k + 1) φ [[a, b]] x
      generalizing φ L
  · rcases forall_le_or_forall_le_of_forall_le_abs hφc' hφ with _ | hφ'
    · contradiction
    convert this (φ := -φ) hφc.neg ?_ (show -L ≠ 0 by simp [hL]) ?_
        (fun x hx ↦ by rw [iteratedDerivWithin_neg]; linarith only [hφ' x hx]) using 3
    · simp
    · simp
    · intro x hx
      simpa [iteratedDerivWithin_neg] using hφ x hx
    · convert hφc'.neg using 2
      exact iteratedDerivWithin_neg _
  clear hφ
  let δ := |L| ^ (-(1 : ℝ) / (k + 1))
  have hφδc := hφc.const_smul δ⁻¹
  obtain ⟨d, hd, hd'⟩ := exists_le_abs_of_le_derivWithin
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
  have hδL_ne : δ * L ≠ 0 := mul_ne_zero hδ_pos.ne' hL
  replace hk : 1 ≤ k := by omega
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
    exact le_trans (by norm_num) <| hφ' x hx'
  have haux {α β : ℝ} (hαβ : [[α, β]] ⊆ [[a, b]])
      (hest : α ≠ β → ∀ x ∈ [[α, β]], δ ≤ |iteratedDerivWithin k φ [[a, b]] x|) :
      ‖∫ x in α..β, exp (L * φ x * I)‖ ≤ c k * (|L| * δ) ^ (-(1 : ℝ) / k) := by
    by_cases hαβ' : α = β
    · simp only [hαβ', integral_same, norm_zero]; have := c_pos k; positivity
    have hud_αβ := uniqueDiffOn_Icc (min_lt_max.mpr hαβ')
    have deriv_eq (x : ℝ) (hx : x ∈ [[α, β]]) :
        iteratedDerivWithin k φ [[α, β]] x = iteratedDerivWithin k φ [[a, b]] x := by
      simp only [iteratedDerivWithin]; congr 1
      exact iteratedFDerivWithin_subset hαβ hud_αβ hud_ab (hφc.of_le (by norm_cast; omega)) hx
    have hψ_bd (x : ℝ) (hx : x ∈ [[α, β]]) :
        1 ≤ |iteratedDerivWithin k (δ⁻¹ • φ) [[α, β]] x| := by
      rw [iteratedDerivWithin_const_smul_field, smul_eq_mul,
          abs_mul, abs_of_pos (inv_pos.mpr hδ_pos), deriv_eq x hx,
          show (1 : ℝ) = δ⁻¹ * δ from (inv_mul_cancel₀ hδ_pos.ne').symm]
      exact mul_le_mul_of_nonneg_left (hest hαβ' x hx) (inv_nonneg.mpr hδ_pos.le)
    have hint_eq (x : ℝ) : cexp (↑L * ↑(φ x) * I) =
        cexp (↑(δ * L) * ↑((δ⁻¹ • φ) x) * I) := by
      simp only [Pi.smul_apply, smul_eq_mul]; congr 2
      rw [← ofReal_mul, ← ofReal_mul]; congr 1
      rw [show δ * L * (δ⁻¹ * φ x) = (δ * δ⁻¹) * (L * φ x) by ring,
          mul_inv_cancel₀ hδ_pos.ne', one_mul]
    simp_rw [hint_eq]
    have hLδ_eq : |δ * L| ^ (-(1 : ℝ) / ↑k) = (|L| * δ) ^ (-(1 : ℝ) / ↑k) := by
      rw [abs_mul, abs_of_pos hδ_pos, mul_comm]
    rcases eq_or_lt_of_le hk with rfl | hk'
    · have deq1 : ∀ z ∈ [[α, β]], derivWithin φ [[α, β]] z = derivWithin φ [[a, b]] z :=
        fun z hz ↦ by simpa only [iteratedDerivWithin_one] using deriv_eq z hz
      have hmono : MonotoneOn (derivWithin (δ⁻¹ • φ) [[α, β]]) [[α, β]] := by
        intro x hx y hy hxy
        simp only [derivWithin_const_smul_field, smul_eq_mul]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hδ_pos.le)
        rw [deq1 x hx, deq1 y hy]
        exact hmono_ab rfl (hαβ hx) (hαβ hy) hxy
      calc _ ≤ c 1 * |δ * L|⁻¹ := norm_integral_exp_mul_I_le_of_order_one'
              (hφδc.mono hαβ)
              (fun x hx ↦ by simpa only [iteratedDerivWithin_one] using hψ_bd x hx)
              hmono hδL_ne
        _ = _ := by
          congr 1; rw [abs_mul, abs_of_pos hδ_pos, mul_comm δ |L|,
            show -(1 : ℝ) / ↑(1 : ℕ) = -1 by norm_num,
            show -(1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg_one]
    · have hψc : ContDiffOn ℝ (k : ℕ∞) (δ⁻¹ • φ) [[α, β]] :=
        (hφδc.mono hαβ).of_le (by exact_mod_cast Nat.le_succ k)
      rcases lt_or_gt_of_ne hαβ' with hlt | hlt
      · exact hLδ_eq ▸ ih hψc hψ_bd hlt hk' hδL_ne
      · rw [integral_symm, norm_neg]
        exact hLδ_eq ▸ ih (by rwa [uIcc_comm]) (by rwa [uIcc_comm]) hlt hk' hδL_ne
  have hest_sub {α β : ℝ} (hαβ : [[α, β]] ⊆ [[a, b]])
      (hle : ∀ x ∈ [[α, β]], δ ≤ |x - d|) :
      ∀ x ∈ [[α, β]], δ ≤ |iteratedDerivWithin k φ [[a, b]] x| := by
    intro x hx
    refine le_trans (hle x hx) ?_
    simpa [uIcc_of_le hab.le] using hd' x (hαβ hx)
  have := hφc.continuousOn
  let f := fun x ↦ cexp (L * φ x * I)
  have hf : ContinuousOn f [[a, b]] := by fun_prop
  rw [← integral_add_adjacent_intervals (b := c₁)
    (ContinuousOn.intervalIntegrable <| ContinuousOn.mono hf hac₁)
    (ContinuousOn.intervalIntegrable <| ContinuousOn.mono hf hc₁b),
    ← integral_add_adjacent_intervals (a := c₁) (b := c₂)
    (ContinuousOn.intervalIntegrable <| ContinuousOn.mono hf hc₁c₂)
    (ContinuousOn.intervalIntegrable <| ContinuousOn.mono hf hc₂b)]
  have hLδ : (|L| * δ) ^ (-(1 : ℝ) / k) = δ := by
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
  calc
      _ ≤ ‖∫ x in a..c₁, exp (L * φ x * I)‖ + ‖∫ x in c₁..c₂, exp (L * φ x * I)‖ +
          ‖∫ x in c₂..b, exp (L * φ x * I)‖ := by
        apply le_trans <| norm_add_le ..
        rw [add_assoc]
        gcongr
        exact norm_add_le ..
      _ ≤ c k * (|L| * δ) ^ (-(1 : ℝ) / k) + 2 * δ + c k * (|L| * δ) ^ (-(1 : ℝ) / k) := by
        gcongr
        · exact haux hac₁ fun hne ↦ hest_sub hac₁ (hac₁_est hne)
        · apply le_trans (norm_integral_le_of_norm_le_const fun x _ ↦ by
            norm_cast; exact le_of_eq <| norm_exp_ofReal_mul_I _)
          simpa using hδ
        · exact haux hc₂b fun hne ↦ hest_sub hc₂b (hc₂b_est hne)
      _ = _ := by
        push_cast
        rw [hLδ, show |L| ^ (-(1 : ℝ) / (↑k + 1)) = δ by rfl, ← c_rec hk]
        ring

end SpecialCase

section GeneralCase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [IsScalarTower ℝ ℂ E]
variable {ψ : ℝ → E}

/-- Auxiliary lemma for proving vector-valued versions of Van der Corput's lemma
from scalar versions. -/
private theorem norm_integral_exp_mul_I_smul_le_of_norm_integral_exp_mul_I {A : ℝ} (hA : 0 < A)
    (hest : ∀ y ∈ [[a, b]], ‖∫ x in a..y, exp (L * φ x * I)‖ ≤ A)
    (hφ_cont : ContinuousOn φ [[a, b]]) (hψ : ContDiffOn ℝ 1 ψ [[a, b]]) :
    ‖∫ x in a..b, exp (L * φ x * I) • ψ x‖ ≤
      A * (‖ψ b‖ + |∫ x in a..b, ‖derivWithin ψ [[a, b]] x‖|) := by
  by_cases hab : a = b
  · simp only [hab, integral_same, norm_zero, Std.le_refl, uIcc_of_le, Icc_self, abs_zero,
    add_zero]; positivity
  have hψ'_cont := hψ.continuousOn_derivWithin (uniqueDiffOn_Icc <| min_lt_max.mpr hab)
    (by norm_num)
  let F := fun x ↦ ∫ t in a..x, exp (L * φ t * I)
  let F' := fun x ↦ exp (L * φ x * I)
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
    (h : ∀ x ∈ [[a, b]], 1 ≤ |derivWithin φ [[a, b]] x|)
    (hφ'_mono : MonotoneOn (derivWithin φ [[a, b]]) [[a, b]])
    (hL : L ≠ 0) :
    ‖∫ x in a..b, exp (L * φ x * I) • ψ x‖ ≤
      c 1 * |L|⁻¹ *
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
    (h : ∀ x ∈ [[a, b]], 1 ≤ |iteratedDerivWithin k φ [[a, b]] x|)
    (hL : L ≠ 0) :
    ‖∫ x in a..b, exp (L * φ x * I) • ψ x‖ ≤
      c k * |L| ^ ((-1 : ℝ) / k) *
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
