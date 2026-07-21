/-
Copyright (c) 2025 Louis (Yiyang) Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis (Yiyang) Liu, Joris Roos
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.MeanValue

import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.Prod

/-!
# First and second mean value theorems for interval integrals

We prove versions of the first and second mean value theorems for interval integrals.

## Main results

First mean value theorem
* `exists_eq_const_mul_intervalIntegral_of_ae_nonneg` (a.e. nonnegativity of `g` on `s`):
    `∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ)`.
* `exists_eq_const_mul_intervalIntegral_of_nonneg` (pointwise nonnegativity of `g` on `s`):
    `∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ)`.

Second mean value theorem
* `exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn`
  For nonnegative and nonincreasing `f : ℝ → ℝ` and integrable `g : ℝ → ℝ` on `Icc a b`:
    `∃ ξ ∈ Icc a b, ∫ x in a..b, f x * g x = f a * ∫ x in a..ξ, g x`
* `exists_eq_const_mul_intervalIntegral_of_nonneg_of_monotoneOn` (nondecreasing variant)

A vector-valued inequality variant of the second mean value theorem
* `exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn`
  Let `E` be a real Banach space. For nonnegative and nonincreasing
  `f : ℝ → ℝ` and integrable `g : ℝ → E` on `Icc a b`:
  `∃ ξ ∈ Icc a b, ‖∫ x in a..b, f x • g x‖ ≤ f a * ‖∫ x in a..ξ, g x‖`
* `exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_monotoneOn` (nondecreasing variant)


## References

* [V. A. Zorich, *Mathematical Analysis I*][zorich2015],
    Thm. 5 (First mean-value theorem for the integral).
* <https://proofwiki.org/wiki/Mean_Value_Theorem_for_Integrals/Generalization>
* [E. T. Whittaker, G. N. Watson, *A Course of Modern Analysis*, 5th edition][WW21]
    p. 63

## Tags

mean value theorem, interval integral
-/

public section

open MeasureTheory Set intervalIntegral

open scoped Interval

variable {a b : ℝ} {f g : ℝ → ℝ}

section First

variable {μ : Measure ℝ}

/-- **First mean value theorem for interval integrals (arbitrary measure, a.e. nonnegativity).**
Let `f g : ℝ → ℝ` and let `μ` be a measure on `ℝ`. Assume that `f` is continuous on `uIcc a b`,
that `g` is interval integrable on `a..b` w.r.t. `μ`, and that `g ≥ 0` a.e. on `Ι a b` w.r.t.
`μ.restrict (Ι a b)`. Then
`∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ)`. -/
theorem exists_eq_const_mul_intervalIntegral_of_ae_nonneg
    (hf : ContinuousOn f (uIcc a b)) (hg : IntervalIntegrable g μ a b)
    (hg0 : ∀ᵐ x ∂(μ.restrict (Ι a b)), 0 ≤ g x) :
    ∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ) := by
  by_cases h : a = b
  · subst h
    exact ⟨a, by simp, by simp⟩
  wlog hab : a < b generalizing a b
  · simp only [not_lt] at hab
    obtain ⟨c, c_in_uIcc, that⟩ :=
      this (by rwa [uIcc_comm]) hg.symm (by rwa [uIoc_comm]) (by lia) (lt_of_le_of_ne' hab h)
    exact ⟨c, by rwa [uIcc_comm], by simpa [integral_symm b a]⟩
  let s := Ι a b
  have hs : s = Ioc a b := uIoc_of_le hab.le
  have hs' : s ⊆ [[a, b]] := uIoc_subset_uIcc
  have hs_conn : IsConnected s := by simpa [hs] using isConnected_Ioc hab
  have hfg : IntegrableOn (fun x ↦ f x * g x) s μ := by
    rw [← intervalIntegrable_iff]
    exact hg.continuousOn_smul hf
  obtain ⟨c, hc, h⟩ := exists_eq_const_mul_setIntegral_of_ae_nonneg
    hs_conn measurableSet_uIoc (hf.mono hs') (by rwa [← intervalIntegrable_iff]) hfg hg0
  have h' : ∫ (x : ℝ) in a..b, f x * g x ∂μ = f c * ∫ (x : ℝ) in a..b, g x ∂μ := by
    simpa [intervalIntegral.integral_of_le hab.le, hs] using h
  exact ⟨c, mem_of_subset_of_mem hs' hc, h'⟩

/-- **First mean value theorem for interval integrals (arbitrary measure, nonnegativity).**
Let `f g : ℝ → ℝ` and let `μ` be a measure on `ℝ`. Assume that `f` is continuous on `uIcc a b`,
that `g` is interval integrable on `a..b` w.r.t. `μ`, and that `g ≥ 0` on `Ι a b`. Then
`∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ)`. -/
theorem exists_eq_const_mul_intervalIntegral_of_nonneg
    (hf : ContinuousOn f (uIcc a b)) (hg : IntervalIntegrable g μ a b)
    (hg0 : ∀ x ∈ Ι a b, 0 ≤ g x) :
    ∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ) := by
  have hg0_ae : ∀ᵐ x ∂(μ.restrict (Ι a b)), 0 ≤ g x := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact ae_of_all μ hg0
  exact exists_eq_const_mul_intervalIntegral_of_ae_nonneg hf hg hg0_ae

end First

section Second

/-- **Second mean value theorem for interval integrals** with a nonnegative antitone weight. -/
theorem exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
    (hab : a ≤ b) (hf : 0 ≤ f b)
    (hf_mon : AntitoneOn f (Icc a b)) (hg : IntervalIntegrable g volume a b) : ∃ ξ ∈ Icc a b,
    ∫ x in a..b, f x * g x = f a * ∫ x in a..ξ, g x := by
  -- The first step is to write `f x` as layercake integral and use Fubini.
  have hsub : Ι a b ⊆ Icc a b := uIcc_of_le hab ▸ uIoc_subset_uIcc
  have hf_nonneg x (hx : x ∈ Icc a b) : 0 ≤ f x := hf.trans (hf_mon.mapsTo_Icc hx).1
  let H := fun r ↦ ∫ x in a..b, ({x | r ≤ f x}.indicator g) x
  have h_int : Integrable ({p : ℝ × ℝ | p.2 ≤ f p.1}.indicator fun p ↦ g p.1)
      ((volume.restrict (uIoc a b)).prod (volume.restrict (uIoc 0 (f a)))) := by
    simpa only [Function.comp_apply, mul_one] using
      (hg.def'.mul_prod (intervalIntegrable_const (c := 1)).def').indicator₀
        (nullMeasurableSet_le measurable_snd.aemeasurable
          (aemeasurable_restrict_of_antitoneOn measurableSet_uIoc (hf_mon.mono hsub)).comp_fst)
  have hfub : ∫ x in a..b, f x * g x = ∫ r in 0..f a, H r := by
    rw [intervalIntegral.integral_congr_ae_restrict <|
      ae_restrict_of_forall_mem measurableSet_uIoc fun x hx ↦ by
      simpa using (intervalIntegral.integral_indicator (μ := volume) (f := fun _ ↦ g x)
        ⟨hf_nonneg x (hsub hx), (hf_mon.mapsTo_Icc (hsub hx)).2⟩).symm]
    apply intervalIntegral_intervalIntegral_swap
    rwa [IntegrableOn, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict]
  -- The case `f a = 0` is trivial because then `f` is zero on the whole interval
  rcases (hf_nonneg a ⟨le_rfl, hab⟩).eq_or_lt with hfa | hfa
  · exact ⟨a, ⟨le_rfl, hab⟩, by simpa [hfa.symm] using hfub⟩
  -- We will use the intermediate value theorem on the following function
  let G := fun x ↦ ∫ t in a..x, g t
  have hGcont := uIcc_of_le hab ▸ continuousOn_primitive_interval' hg left_mem_uIcc
  obtain ⟨ξmin, hξmin, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hGcont
  obtain ⟨ξmax, hξmax, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) hGcont
  have hH_int : IntervalIntegrable H volume 0 (f a) := by
    rw [intervalIntegrable_iff, IntegrableOn]
    simp_rw [H, intervalIntegral_eq_integral_uIoc]
    exact (h_int.swap.integral_prod_left).const_mul _
  -- Since `f` is nonincreasing, the superlevel sets are intervals and `H r` is in the range of `G`.
  have hH_bounds r (hr : r ∈ Icc 0 (f a)) : G ξmin ≤ H r ∧ H r ≤ G ξmax := by
    let S := {x | x ∈ Icc a b ∧ r ≤ f x}
    have hS := isLUB_csSup (s := S) ⟨a, ⟨⟨le_rfl, hab⟩, hr.2⟩⟩ ⟨b, fun _ h ↦ h.1.2⟩
    have hc : sSup S ∈ Icc a b :=
      ⟨hS.1 ⟨⟨le_rfl, hab⟩, hr.2⟩, hS.2 fun _ h ↦ h.1.2⟩
    -- We use a.e. here because `f` may have a jump discontinuity at the interval endpoint `sSup S`
    have hc_eq : ∀ᵐ x ∂volume.restrict (Ι a b), (r ≤ f x ↔ x ≤ sSup S) := by
      filter_upwards [Measure.ae_ne _ _, ae_restrict_mem measurableSet_uIoc] with x hxne hxI
      have hxIcc := hsub hxI
      constructor <;> intro hx
      · exact hS.1 ⟨hxIcc, hx⟩
      · obtain ⟨y, hy, hxy⟩ := (lt_isLUB_iff hS).1 (lt_of_le_of_ne hx hxne)
        exact hy.2.trans (hf_mon hxIcc hy.1 hxy.le)
    simpa only [show H r = G (sSup S) from
      (intervalIntegral.integral_congr_ae_restrict <|
        indicator_ae_eq_of_ae_eq_set (hc_eq.mono fun _ ↦ propext)).trans
        (intervalIntegral.integral_indicator hc)] using ⟨hmin hc, hmax hc⟩
  -- Finally, integrate over `r`, divide by `f a` and apply the intermediate value theorem
  have hy_mem : (∫ x in a..b, f x * g x) / f a ∈ Icc (G ξmin) (G ξmax) := by
    rw [mem_Icc, le_div_iff₀ hfa, div_le_iff₀ hfa, hfub]
    constructor
    · simpa [mul_comm] using intervalIntegral.integral_mono_on hfa.le
        intervalIntegrable_const hH_int fun r hr ↦ (hH_bounds r hr).1
    · simpa [mul_comm] using intervalIntegral.integral_mono_on hfa.le hH_int
        intervalIntegrable_const fun r hr ↦ (hH_bounds r hr).2
  obtain ⟨ξ, hξ, hGξ⟩ := (isPreconnected_Icc.intermediate_value hξmin hξmax hGcont) hy_mem
  exact ⟨ξ, hξ, by grind⟩

/-- **Second mean value theorem for interval integrals** with a nonnegative monotone weight. -/
theorem exists_eq_const_mul_intervalIntegral_of_nonneg_of_monotoneOn
    (hab : a ≤ b) (hf : 0 ≤ f a) (hf_mon : MonotoneOn f (Icc a b))
    (hg : IntervalIntegrable g volume a b) : ∃ ξ ∈ Icc a b,
    ∫ x in a..b, f x * g x = f b * ∫ x in ξ..b, g x := by
  obtain ⟨ξ, hξ_mem, hξ⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
    (f := fun x ↦ f (-x)) (by simpa) (by simpa)
    (by intro x hx y hy hxy; apply hf_mon <;> grind)
    <| (IntervalIntegrable.iff_comp_neg).mp hg.symm
  refine ⟨-ξ, by grind, ?_⟩
  simpa using (intervalIntegral.integral_comp_neg (fun x ↦ f (-x) * g (-x))).trans hξ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {g : ℝ → E}

/-- An inequality version of the second mean value theorem for interval integrals
for Banach-space-valued functions. -/
theorem exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn
    (hab : a ≤ b) (hf : 0 ≤ f b) (hf_mon : AntitoneOn f (Icc a b))
    (hg : IntervalIntegrable g volume a b) : ∃ ξ ∈ Icc a b,
    ‖∫ x in a..b, f x • g x‖ ≤ f a * ‖∫ x in a..ξ, g x‖ := by
  -- Reduce to the scalar-valued theorem by applying a linear functional witnessing the norm
  have hfa := hf.trans (hf_mon.mapsTo_Icc ⟨le_rfl, hab⟩).1
  obtain ⟨L, hL_norm, hLI⟩ := exists_dual_vector'' ℝ (∫ x in a..b, f x • g x)
  obtain ⟨ξ, hξ, hξ_eq⟩ :=
    exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn hab hf hf_mon
      (g := fun x ↦ L (g x)) (intervalIntegrable_iff.2 <| L.integrable_comp hg.def')
  refine ⟨ξ, hξ, ?_⟩
  have hfg_interval : IntervalIntegrable (fun x ↦ f x • g x) volume a b :=
    intervalIntegrable_iff.2 <| hg.def'.smul_of_top_right <|
      (hf_mon.memLp_isCompact isCompact_Icc).mono_measure <|
        Measure.restrict_mono_set volume (uIcc_of_le hab ▸ uIoc_subset_uIcc)
  have hg_aξ := hg.mono_set <| uIcc_subset_uIcc_left (by rwa [uIcc_of_le hab])
  calc
    ‖∫ x in a..b, f x • g x‖ = L (∫ x in a..b, f x • g x) := hLI.symm
    _ = ∫ x in a..b, f x * L (g x) := by rw [← L.intervalIntegral_comp_comm hfg_interval]; simp
    _ = f a * ∫ x in a..ξ, L (g x) := hξ_eq
    _ = f a * L (∫ x in a..ξ, g x) := by rw [L.intervalIntegral_comp_comm hg_aξ]
    _ ≤ f a * ‖∫ x in a..ξ, g x‖ := mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans <| by simpa using
        (L.le_of_opNorm_le hL_norm (∫ x in a..ξ, g x))) hfa

/-- Monotone variant of `exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn` -/
theorem exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_monotoneOn
    (hab : a ≤ b) (hf : 0 ≤ f a) (hf_mon : MonotoneOn f (Icc a b))
    (hg : IntervalIntegrable g volume a b) : ∃ ξ ∈ Icc a b,
    ‖∫ x in a..b, f x • g x‖ ≤ f b * ‖∫ x in ξ..b, g x‖ := by
  obtain ⟨ξ, hξ_mem, hξ⟩ := exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn
    (f := fun x ↦ f (-x)) (g := fun x ↦ g (-x)) (by simpa) (by simpa)
    (by intro x hx y hy hxy; apply hf_mon <;> grind)
    <| (IntervalIntegrable.iff_comp_neg).mp hg.symm
  rw [← intervalIntegral.integral_comp_neg] at hξ
  exact ⟨-ξ, by grind, by simpa using hξ⟩


end Second
