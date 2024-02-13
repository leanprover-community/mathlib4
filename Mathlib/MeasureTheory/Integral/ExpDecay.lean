/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

#align_import measure_theory.integral.exp_decay from "leanprover-community/mathlib"@"d4817f8867c368d6c5571f7379b3888aaec1d95a"

/-!
# Integrals with exponential decay at ∞

As easy special cases of general theorems in the library, we prove the following test
for integrability:

* `integrable_of_isBigO_exp_neg`: If `f` is continuous on `[a,∞)`, for some `a ∈ ℝ`, and there
  exists `b > 0` such that `f(x) = O(exp(-b x))` as `x → ∞`, then `f` is integrable on `(a, ∞)`.
-/


noncomputable section

open Real intervalIntegral MeasureTheory Set Filter

open scoped Topology

/-- `exp (-b * x)` is integrable on `(a, ∞)`. -/
theorem exp_neg_integrableOn_Ioi (a : ℝ) {b : ℝ} (h : 0 < b) :
    IntegrableOn (fun x : ℝ => exp (-b * x)) (Ioi a) := by
  have : Tendsto (fun x => -exp (-b * x) / b) atTop (𝓝 (-0 / b)) := by
    refine' Tendsto.div_const (Tendsto.neg _) _
    exact tendsto_exp_atBot.comp (tendsto_id.neg_const_mul_atTop (Right.neg_neg_iff.2 h))
  refine' integrableOn_Ioi_deriv_of_nonneg' (fun x _ => _) (fun x _ => (exp_pos _).le) this
  simpa [h.ne'] using ((hasDerivAt_id x).const_mul b).neg.exp.neg.div_const b
#align exp_neg_integrable_on_Ioi exp_neg_integrableOn_Ioi

/-- If `f` is continuous on `[a, ∞)`, and is `O (exp (-b * x))` at `∞` for some `b > 0`, then
`f` is integrable on `(a, ∞)`. -/
theorem integrable_of_isBigO_exp_neg {f : ℝ → ℝ} {a b : ℝ} (h0 : 0 < b)
    (h1 : ContinuousOn f (Ici a)) (h2 : f =O[atTop] fun x => exp (-b * x)) :
    IntegrableOn f (Ioi a) := by
  cases' h2.isBigOWith with c h3
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at h3
  cases' h3 with r bdr
  let v := max a r
  -- show integrable on `(a, v]` from continuity
  have int_left : IntegrableOn f (Ioc a v) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (le_max_left a r)]
    have u : Icc a v ⊆ Ici a := Icc_subset_Ici_self
    exact (h1.mono u).intervalIntegrable_of_Icc (le_max_left a r)
  suffices IntegrableOn f (Ioi v) by
    have t := integrableOn_union.mpr ⟨int_left, this⟩
    simpa only [Ioc_union_Ioi_eq_Ioi, le_max_iff, le_refl, true_or_iff] using t
  -- now show integrable on `(v, ∞)` from asymptotic
  constructor
  · exact (h1.mono <| Ioi_subset_Ici <| le_max_left a r).aestronglyMeasurable measurableSet_Ioi
  have : HasFiniteIntegral (fun x : ℝ => c * exp (-b * x)) (volume.restrict (Ioi v)) :=
    (exp_neg_integrableOn_Ioi v h0).hasFiniteIntegral.const_mul c
  apply this.mono
  refine' (ae_restrict_iff' measurableSet_Ioi).mpr _
  refine' ae_of_all _ fun x h1x => _
  rw [norm_mul, norm_eq_abs]
  rw [mem_Ioi] at h1x
  specialize bdr x ((le_max_right a r).trans h1x.le)
  exact bdr.trans (mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _))
set_option linter.uppercaseLean3 false in
#align integrable_of_is_O_exp_neg integrable_of_isBigO_exp_neg
