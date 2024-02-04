/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Bounding of integrals by asymptotics

We establish 0 < `integral f` < `∞` using `f = O(g)` and `g = O(f)`.

## Main results

* `integrable_Ioi_of_isBigO_integrable_Ioi`: If `f` is continuous on `[a, ∞)`, for some `a ∈ ℝ`,
  `g` is integrable on `(b, ∞)` for some `b ∈ ℝ`, and `f(x) = O(g(x))`, then
  `f` is integrable on `(a, ∞)`.
* `integrable_of_isBigO_integrable`: If `f` is continuous, `‖f(x)‖ = ‖f(-x)‖`,
  `g` is integrable on `(b, ∞)` for some `b ∈ ℝ`, and `f(x) = O(g(x))`, then
  `f` is integrable.
* `integral_pos_of_isBigO_integral_pos`: If `f` is continuous and integrable on `[a, ∞)`,
  `g(x) = O(f(x))`, and `∫ x in Ioi b, g x > 0` as `b` → `atTop`,
   then `∫ x in Ioi b, f x > 0` for all `b ≥ a`.
-/

noncomputable section

open MeasureTheory Set Filter

variable {E : Type*} [NormedDivisionRing E] [NormedSpace ℝ E] [Nontrivial E] {f g : ℝ → E} {a b : ℝ}
  {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

/-- If `f` is continuous on `[a, ∞)`, for some `a ∈ ℝ`,
`g` is integrable on `(b, ∞)` for some `b ∈ ℝ`, and `f(x) = O(g(x))`, then
`f` is integrable on `(a, ∞)`. -/
theorem integrable_Ioi_of_isBigO_integrable_Ioi (hf : ContinuousOn f (Ici a))
    (hg : IntegrableOn g (Ioi b) μ) (ho : f =O[atTop] g) : IntegrableOn f (Ioi a) μ := by
  obtain ⟨C, hC⟩ := ho.isBigOWith
  obtain ⟨C', hC'⟩ := exists_norm_eq E <| le_max_right C 0
  rewrite [Asymptotics.isBigOWith_iff, eventually_atTop] at hC
  obtain ⟨x', hx'⟩ := hC
  let x := max a (max b x')
  obtain ⟨h_ax, h_bx, h_x'x⟩ := show a ≤ x ∧ b ≤ x ∧ x' ≤ x by simp
  rewrite [← Ioc_union_Ioi_eq_Ioi h_ax]
  refine integrableOn_union.mpr ⟨?_, ?_, ?_⟩
  -- show integrable on `(a, x]` from continuity
  · exact intervalIntegrable_iff_integrableOn_Ioc_of_le h_ax
      |>.mp <| (hf.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc h_ax
  -- now show integrable on `(x, ∞)` from asymptotic
  · exact (hf.mono <| Ioi_subset_Ici <| h_ax).aestronglyMeasurable measurableSet_Ioi
  · refine hg.mono (Ioi_subset_Ioi h_bx) le_rfl |>.2.const_mul C' |>.mono
      <| (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x'' hx'' => ?_)
    apply hx' x'' (h_x'x.trans_lt hx'').le |>.trans
    rewrite [norm_mul, hC']
    gcongr
    apply le_max_left

/-- If `f` is continuous, `‖f(x)‖ = ‖f(-x)‖`, `g` is integrable on `(b, ∞)` for some `b ∈ ℝ`,
and `f(x) = O(g(x))`, then `f` is integrable. -/
theorem integrable_of_isBigO_integrable (hf : Continuous f) (hsymm : ∀ x, ‖f x‖ = ‖f (-x)‖)
   (hg : IntegrableOn g (Ioi b) μ) (ho : f =O[atTop] g) : Integrable f μ := by
  sorry

/-- If `f` is continuous and integrable on `[a, ∞)`, `g(x) = O(f(x))`,
and `∫ x in Ioi b, g x > 0` as `b` → `atTop`, then `∫ x in Ioi b, f x > 0` for all `b ≥ a`. -/
theorem integral_pos_of_isBigO_integral_pos [LT E] (hf : ContinuousOn f (Ici a))
    (hf_int : IntegrableOn f (Ioi a) μ) (hg : ∀ᶠ b in atTop, ∫ x in Ioi b, g x > 0) :
    ∀ b ≥ a, ∫ x in Ioi b, g x > 0 := by
  sorry
