/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The one-dimensional Poincaré inequality

For a function `f : ℝ → E` valued in a normed space that is continuous on a
compact interval `[a, b]`, continuously differentiable on the open interval
`(a, b)`, and vanishes at the left endpoint, the `Lᵖ` norm of `f` is controlled
by the `Lᵖ` norm of its derivative, for any `1 ≤ p`:
`∫⁻ x in Icc a b, ‖f x‖ₑ ^ p ≤`
`ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p`.

The statement is phrased with lower Lebesgue integrals, so that no integrability
hypothesis on the derivative is needed: if the right-hand side integral is
infinite the inequality is automatic, and otherwise the derivative is `Lᵖ` and
the analytic argument goes through.

## Proof outline

* `enorm_sub_le_lintegral_deriv_of_contDiffOn_Ioo` is the pointwise estimate
  coming from the fundamental theorem of calculus: `‖f x - f a‖ₑ ≤ ∫⁻ t in
  Ioc a x, ‖deriv f t‖ₑ`. It holds with no integrability hypothesis and only
  requires `f` to be `C¹` on the open interval.
* `ENNReal.rpow_lintegral_le_measure_rpow_mul_lintegral_rpow` is the power-mean
  inequality against the constant function `1`, in the form
  `(∫⁻ t in s, g t) ^ p ≤ μ s ^ (p - 1) * ∫⁻ t in s, g t ^ p`. It is obtained
  from the Hölder inequality `ENNReal.lintegral_mul_le_Lp_mul_Lq` with conjugate
  exponents `p` and `p / (p - 1)`.
* Combining the two gives the pointwise bound `‖f x‖ₑ ^ p ≤ ENNReal.ofReal
  ((x - a) ^ (p - 1)) * M` with `M = ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p`.
  Integrating over `[a, b]` and using `∫ x in a..b, (x - a) ^ (p - 1)
  = (b - a) ^ p / p` yields the constant.

## Main results

* `MeasureTheory.poincare_1d`: the one-dimensional `Lᵖ` Poincaré inequality.
* `MeasureTheory.poincare_1d_uIcc`: the same inequality over the unordered
  interval `[[a, b]]`, requiring only `f a = 0`.
-/

public section

open scoped ENNReal NNReal

open MeasureTheory Set

/-- **The one-dimensional `Lᵖ` Poincaré inequality.** For `1 ≤ p` and `f : ℝ → E`
continuous on `[a, b]`, continuously differentiable on `(a, b)`, and vanishing at
the left endpoint, the `Lᵖ` norm of `f` is controlled by the `Lᵖ` norm of its
derivative:
`∫⁻ x in Icc a b, ‖f x‖ₑ ^ p ≤`
`ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p`.

No integrability hypothesis on the derivative is required: the bound is phrased
with lower Lebesgue integrals, so it is automatic when the right-hand side is
infinite. -/
theorem MeasureTheory.poincare_1d {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b p : ℝ} (hab : a ≤ b) (hp : 1 ≤ p) {f : ℝ → E}
    (hcont : ContinuousOn f (Icc a b)) (hdiff : ContDiffOn ℝ 1 f (Ioo a b))
    (ha : f a = 0) :
    ∫⁻ x in Icc a b, ‖f x‖ₑ ^ p
      ≤ ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p := by
  have hp0 : 0 < p := one_pos.trans_le hp
  set M : ℝ≥0∞ := ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p
  have hderiv_cont : ContinuousOn (deriv f) (Ioo a b) :=
    (hdiff.continuousOn_derivWithin isOpen_Ioo.uniqueDiffOn le_rfl).congr
      fun x hx => (derivWithin_of_isOpen isOpen_Ioo hx).symm
  -- Pointwise bound: the FTC estimate followed by the power-mean inequality on `Ioc a x`.
  have pointwise : ∀ x ∈ Icc a b, ‖f x‖ₑ ^ p ≤ ENNReal.ofReal ((x - a) ^ (p - 1)) * M := by
    intro x ⟨hax, hxb⟩
    have hmeas : AEMeasurable (fun t => ‖deriv f t‖ₑ) (volume.restrict (Ioc a x)) := by
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
      exact ((hderiv_cont.mono (Ioo_subset_Ioo_right hxb)).aestronglyMeasurable
        measurableSet_Ioo).enorm
    calc ‖f x‖ₑ ^ p
        = ‖f x - f a‖ₑ ^ p := by rw [ha, sub_zero]
      _ ≤ (∫⁻ t in Ioc a x, ‖deriv f t‖ₑ) ^ p :=
          ENNReal.rpow_le_rpow (enorm_sub_le_lintegral_deriv_of_contDiffOn_Ioo
            (hcont.mono (Icc_subset_Icc_right hxb)) (hdiff.mono (Ioo_subset_Ioo_right hxb)) hax)
            hp0.le
      _ ≤ volume (Ioc a x) ^ (p - 1) * ∫⁻ t in Ioc a x, ‖deriv f t‖ₑ ^ p :=
          ENNReal.rpow_lintegral_le_measure_rpow_mul_lintegral_rpow hp hmeas
      _ = ENNReal.ofReal ((x - a) ^ (p - 1)) * ∫⁻ t in Ioc a x, ‖deriv f t‖ₑ ^ p := by
          rw [Real.volume_Ioc, ← ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith)]
      _ ≤ ENNReal.ofReal ((x - a) ^ (p - 1)) * M := by
          gcongr
          exact lintegral_mono_set ((Ioc_subset_Ioc_right hxb).trans Ioc_subset_Icc_self)
  -- The remaining integral evaluates to `(b - a) ^ p / p`.
  have hxa : ∫⁻ x in Icc a b, ENNReal.ofReal ((x - a) ^ (p - 1))
      = ENNReal.ofReal ((b - a) ^ p / p) := by
    have hcontxa : ContinuousOn (fun x : ℝ => (x - a) ^ (p - 1)) (Icc a b) :=
      (show ContinuousOn (fun x : ℝ => x - a) (Icc a b) by fun_prop).rpow_const
        fun x _ => Or.inr (by linarith)
    have hnn : 0 ≤ᵐ[volume.restrict (Icc a b)] fun x : ℝ => (x - a) ^ (p - 1) := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
      exact .of_forall fun x hx => Real.rpow_nonneg (by linarith [hx.1]) _
    rw [← ofReal_integral_eq_lintegral_ofReal (hcontxa.integrableOn_compact isCompact_Icc) hnn]
    congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_comp_sub_right (fun y => y ^ (p - 1)) a]
    simp only [sub_self]
    rw [integral_rpow (Or.inl (by linarith)), show p - 1 + 1 = p by ring,
      Real.zero_rpow hp0.ne', sub_zero]
  -- Integrate the pointwise estimate and pull out the constant `M`.
  have hmeasf : Measurable fun x : ℝ => ENNReal.ofReal ((x - a) ^ (p - 1)) := by fun_prop
  calc ∫⁻ x in Icc a b, ‖f x‖ₑ ^ p
      ≤ ∫⁻ x in Icc a b, ENNReal.ofReal ((x - a) ^ (p - 1)) * M :=
        setLIntegral_mono_ae (hmeasf.mul measurable_const).aemeasurable (.of_forall pointwise)
    _ = (∫⁻ x in Icc a b, ENNReal.ofReal ((x - a) ^ (p - 1))) * M := lintegral_mul_const M hmeasf
    _ = ENNReal.ofReal ((b - a) ^ p / p) * M := by rw [hxa]

/-- **The one-dimensional `Lᵖ` Poincaré inequality on an unordered interval.** For
`1 ≤ p` and `f : ℝ → E` continuous on `[[a, b]]`, continuously differentiable on
the interior `(a ⊓ b, a ⊔ b)`, and vanishing at `a`, the `Lᵖ` norm of `f` is
controlled by the `Lᵖ` norm of its derivative, with constant
`edist a b ^ p / ENNReal.ofReal p`. -/
theorem MeasureTheory.poincare_1d_uIcc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b p : ℝ} (hp : 1 ≤ p) {f : ℝ → E}
    (hcont : ContinuousOn f (uIcc a b)) (hdiff : ContDiffOn ℝ 1 f (Ioo (a ⊓ b) (a ⊔ b)))
    (ha : f a = 0) :
    ∫⁻ x in uIcc a b, ‖f x‖ₑ ^ p
      ≤ edist a b ^ p / ENNReal.ofReal p * ∫⁻ x in uIcc a b, ‖deriv f x‖ₑ ^ p := by
  have hp0 : 0 < p := one_pos.trans_le hp
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at hcont ⊢
    rw [inf_eq_left.2 hab, sup_eq_right.2 hab] at hdiff
    have hedist : edist a b ^ p / ENNReal.ofReal p = ENNReal.ofReal ((b - a) ^ p / p) := by
      rw [ENNReal.ofReal_div_of_pos hp0,
        ← ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.2 hab) hp0.le,
        show edist a b = ENNReal.ofReal (b - a) by
          rw [edist_dist, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hab)]]
    rw [hedist]
    exact poincare_1d hab hp hcont hdiff ha
  · -- Reflect through `x ↦ (a + b) - x`, which fixes `[b, a]` and sends the right
    -- endpoint `a` to the left endpoint `b`, reducing to `poincare_1d`.
    rw [uIcc_of_ge hba] at hcont ⊢
    rw [inf_eq_right.2 hba, sup_eq_left.2 hba] at hdiff
    set R : ℝ → ℝ := fun x => (a + b) - x with hR
    set g : ℝ → E := fun x => f (R x) with hg
    have hRmem : ∀ {x : ℝ}, R x ∈ Icc b a ↔ x ∈ Icc b a := by
      intro x; simp only [hR, mem_Icc]; constructor <;> intro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    have hRmapsIoo : MapsTo R (Ioo b a) (Ioo b a) := by
      intro x hx; simp only [hR, mem_Ioo] at hx ⊢; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hRcont : Continuous R := by fun_prop
    -- `g` inherits the Poincaré hypotheses on `[b, a]`, with `g b = f a = 0`.
    have hgcont : ContinuousOn g (Icc b a) :=
      hcont.comp hRcont.continuousOn fun x hx => hRmem.2 hx
    have hgdiff : ContDiffOn ℝ 1 g (Ioo b a) :=
      hdiff.comp ((contDiff_const.sub contDiff_id).contDiffOn) hRmapsIoo
    have hgb : g b = 0 := by simp only [hg, hR, add_sub_cancel_right, ha]
    -- `R` is a measure-preserving measurable embedding fixing `[b, a]` setwise.
    have hRmp : MeasurePreserving R volume volume := by
      have hneg : MeasurePreserving (fun x : ℝ => -1 * x) volume volume :=
        ⟨by fun_prop, by rw [Real.map_volume_mul_left (by norm_num)]; norm_num⟩
      have hadd : MeasurePreserving (fun x : ℝ => (a + b) + x) volume volume :=
        measurePreserving_add_left volume (a + b)
      simpa only [hR, Function.comp_def, neg_one_mul, ← sub_eq_add_neg] using hadd.comp hneg
    have hRemb : MeasurableEmbedding R := (Homeomorph.subLeft (a + b)).measurableEmbedding
    have hRpre : R ⁻¹' Icc b a = Icc b a := by ext x; exact hRmem
    have hRderiv : ∀ x, deriv g x = -deriv f (R x) := fun x => deriv_comp_const_sub f (a + b) x
    have hedist : edist a b ^ p / ENNReal.ofReal p = ENNReal.ofReal ((a - b) ^ p / p) := by
      rw [ENNReal.ofReal_div_of_pos hp0,
        ← ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.2 hba) hp0.le,
        show edist a b = ENNReal.ofReal (a - b) by
          rw [edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hba)]]
    -- Reflect both integrals back to `f` via the measure-preserving change of variables.
    have hlhs : ∫⁻ x in Icc b a, ‖g x‖ₑ ^ p = ∫⁻ x in Icc b a, ‖f x‖ₑ ^ p := by
      have := hRmp.setLIntegral_comp_preimage_emb hRemb (fun x => ‖f x‖ₑ ^ p) (Icc b a)
      rwa [hRpre] at this
    have hrhs : ∫⁻ x in Icc b a, ‖deriv g x‖ₑ ^ p = ∫⁻ x in Icc b a, ‖deriv f x‖ₑ ^ p := by
      have hcomp : ∫⁻ x in Icc b a, ‖deriv f (R x)‖ₑ ^ p = ∫⁻ x in Icc b a, ‖deriv f x‖ₑ ^ p := by
        have := hRmp.setLIntegral_comp_preimage_emb hRemb
          (fun x => ‖deriv f x‖ₑ ^ p) (Icc b a)
        rwa [hRpre] at this
      rw [← hcomp]
      refine lintegral_congr fun x => ?_
      rw [hRderiv, enorm_neg]
    rw [hedist, ← hlhs, ← hrhs]
    exact poincare_1d hba hp hgcont hgdiff hgb
