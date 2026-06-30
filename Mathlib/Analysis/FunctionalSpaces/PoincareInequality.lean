/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The one-dimensional Poincaré inequality

For a function `f : ℝ → E` valued in a normed space that is continuous on a
compact interval `[a, b]`, differentiable on the open interval
`(a, b)`, and vanishes at the left endpoint, the `Lᵖ` norm of `f` is controlled
by the `Lᵖ` norm of its derivative, for any `1 ≤ p`:
`∫⁻ x in Icc a b, ‖f x‖ₑ ^ p ≤`
`ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p`.

The statement is phrased with lower Lebesgue integrals, so that no integrability
hypothesis on the derivative is needed: if the right-hand side integral is
infinite the inequality is automatic, and otherwise the derivative is `Lᵖ` and
the analytic argument goes through.

## Proof outline

* `enorm_sub_le_lintegral_deriv_of_differentiableOn_Ioo` is the pointwise estimate
  coming from the fundamental theorem of calculus: `‖f x - f a‖ₑ ≤ ∫⁻ t in
  Ioc a x, ‖deriv f t‖ₑ`. It holds with no integrability hypothesis and only
  requires `f` to be differentiable on the open interval.
* `ENNReal.rpow_lintegral_le_measure_rpow_mul_lintegral_rpow` is the power-mean
  inequality against the constant function `1`, in the form
  `(∫⁻ t in s, g t) ^ p ≤ μ s ^ (p - 1) * ∫⁻ t in s, g t ^ p`. It is obtained
  from the Hölder inequality `ENNReal.lintegral_mul_le_Lp_mul_Lq` with conjugate
  exponents `p` and `p / (p - 1)`.
* Combining the two gives the pointwise bound `‖f x‖ₑ ^ p ≤ ENNReal.ofReal
  ((x - a) ^ (p - 1)) * M` with `M = ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p`.
  Integrating over `[a, b]` and using `∫ x in a..b, (x - a) ^ (p - 1)
  = (b - a) ^ p / p` yields the constant.

All results require only that `f` be differentiable (not `C¹`) on the open interval.

## Main results

* `MeasureTheory.poincare_1d`: the base inequality, with `f` vanishing at the left endpoint and
  constant `(b - a) ^ p / p`.
* `MeasureTheory.poincare_1d_right` / `MeasureTheory.poincare_1d_uIcc`: the right-endpoint and
  unordered-interval variants.
* `MeasureTheory.poincare_1d_of_exists_eq_zero`: `f` vanishes at *some* point of `[a, b]`; same
  constant `(b - a) ^ p / p`.
* `MeasureTheory.poincare_1d_of_zero_mem_closure_convexHull`: the most general centering, requiring
  only `0 ∈ closure (convexHull ℝ (f '' [a, b]))`, with the sharp constant `(b - a) ^ p / p`.
* `MeasureTheory.poincare_1d_of_integral_eq_zero`: vector-valued `f` with zero average, with
  constant `(b - a) ^ p / p`.
-/

public section

open scoped ENNReal NNReal

open MeasureTheory Set

/-- Auxiliary form of `enorm_sub_le_lintegral_deriv_of_differentiableOn_Ioo` for a complete
codomain, where the second fundamental theorem of calculus and the measurability of `deriv f`
are available. -/
private theorem enorm_sub_le_lintegral_deriv_diff_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} {f : ℝ → E}
    (hcont : ContinuousOn f (Icc a b)) (hdiff : DifferentiableOn ℝ f (Ioo a b)) (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ t in Ioc a b, ‖deriv f t‖ₑ := by
  by_cases hint : IntegrableOn (deriv f) (Ioc a b) volume
  · -- The fundamental theorem of calculus writes `f b - f a` as an integral.
    have hftc : f b - f a = ∫ t in a..b, deriv f t :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
        (fun t ht => (hdiff.differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hint)).symm
    rw [hftc, intervalIntegral.integral_of_le hab]
    exact enorm_integral_le_lintegral_enorm _
  · -- Otherwise `deriv f` has infinite enorm integral, so the right-hand side is `⊤`.
    rw [show ∫⁻ t in Ioc a b, ‖deriv f t‖ₑ = ⊤ by
      by_contra h
      exact hint ⟨aestronglyMeasurable_deriv f _,
        hasFiniteIntegral_iff_enorm.mpr (lt_top_iff_ne_top.2 h)⟩]
    exact le_top

open UniformSpace in
/-- **The second fundamental theorem of calculus, as an extended-norm bound, for merely
differentiable functions.** If `f : ℝ → E` is continuous on `[a, b]` and differentiable on the
open interval `(a, b)`, then `‖f b - f a‖ₑ ≤ ∫⁻ t in Ioc a b, ‖deriv f t‖ₑ`. Neither integrability
nor `C¹` is required: when the derivative is not integrable the right-hand side is `⊤`. This
weakens the `C¹` hypothesis of `enorm_sub_le_lintegral_deriv_of_contDiffOn_Ioo`. -/
theorem enorm_sub_le_lintegral_deriv_of_differentiableOn_Ioo {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}
    (hcont : ContinuousOn f (Icc a b)) (hdiff : DifferentiableOn ℝ f (Ioo a b)) (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ t in Ioc a b, ‖deriv f t‖ₑ := by
  -- Compose with the isometric inclusion into the completion, apply the complete-space lemma,
  -- then transfer back: the inclusion preserves norms and derivatives.
  set ι : E →ₗᵢ[ℝ] Completion E := Completion.toComplₗᵢ
  have key := enorm_sub_le_lintegral_deriv_diff_aux (ι.continuous.comp_continuousOn hcont)
    (ι.toContinuousLinearMap.differentiable.comp_differentiableOn hdiff) hab
  simp only [Function.comp_def, ← map_sub, ι.enorm_map] at key
  refine key.trans (le_of_eq (lintegral_congr_ae ?_))
  have hae : ∀ᵐ t ∂volume.restrict (Ioc a b), t ∈ Ioo a b := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hae] with t ht
  have hfx : DifferentiableAt ℝ f t := hdiff.differentiableAt (isOpen_Ioo.mem_nhds ht)
  have hg : HasDerivAt (fun y => ι (f y)) (ι (deriv f t)) t :=
    ι.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hfx.hasDerivAt
  rw [hg.deriv, ι.enorm_map]

open UniformSpace in
/-- For `f` differentiable on `(a, b)`, the map `t ↦ ‖deriv f t‖ₑ` is a.e. measurable there, with
no completeness or measurability assumption on `E`: the derivative is measurable in the completion,
where its norm agrees with that of `deriv f`. -/
theorem aemeasurable_enorm_deriv_of_differentiableOn_Ioo {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E} (hdiff : DifferentiableOn ℝ f (Ioo a b)) :
    AEMeasurable (fun t => ‖deriv f t‖ₑ) (volume.restrict (Ioo a b)) := by
  set ι : E →ₗᵢ[ℝ] Completion E := Completion.toComplₗᵢ
  refine ((aestronglyMeasurable_deriv (fun y => ι (f y))
    (volume.restrict (Ioo a b))).enorm).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hg : HasDerivAt (fun y => ι (f y)) (ι (deriv f t)) t :=
    ι.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      ((hdiff.differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt)
  rw [hg.deriv, ι.enorm_map]

/-- **The one-dimensional `Lᵖ` Poincaré inequality.** For `1 ≤ p` and `f : ℝ → E`
continuous on `[a, b]`, differentiable on `(a, b)`, and vanishing at
the left endpoint, the `Lᵖ` norm of `f` is controlled by the `Lᵖ` norm of its
derivative:
`∫⁻ x in Icc a b, ‖f x‖ₑ ^ p ≤`
`ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p`.

No integrability hypothesis on the derivative is required: the bound is phrased
with lower Lebesgue integrals, so it is automatic when the right-hand side is
infinite. -/
theorem MeasureTheory.poincare_1d {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b p : ℝ} (hab : a ≤ b) (hp : 1 ≤ p) {f : ℝ → E}
    (hcont : ContinuousOn f (Icc a b)) (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (ha : f a = 0) :
    ∫⁻ x in Icc a b, ‖f x‖ₑ ^ p
      ≤ ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p := by
  have hp0 : 0 < p := one_pos.trans_le hp
  set M : ℝ≥0∞ := ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p
  -- Pointwise bound: the FTC estimate followed by the power-mean inequality on `Ioc a x`.
  have pointwise : ∀ x ∈ Icc a b, ‖f x‖ₑ ^ p ≤ ENNReal.ofReal ((x - a) ^ (p - 1)) * M := by
    intro x ⟨hax, hxb⟩
    have hmeas : AEMeasurable (fun t => ‖deriv f t‖ₑ) (volume.restrict (Ioc a x)) := by
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
      exact aemeasurable_enorm_deriv_of_differentiableOn_Ioo
        (hdiff.mono (Ioo_subset_Ioo_right hxb))
    calc ‖f x‖ₑ ^ p
        = ‖f x - f a‖ₑ ^ p := by rw [ha, sub_zero]
      _ ≤ (∫⁻ t in Ioc a x, ‖deriv f t‖ₑ) ^ p :=
          ENNReal.rpow_le_rpow (enorm_sub_le_lintegral_deriv_of_differentiableOn_Ioo
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

/-- **Right-endpoint one-dimensional `Lᵖ` Poincaré inequality.** Same as
`poincare_1d`, but with `f` vanishing at the right endpoint `b` instead of the
left endpoint `a`. Obtained from `poincare_1d` by reflecting through
`x ↦ (a + b) - x`. -/
theorem MeasureTheory.poincare_1d_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b p : ℝ} (hab : a ≤ b) (hp : 1 ≤ p) {f : ℝ → E}
    (hcont : ContinuousOn f (Icc a b)) (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hb : f b = 0) :
    ∫⁻ x in Icc a b, ‖f x‖ₑ ^ p
      ≤ ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p := by
  set R : ℝ → ℝ := fun x => (a + b) - x with hR
  set g : ℝ → E := fun x => f (R x) with hg
  have hRmem : ∀ {x : ℝ}, R x ∈ Icc a b ↔ x ∈ Icc a b := by
    intro x; simp only [hR, mem_Icc]; constructor <;> intro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hRmapsIoo : MapsTo R (Ioo a b) (Ioo a b) := by
    intro x hx; simp only [hR, mem_Ioo] at hx ⊢; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hRcont : Continuous R := by fun_prop
  have hgcont : ContinuousOn g (Icc a b) :=
    hcont.comp hRcont.continuousOn fun x hx => hRmem.2 hx
  have hRdiff : Differentiable ℝ R := by simp only [hR]; fun_prop
  have hgdiff : DifferentiableOn ℝ g (Ioo a b) :=
    hdiff.comp hRdiff.differentiableOn hRmapsIoo
  have hga : g a = 0 := by simp only [hg, hR]; rw [show a + b - a = b by ring]; exact hb
  have hRmp : MeasurePreserving R volume volume := by
    have hneg : MeasurePreserving (fun x : ℝ => -1 * x) volume volume :=
      ⟨by fun_prop, by rw [Real.map_volume_mul_left (by norm_num)]; norm_num⟩
    have hadd : MeasurePreserving (fun x : ℝ => (a + b) + x) volume volume :=
      measurePreserving_add_left volume (a + b)
    simpa only [hR, Function.comp_def, neg_one_mul, ← sub_eq_add_neg] using hadd.comp hneg
  have hRemb : MeasurableEmbedding R := (Homeomorph.subLeft (a + b)).measurableEmbedding
  have hRpre : R ⁻¹' Icc a b = Icc a b := by ext x; exact hRmem
  have hRderiv : ∀ x, deriv g x = -deriv f (R x) := fun x => deriv_comp_const_sub f (a + b) x
  have hlhs : ∫⁻ x in Icc a b, ‖g x‖ₑ ^ p = ∫⁻ x in Icc a b, ‖f x‖ₑ ^ p := by
    have := hRmp.setLIntegral_comp_preimage_emb hRemb (fun x => ‖f x‖ₑ ^ p) (Icc a b)
    rwa [hRpre] at this
  have hrhs : ∫⁻ x in Icc a b, ‖deriv g x‖ₑ ^ p = ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p := by
    have hcomp : ∫⁻ x in Icc a b, ‖deriv f (R x)‖ₑ ^ p = ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p := by
      have := hRmp.setLIntegral_comp_preimage_emb hRemb (fun x => ‖deriv f x‖ₑ ^ p) (Icc a b)
      rwa [hRpre] at this
    rw [← hcomp]
    refine lintegral_congr fun x => ?_
    rw [hRderiv, enorm_neg]
  rw [← hlhs, ← hrhs]
  exact poincare_1d hab hp hgcont hgdiff hga

/-- **The one-dimensional `Lᵖ` Poincaré inequality on an unordered interval.** For
`1 ≤ p` and `f : ℝ → E` continuous on `[[a, b]]`, differentiable on
the interior `(a ⊓ b, a ⊔ b)`, and vanishing at `a`, the `Lᵖ` norm of `f` is
controlled by the `Lᵖ` norm of its derivative, with constant
`edist a b ^ p / ENNReal.ofReal p`. -/
theorem MeasureTheory.poincare_1d_uIcc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b p : ℝ} (hp : 1 ≤ p) {f : ℝ → E}
    (hcont : ContinuousOn f (uIcc a b)) (hdiff : DifferentiableOn ℝ f (Ioo (a ⊓ b) (a ⊔ b)))
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
  · -- `b ≤ a`: `a` is the right endpoint of `[b, a]`, so this is `poincare_1d_right`.
    rw [uIcc_of_ge hba] at hcont ⊢
    rw [inf_eq_right.2 hba, sup_eq_left.2 hba] at hdiff
    have hedist : edist a b ^ p / ENNReal.ofReal p = ENNReal.ofReal ((a - b) ^ p / p) := by
      rw [ENNReal.ofReal_div_of_pos hp0,
        ← ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.2 hba) hp0.le,
        show edist a b = ENNReal.ofReal (a - b) by
          rw [edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hba)]]
    rw [hedist]
    exact poincare_1d_right hba hp hcont hdiff ha

/-- **One-dimensional `Lᵖ` Poincaré inequality with an interior zero.** It suffices
that `f` vanishes at *some* point `c ∈ [a, b]`, not necessarily an endpoint, and the
constant `(b - a) ^ p / p` is unchanged. The two endpoint cases (`poincare_1d` and
`poincare_1d_right`) are the special cases `c = a` and `c = b`. -/
theorem MeasureTheory.poincare_1d_of_exists_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b p : ℝ} (hp : 1 ≤ p) {f : ℝ → E}
    (hcont : ContinuousOn f (Icc a b)) (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hzero : ∃ c ∈ Icc a b, f c = 0) :
    ∫⁻ x in Icc a b, ‖f x‖ₑ ^ p
      ≤ ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p := by
  have hp0 : 0 < p := one_pos.trans_le hp
  obtain ⟨c, ⟨hac, hcb⟩, hfc⟩ := hzero
  -- On `[a, c]` the point `c` is the right endpoint; on `[c, b]` it is the left
  -- endpoint. Bound each piece's derivative integral by the full one.
  have left_bound : ∫⁻ x in Icc a c, ‖f x‖ₑ ^ p
      ≤ ENNReal.ofReal ((c - a) ^ p / p) * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p := by
    refine (poincare_1d_right hac hp (hcont.mono (Icc_subset_Icc le_rfl hcb))
      (hdiff.mono (Ioo_subset_Ioo_right hcb)) hfc).trans ?_
    exact mul_le_mul_right (lintegral_mono_set (Icc_subset_Icc le_rfl hcb)) _
  have right_bound : ∫⁻ x in Icc c b, ‖f x‖ₑ ^ p
      ≤ ENNReal.ofReal ((b - c) ^ p / p) * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p := by
    refine (poincare_1d hcb hp (hcont.mono (Icc_subset_Icc hac le_rfl))
      (hdiff.mono (Ioo_subset_Ioo_left hac)) hfc).trans ?_
    exact mul_le_mul_right (lintegral_mono_set (Icc_subset_Icc hac le_rfl)) _
  calc ∫⁻ x in Icc a b, ‖f x‖ₑ ^ p
      = ∫⁻ x in Icc a c ∪ Icc c b, ‖f x‖ₑ ^ p := by rw [Icc_union_Icc_eq_Icc hac hcb]
    _ ≤ (∫⁻ x in Icc a c, ‖f x‖ₑ ^ p) + ∫⁻ x in Icc c b, ‖f x‖ₑ ^ p :=
        lintegral_union_le (μ := volume) (fun x => ‖f x‖ₑ ^ p) (Icc a c) (Icc c b)
    _ ≤ ENNReal.ofReal ((c - a) ^ p / p) * (∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p)
        + ENNReal.ofReal ((b - c) ^ p / p) * (∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p) :=
        add_le_add left_bound right_bound
    _ = (ENNReal.ofReal ((c - a) ^ p / p) + ENNReal.ofReal ((b - c) ^ p / p))
        * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p := by rw [add_mul]
    _ ≤ ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p := by
        gcongr
        rw [← ENNReal.ofReal_add (div_nonneg (Real.rpow_nonneg (by linarith) p) hp0.le)
          (div_nonneg (Real.rpow_nonneg (by linarith) p) hp0.le)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hsuper : (c - a) ^ p + (b - c) ^ p ≤ (b - a) ^ p := by
          calc (c - a) ^ p + (b - c) ^ p
              ≤ ((c - a) + (b - c)) ^ p :=
                Real.add_rpow_le_rpow_add (by linarith) (by linarith) hp
            _ = (b - a) ^ p := by rw [show c - a + (b - c) = b - a by ring]
        calc (c - a) ^ p / p + (b - c) ^ p / p
            = ((c - a) ^ p + (b - c) ^ p) / p := by ring
          _ ≤ (b - a) ^ p / p := div_le_div_of_nonneg_right hsuper hp0.le

/-- **Most general one-dimensional `Lᵖ` Poincaré inequality.** It suffices that `0` lies in the
closure of the convex hull of the image `f '' [a, b]`. This is the weakest possible centering
condition: it is implied both by `f` vanishing somewhere on `[a, b]` and by `f` having zero
average, and it makes sense for an arbitrary normed space `E`. The constant is the sharp
`(b - a) ^ p / p`, matching `poincare_1d_of_exists_eq_zero`: writing `0` as a convex combination
`∑ wᵢ • f cᵢ` and averaging the per-point estimates `‖f x - f cᵢ‖` against the weights `wᵢ`
recovers the `1 / p` factor, so the convex-hull hypothesis costs nothing in the constant. -/
theorem MeasureTheory.poincare_1d_of_zero_mem_closure_convexHull {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b p : ℝ} (hp : 1 ≤ p) {f : ℝ → E}
    (hcont : ContinuousOn f (Icc a b)) (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hmem : 0 ∈ closure (convexHull ℝ (f '' Icc a b))) :
    ∫⁻ x in Icc a b, ‖f x‖ₑ ^ p
      ≤ ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p := by
  have hp0 : 0 < p := one_pos.trans_le hp
  set M : ℝ≥0∞ := ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p with hMdef
  set K : ℝ≥0∞ := ENNReal.ofReal ((b - a) ^ p / p) * M with hKdef
  -- Measurability of `x ↦ ‖f x - v‖ₑ` and of its `p`-th power on `[a, b]`.
  have hmeasE : ∀ v : E, AEMeasurable (fun x => ‖f x - v‖ₑ) (volume.restrict (Icc a b)) :=
    fun v => (continuous_enorm.comp_aestronglyMeasurable
      ((hcont.sub continuousOn_const).aestronglyMeasurable measurableSet_Icc)).aemeasurable
  have hmeasP : ∀ v : E, AEMeasurable (fun x => ‖f x - v‖ₑ ^ p) (volume.restrict (Icc a b)) :=
    fun v => ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hmeasE v)
  -- Per-point estimate. Shifting `f` by the constant `f c` gives a function vanishing at `c`, so
  -- the attained-zero inequality applies and keeps the sharp constant `(b - a) ^ p / p`.
  have perpoint : ∀ c ∈ Icc a b, ∫⁻ x in Icc a b, ‖f x - f c‖ₑ ^ p ≤ K := by
    intro c hc
    refine (poincare_1d_of_exists_eq_zero hp
      (show ContinuousOn (fun y => f y - f c) (Icc a b) from hcont.sub continuousOn_const)
      (show DifferentiableOn ℝ (fun y => f y - f c) (Ioo a b) from
        hdiff.sub (differentiableOn_const (f c))) ⟨c, hc, by simp⟩).trans (le_of_eq ?_)
    rw [hKdef, hMdef]
    congr 1
    exact lintegral_congr fun x => by rw [deriv_sub_const]
  -- Estimate at a convex-hull point `v = ∑ wᵢ • z i`: average the per-point bounds.
  have hull : ∀ v ∈ convexHull ℝ (f '' Icc a b), ∫⁻ x in Icc a b, ‖f x - v‖ₑ ^ p ≤ K := by
    intro v hv
    rw [convexHull_eq, Set.mem_setOf_eq] at hv
    obtain ⟨ι, t, w, z, hw0, hw1, hz, hcm⟩ := hv
    have hsum1 : ∑ i ∈ t, ENNReal.ofReal (w i) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg hw0, hw1, ENNReal.ofReal_one]
    have hzbound : ∀ i ∈ t, ∫⁻ x in Icc a b, ‖f x - z i‖ₑ ^ p ≤ K := fun i hi => by
      obtain ⟨c, hc, hfc⟩ := hz i hi
      rw [← hfc]; exact perpoint c hc
    have hptwise : ∀ x, ‖f x - v‖ₑ ≤ ∑ i ∈ t, ENNReal.ofReal (w i) * ‖f x - z i‖ₑ := by
      intro x
      have hvx : f x - v = ∑ i ∈ t, w i • (f x - z i) := by
        rw [← hcm, Finset.centerMass_eq_of_sum_1 t z hw1]
        simp only [smul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul]
      calc ‖f x - v‖ₑ = ‖∑ i ∈ t, w i • (f x - z i)‖ₑ := by rw [hvx]
        _ ≤ ∑ i ∈ t, ‖w i • (f x - z i)‖ₑ := enorm_sum_le _ _
        _ = ∑ i ∈ t, ENNReal.ofReal (w i) * ‖f x - z i‖ₑ :=
            Finset.sum_congr rfl fun i hi => by rw [enorm_smul, Real.enorm_eq_ofReal (hw0 i hi)]
    calc ∫⁻ x in Icc a b, ‖f x - v‖ₑ ^ p
        ≤ ∫⁻ x in Icc a b, (∑ i ∈ t, ENNReal.ofReal (w i) * ‖f x - z i‖ₑ) ^ p :=
          setLIntegral_mono_ae
            (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
              (Finset.aemeasurable_fun_sum t fun i _ => (hmeasE (z i)).const_mul _))
            (.of_forall fun x _ => ENNReal.rpow_le_rpow (hptwise x) hp0.le)
      _ ≤ ∫⁻ x in Icc a b, ∑ i ∈ t, ENNReal.ofReal (w i) * ‖f x - z i‖ₑ ^ p :=
          setLIntegral_mono_ae
            (Finset.aemeasurable_fun_sum t fun i _ => (hmeasP (z i)).const_mul _)
            (.of_forall fun x _ => ENNReal.rpow_arith_mean_le_arith_mean_rpow t
              (fun i => ENNReal.ofReal (w i)) (fun i => ‖f x - z i‖ₑ) hsum1 hp)
      _ = ∑ i ∈ t, ENNReal.ofReal (w i) * ∫⁻ x in Icc a b, ‖f x - z i‖ₑ ^ p := by
          rw [lintegral_finsetSum' t fun i _ => (hmeasP (z i)).const_mul _]
          exact Finset.sum_congr rfl fun i _ => lintegral_const_mul'' _ (hmeasP (z i))
      _ ≤ ∑ i ∈ t, ENNReal.ofReal (w i) * K := by gcongr with i hi; exact hzbound i hi
      _ = K := by rw [← Finset.sum_mul, hsum1, one_mul]
  -- Pass from the convex hull to its closure by Fatou: `0` is a sequential limit of hull points.
  obtain ⟨u, humem, hulim⟩ := mem_closure_iff_seq_limit.mp hmem
  have hliminf : ∀ x, ‖f x‖ₑ ^ p
      = Filter.liminf (fun n => ‖f x - u n‖ₑ ^ p) Filter.atTop := fun x => by
    have htend : Filter.Tendsto (fun n => ‖f x - u n‖ₑ ^ p) Filter.atTop (nhds (‖f x‖ₑ ^ p)) := by
      have h1 : Filter.Tendsto (fun n => f x - u n) Filter.atTop (nhds (f x)) := by
        simpa using tendsto_const_nhds.sub hulim
      exact (ENNReal.continuous_rpow_const.tendsto _).comp ((continuous_enorm.tendsto _).comp h1)
    exact htend.liminf_eq.symm
  calc ∫⁻ x in Icc a b, ‖f x‖ₑ ^ p
      = ∫⁻ x in Icc a b, Filter.liminf (fun n => ‖f x - u n‖ₑ ^ p) Filter.atTop :=
        lintegral_congr hliminf
    _ ≤ Filter.liminf (fun n => ∫⁻ x in Icc a b, ‖f x - u n‖ₑ ^ p) Filter.atTop :=
        lintegral_liminf_le' fun n => hmeasP (u n)
    _ ≤ Filter.liminf (fun _ : ℕ => K) Filter.atTop :=
        Filter.liminf_le_liminf (.of_forall fun n => hull (u n) (humem n))
    _ = K := Filter.liminf_const K

/-- **One-dimensional `Lᵖ` Poincaré inequality with zero average, vector-valued.** For a complete
normed space `E` and `f` whose integral over `[a, b]` vanishes, the inequality holds with the sharp
constant `(b - a) ^ p / p`. The average of `f` is `0` and lies in the closed convex hull of the
range, so this reduces to `poincare_1d_of_zero_mem_closure_convexHull`. -/
theorem MeasureTheory.poincare_1d_of_integral_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b p : ℝ} (hab : a ≤ b) (hp : 1 ≤ p) {f : ℝ → E}
    (hcont : ContinuousOn f (Icc a b)) (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hint : ∫ x in a..b, f x = 0) :
    ∫⁻ x in Icc a b, ‖f x‖ₑ ^ p
      ≤ ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Icc a b, ‖deriv f x‖ₑ ^ p := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · rw [Icc_self, setLIntegral_measure_zero _ _ (measure_singleton a)]
    exact zero_le
  · refine poincare_1d_of_zero_mem_closure_convexHull hp hcont hdiff ?_
    have havg : ⨍ x in Icc a b, f x = 0 := by
      rw [setAverage_eq, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, hint,
        smul_zero]
    rw [← havg]
    refine Convex.set_average_mem_closure (convex_convexHull ℝ _) ?_
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) ?_
      (hcont.integrableOn_compact isCompact_Icc)
    · rw [Real.volume_Icc]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
    · exact (ae_restrict_iff' measurableSet_Icc).mpr
        (.of_forall fun x hx => subset_convexHull ℝ _ (mem_image_of_mem f hx))
