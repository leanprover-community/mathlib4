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
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The one-dimensional Poincaré inequality

For `f : ℝ → E` valued in a normed space and `1 ≤ p`, the `Lᵖ` norm of `f` on a bounded interval is
controlled by the `Lᵖ` norm of its derivative, provided `f` is suitably centred. The most general
statement, `lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_mem_closure_convexHull`, holds on an
arbitrary convex set `s ⊆ ℝ`, needs only that `f` is differentiable on the interior of `s` and that
`0` lies in the closure of the convex hull of the image `f '' interior s`, and carries the sharp
constant `(volume s) ^ p / p`. A single inequality then covers every interval shape (`Icc`, `Ico`,
`Ioc`, `Ioo`, and the semi-infinite intervals), since these differ only on the null frontier.

All statements are phrased with lower Lebesgue integrals, so no integrability hypothesis on the
derivative is needed: if the right-hand side is infinite the inequality is automatic, and otherwise
the derivative is `Lᵖ` and the analytic argument goes through. Integrals over intervals are written
on `Ioc`, matching the convention of the interval integral.

## Proof outline

* `enorm_sub_le_lintegral_deriv_of_differentiableOn_Ioo` is the pointwise estimate coming from the
  fundamental theorem of calculus: `‖f x - f a‖ₑ ≤ ∫⁻ t in Ioc a x, ‖deriv f t‖ₑ`. It holds with no
  integrability hypothesis and only requires `f` to be differentiable on the open interval.
* `ENNReal.rpow_lintegral_le_measure_rpow_mul_lintegral_rpow` is the power-mean inequality against
  the constant function `1`: `(∫⁻ t in s, g t) ^ p ≤ μ s ^ (p - 1) * ∫⁻ t in s, g t ^ p`.
* Combining the two between an interior point `c` and a running point `x` gives a two-sided estimate
  `poincare_sub_const_Ioo` for `f - f c`, with the sharp constant `(b - a) ^ p / p` obtained by
  integrating `|x - c| ^ (p - 1)` over the two sides of `c`.
* `poincare_hull_fatou_aux` averages the per-point estimates against the weights of a convex-hull
  representation of `0` and passes to the closure by Fatou, yielding the general centred inequality.

## Main results

* `MeasureTheory.lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_mem_closure_convexHull`: the most
  general statement, on an arbitrary convex set `s ⊆ ℝ`, with the weakest centring
  `0 ∈ closure (convexHull ℝ (f '' interior s))` and the sharp constant `(volume s) ^ p / p`.
* `MeasureTheory.lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_left` /
  `..._of_zero_right`: `f` tends to `0` at the left, respectively right, endpoint; constant
  `(b - a) ^ p / p`.
* `MeasureTheory.lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_uIcc`: the unordered-interval
  variant, with constant `edist a b ^ p / p`.
* `MeasureTheory.lintegral_pow_le_mul_lintegral_pow_deriv_of_eq_zero`: `f` vanishes at *some*
  interior point of `(a, b)`; same constant `(b - a) ^ p / p`.
* `MeasureTheory.lintegral_pow_le_mul_lintegral_pow_deriv_of_integral_eq_zero`: vector-valued `f`
  with zero average, with constant `(b - a) ^ p / p`.
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
/-- For `f` differentiable on `(a, b)`, the map `t ↦ ‖deriv f t‖ₑ` is a.e. measurable there, with no
completeness or `BorelSpace` assumption on `E`: the derivative is measurable in the completion,
where its norm agrees with that of `deriv f`. Note that `measurable_deriv` and
`stronglyMeasurable_deriv` require a complete codomain, so they do not apply to a general `E`. -/
private theorem aemeasurable_enorm_deriv_of_differentiableOn_Ioo {E : Type*} [NormedAddCommGroup E]
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

/-- **Two-sided per-point Poincaré estimate on an open interval.** For `c ∈ (a, b)`, the shift
`f - f c` vanishes at `c`, and its `Lᵖ` norm on `(a, b)` is controlled with the sharp constant
`(b - a) ^ p / p`, requiring only differentiability on `(a, b)`. The pointwise fundamental theorem
of calculus bounds `‖f x - f c‖` by the derivative integral between `c` and `x`; the power-mean
inequality turns this into the `Lᵖ` estimate, and integrating `|x - c| ^ (p - 1)` over the two
sides of `c` yields the constant. -/
private theorem poincare_sub_const_Ioo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b p : ℝ} (hp : 1 ≤ p) {f : ℝ → E} (hdiff : DifferentiableOn ℝ f (Ioo a b))
    {c : ℝ} (hc : c ∈ Ioo a b) :
    ∫⁻ x in Ioo a b, ‖f x - f c‖ₑ ^ p
      ≤ ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Ioo a b, ‖deriv f x‖ₑ ^ p := by
  obtain ⟨hac, hcb⟩ := hc
  have hp0 : (0 : ℝ) < p := one_pos.trans_le hp
  set M : ℝ≥0∞ := ∫⁻ x in Ioo a b, ‖deriv f x‖ₑ ^ p with hMdef
  -- Values of the one-sided model integrals `∫ (x - u) ^ (p - 1)` and `∫ (v - x) ^ (p - 1)`.
  have half : ∀ u v : ℝ, u ≤ v →
      ∫⁻ x in Ioc u v, ENNReal.ofReal ((x - u) ^ (p - 1)) = ENNReal.ofReal ((v - u) ^ p / p) := by
    intro u v huv
    have hcont : ContinuousOn (fun x : ℝ => (x - u) ^ (p - 1)) (Icc u v) :=
      (continuousOn_id.sub continuousOn_const).rpow_const fun x _ => Or.inr (by linarith)
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc u v)] fun x : ℝ => (x - u) ^ (p - 1) := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact .of_forall fun x hx => Real.rpow_nonneg (by linarith [hx.1]) _
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hcont.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self) hnn]
    congr 1
    rw [← intervalIntegral.integral_of_le huv,
      intervalIntegral.integral_comp_sub_right (fun y => y ^ (p - 1)) u]
    simp only [sub_self]
    rw [integral_rpow (Or.inl (by linarith)), show p - 1 + 1 = p by ring,
      Real.zero_rpow hp0.ne', sub_zero]
  have halfL : ∀ u v : ℝ, u ≤ v →
      ∫⁻ x in Ioc u v, ENNReal.ofReal ((v - x) ^ (p - 1)) = ENNReal.ofReal ((v - u) ^ p / p) := by
    intro u v huv
    have hcont : ContinuousOn (fun x : ℝ => (v - x) ^ (p - 1)) (Icc u v) :=
      (continuousOn_const.sub continuousOn_id).rpow_const fun x _ => Or.inr (by linarith)
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc u v)] fun x : ℝ => (v - x) ^ (p - 1) := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact .of_forall fun x hx => Real.rpow_nonneg (by linarith [hx.2]) _
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hcont.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self) hnn]
    congr 1
    rw [← intervalIntegral.integral_of_le huv,
      intervalIntegral.integral_comp_sub_left (fun y => y ^ (p - 1)) v]
    simp only [sub_self]
    rw [integral_rpow (Or.inl (by linarith)), show p - 1 + 1 = p by ring,
      Real.zero_rpow hp0.ne', sub_zero]
  -- Pointwise estimate from the fundamental theorem of calculus between `c` and `x`.
  have pointwise : ∀ x ∈ Ioo a b,
      ‖f x - f c‖ₑ ^ p ≤ ENNReal.ofReal (|x - c| ^ (p - 1)) * M := by
    intro x hx
    obtain ⟨hax, hxb⟩ := hx
    have hlmem : min c x ∈ Ioo a b := ⟨lt_min hac hax, (min_le_left c x).trans_lt hcb⟩
    have hrmem : max c x ∈ Ioo a b := ⟨hac.trans_le (le_max_left c x), max_lt hcb hxb⟩
    have hIcc : Icc (min c x) (max c x) ⊆ Ioo a b := ordConnected_Ioo.out hlmem hrmem
    have hlr : min c x ≤ max c x := min_le_max
    have hftc : ‖f (max c x) - f (min c x)‖ₑ ≤ ∫⁻ t in Ioc (min c x) (max c x), ‖deriv f t‖ₑ :=
      enorm_sub_le_lintegral_deriv_of_differentiableOn_Ioo (hdiff.mono hIcc).continuousOn
        (hdiff.mono (Ioo_subset_Icc_self.trans hIcc)) hlr
    have hnorm_eq : ‖f x - f c‖ₑ = ‖f (max c x) - f (min c x)‖ₑ := by
      rcases le_total c x with h | h
      · rw [max_eq_right h, min_eq_left h]
      · rw [max_eq_left h, min_eq_right h, ← enorm_neg, neg_sub]
    have hvol : volume (Ioc (min c x) (max c x)) ^ (p - 1)
        = ENNReal.ofReal (|x - c| ^ (p - 1)) := by
      rw [Real.volume_Ioc, max_sub_min_eq_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (x - c)) (show (0 : ℝ) ≤ p - 1 by linarith)]
    calc ‖f x - f c‖ₑ ^ p
        = ‖f (max c x) - f (min c x)‖ₑ ^ p := by rw [hnorm_eq]
      _ ≤ (∫⁻ t in Ioc (min c x) (max c x), ‖deriv f t‖ₑ) ^ p := ENNReal.rpow_le_rpow hftc hp0.le
      _ ≤ volume (Ioc (min c x) (max c x)) ^ (p - 1)
            * ∫⁻ t in Ioc (min c x) (max c x), ‖deriv f t‖ₑ ^ p :=
          ENNReal.rpow_lintegral_le_measure_rpow_mul_lintegral_rpow hp
            ((aemeasurable_enorm_deriv_of_differentiableOn_Ioo hdiff).mono_measure
              (Measure.restrict_mono (Ioc_subset_Icc_self.trans hIcc) le_rfl))
      _ = ENNReal.ofReal (|x - c| ^ (p - 1))
            * ∫⁻ t in Ioc (min c x) (max c x), ‖deriv f t‖ₑ ^ p := by rw [hvol]
      _ ≤ ENNReal.ofReal (|x - c| ^ (p - 1)) * M :=
          mul_le_mul' le_rfl (lintegral_mono_set (Ioc_subset_Icc_self.trans hIcc))
  -- The model integral of `|x - c| ^ (p - 1)` over `(a, b)` is bounded by the constant.
  have hbound : ∫⁻ x in Ioo a b, ENNReal.ofReal (|x - c| ^ (p - 1))
      ≤ ENNReal.ofReal ((b - a) ^ p / p) := by
    have hsub : Ioo a b ⊆ Ioc a c ∪ Ioc c b := by
      intro x hx
      obtain ⟨hax, hxb⟩ := hx
      rcases lt_or_ge c x with h | h
      · exact Or.inr ⟨h, hxb.le⟩
      · exact Or.inl ⟨hax, h⟩
    have hLcongr : ∫⁻ x in Ioc a c, ENNReal.ofReal (|x - c| ^ (p - 1))
        = ENNReal.ofReal ((c - a) ^ p / p) := by
      rw [lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioc).2 (.of_forall
        fun x hx => by rw [abs_of_nonpos (by linarith [hx.2] : x - c ≤ 0), neg_sub]))]
      exact halfL a c hac.le
    have hRcongr : ∫⁻ x in Ioc c b, ENNReal.ofReal (|x - c| ^ (p - 1))
        = ENNReal.ofReal ((b - c) ^ p / p) := by
      rw [lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioc).2 (.of_forall
        fun x hx => by rw [abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x - c)]))]
      exact half c b hcb.le
    calc ∫⁻ x in Ioo a b, ENNReal.ofReal (|x - c| ^ (p - 1))
        ≤ ∫⁻ x in Ioc a c ∪ Ioc c b, ENNReal.ofReal (|x - c| ^ (p - 1)) := lintegral_mono_set hsub
      _ ≤ (∫⁻ x in Ioc a c, ENNReal.ofReal (|x - c| ^ (p - 1)))
            + ∫⁻ x in Ioc c b, ENNReal.ofReal (|x - c| ^ (p - 1)) :=
          lintegral_union_le _ (Ioc a c) (Ioc c b)
      _ = ENNReal.ofReal ((c - a) ^ p / p) + ENNReal.ofReal ((b - c) ^ p / p) := by
          rw [hLcongr, hRcongr]
      _ ≤ ENNReal.ofReal ((b - a) ^ p / p) := by
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
  -- Integrate the pointwise estimate and pull out the constant `M`.
  have hmeasg : Measurable fun x : ℝ => ENNReal.ofReal (|x - c| ^ (p - 1)) := by fun_prop
  calc ∫⁻ x in Ioo a b, ‖f x - f c‖ₑ ^ p
      ≤ ∫⁻ x in Ioo a b, ENNReal.ofReal (|x - c| ^ (p - 1)) * M :=
        setLIntegral_mono_ae (hmeasg.mul_const M).aemeasurable (.of_forall pointwise)
    _ = (∫⁻ x in Ioo a b, ENNReal.ofReal (|x - c| ^ (p - 1))) * M := lintegral_mul_const M hmeasg
    _ ≤ ENNReal.ofReal ((b - a) ^ p / p) * M := mul_le_mul' hbound le_rfl

/-- A nonempty bounded open convex subset of `ℝ` is the open interval between its bounds. -/
private theorem open_convex_eq_Ioo {O : Set ℝ} (hO : IsOpen O) (hOc : Convex ℝ O)
    (hne : O.Nonempty) (hb : BddBelow O) (ha : BddAbove O) :
    O = Ioo (sInf O) (sSup O) := by
  refine Set.Subset.antisymm ?_
    (IsConnected.Ioo_csInf_csSup_subset ⟨hne, Convex.isPreconnected hOc⟩ hb ha)
  have hsub : O ⊆ interior (Icc (sInf O) (sSup O)) :=
    interior_maximal (subset_Icc_csInf_csSup hb ha) hO
  rwa [interior_Icc] at hsub

/-- **Per-point Poincaré estimate on an open convex set.** For an open convex `U ⊆ ℝ` and `c ∈ U`,
the shift `f - f c` is controlled with the constant `(volume U) ^ p / p`. When `U` is a bounded
interval this is `poincare_sub_const_Ioo`; when `U` is unbounded the constant is `⊤`, so the bound
is automatic unless the derivative integral vanishes, in which case `f` is almost everywhere equal
to `f c` on every bounded subinterval and hence on `U`. -/
private theorem poincare_sub_const_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ} (hp : 1 ≤ p) {f : ℝ → E} {U : Set ℝ} (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hdiff : DifferentiableOn ℝ f U) {c : ℝ} (hcU : c ∈ U) :
    ∫⁻ x in U, ‖f x - f c‖ₑ ^ p
      ≤ volume U ^ p / ENNReal.ofReal p * ∫⁻ x in U, ‖deriv f x‖ₑ ^ p := by
  have hp0 : (0 : ℝ) < p := one_pos.trans_le hp
  by_cases hbdd : BddBelow U ∧ BddAbove U
  · -- Bounded: `U` is an open interval and the interval estimate applies directly.
    obtain ⟨hbb, hba⟩ := hbdd
    set a := sInf U with hadef
    set b := sSup U with hbdef
    have hUeq : U = Ioo a b := open_convex_eq_Ioo hUo hUc ⟨c, hcU⟩ hbb hba
    have hcab : c ∈ Ioo a b := hUeq ▸ hcU
    have hpos : (0 : ℝ) ≤ b - a := by linarith [hcab.1, hcab.2]
    have hconstU : volume U ^ p / ENNReal.ofReal p = ENNReal.ofReal ((b - a) ^ p / p) := by
      rw [hUeq, Real.volume_Ioo, ENNReal.ofReal_rpow_of_nonneg hpos hp0.le,
        ← ENNReal.ofReal_div_of_pos hp0]
    rw [hconstU, hUeq]
    exact poincare_sub_const_Ioo hp (hUeq ▸ hdiff) hcab
  · -- Unbounded: the measure is infinite.
    have hUtop : volume U = ⊤ := by
      rw [not_and_or] at hbdd
      rcases hbdd with hnb | hna
      · have hIic : Iic c ⊆ U := fun z hz => by
          obtain ⟨y, hyU, hyz⟩ := not_bddBelow_iff.1 hnb z
          exact hUc.ordConnected.out hyU hcU ⟨hyz.le, hz⟩
        exact top_le_iff.1 (Real.volume_Iic ▸ measure_mono hIic)
      · have hIci : Ici c ⊆ U := fun z hz => by
          obtain ⟨y, hyU, hzy⟩ := not_bddAbove_iff.1 hna z
          exact hUc.ordConnected.out hcU hyU ⟨hz, hzy.le⟩
        exact top_le_iff.1 (Real.volume_Ici ▸ measure_mono hIci)
    by_cases hM : ∫⁻ x in U, ‖deriv f x‖ₑ ^ p = 0
    · -- The derivative integral vanishes, so `f = f c` a.e. on each bounded subinterval, then
      -- on `U`, which forces the left-hand integral to vanish too.
      have hLHS0 : ∫⁻ x in U, ‖f x - f c‖ₑ ^ p = 0 := by
        set J : ℕ → Set ℝ := fun n => Ioo (c - ((n : ℝ) + 1)) (c + ((n : ℝ) + 1)) ∩ U with hJdef
        have hJsub : ∀ n, J n ⊆ U := fun n => Set.inter_subset_right
        have hcpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
        have hcJ : ∀ n, c ∈ J n := fun n =>
          ⟨⟨by linarith [hcpos n], by linarith [hcpos n]⟩, hcU⟩
        have hJint : ∀ n, ∫⁻ x in J n, ‖f x - f c‖ₑ ^ p = 0 := by
          intro n
          have hJeq : J n = Ioo (sInf (J n)) (sSup (J n)) :=
            open_convex_eq_Ioo (isOpen_Ioo.inter hUo) ((convex_Ioo _ _).inter hUc) ⟨c, hcJ n⟩
              (bddBelow_Ioo.mono Set.inter_subset_left) (bddAbove_Ioo.mono Set.inter_subset_left)
          have hcJab : c ∈ Ioo (sInf (J n)) (sSup (J n)) := hJeq ▸ hcJ n
          have hkey := poincare_sub_const_Ioo hp (hJeq ▸ (hdiff.mono (hJsub n))) hcJab
          rw [← hJeq] at hkey
          have hMJ : ∫⁻ x in J n, ‖deriv f x‖ₑ ^ p = 0 :=
            le_antisymm (hM ▸ lintegral_mono_set (hJsub n)) zero_le
          rw [hMJ, mul_zero] at hkey
          exact le_antisymm hkey zero_le
        have hJmono : Monotone J := fun m n hmn => by
          have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
          simp only [hJdef]
          exact Set.inter_subset_inter (Ioo_subset_Ioo (by linarith) (by linarith)) subset_rfl
        have hUunion : U = ⋃ n, J n := by
          ext x
          simp only [hJdef, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Ioo]
          refine ⟨fun hxU => ?_, fun ⟨_, _, hxU⟩ => hxU⟩
          obtain ⟨n, hn⟩ := exists_nat_gt (|x - c|)
          have hlt : |x - c| < (n : ℝ) + 1 := by linarith
          rw [abs_lt] at hlt
          exact ⟨n, ⟨by linarith [hlt.1], by linarith [hlt.2]⟩, hxU⟩
        rw [hUunion, setLIntegral_iUnion_of_directed _ hJmono.directed_le]
        exact le_antisymm (iSup_le fun n => (hJint n).le) zero_le
      rw [hLHS0]; exact zero_le
    · -- The derivative integral is nonzero, so the right-hand side is `⊤`.
      rw [hUtop, ENNReal.top_rpow_of_pos hp0,
        ENNReal.div_eq_top.2 (Or.inr ⟨rfl, ENNReal.ofReal_ne_top⟩), ENNReal.top_mul hM]
      exact le_top

/-- **Convex-combination averaging core.** On a measurable set `D` on which `f` is continuous,
suppose every per-point shift `f - f c` (for `c ∈ D`) satisfies `∫⁻ x in D, ‖f x - f c‖ₑ ^ p ≤ K`.
If `0` lies in the closure of the convex hull of `f '' D`, then `∫⁻ x in D, ‖f x‖ₑ ^ p ≤ K`. This is
the part of the Poincaré argument that turns the per-point estimates into the centred one: a
convex-hull point is averaged against its weights via the power-mean inequality, and the closure is
reached by Fatou. The constant `K` is whatever the per-point bound provides, so this lemma keeps the
sharp constant intact. -/
private theorem poincare_hull_fatou_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ} (hp : 1 ≤ p) {f : ℝ → E} {D : Set ℝ} (hD : MeasurableSet D)
    (hcont : ContinuousOn f D) {K : ℝ≥0∞}
    (hperp : ∀ c ∈ D, ∫⁻ x in D, ‖f x - f c‖ₑ ^ p ≤ K)
    (hmem : 0 ∈ closure (convexHull ℝ (f '' D))) :
    ∫⁻ x in D, ‖f x‖ₑ ^ p ≤ K := by
  have hp0 : 0 < p := one_pos.trans_le hp
  have hmeasE : ∀ v : E, AEMeasurable (fun x => ‖f x - v‖ₑ) (volume.restrict D) :=
    fun v => (continuous_enorm.comp_aestronglyMeasurable
      ((hcont.sub continuousOn_const).aestronglyMeasurable hD)).aemeasurable
  have hmeasP : ∀ v : E, AEMeasurable (fun x => ‖f x - v‖ₑ ^ p) (volume.restrict D) :=
    fun v => ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hmeasE v)
  -- Estimate at a convex-hull point `v = ∑ wᵢ • z i`: average the per-point bounds.
  have hull : ∀ v ∈ convexHull ℝ (f '' D), ∫⁻ x in D, ‖f x - v‖ₑ ^ p ≤ K := by
    intro v hv
    rw [convexHull_eq, Set.mem_setOf_eq] at hv
    obtain ⟨ι, t, w, z, hw0, hw1, hz, hcm⟩ := hv
    have hsum1 : ∑ i ∈ t, ENNReal.ofReal (w i) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg hw0, hw1, ENNReal.ofReal_one]
    have hzbound : ∀ i ∈ t, ∫⁻ x in D, ‖f x - z i‖ₑ ^ p ≤ K := fun i hi => by
      obtain ⟨c, hc, hfc⟩ := hz i hi
      rw [← hfc]; exact hperp c hc
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
    calc ∫⁻ x in D, ‖f x - v‖ₑ ^ p
        ≤ ∫⁻ x in D, (∑ i ∈ t, ENNReal.ofReal (w i) * ‖f x - z i‖ₑ) ^ p :=
          setLIntegral_mono_ae
            (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
              (Finset.aemeasurable_fun_sum t fun i _ => (hmeasE (z i)).const_mul _))
            (.of_forall fun x _ => ENNReal.rpow_le_rpow (hptwise x) hp0.le)
      _ ≤ ∫⁻ x in D, ∑ i ∈ t, ENNReal.ofReal (w i) * ‖f x - z i‖ₑ ^ p :=
          setLIntegral_mono_ae
            (Finset.aemeasurable_fun_sum t fun i _ => (hmeasP (z i)).const_mul _)
            (.of_forall fun x _ => ENNReal.rpow_arith_mean_le_arith_mean_rpow t
              (fun i => ENNReal.ofReal (w i)) (fun i => ‖f x - z i‖ₑ) hsum1 hp)
      _ = ∑ i ∈ t, ENNReal.ofReal (w i) * ∫⁻ x in D, ‖f x - z i‖ₑ ^ p := by
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
  calc ∫⁻ x in D, ‖f x‖ₑ ^ p
      = ∫⁻ x in D, Filter.liminf (fun n => ‖f x - u n‖ₑ ^ p) Filter.atTop :=
        lintegral_congr hliminf
    _ ≤ Filter.liminf (fun n => ∫⁻ x in D, ‖f x - u n‖ₑ ^ p) Filter.atTop :=
        lintegral_liminf_le' fun n => hmeasP (u n)
    _ ≤ Filter.liminf (fun _ : ℕ => K) Filter.atTop :=
        Filter.liminf_le_liminf (.of_forall fun n => hull (u n) (humem n))
    _ = K := Filter.liminf_const K

/-- **Most general one-dimensional `Lᵖ` Poincaré inequality.** For an arbitrary convex set `s ⊆ ℝ`,
with `f` differentiable on its interior, it suffices that `0` lies in the closure of the convex hull
of the image `f '' interior s`. The constant is `(volume s) ^ p / p`, where `volume s` is the length
of `s`. A single statement covers every interval shape — `Icc`, `Ico`, `Ioc`, `Ioo`, and the
semi-infinite intervals — since these differ only on the null frontier. The centring condition is
the weakest possible: it is implied both by `f` vanishing somewhere on the interior and by `f`
having zero average, and it makes sense for an arbitrary normed space `E`. The constant is sharp,
matching the endpoint case: writing `0` as a convex combination `∑ wᵢ • f cᵢ` and averaging the
per-point estimates `‖f x - f cᵢ‖` against the weights `wᵢ` recovers the `1 / p` factor, so the
convex-hull hypothesis costs nothing in the constant. -/
theorem MeasureTheory.lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_mem_closure_convexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ} {s : Set ℝ} {f : ℝ → E}
    (hp : 1 ≤ p) (hs : Convex ℝ s) (hdiff : DifferentiableOn ℝ f (interior s))
    (hmem : 0 ∈ closure (convexHull ℝ (f '' interior s))) :
    ∫⁻ x in s, ‖f x‖ₑ ^ p
      ≤ volume s ^ p / ENNReal.ofReal p * ∫⁻ x in s, ‖deriv f x‖ₑ ^ p := by
  -- `s` differs from its open interior only on the null frontier, so reduce to the interior.
  have hsae : s =ᵐ[volume] interior s := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null ?_ (Convex.addHaar_frontier volume hs), ?_⟩
    · exact fun x hx => ⟨subset_closure hx.1, hx.2⟩
    · rw [sdiff_eq_empty.2 interior_subset]; exact measure_empty
  have hLHS : ∫⁻ x in s, ‖f x‖ₑ ^ p = ∫⁻ x in interior s, ‖f x‖ₑ ^ p := by
    rw [Measure.restrict_congr_set hsae]
  have hRHS : ∫⁻ x in s, ‖deriv f x‖ₑ ^ p = ∫⁻ x in interior s, ‖deriv f x‖ₑ ^ p := by
    rw [Measure.restrict_congr_set hsae]
  rw [hLHS, hRHS, measure_congr hsae]
  by_cases hUne : (interior s).Nonempty
  · exact poincare_hull_fatou_aux hp isOpen_interior.measurableSet hdiff.continuousOn
      (fun c hc => poincare_sub_const_open hp isOpen_interior (Convex.interior hs) hdiff hc) hmem
  · rw [Set.not_nonempty_iff_eq_empty] at hUne
    simp only [hUne, setLIntegral_empty]
    exact zero_le

/-- **One-dimensional `Lᵖ` Poincaré inequality with an interior zero.** It suffices that `f`
vanishes at *some* interior point `c ∈ (a, b)`, and the constant `(b - a) ^ p / p` is sharp. No
continuity hypothesis is needed. -/
theorem MeasureTheory.lintegral_pow_le_mul_lintegral_pow_deriv_of_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b p : ℝ} (hp : 1 ≤ p) {f : ℝ → E}
    (hdiff : DifferentiableOn ℝ f (Ioo a b)) {c : ℝ} (hc : c ∈ Ioo a b) (hfc : f c = 0) :
    ∫⁻ x in Ioc a b, ‖f x‖ₑ ^ p
      ≤ ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Ioc a b, ‖deriv f x‖ₑ ^ p := by
  have hp0 : (0 : ℝ) < p := one_pos.trans_le hp
  have hconst : volume (Ioc a b) ^ p / ENNReal.ofReal p = ENNReal.ofReal ((b - a) ^ p / p) := by
    rw [Real.volume_Ioc, ENNReal.ofReal_rpow_of_nonneg (by linarith [hc.1, hc.2]) hp0.le,
      ← ENNReal.ofReal_div_of_pos hp0]
  rw [← hconst]
  refine lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_mem_closure_convexHull hp
    (convex_Ioc a b) ?_ ?_
  · rwa [interior_Ioc]
  · rw [interior_Ioc]
    exact subset_closure (subset_convexHull ℝ _ (hfc ▸ mem_image_of_mem f hc))

/-- **One-dimensional `Lᵖ` Poincaré inequality, left endpoint.** For `1 ≤ p` and `f` differentiable
on `(a, b)` with `f` tending to `0` on the right of `a`, the `Lᵖ` norm of `f` is controlled by the
`Lᵖ` norm of its derivative, with the sharp constant `(b - a) ^ p / p`. Neither continuity at the
endpoints nor `a ≤ b` is required. -/
theorem MeasureTheory.lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_left {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b p : ℝ} (hp : 1 ≤ p) {f : ℝ → E}
    (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (ha : Filter.Tendsto f (nhdsWithin a (Ioo a b)) (nhds 0)) :
    ∫⁻ x in Ioc a b, ‖f x‖ₑ ^ p
      ≤ ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Ioc a b, ‖deriv f x‖ₑ ^ p := by
  rcases lt_or_ge a b with hab | hab
  · have hp0 : (0 : ℝ) < p := one_pos.trans_le hp
    have hconst : volume (Ioc a b) ^ p / ENNReal.ofReal p = ENNReal.ofReal ((b - a) ^ p / p) := by
      rw [Real.volume_Ioc, ENNReal.ofReal_rpow_of_nonneg (by linarith) hp0.le,
        ← ENNReal.ofReal_div_of_pos hp0]
    rw [← hconst]
    refine lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_mem_closure_convexHull hp
      (convex_Ioc a b) ?_ ?_
    · rwa [interior_Ioc]
    · rw [interior_Ioc]
      haveI : (nhdsWithin a (Ioo a b)).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_Ioo hab.ne]; exact left_mem_Icc.2 hab.le)
      exact closure_mono (subset_convexHull ℝ _)
        (mem_closure_of_tendsto ha (Filter.eventually_of_mem self_mem_nhdsWithin
          fun x hx => mem_image_of_mem f hx))
  · rw [Ioc_eq_empty (not_lt.2 hab), setLIntegral_empty]
    exact zero_le

/-- **One-dimensional `Lᵖ` Poincaré inequality, right endpoint.** As
`lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_left`, but with `f` tending to `0` on the left of
the right endpoint `b`. -/
theorem MeasureTheory.lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_right {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b p : ℝ} (hp : 1 ≤ p) {f : ℝ → E}
    (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hb : Filter.Tendsto f (nhdsWithin b (Ioo a b)) (nhds 0)) :
    ∫⁻ x in Ioc a b, ‖f x‖ₑ ^ p
      ≤ ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Ioc a b, ‖deriv f x‖ₑ ^ p := by
  rcases lt_or_ge a b with hab | hab
  · have hp0 : (0 : ℝ) < p := one_pos.trans_le hp
    have hconst : volume (Ioc a b) ^ p / ENNReal.ofReal p = ENNReal.ofReal ((b - a) ^ p / p) := by
      rw [Real.volume_Ioc, ENNReal.ofReal_rpow_of_nonneg (by linarith) hp0.le,
        ← ENNReal.ofReal_div_of_pos hp0]
    rw [← hconst]
    refine lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_mem_closure_convexHull hp
      (convex_Ioc a b) ?_ ?_
    · rwa [interior_Ioc]
    · rw [interior_Ioc]
      haveI : (nhdsWithin b (Ioo a b)).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.1
          (by rw [closure_Ioo hab.ne]; exact right_mem_Icc.2 hab.le)
      exact closure_mono (subset_convexHull ℝ _)
        (mem_closure_of_tendsto hb (Filter.eventually_of_mem self_mem_nhdsWithin
          fun x hx => mem_image_of_mem f hx))
  · rw [Ioc_eq_empty (not_lt.2 hab), setLIntegral_empty]
    exact zero_le

/-- **One-dimensional `Lᵖ` Poincaré inequality on an unordered interval.** For `1 ≤ p` and `f`
differentiable on the interior `(a ⊓ b, a ⊔ b)` with `f` tending to `0` at `a` from inside the
interval, the `Lᵖ` norm of `f` is controlled by the `Lᵖ` norm of its derivative, with constant
`edist a b ^ p / p`. -/
theorem MeasureTheory.lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_uIcc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b p : ℝ} (hp : 1 ≤ p) {f : ℝ → E}
    (hdiff : DifferentiableOn ℝ f (Ioo (a ⊓ b) (a ⊔ b)))
    (ha : Filter.Tendsto f (nhdsWithin a (Ioo (a ⊓ b) (a ⊔ b))) (nhds 0)) :
    ∫⁻ x in uIcc a b, ‖f x‖ₑ ^ p
      ≤ edist a b ^ p / ENNReal.ofReal p * ∫⁻ x in uIcc a b, ‖deriv f x‖ₑ ^ p := by
  have hp0 : (0 : ℝ) < p := one_pos.trans_le hp
  have hbridge : ∀ (u v : ℝ) (g : ℝ → E),
      ∫⁻ x in Icc u v, ‖g x‖ₑ ^ p = ∫⁻ x in Ioc u v, ‖g x‖ₑ ^ p := fun u v g => by
    rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume))]
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab, hbridge a b f, hbridge a b (deriv f)]
    rw [inf_eq_left.2 hab, sup_eq_right.2 hab] at hdiff ha
    have hedist : edist a b ^ p / ENNReal.ofReal p = ENNReal.ofReal ((b - a) ^ p / p) := by
      rw [ENNReal.ofReal_div_of_pos hp0,
        ← ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.2 hab) hp0.le,
        show edist a b = ENNReal.ofReal (b - a) by
          rw [edist_dist, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hab)]]
    rw [hedist]
    exact lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_left hp hdiff ha
  · rw [uIcc_of_ge hba, hbridge b a f, hbridge b a (deriv f)]
    rw [inf_eq_right.2 hba, sup_eq_left.2 hba] at hdiff ha
    have hedist : edist a b ^ p / ENNReal.ofReal p = ENNReal.ofReal ((a - b) ^ p / p) := by
      rw [ENNReal.ofReal_div_of_pos hp0,
        ← ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.2 hba) hp0.le,
        show edist a b = ENNReal.ofReal (a - b) by
          rw [edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hba)]]
    rw [hedist]
    exact lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_right hp hdiff ha

/-- **One-dimensional `Lᵖ` Poincaré inequality with zero average, vector-valued.** For a complete
normed space `E` and `f` whose integral over `[a, b]` vanishes, the inequality holds with the sharp
constant `(b - a) ^ p / p`. The average of `f` is `0` and lies in the closed convex hull of the
range, so this reduces to `lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_mem_closure_convexHull`.
-/
theorem MeasureTheory.lintegral_pow_le_mul_lintegral_pow_deriv_of_integral_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {a b p : ℝ} (hab : a ≤ b)
    (hp : 1 ≤ p) {f : ℝ → E} (hcont : ContinuousOn f (Icc a b))
    (hdiff : DifferentiableOn ℝ f (Ioo a b)) (hint : ∫ x in a..b, f x = 0) :
    ∫⁻ x in Ioc a b, ‖f x‖ₑ ^ p
      ≤ ENNReal.ofReal ((b - a) ^ p / p) * ∫⁻ x in Ioc a b, ‖deriv f x‖ₑ ^ p := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · rw [Ioc_self, setLIntegral_empty]
    exact zero_le
  · have hp0 : (0 : ℝ) < p := one_pos.trans_le hp
    have hconst : volume (Ioc a b) ^ p / ENNReal.ofReal p = ENNReal.ofReal ((b - a) ^ p / p) := by
      rw [Real.volume_Ioc, ENNReal.ofReal_rpow_of_nonneg (by linarith) hp0.le,
        ← ENNReal.ofReal_div_of_pos hp0]
    rw [← hconst]
    refine lintegral_pow_le_mul_lintegral_pow_deriv_of_zero_mem_closure_convexHull hp
      (convex_Ioc a b) ?_ ?_
    · rwa [interior_Ioc]
    · rw [interior_Ioc]
      have hintIoo : IntegrableOn f (Ioo a b) volume :=
        (hcont.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
      have havg : ⨍ x in Ioo a b, f x = 0 := by
        rw [setAverage_eq, setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume)),
          ← intervalIntegral.integral_of_le hab, hint, smul_zero]
      rw [← havg]
      refine Convex.set_average_mem_closure (convex_convexHull ℝ _) ?_
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) ?_ hintIoo
      · rw [Real.volume_Ioo]
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        linarith
      · exact (ae_restrict_iff' measurableSet_Ioo).mpr
          (.of_forall fun x hx => subset_convexHull ℝ _ (mem_image_of_mem f hx))
