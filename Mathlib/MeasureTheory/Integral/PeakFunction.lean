/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

#align_import measure_theory.integral.peak_function from "leanprover-community/mathlib"@"13b0d72fd8533ba459ac66e9a885e35ffabb32b2"

/-!
# Integrals against peak functions

A sequence of peak functions is a sequence of functions with average one concentrating around
a point `x₀`. Given such a sequence `φₙ`, then `∫ φₙ g` tends to `g x₀` in many situations, with
a whole zoo of possible assumptions on `φₙ` and `g`. This file is devoted to such results.

## Main results

* `tendsto_set_integral_peak_smul_of_integrableOn_of_continuousWithinAt`: If a sequence of peak
  functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
  `g` is integrable and continuous at `x₀`, then `∫ φᵢ • g` converges to `g x₀`.
* `tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`:
  If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
  then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
  concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀`
  if `g` is continuous on `s`.

Note that there are related results about convolution with respect to peak functions in the file
`Analysis.Convolution`, such as `convolution_tendsto_right` there.
-/

open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric

open scoped Topology ENNReal

/-- This lemma exists for finsets, but not for sets currently. porting note: move to
data.set.basic after the port. -/
theorem Set.disjoint_sdiff_inter {α : Type*} (s t : Set α) : Disjoint (s \ t) (s ∩ t) :=
  disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left
#align set.disjoint_sdiff_inter Set.disjoint_sdiff_inter

open Set

variable {α E ι : Type*} {hm : MeasurableSpace α} {μ : Measure α} [TopologicalSpace α]
  [BorelSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] {g : α → E} {l : Filter ι} {x₀ : α}
  {s : Set α} {φ : ι → α → ℝ}

/-- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
`g` is integrable and continuous at `x₀`, then `φᵢ • g` is eventually integrable. -/
theorem integrableOn_peak_smul_of_integrableOn_of_continuousWithinAt (hs : MeasurableSet s)
    (hlφ : ∀ u : Set α, IsOpen u → x₀ ∈ u → TendstoUniformlyOn φ 0 l (s \ u))
    (hiφ : ∀ᶠ i in l, ∫ x in s, φ i x ∂μ = 1) (hmg : IntegrableOn g s μ)
    (hcg : ContinuousWithinAt g s x₀) : ∀ᶠ i in l, IntegrableOn (fun x => φ i x • g x) s μ := by
  obtain ⟨u, u_open, x₀u, hu⟩ : ∃ u, IsOpen u ∧ x₀ ∈ u ∧ ∀ x ∈ u ∩ s, g x ∈ ball (g x₀) 1
  exact mem_nhdsWithin.1 (hcg (ball_mem_nhds _ zero_lt_one))
  filter_upwards [tendstoUniformlyOn_iff.1 (hlφ u u_open x₀u) 1 zero_lt_one, hiφ] with i hi h'i
  have A : IntegrableOn (fun x => φ i x • g x) (s \ u) μ := by
    refine' Integrable.smul_of_top_right (hmg.mono (diff_subset _ _) le_rfl) _
    apply
      memℒp_top_of_bound
        ((integrable_of_integral_eq_one h'i).aestronglyMeasurable.mono_set (diff_subset _ _)) 1
    filter_upwards [self_mem_ae_restrict (hs.diff u_open.measurableSet)] with x hx
    simpa only [Pi.zero_apply, dist_zero_left] using (hi x hx).le
  have B : IntegrableOn (fun x => φ i x • g x) (s ∩ u) μ := by
    apply Integrable.smul_of_top_left
    · exact IntegrableOn.mono_set (integrable_of_integral_eq_one h'i) (inter_subset_left _ _)
    · apply
        memℒp_top_of_bound (hmg.mono_set (inter_subset_left _ _)).aestronglyMeasurable (‖g x₀‖ + 1)
      filter_upwards [self_mem_ae_restrict (hs.inter u_open.measurableSet)] with x hx
      rw [inter_comm] at hx
      exact (norm_lt_of_mem_ball (hu x hx)).le
  convert A.union B
  simp only [diff_union_inter]
#align integrable_on_peak_smul_of_integrable_on_of_continuous_within_at integrableOn_peak_smul_of_integrableOn_of_continuousWithinAt

variable [CompleteSpace E]

/-- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
`g` is integrable and continuous at `x₀`, then `∫ φᵢ • g` converges to `x₀`. Auxiliary lemma
where one assumes additionally `g x₀ = 0`. -/
theorem tendsto_set_integral_peak_smul_of_integrableOn_of_continuousWithinAt_aux
    (hs : MeasurableSet s) (hnφ : ∀ᶠ i in l, ∀ x ∈ s, 0 ≤ φ i x)
    (hlφ : ∀ u : Set α, IsOpen u → x₀ ∈ u → TendstoUniformlyOn φ 0 l (s \ u))
    (hiφ : ∀ᶠ i in l, ∫ x in s, φ i x ∂μ = 1) (hmg : IntegrableOn g s μ) (h'g : g x₀ = 0)
    (hcg : ContinuousWithinAt g s x₀) :
    Tendsto (fun i : ι => ∫ x in s, φ i x • g x ∂μ) l (𝓝 0) := by
  refine' Metric.tendsto_nhds.2 fun ε εpos => _
  obtain ⟨δ, hδ, δpos⟩ : ∃ δ, (δ * ∫ x in s, ‖g x‖ ∂μ) + δ < ε ∧ 0 < δ := by
    have A :
      Tendsto (fun δ => (δ * ∫ x in s, ‖g x‖ ∂μ) + δ) (𝓝[>] 0)
        (𝓝 ((0 * ∫ x in s, ‖g x‖ ∂μ) + 0)) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact (tendsto_id.mul tendsto_const_nhds).add tendsto_id
    rw [zero_mul, zero_add] at A
    exact (((tendsto_order.1 A).2 ε εpos).and self_mem_nhdsWithin).exists
  suffices ∀ᶠ i in l, ‖∫ x in s, φ i x • g x ∂μ‖ ≤ (δ * ∫ x in s, ‖g x‖ ∂μ) + δ by
    filter_upwards [this] with i hi
    simp only [dist_zero_right]
    exact hi.trans_lt hδ
  obtain ⟨u, u_open, x₀u, hu⟩ : ∃ u, IsOpen u ∧ x₀ ∈ u ∧ ∀ x ∈ u ∩ s, g x ∈ ball (g x₀) δ
  exact mem_nhdsWithin.1 (hcg (ball_mem_nhds _ δpos))
  filter_upwards [tendstoUniformlyOn_iff.1 (hlφ u u_open x₀u) δ δpos, hiφ, hnφ,
    integrableOn_peak_smul_of_integrableOn_of_continuousWithinAt hs hlφ hiφ hmg hcg] with i hi h'i
    hφpos h''i
  have B : ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ ≤ δ :=
    calc
      ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ ≤ ∫ x in s ∩ u, ‖φ i x • g x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x in s ∩ u, ‖φ i x‖ * δ ∂μ := by
        refine' set_integral_mono_on _ _ (hs.inter u_open.measurableSet) fun x hx => _
        · exact IntegrableOn.mono_set h''i.norm (inter_subset_left _ _)
        · exact
            IntegrableOn.mono_set ((integrable_of_integral_eq_one h'i).norm.mul_const _)
              (inter_subset_left _ _)
        rw [norm_smul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [inter_comm, h'g] at hu
        exact (mem_ball_zero_iff.1 (hu x hx)).le
      _ ≤ ∫ x in s, ‖φ i x‖ * δ ∂μ := by
        apply set_integral_mono_set
        · exact (integrable_of_integral_eq_one h'i).norm.mul_const _
        · exact eventually_of_forall fun x => mul_nonneg (norm_nonneg _) δpos.le
        · apply eventually_of_forall; exact inter_subset_left s u
      _ = ∫ x in s, φ i x * δ ∂μ := by
        apply set_integral_congr hs fun x hx => ?_
        rw [Real.norm_of_nonneg (hφpos _ hx)]
      _ = δ := by rw [integral_mul_right, h'i, one_mul]
  have C : ‖∫ x in s \ u, φ i x • g x ∂μ‖ ≤ δ * ∫ x in s, ‖g x‖ ∂μ :=
    calc
      ‖∫ x in s \ u, φ i x • g x ∂μ‖ ≤ ∫ x in s \ u, ‖φ i x • g x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x in s \ u, δ * ‖g x‖ ∂μ := by
        refine' set_integral_mono_on _ _ (hs.diff u_open.measurableSet) fun x hx => _
        · exact IntegrableOn.mono_set h''i.norm (diff_subset _ _)
        · exact IntegrableOn.mono_set (hmg.norm.const_mul _) (diff_subset _ _)
        rw [norm_smul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [Pi.zero_apply, dist_zero_left] using (hi x hx).le
      _ ≤ δ * ∫ x in s, ‖g x‖ ∂μ := by
        rw [integral_mul_left]
        apply mul_le_mul_of_nonneg_left (set_integral_mono_set hmg.norm _ _) δpos.le
        · exact eventually_of_forall fun x => norm_nonneg _
        · apply eventually_of_forall; exact diff_subset s u
  calc
    ‖∫ x in s, φ i x • g x ∂μ‖ =
      ‖(∫ x in s \ u, φ i x • g x ∂μ) + ∫ x in s ∩ u, φ i x • g x ∂μ‖ := by
      conv_lhs => rw [← diff_union_inter s u]
      rw [integral_union (disjoint_sdiff_inter _ _) (hs.inter u_open.measurableSet)
          (h''i.mono_set (diff_subset _ _)) (h''i.mono_set (inter_subset_left _ _))]
    _ ≤ ‖∫ x in s \ u, φ i x • g x ∂μ‖ + ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ := (norm_add_le _ _)
    _ ≤ (δ * ∫ x in s, ‖g x‖ ∂μ) + δ := add_le_add C B
#align tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at_aux tendsto_set_integral_peak_smul_of_integrableOn_of_continuousWithinAt_aux

/- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
`g` is integrable and continuous at `x₀`, then `∫ φᵢ • g` converges to `x₀`. -/
theorem tendsto_set_integral_peak_smul_of_integrableOn_of_continuousWithinAt (hs : MeasurableSet s)
    (h's : μ s ≠ ∞) (hnφ : ∀ᶠ i in l, ∀ x ∈ s, 0 ≤ φ i x)
    (hlφ : ∀ u : Set α, IsOpen u → x₀ ∈ u → TendstoUniformlyOn φ 0 l (s \ u))
    (hiφ : (fun i => ∫ x in s, φ i x ∂μ) =ᶠ[l] 1) (hmg : IntegrableOn g s μ)
    (hcg : ContinuousWithinAt g s x₀) :
    Tendsto (fun i : ι => ∫ x in s, φ i x • g x ∂μ) l (𝓝 (g x₀)) := by
  let h := g - fun _ => g x₀
  have A :
    Tendsto (fun i : ι => (∫ x in s, φ i x • h x ∂μ) + (∫ x in s, φ i x ∂μ) • g x₀) l
      (𝓝 (0 + (1 : ℝ) • g x₀)) := by
    refine' Tendsto.add _ (Tendsto.smul (tendsto_const_nhds.congr' hiφ.symm) tendsto_const_nhds)
    apply tendsto_set_integral_peak_smul_of_integrableOn_of_continuousWithinAt_aux hs hnφ hlφ hiφ
    · apply Integrable.sub hmg
      apply integrableOn_const.2
      simp only [h's.lt_top, or_true_iff]
    · simp only [Pi.sub_apply, sub_self]
    · exact hcg.sub continuousWithinAt_const
  simp only [one_smul, zero_add] at A
  refine' Tendsto.congr' _ A
  filter_upwards [integrableOn_peak_smul_of_integrableOn_of_continuousWithinAt hs hlφ hiφ hmg hcg,
    hiφ] with i hi h'i
  simp only [Pi.sub_apply, smul_sub]
  rw [integral_sub hi, integral_smul_const, sub_add_cancel]
  exact Integrable.smul_const (integrable_of_integral_eq_one h'i) _
#align tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at tendsto_set_integral_peak_smul_of_integrableOn_of_continuousWithinAt

/-- If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀` if `g` is
integrable on `s` and continuous at `x₀`.

Version assuming that `μ` gives positive mass to all neighborhoods of `x₀` within `s`.
For a less precise but more usable version, see
`tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`.
 -/
theorem tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos
    [MetrizableSpace α] [IsLocallyFiniteMeasure μ] (hs : IsCompact s)
    (hμ : ∀ u, IsOpen u → x₀ ∈ u → 0 < μ (u ∩ s)) {c : α → ℝ} (hc : ContinuousOn c s)
    (h'c : ∀ y ∈ s, y ≠ x₀ → c y < c x₀) (hnc : ∀ x ∈ s, 0 ≤ c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ ∈ s)
    (hmg : IntegrableOn g s μ) (hcg : ContinuousWithinAt g s x₀) :
    Tendsto (fun n : ℕ => (∫ x in s, c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ)
      atTop (𝓝 (g x₀)) := by
  /- We apply the general result
    `tendsto_set_integral_peak_smul_of_integrableOn_of_continuousWithinAt` to the sequence of
    peak functions `φₙ = (c x) ^ n / ∫ (c x) ^ n`. The only nontrivial bit is to check that this
    sequence converges uniformly to zero on any set `s \ u` away from `x₀`. By compactness, the
    function `c` is bounded by `t < c x₀` there. Consider `t' ∈ (t, c x₀)`, and a neighborhood `v`
    of `x₀` where `c x ≥ t'`, by continuity. Then `∫ (c x) ^ n` is bounded below by `t' ^ n μ v`.
    It follows that, on `s \ u`, then `φₙ x ≤ t ^ n / (t' ^ n μ v)`,
    which tends (exponentially fast) to zero with `n`. -/
  let φ : ℕ → α → ℝ := fun n x => (∫ x in s, c x ^ n ∂μ)⁻¹ * c x ^ n
  have hnφ : ∀ n, ∀ x ∈ s, 0 ≤ φ n x := by
    intro n x hx
    apply mul_nonneg (inv_nonneg.2 _) (pow_nonneg (hnc x hx) _)
    exact set_integral_nonneg hs.measurableSet fun x hx => pow_nonneg (hnc x hx) _
  have I : ∀ n, IntegrableOn (fun x => c x ^ n) s μ := fun n =>
    ContinuousOn.integrableOn_compact hs (hc.pow n)
  have J : ∀ n, 0 ≤ᵐ[μ.restrict s] fun x : α => c x ^ n := by
    intro n
    filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
    exact pow_nonneg (hnc x hx) n
  have P : ∀ n, (0 : ℝ) < ∫ x in s, c x ^ n ∂μ := by
    intro n
    refine' (set_integral_pos_iff_support_of_nonneg_ae (J n) (I n)).2 _
    obtain ⟨u, u_open, x₀_u, hu⟩ : ∃ u : Set α, IsOpen u ∧ x₀ ∈ u ∧ u ∩ s ⊆ c ⁻¹' Ioi 0 :=
      _root_.continuousOn_iff.1 hc x₀ h₀ (Ioi (0 : ℝ)) isOpen_Ioi hnc₀
    apply (hμ u u_open x₀_u).trans_le
    exact measure_mono fun x hx => ⟨ne_of_gt (pow_pos (a := c x) (hu hx) _), hx.2⟩
  have hiφ : ∀ n, ∫ x in s, φ n x ∂μ = 1 := fun n => by
    rw [integral_mul_left, inv_mul_cancel (P n).ne']
  have A : ∀ u : Set α, IsOpen u → x₀ ∈ u → TendstoUniformlyOn φ 0 atTop (s \ u) := by
    intro u u_open x₀u
    obtain ⟨t, t_pos, tx₀, ht⟩ : ∃ t, 0 ≤ t ∧ t < c x₀ ∧ ∀ x ∈ s \ u, c x ≤ t := by
      rcases eq_empty_or_nonempty (s \ u) with (h | h)
      · exact
          ⟨0, le_rfl, hnc₀, by simp only [h, mem_empty_iff_false, IsEmpty.forall_iff, imp_true_iff]⟩
      obtain ⟨x, hx, h'x⟩ : ∃ x ∈ s \ u, ∀ y ∈ s \ u, c y ≤ c x :=
        IsCompact.exists_isMaxOn (hs.diff u_open) h (hc.mono (diff_subset _ _))
      refine' ⟨c x, hnc x hx.1, h'c x hx.1 _, h'x⟩
      rintro rfl
      exact hx.2 x₀u
    obtain ⟨t', tt', t'x₀⟩ : ∃ t', t < t' ∧ t' < c x₀ := exists_between tx₀
    have t'_pos : 0 < t' := t_pos.trans_lt tt'
    obtain ⟨v, v_open, x₀_v, hv⟩ : ∃ v : Set α, IsOpen v ∧ x₀ ∈ v ∧ v ∩ s ⊆ c ⁻¹' Ioi t' :=
      _root_.continuousOn_iff.1 hc x₀ h₀ (Ioi t') isOpen_Ioi t'x₀
    have M : ∀ n, ∀ x ∈ s \ u, φ n x ≤ (μ (v ∩ s)).toReal⁻¹ * (t / t') ^ n := by
      intro n x hx
      have B : t' ^ n * (μ (v ∩ s)).toReal ≤ ∫ y in s, c y ^ n ∂μ :=
        calc
          t' ^ n * (μ (v ∩ s)).toReal = ∫ _ in v ∩ s, t' ^ n ∂μ := by
            simp only [integral_const, Measure.restrict_apply, MeasurableSet.univ, univ_inter,
              Algebra.id.smul_eq_mul, mul_comm]
          _ ≤ ∫ y in v ∩ s, c y ^ n ∂μ := by
            apply set_integral_mono_on _ _ (v_open.measurableSet.inter hs.measurableSet) _
            · apply integrableOn_const.2 (Or.inr _)
              exact lt_of_le_of_lt (measure_mono (inter_subset_right _ _)) hs.measure_lt_top
            · exact (I n).mono (inter_subset_right _ _) le_rfl
            · intro x hx
              exact pow_le_pow_of_le_left t'_pos.le (le_of_lt (hv hx)) _
          _ ≤ ∫ y in s, c y ^ n ∂μ :=
            set_integral_mono_set (I n) (J n) (eventually_of_forall (inter_subset_right _ _))
      simp_rw [← div_eq_inv_mul, div_pow, div_div]
      apply div_le_div (pow_nonneg t_pos n) _ _ B
      · exact pow_le_pow_of_le_left (hnc _ hx.1) (ht x hx) _
      · apply mul_pos (pow_pos (t_pos.trans_lt tt') _) (ENNReal.toReal_pos (hμ v v_open x₀_v).ne' _)
        have : μ (v ∩ s) ≤ μ s := measure_mono (inter_subset_right _ _)
        exact ne_of_lt (lt_of_le_of_lt this hs.measure_lt_top)
    have N :
      Tendsto (fun n => (μ (v ∩ s)).toReal⁻¹ * (t / t') ^ n) atTop
        (𝓝 ((μ (v ∩ s)).toReal⁻¹ * 0)) := by
      apply Tendsto.mul tendsto_const_nhds _
      apply tendsto_pow_atTop_nhds_0_of_lt_1 (div_nonneg t_pos t'_pos.le)
      exact (div_lt_one t'_pos).2 tt'
    rw [mul_zero] at N
    refine' tendstoUniformlyOn_iff.2 fun ε εpos => _
    filter_upwards [(tendsto_order.1 N).2 ε εpos] with n hn x hx
    simp only [Pi.zero_apply, dist_zero_left, Real.norm_of_nonneg (hnφ n x hx.1)]
    exact (M n x hx).trans_lt hn
  have : Tendsto (fun i : ℕ => ∫ x : α in s, φ i x • g x ∂μ) atTop (𝓝 (g x₀)) :=
    tendsto_set_integral_peak_smul_of_integrableOn_of_continuousWithinAt hs.measurableSet
      hs.measure_lt_top.ne (eventually_of_forall hnφ) A (eventually_of_forall hiφ) hmg hcg
  convert this
  simp_rw [← smul_smul, integral_smul]
#align tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_measure_nhds_within_pos tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos

/-- If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀` if `g` is
integrable on `s` and continuous at `x₀`.

Version assuming that `μ` gives positive mass to all open sets.
For a less precise but more usable version, see
`tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`.
-/
theorem tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn
    [MetrizableSpace α] [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure μ] (hs : IsCompact s)
    {c : α → ℝ} (hc : ContinuousOn c s) (h'c : ∀ y ∈ s, y ≠ x₀ → c y < c x₀)
    (hnc : ∀ x ∈ s, 0 ≤ c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ ∈ closure (interior s))
    (hmg : IntegrableOn g s μ) (hcg : ContinuousWithinAt g s x₀) :
    Tendsto (fun n : ℕ => (∫ x in s, c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ) atTop
      (𝓝 (g x₀)) := by
  have : x₀ ∈ s := by rw [← hs.isClosed.closure_eq]; exact closure_mono interior_subset h₀
  apply
    tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos hs _ hc
      h'c hnc hnc₀ this hmg hcg
  intro u u_open x₀_u
  calc
    0 < μ (u ∩ interior s) :=
      (u_open.inter isOpen_interior).measure_pos μ (_root_.mem_closure_iff.1 h₀ u u_open x₀_u)
    _ ≤ μ (u ∩ s) := measure_mono (inter_subset_inter_right _ interior_subset)
#align tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_integrable_on tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn

/-- If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀` if `g` is
continuous on `s`. -/
theorem tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    [MetrizableSpace α] [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure μ] (hs : IsCompact s)
    {c : α → ℝ} (hc : ContinuousOn c s) (h'c : ∀ y ∈ s, y ≠ x₀ → c y < c x₀)
    (hnc : ∀ x ∈ s, 0 ≤ c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ ∈ closure (interior s))
    (hmg : ContinuousOn g s) :
    Tendsto (fun n : ℕ => (∫ x in s, c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ) atTop (𝓝 (g x₀)) :=
  haveI : x₀ ∈ s := by rw [← hs.isClosed.closure_eq]; exact closure_mono interior_subset h₀
  tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn hs hc h'c hnc hnc₀ h₀
    (hmg.integrableOn_compact hs) (hmg x₀ this)
#align tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_continuous_on tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
