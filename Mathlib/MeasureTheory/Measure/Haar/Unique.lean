/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Convolution

/-!
# Uniqueness of Haar measure, again

-/

open MeasureTheory Filter Set TopologicalSpace
open scoped Uniformity Topology ENNReal

section

variable {X Y α : Type*} [Zero α]
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]


/-- A continuous function with compact support on a product space can be uniformly approximated by
simple functions. The subtlety is that we do not assume that the spaces are separable, so the
product of the Borel sigma algebras might not contain all open sets, but still it contains enough
of them to approximate compactly supported continuous functions. -/
lemma HasCompactSupport.exists_simpleFunc_approx_of_prod [PseudoMetricSpace α]
    {f : X × Y → α} (hf : Continuous f) (h'f : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : SimpleFunc (X × Y) α), ∀ x, dist (f x) (g x) < ε := by
  have M : ∀ (K : Set (X × Y)), IsCompact K →
      ∃ (g : SimpleFunc (X × Y) α), ∃ (s : Set (X × Y)), MeasurableSet s ∧ K ⊆ s ∧
      ∀ x ∈ s, dist (f x) (g x) < ε := by
    intro K hK
    apply IsCompact.induction_on
      (p := fun t ↦ ∃ (g : SimpleFunc (X × Y) α), ∃ (s : Set (X × Y)), MeasurableSet s ∧ t ⊆ s ∧
        ∀ x ∈ s, dist (f x) (g x) < ε) hK
    · exact ⟨0, ∅, by simp⟩
    · intro t t' htt' ⟨g, s, s_meas, ts, hg⟩
      exact ⟨g, s, s_meas, htt'.trans ts, hg⟩
    · intro t t' ⟨g, s, s_meas, ts, hg⟩ ⟨g', s', s'_meas, t's', hg'⟩
      refine ⟨g.piecewise s s_meas g', s ∪ s', s_meas.union s'_meas,
        union_subset_union ts t's', fun p hp ↦ ?_⟩
      by_cases H : p ∈ s
      · simpa [H, SimpleFunc.piecewise_apply] using hg p H
      · simp only [SimpleFunc.piecewise_apply, H, ite_false]
        apply hg'
        simpa [H] using (mem_union _ _ _).1 hp
    · rintro ⟨x, y⟩ -
      obtain ⟨u, v, hu, xu, hv, yv, huv⟩ : ∃ u v, IsOpen u ∧ x ∈ u ∧ IsOpen v ∧ y ∈ v ∧
        u ×ˢ v ⊆ {z | dist (f z) (f (x, y)) < ε} :=
          mem_nhds_prod_iff'.1 <| Metric.continuousAt_iff'.1 hf.continuousAt ε hε
      refine ⟨u ×ˢ v, nhdsWithin_le_nhds <| (hu.prod hv).mem_nhds (mk_mem_prod xu yv), ?_⟩
      exact ⟨SimpleFunc.const _ (f (x, y)), u ×ˢ v, hu.measurableSet.prod hv.measurableSet,
        Subset.rfl, fun z hz ↦ huv hz⟩
  obtain ⟨g, s, s_meas, fs, hg⟩ : ∃ g s, MeasurableSet s ∧ tsupport f ⊆ s ∧
    ∀ (x : X × Y), x ∈ s → dist (f x) (g x) < ε := M _ h'f
  refine ⟨g.piecewise s s_meas 0, fun p ↦ ?_⟩
  by_cases H : p ∈ s
  · simpa [H, SimpleFunc.piecewise_apply] using hg p H
  · have : f p = 0 := by
      contrapose! H
      rw [← Function.mem_support] at H
      exact fs (subset_tsupport _ H)
    simp [SimpleFunc.piecewise_apply, H, ite_false, this, hε]

/-- A continuous function with compact support on a product space is measurable for the product
sigma-algebra. The subtlety is that we do not assume that the spaces are separable, so the
product of the Borel sigma algebras might not contain all open sets, but still it contains enough
of them to approximate compactly supported continuous functions. -/
lemma HasCompactSupport.measurable_of_prod
    [TopologicalSpace α] [PseudoMetrizableSpace α] [MeasurableSpace α] [BorelSpace α]
    {f : X × Y → α} (hf : Continuous f) (h'f : HasCompactSupport f) :
    Measurable f := by
  letI : PseudoMetricSpace α := TopologicalSpace.pseudoMetrizableSpacePseudoMetric α
  obtain ⟨u, -, u_pos, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have : ∀ n, ∃ (g : SimpleFunc (X × Y) α), ∀ x, dist (f x) (g x) < u n :=
    fun n ↦ h'f.exists_simpleFunc_approx_of_prod hf (u_pos n)
  choose g hg using this
  have A : ∀ x, Tendsto (fun n ↦ g n x) atTop (𝓝 (f x)) := by
    intro x
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) u_lim
    rw [dist_comm]
    exact (hg n x).le
  apply measurable_of_tendsto_metrizable (fun n ↦ (g n).measurable) (tendsto_pi_nhds.2 A)

/-- A continuous function with compact support on a product space is measurable for the product
sigma-algebra. The subtlety is that we do not assume that the spaces are separable, so the
product of the Borel sigma algebras might not contain all open sets, but still it contains enough
of them to approximate compactly supported continuous functions. -/
lemma HasCompactSupport.stronglyMeasurable_of_prod
    [TopologicalSpace α] [PseudoMetrizableSpace α]
    {f : X × Y → α} (hf : Continuous f) (h'f : HasCompactSupport f) :
    StronglyMeasurable f := by
  borelize α
  apply stronglyMeasurable_iff_measurable_separable.2 ⟨h'f.measurable_of_prod hf, ?_⟩
  letI : PseudoMetricSpace α := pseudoMetrizableSpacePseudoMetric α
  exact IsCompact.isSeparable (s := range f) (h'f.isCompact_range hf)

/-- A version of *Fubini theorem* for continuous functions with compact support: one may swap
the order of integration with respect to locally finite measures. One does not assume that the
measures are σ-finite, contrary to the usual Fubini theorem. -/
lemma integral_integral_swap_of_hasCompactSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → Y → E} (hf : Continuous f.uncurry) (h'f : HasCompactSupport f.uncurry)
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    ∫ x, (∫ y, f x y ∂ν) ∂μ = ∫ y, (∫ x, f x y ∂μ) ∂ν := by
  let U := Prod.fst '' (tsupport f.uncurry)
  have : Fact (μ U < ∞) := ⟨(IsCompact.image h'f continuous_fst).measure_lt_top⟩
  let V := Prod.snd '' (tsupport f.uncurry)
  have : Fact (ν V < ∞) := ⟨(IsCompact.image h'f continuous_snd).measure_lt_top⟩
  calc
  ∫ x, (∫ y, f x y ∂ν) ∂μ = ∫ x, (∫ y in V, f x y ∂ν) ∂μ := by
    congr 1 with x
    apply (set_integral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)).symm
    contrapose! hy
    have : (x, y) ∈ Function.support f.uncurry := hy
    exact mem_image_of_mem _ (subset_tsupport _ this)
  _ = ∫ x in U, (∫ y in V, f x y ∂ν) ∂μ := by
    apply (set_integral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ ?_)).symm
    have : ∀ y, f x y = 0 := by
      intro y
      contrapose! hx
      have : (x, y) ∈ Function.support f.uncurry := hx
      exact mem_image_of_mem _ (subset_tsupport _ this)
    simp [this]
  _ = ∫ y in V, (∫ x in U, f x y ∂μ) ∂ν := by
    apply integral_integral_swap
    apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f.uncurry)).mp
    refine ⟨(h'f.stronglyMeasurable_of_prod hf).aestronglyMeasurable, ?_⟩
    obtain ⟨C, hC⟩ : ∃ C, ∀ p, ‖f.uncurry p‖ ≤ C := hf.bounded_above_of_compact_support h'f
    exact hasFiniteIntegral_of_bounded (C := C) (eventually_of_forall hC)
  _ = ∫ y, (∫ x in U, f x y ∂μ) ∂ν := by
    apply set_integral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)
    have : ∀ x, f x y = 0 := by
      intro x
      contrapose! hy
      have : (x, y) ∈ Function.support f.uncurry := hy
      exact mem_image_of_mem _ (subset_tsupport _ this)
    simp [this]
  _ = ∫ y, (∫ x, f x y ∂μ) ∂ν := by
    congr 1 with y
    apply set_integral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ ?_)
    contrapose! hx
    have : (x, y) ∈ Function.support f.uncurry := hx
    exact mem_image_of_mem _ (subset_tsupport _ this)

#check continuousWithinAt_of_dominated

open Bornology Metric

lemma blou {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : X → Y → E} {s : Set X} (hf : ContinuousOn f.uncurry (s ×ˢ univ))
    {k : Set Y}
    (hk : IsCompact k) (h'k : IsClosed k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → f p x = 0)
    {ν : Measure Y} [IsFiniteMeasureOnCompacts ν] :
    ContinuousOn (fun x ↦ ∫ y, f x y ∂ν) s := by
  intro q₀ hq₀
  have A : ∀ p ∈ s, Continuous (f p) := fun p hp ↦ by
    refine hf.comp_continuous (continuous_const.prod_mk continuous_id') fun x => ?_
    simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true] using hp
--  have B : ∀ p ∈ s, tsupport (f p) ⊆ k := fun p hp =>
--    closure_minimal (support_subset_iff'.2 fun z hz => hgs _ _ hp hz) h'k
  /- We find a small neighborhood of `{q₀.1} × k` on which the function is uniformly bounded.
      This follows from the continuity at all points of the compact set `k`. -/
  obtain ⟨w, C, w_open, q₀w, hw⟩ :
    ∃ w C, IsOpen w ∧ q₀ ∈ w ∧ ∀ p x, p ∈ w ∩ s → ‖f p x‖ ≤ C := by
    have A : IsCompact ({q₀} ×ˢ k) := isCompact_singleton.prod hk
    obtain ⟨t, kt, t_open, ht⟩ :
        ∃ t, {q₀} ×ˢ k ⊆ t ∧ IsOpen t ∧ IsBounded (↿f '' (t ∩ s ×ˢ univ)) := by
      apply exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn A _ hf
      simp only [prod_subset_prod_iff, hq₀, singleton_subset_iff, subset_univ, and_self_iff,
        true_or_iff]
    obtain ⟨C, Cpos, hC⟩ : ∃ C, 0 < C ∧ ↿f '' (t ∩ s ×ˢ univ) ⊆ closedBall (0 : E) C :=
      ht.subset_closedBall_lt 0 0
    obtain ⟨w, w_open, q₀w, hw⟩ : ∃ w, IsOpen w ∧ q₀ ∈ w ∧ w ×ˢ k ⊆ t
    · obtain ⟨w, v, w_open, -, hw, hv, hvw⟩ :
        ∃ (w : Set X) (v : Set Y), IsOpen w ∧ IsOpen v ∧ {q₀} ⊆ w ∧ k ⊆ v ∧ w ×ˢ v ⊆ t
      exact generalized_tube_lemma isCompact_singleton hk t_open kt
      exact ⟨w, w_open, singleton_subset_iff.1 hw, Subset.trans (Set.prod_mono Subset.rfl hv) hvw⟩
    refine' ⟨w, C, w_open, q₀w, _⟩
    rintro p x ⟨hp, hps⟩
    by_cases hx : x ∈ k
    · have H : (p, x) ∈ t := by
        apply hw
        simp only [prod_mk_mem_set_prod_eq, hp, hx, and_true_iff]
      have H' : (p, x) ∈ (s ×ˢ univ : Set (X × Y)) := by
        simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true_iff] using hps
      have : f p x ∈ closedBall (0 : E) C := hC (mem_image_of_mem _ (mem_inter H H'))
      rwa [mem_closedBall_zero_iff] at this
    · have : f p x = 0 := hgs _ _ hps hx
      rw [this]
      simpa only [norm_zero] using Cpos.le
  have I1 :
    ∀ᶠ q : P × G in 𝓝[s ×ˢ univ] q₀,
      AEStronglyMeasurable (fun a : G => L (f a) (g q.1 (q.2 - a))) μ := by
    filter_upwards [self_mem_nhdsWithin]
    rintro ⟨p, x⟩ ⟨hp, -⟩
    refine' (HasCompactSupport.convolutionExists_right L _ hf (A _ hp) _).1
    exact hk.of_isClosed_subset (isClosed_tsupport _) (B p hp)
  let K' := -k + {q₀.2}
  have hK' : IsCompact K' := hk.neg.add isCompact_singleton
  obtain ⟨U, U_open, K'U, hU⟩ : ∃ U, IsOpen U ∧ K' ⊆ U ∧ IntegrableOn f U μ :=
    hf.integrableOn_nhds_isCompact hK'
  let bound : G → ℝ := indicator U fun a => ‖L‖ * ‖f a‖ * C
  have I2 : ∀ᶠ q : P × G in 𝓝[s ×ˢ univ] q₀, ∀ᵐ a ∂μ, ‖L (f a) (g q.1 (q.2 - a))‖ ≤ bound a := by
    obtain ⟨V, V_mem, hV⟩ : ∃ V ∈ 𝓝 (0 : G), K' + V ⊆ U :=
      compact_open_separated_add_right hK' U_open K'U
    have : ((w ∩ s) ×ˢ ({q₀.2} + V) : Set (P × G)) ∈ 𝓝[s ×ˢ univ] q₀ := by
      conv_rhs => rw [nhdsWithin_prod_eq, nhdsWithin_univ]
      refine' Filter.prod_mem_prod _ (singleton_add_mem_nhds_of_nhds_zero q₀.2 V_mem)
      exact mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨w, w_open.mem_nhds q₀w, Subset.rfl⟩
    filter_upwards [this]
    rintro ⟨p, x⟩ hpx
    simp only [prod_mk_mem_set_prod_eq] at hpx
    refine eventually_of_forall fun a => ?_
    apply convolution_integrand_bound_right_of_le_of_subset _ _ hpx.2 _
    · intro x
      exact hw _ _ hpx.1
    · rw [← add_assoc]
      apply Subset.trans (add_subset_add_right (add_subset_add_right _)) hV
      rw [neg_subset_neg]
      exact B p hpx.1.2
  have I3 : Integrable bound μ := by
    rw [integrable_indicator_iff U_open.measurableSet]
    exact (hU.norm.const_mul _).mul_const _
  have I4 : ∀ᵐ a : G ∂μ,
      ContinuousWithinAt (fun q : P × G => L (f a) (g q.1 (q.2 - a))) (s ×ˢ univ) q₀ := by
    refine eventually_of_forall fun a => ?_
    suffices H : ContinuousWithinAt (fun q : P × G => (f a, g q.1 (q.2 - a))) (s ×ˢ univ) q₀
    exact L.continuous₂.continuousAt.comp_continuousWithinAt H
    apply continuousWithinAt_const.prod
    change ContinuousWithinAt (fun q : P × G => (↿g) (q.1, q.2 - a)) (s ×ˢ univ) q₀
    have : ContinuousAt (fun q : P × G => (q.1, q.2 - a)) (q₀.1, q₀.2) :=
      (continuous_fst.prod_mk (continuous_snd.sub continuous_const)).continuousAt
    have h'q₀ : (q₀.1, q₀.2 - a) ∈ (s ×ˢ univ : Set (P × G)) := ⟨hq₀, mem_univ _⟩
    refine' ContinuousWithinAt.comp (hg _ h'q₀) this.continuousWithinAt _
    rintro ⟨q, x⟩ ⟨hq, -⟩
    exact ⟨hq, mem_univ _⟩
  exact continuousWithinAt_of_dominated I1 I2 I3 I4


#exit

theorem continuousOn_convolution_right_with_param' {g : P → G → E'} {s : Set P} {k : Set G}
    (hk : IsCompact k) (h'k : IsClosed k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContinuousOn (↿g) (s ×ˢ univ)) :
    ContinuousOn (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) := by


end

open Function MeasureTheory Measure

variable {G : Type*} [TopologicalSpace G] [LocallyCompactSpace G] [Group G] [TopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

lemma boulb {μ ν : Measure G} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    [IsMulLeftInvariant μ] [IsMulRightInvariant ν]
    {f g : G → ℝ} (hf : Continuous f) (h'f : HasCompactSupport f)
    (hg : Continuous g) (h'g : HasCompactSupport g) :
    let D : G → ℝ := fun (x : G) ↦ ∫ y, g (y⁻¹ * x) ∂ν
    ∫ x, f x ∂μ = (∫ y, f y * (D y) ⁻¹ ∂ν) * ∫ x, g x ∂μ := by
  let D : G → ℝ := fun (x : G) ↦ ∫ y, g (y⁻¹ * x) ∂ν
  have D_cont : Continuous D := sorry
  have D_pos : ∀ x, 0 < D x := sorry
  calc
  ∫ x, f x ∂μ = ∫ x, f x * (D x)⁻¹ * D x ∂μ := by
    congr with x; rw [mul_assoc, inv_mul_cancel (D_pos x).ne', mul_one]
  _ = ∫ x, (∫ y, f x * (D x)⁻¹ * g (y⁻¹ * x) ∂ν) ∂μ := by simp_rw [integral_mul_left]
  _ = ∫ y, (∫ x, f x * (D x)⁻¹ * g (y⁻¹ * x) ∂μ) ∂ν := by
      apply integral_integral_swap_of_hasCompactSupport
      · apply Continuous.mul
        · exact (hf.comp continuous_fst).mul
            ((D_cont.comp continuous_fst).inv₀ (fun x ↦ (D_pos _).ne'))
        · exact hg.comp (continuous_snd.inv.mul continuous_fst)
      · let K := tsupport f
        have K_comp : IsCompact K := h'f
        let L := tsupport g
        have L_comp : IsCompact L := h'g
        let M := (fun (p : G × G) ↦ p.1 * p.2⁻¹) '' (K ×ˢ L)
        have M_comp : IsCompact M :=
          (K_comp.prod L_comp).image (continuous_fst.mul continuous_snd.inv)
        have : ∀ (p : G × G), p ∉ K ×ˢ M → f p.1 * (D p.1)⁻¹ * g (p.2⁻¹ * p.1) = 0 := by
          rintro ⟨x, y⟩ hxy
          by_cases H : x ∈ K; swap
          · simp [image_eq_zero_of_nmem_tsupport H]
          have : g (y⁻¹ * x) = 0 := by
            apply image_eq_zero_of_nmem_tsupport
            contrapose! hxy
            simp only [mem_prod, H, mem_image, Prod.exists, true_and]
            exact ⟨x, y⁻¹ * x, ⟨H, hxy⟩, by group⟩
          simp [this]
        apply HasCompactSupport.intro' (K_comp.prod M_comp) ?_ this
        apply (isClosed_tsupport f).prod
  _ = ∫ y, (∫ x, f (y * x) * (D (y * x))⁻¹ * g x ∂μ) ∂ν := by
      congr with y
      rw [← integral_mul_left_eq_self _ y]
      congr with x
      congr
      group
  _ = ∫ x, (∫ y, f (y * x) * (D (y * x))⁻¹ * g x ∂ν) ∂μ := by
      apply (integral_integral_swap_of_hasCompactSupport _ _).symm
      · apply Continuous.mul ?_ (hg.comp continuous_fst)
        exact (hf.comp (continuous_snd.mul continuous_fst)).mul
          ((D_cont.comp (continuous_snd.mul continuous_fst)).inv₀ (fun x ↦ (D_pos _).ne'))
      · let K := tsupport f
        have K_comp : IsCompact K := h'f
        let L := tsupport g
        have L_comp : IsCompact L := h'g
        let M := (fun (p : G × G) ↦ p.1 * p.2⁻¹) '' (K ×ˢ L)
        have M_comp : IsCompact M :=
          (K_comp.prod L_comp).image (continuous_fst.mul continuous_snd.inv)
        have : ∀ (p : G × G), p ∉ L ×ˢ M → f (p.2 * p.1) * (D (p.2 * p.1))⁻¹ * g p.1 = 0 := by
          rintro ⟨x, y⟩ hxy
          by_cases H : x ∈ L; swap
          · simp [image_eq_zero_of_nmem_tsupport H]
          have : f (y * x) = 0 := by
            apply image_eq_zero_of_nmem_tsupport
            contrapose! hxy
            simp only [mem_prod, H, mem_image, Prod.exists, true_and, and_true]
            refine ⟨y * x, x, ⟨hxy, H⟩, by group⟩
          simp [this]
        exact HasCompactSupport.intro (L_comp.prod M_comp) this
  _ = ∫ x, (∫ y, f y * (D y)⁻¹ ∂ν) * g x ∂μ := by
      simp_rw [integral_mul_right]
      congr with x
      congr 1
      conv_rhs => rw [← integral_mul_right_eq_self _ x]
  _ = (∫ y, f y * (D y)⁻¹ ∂ν) * ∫ x, g x ∂μ := integral_mul_left _ _
