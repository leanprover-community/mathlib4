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
import Mathlib.Topology.UrysohnsLemma

/-!
# Uniqueness of Haar measure, again

-/

open MeasureTheory Filter Set TopologicalSpace
open scoped Uniformity Topology ENNReal Pointwise

section

lemma foo {G : Type*} [TopologicalSpace G] [Group G] [TopologicalGroup G]
    [LocallyCompactSpace G] {k u : Set G}
    (hk : IsCompact k) (hu : IsOpen u) (h : k ⊆ u) :
    ∃ f : G → ℝ, Continuous f ∧ EqOn f 1 k ∧ EqOn f 0 u := by
  let N : Subgroup G := (⊥ : Subgroup G).topologicalClosure
  let H := G ⧸ N
  have : N.Normal := Subgroup.is_normal_topologicalClosure ⊥
  let π := ((↑) : G → H)
  have : IsClosed (N : Set G) := Subgroup.isClosed_topologicalClosure ⊥
  let k' := π '' k
  have k'_comp : IsCompact k' := hk.image continuous_coinduced_rng
  have k'_closed : IsClosed k' := k'_comp.isClosed
  let u' := π '' u
  have u'_open : IsOpen u' := QuotientGroup.isOpenMap_coe N u hu
  have : k' ⊆ u' := image_subset π h
  have T := exists_continuous_zero_one_of_closed k'_closed u'_open


end

#exit


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

end

open Function MeasureTheory Measure

variable {G : Type*} [TopologicalSpace G] [LocallyCompactSpace G] [Group G] [TopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

lemma continuous_integral_apply_inv_mul
    {μ : Measure G} [IsFiniteMeasureOnCompacts μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : G → E}
    (hg : Continuous g) (h'g : HasCompactSupport g) :
    Continuous (fun (x : G) ↦ ∫ y, g (y⁻¹ * x) ∂μ) := by
  let k := tsupport g
  have k_comp : IsCompact k := h'g
  apply continuous_iff_continuousAt.2 (fun x₀ ↦ ?_)
  obtain ⟨t, t_comp, ht⟩ : ∃ t, IsCompact t ∧ t ∈ 𝓝 x₀ := exists_compact_mem_nhds x₀
  let k' : Set G := t • k⁻¹
  have k'_comp : IsCompact k' := t_comp.smul_set k_comp.inv
  have A : ContinuousOn (fun (x : G) ↦ ∫ y, g (y⁻¹ * x) ∂μ) t := by
    apply continuousOn_integral_of_compact_support k'_comp
    · exact (hg.comp (continuous_snd.inv.mul continuous_fst)).continuousOn
    · intro p x hp hx
      contrapose! hx
      refine ⟨p, p⁻¹ * x, hp, ?_, by simp⟩
      simpa only [Set.mem_inv, mul_inv_rev, inv_inv] using subset_tsupport _ hx
  exact A.continuousAt ht

lemma integral_mulLeftInvariant_mulRightInvariant_combo
    {μ ν : Measure G} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    [IsMulLeftInvariant μ] [IsMulRightInvariant ν] [IsOpenPosMeasure ν]
    {f g : G → ℝ} (hf : Continuous f) (h'f : HasCompactSupport f)
    (hg : Continuous g) (h'g : HasCompactSupport g) (g_nonneg : 0 ≤ g) {x₀ : G} (g_pos : g x₀ ≠ 0) :
    ∫ x, f x ∂μ = (∫ y, f y * (∫ z, g (z⁻¹ * y) ∂ν)⁻¹ ∂ν) * ∫ x, g x ∂μ := by
  let D : G → ℝ := fun (x : G) ↦ ∫ y, g (y⁻¹ * x) ∂ν
  have D_cont : Continuous D := continuous_integral_apply_inv_mul hg h'g
  have D_pos : ∀ x, 0 < D x := by
    intro x
    have C : Continuous (fun y ↦ g (y⁻¹ * x)) := hg.comp (continuous_inv.mul continuous_const)
    apply (integral_pos_iff_support_of_nonneg _ _).2
    · apply C.isOpen_support.measure_pos ν
      exact ⟨x * x₀⁻¹, by simpa using g_pos⟩
    · exact fun y ↦ g_nonneg (y⁻¹ * x)
    · apply C.integrable_of_hasCompactSupport
      exact h'g.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight x))
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
        have M'_comp : IsCompact (closure M) := M_comp.closure
        have : ∀ (p : G × G), p ∉ K ×ˢ closure M → f p.1 * (D p.1)⁻¹ * g (p.2⁻¹ * p.1) = 0 := by
          rintro ⟨x, y⟩ hxy
          by_cases H : x ∈ K; swap
          · simp [image_eq_zero_of_nmem_tsupport H]
          have : g (y⁻¹ * x) = 0 := by
            apply image_eq_zero_of_nmem_tsupport
            contrapose! hxy
            simp only [mem_prod, H, true_and]
            apply subset_closure
            simp only [mem_image, mem_prod, Prod.exists]
            exact ⟨x, y⁻¹ * x, ⟨H, hxy⟩, by group⟩
          simp [this]
        apply HasCompactSupport.intro' (K_comp.prod M'_comp) ?_ this
        exact (isClosed_tsupport f).prod isClosed_closure
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
        have M'_comp : IsCompact (closure M) := M_comp.closure
        have : ∀ (p : G × G), p ∉ L ×ˢ closure M →
            f (p.2 * p.1) * (D (p.2 * p.1))⁻¹ * g p.1 = 0 := by
          rintro ⟨x, y⟩ hxy
          by_cases H : x ∈ L; swap
          · simp [image_eq_zero_of_nmem_tsupport H]
          have : f (y * x) = 0 := by
            apply image_eq_zero_of_nmem_tsupport
            contrapose! hxy
            simp only [mem_prod, H, true_and]
            apply subset_closure
            simp only [mem_image, mem_prod, Prod.exists]
            refine ⟨y * x, x, ⟨hxy, H⟩, by group⟩
          simp [this]
        apply HasCompactSupport.intro' (L_comp.prod M'_comp) ?_ this
        exact (isClosed_tsupport g).prod isClosed_closure
  _ = ∫ x, (∫ y, f y * (D y)⁻¹ ∂ν) * g x ∂μ := by
      simp_rw [integral_mul_right]
      congr with x
      congr 1
      conv_rhs => rw [← integral_mul_right_eq_self _ x]
  _ = (∫ y, f y * (D y)⁻¹ ∂ν) * ∫ x, g x ∂μ := integral_mul_left _ _


lemma integral_mulLeftInvariant_unique_of_hasCompactSupport
    {μ μ' : Measure G} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts μ']
    [IsMulLeftInvariant μ] [IsMulLeftInvariant μ'] [IsOpenPosMeasure μ] :
    ∃ (c : ℝ), ∀ (f : G → ℝ), Continuous f → HasCompactSupport f →
      ∫ x, f x ∂μ' = c * ∫ x, f x ∂μ := by
  by_cases H : LocallyCompactSpace G; swap
  · refine ⟨0, fun f f_cont f_comp ↦ ?_⟩
    rcases f_comp.eq_zero_or_locallyCompactSpace_of_group f_cont with hf|hf
    · simp [hf]
    · exact (H hf).elim
