/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Constructions.Prod.Integral

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
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
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

open Function

variable {G : Type*} [TopologicalSpace G] [LocallyCompactSpace G] [Group G] [TopologicalGroup G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

lemma boulb {μ ν : Measure G} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {f g : G → ℝ} (hf : Continuous f) (h'f : HasCompactSupport f)
    (hg : Continuous g) (h'g : HasCompactSupport g) :
    let D : G → ℝ := fun (x : G) ↦ ∫ y, g (y⁻¹ * x) ∂ν
    ∫ x, f x ∂μ = (∫ y, f y / D y ∂ν) * ∫ x, g x ∂μ := by
  set D : G → ℝ := fun (x : G) ↦ ∫ y, g (y⁻¹ * x) ∂ν with D_def
  have D_cont : Continuous D := sorry
  have D_pos : ∀ x, 0 < D x := sorry
  have :
  ∫ x, (∫ y, f x * (D x)⁻¹ * g (y⁻¹ * x) ∂ν) ∂μ = ∫ y, (∫ x, f x * (D x)⁻¹ * g (y⁻¹ * x) ∂μ) ∂ν := by
    apply integral_integral_swap_of_hasCompactSupport
    · apply Continuous.mul
      · exact (hf.comp continuous_fst).mul
          ((D_cont.comp continuous_fst).inv₀ (fun x ↦ (D_pos _).ne'))
      · exact hg.comp (continuous_snd.inv.mul continuous_fst)
    · let K := tsupport f
      have K_comp : IsCompact K := h'f
      let L := tsupport g
      have L_comp : IsCompact L := h'g
      let M := (fun (p : G × G) ↦ p.2⁻¹ * p.1) '' (K ×ˢ L)
      have M_comp : IsCompact M :=
        (K_comp.prod L_comp).image (continuous_snd.inv.mul continuous_fst)
      have : support (fun (p : G × G) ↦ f p.1 * (D p.1)⁻¹ * g (p.2⁻¹ * p.1)) ⊆ K ×ˢ M := by
        apply support_subset_iff'.2
        rintro ⟨x, y⟩ hxy
        by_cases H : x ∈ K; swap
        · simp [image_eq_zero_of_nmem_tsupport H]
        have : g (y⁻¹ * x) = 0 := by
          apply image_eq_zero_of_nmem_tsupport
          contrapose! hxy


#exit
  calc
  ∫ x, f x ∂μ = ∫ x, f x * (D x)⁻¹ * D x ∂μ := by
    congr with x; rw [mul_assoc, inv_mul_cancel (D_pos x).ne', mul_one]
  _ = ∫ x, (∫ y, f x * (D x)⁻¹ * g (y⁻¹ * x) ∂ν) ∂μ := by simp_rw [integral_mul_left]
  _ = ∫ y, (∫ x, f x * (D x)⁻¹ * g (y⁻¹ * x) ∂μ) ∂ν := by
      apply integral_prod
      sorry
  _ = (∫ y, f y / D y ∂ν) * ∫ x, g x ∂μ := sorry
