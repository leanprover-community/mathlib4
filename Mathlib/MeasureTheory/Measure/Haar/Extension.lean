/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.Algebra.Group.Extension

/-!
# Haar measures on group extensions

In this file, if `1 → A → B → C → 1` is a short exact sequence of topological groups,
we construct a Haar measure on `B` from Haar measures on `A` and `C`.

## Main definitions

* `TopologicalGroup.IsSES.inducedMeasure`: The Haar measure on `B` induced by Haar measures
  on `A` and `C`.

## Main results

* `TopologicalGroup.IsSES.isHaarMeasure_inducedMeasure`: `inducedMeasure` is a Haar measure.
* `TopologicalGroup.IsSES.inducedMeasure_lt_of_injOn`: If `ψ` is injective on an open set `U`,
then `U` has bounded measure.

-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure

open scoped Pointwise

namespace TopologicalGroup.IsSES

variable {A B C E : Type*} [Group A] [Group B] [Group C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  {φ : A →* B} {ψ : B →* C} (H : TopologicalGroup.IsSES φ ψ)
  [IsTopologicalGroup A] [IsTopologicalGroup B] [NormedAddCommGroup E]

/-- Pullback a continuous compactly supported function `f` on `B` to the
continuous compactly supported function `a ↦ f (b * φ a)` on `A`. -/
@[to_additive /--Pullback a continuous compactly supported function `f` on `B` to the
continuous compactly supported function `a ↦ f (b * φ a)` on `A`.-/]
noncomputable def pullback (f : CompactlySupportedContinuousMap B E) (b : B) :
    CompactlySupportedContinuousMap A E where
  toFun a := f (b * φ a)
  hasCompactSupport' := by
    obtain ⟨K, hK, hf⟩ := exists_compact_iff_hasCompactSupport.mpr f.hasCompactSupport
    refine exists_compact_iff_hasCompactSupport.mp ⟨φ ⁻¹' (b⁻¹ • K),
      H.isClosedEmbedding.isCompact_preimage (hK.smul b⁻¹), fun x hx ↦ hf _ ?_⟩
    simpa [Set.mem_smul_set_iff_inv_smul_mem] using hx
  continuous_toFun := by
    have : Continuous φ := H.isClosedEmbedding.continuous
    fun_prop

@[to_additive]
theorem pullback_def (f : CompactlySupportedContinuousMap B E) (b : B) (a : A) :
    pullback H f b a = f (b * φ a) :=
  rfl

variable [MeasurableSpace A] [BorelSpace A] (μA : Measure A) [hμA : IsHaarMeasure μA]
  [NormedSpace ℝ E]

@[to_additive]
theorem integral_pullback_invFun_apply (f : CompactlySupportedContinuousMap B E) (b : B) :
    ∫ a, H.pullback f (Function.invFun ψ (ψ b)) a ∂μA = ∫ a, H.pullback f b a ∂μA := by
  have h : ψ ((Function.invFun ψ (ψ b))⁻¹ * b) = 1 := by simp [Function.apply_invFun_apply]
  rw [← ψ.mem_ker, H.mulExact.monoidHom_ker_eq] at h
  obtain ⟨a, ha⟩ := h
  rw [← integral_mul_left_eq_self _ a]
  simp [pullback, ha, mul_assoc]

variable [IsTopologicalGroup C] [LocallyCompactSpace B]

/-- Pushforward a continuous comapctly supported function on `B` to a
continuous compactly supported function on `C` by integrating over `A`. -/
@[to_additive /-- Pushforward a continuous comapctly supported function on `B` to a
continuous compactly supported function on `C` by integrating over `A`. -/]
noncomputable def pushforward :
    CompactlySupportedContinuousMap B E →ₗ[ℝ] CompactlySupportedContinuousMap C E where
  toFun f :=
  { toFun := fun c ↦ ∫ a, pullback H f (Function.invFun ψ c) a ∂μA
    hasCompactSupport' := by
      obtain ⟨K, hK, hf⟩ := exists_compact_iff_hasCompactSupport.mpr f.hasCompactSupport
      refine exists_compact_iff_hasCompactSupport.mp
        ⟨ψ '' K, hK.image H.isOpenQuotientMap.continuous, fun x hx ↦ ?_⟩
      suffices ∀ a : A, f (Function.invFun ψ x * φ a) = 0 by simp [this, pullback]
      intro a
      apply hf
      contrapose! hx
      refine ⟨_, hx, ?_⟩
      rw [map_mul, Function.rightInverse_invFun H.isOpenQuotientMap.surjective, mul_eq_left,
        ← ψ.mem_ker, H.mulExact.monoidHom_ker_eq]
      use a
    continuous_toFun := by
      rw [← H.isOpenQuotientMap.continuous_comp_iff, Function.comp_def]
      simp only [integral_pullback_invFun_apply]
      let p : B → A → E := fun b a ↦ f (b * φ a)
      have hp (b : B) : MemLp (p b) 1 μA :=
        (pullback H f b).continuous.memLp_of_hasCompactSupport (pullback H f b).hasCompactSupport
      suffices Continuous (fun b ↦ MemLp.toLp (p b) (hp b)) from by
        refine (continuous_congr (fun b ↦ integral_congr_ae (hp b).coeFn_toLp)).mp ?_
        exact continuous_integral.comp this
      simp only [p]
      let := IsTopologicalGroup.rightUniformSpace B
      rw [Metric.continuous_iff']
      intro b ε hε
      obtain ⟨U₀, hU₀, hb⟩ := exists_compact_mem_nhds b
      have hf₀ := f.hasCompactSupport
      rw [← exists_compact_iff_hasCompactSupport] at hf₀
      obtain ⟨K, hK, hf₀⟩ := hf₀
      let S : Set A := φ ⁻¹' (U₀⁻¹ * K)
      have hS : IsCompact S := H.isClosedEmbedding.isCompact_preimage (hU₀.inv.mul hK)
      have hS' : ∀ x ∈ U₀, ∀ y : A, f (x * φ y) ≠ 0 → y ∈ S := by
        intro x hx y h
        contrapose! h
        apply hf₀
        contrapose! h
        replace h := Set.mul_mem_mul (Set.inv_mem_inv.mpr hx) h
        rwa [inv_mul_cancel_left] at h
      set V₀ := μA S with hV₀
      have hV₀' : V₀ < ⊤ := hS.measure_lt_top
      have : ∃ v : ℝ, 0 < v ∧ v * ENNReal.toReal V₀ < ε := by
        by_cases h : V₀ = 0
        · exact ⟨1, one_pos, by simpa [h]⟩
        · replace h := ENNReal.toReal_pos h hV₀'.ne
          refine ⟨(ε / 2) / ENNReal.toReal (μA S), div_pos (div_pos hε two_pos) h, ?_⟩
          rw [div_mul_cancel₀ _ h.ne']
          exact half_lt_self hε
      obtain ⟨v, hv0, hv⟩ := this
      simp only [dist_eq_norm_sub, ← MemLp.toLp_sub, MeasureTheory.Lp.norm_toLp]
      have ha := f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
      rw [UniformContinuous, Filter.tendsto_iff_forall_eventually_mem] at ha
      obtain ⟨U, hU, hf⟩ := ha _ (Metric.dist_mem_uniformity hv0)
      refine Filter.mem_of_superset (Filter.inter_mem
        (mul_singleton_mem_nhds_of_nhds_one b (inv_mem_nhds_one B hU)) hb) ?_
      rintro - ⟨⟨t, ht, b, rfl, -, rfl⟩, htb⟩
      have hd (a : A) : dist (f (t * b * φ a)) (f (b * φ a)) < v := by
        simpa using @hf ⟨t * b * φ a, b * φ a⟩ (by simpa)
      replace hd (a : A) : ‖f (t * b * φ a) - f (b * φ a)‖ₑ ≤ ENNReal.ofReal v := by
        rw [← ofReal_norm_eq_enorm, ← dist_eq_norm_sub]
        exact ENNReal.ofReal_le_ofReal (hd a).le
      apply ENNReal.toReal_lt_of_lt_ofReal
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
        ← MeasureTheory.setLIntegral_eq_of_support_subset (s := S)]
      · apply (MeasureTheory.lintegral_mono hd).trans_lt
        rwa [lintegral_const, Measure.restrict_apply_univ, ← hV₀,
          ← ENNReal.ofReal_toReal hV₀'.ne, ← ENNReal.ofReal_mul hv0.le,
          ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
      · intro x hx
        have : f (t * b * φ x) ≠ 0 ∨ f (b * φ x) ≠ 0 := by
          contrapose! hx
          simp [hx.1, hx.2]
        rcases this with h | h
        · exact hS' (t * b) htb x h
        · exact hS' b (mem_of_mem_nhds hb) x h }
  map_add' f g := by
    ext c
    apply integral_add
    · exact (pullback H f _).integrable
    · exact (pullback H g _).integrable
  map_smul' x f := by
    ext c
    apply integral_smul

@[to_additive]
theorem pushforward_def (f : CompactlySupportedContinuousMap B E) (c : C) :
    pushforward H μA f c = ∫ a, pullback H f (Function.invFun ψ c) a ∂μA :=
  rfl

@[to_additive]
theorem pushforward_apply (f : CompactlySupportedContinuousMap B E) (b : B) :
    pushforward H μA f (ψ b) = ∫ a, pullback H f b a ∂μA :=
  integral_pullback_invFun_apply H μA f b

@[to_additive]
theorem pushforward_mono (f g : CompactlySupportedContinuousMap B ℝ) (h : f ≤ g) :
    pushforward H μA f ≤ pushforward H μA g := by
  intro c
  apply integral_mono
  · exact (pullback H f _).integrable
  · exact (pullback H g _).integrable
  · intro a
    apply h

variable [MeasurableSpace C] [BorelSpace C] (μC : Measure C) [hμC : IsHaarMeasure μC]

/-- Integrate a continuous comapctly supported function on `B` by integrating over `A` and `C`. -/
@[to_additive /-- Integrate a continuous comapctly supported function on `B` by integrating
over `A` and `C`. -/]
noncomputable def integrate : CompactlySupportedContinuousMap B E →ₗ[ℝ] E where
  toFun f := ∫ c, pushforward H μA f c ∂μC
  map_add' f g := by
    rw [map_add]
    exact integral_add (pushforward H μA f).integrable (pushforward H μA g).integrable
  map_smul' x f := by
    rw [map_smul]
    exact integral_smul x (H.pushforward μA f)

@[to_additive]
theorem integrate_apply (f : CompactlySupportedContinuousMap B E) :
    H.integrate μA μC f = ∫ c, pushforward H μA f c ∂μC :=
  rfl

@[to_additive]
theorem integrate_mono (f g : CompactlySupportedContinuousMap B ℝ) (h : f ≤ g) :
    integrate H μA μC f ≤ integrate H μA μC g :=
  integral_mono  (pushforward H μA f).integrable (pushforward H μA g).integrable
    (pushforward_mono H μA f g h)

variable [T2Space B] [MeasurableSpace B] [BorelSpace B]

/-- The Haar measure on `B` induced by the Haar measures on `A` and `C`. -/
@[to_additive /-- The Haar measure on `B` induced by the Haar measures on `A` and `C`. -/]
noncomputable def inducedMeasure : Measure B :=
  RealRMK.rieszMeasure ⟨integrate H μA μC, integrate_mono H μA μC⟩

@[to_additive]
instance inducedMeasure_regular : (inducedMeasure H μA μC).Regular :=
  RealRMK.regular_rieszMeasure _

@[to_additive]
theorem integral_inducedMeasure (f : CompactlySupportedContinuousMap B ℝ) :
    ∫ b : B, f b ∂(inducedMeasure H μA μC) = integrate H μA μC f := by
  apply RealRMK.integral_rieszMeasure

@[to_additive]
instance isHaarMeasure_inducedMeasure : IsHaarMeasure (inducedMeasure H μA μC) where
  lt_top_of_isCompact K hK := by
    let U : Set B := Set.univ
    have hU : IsOpen U := isOpen_univ
    have hKU : K ⊆ U := K.subset_univ
    obtain ⟨f, hf1, hf2, hf3, hf4⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
    exact lt_of_le_of_lt (RealRMK.rieszMeasure_le_of_eq_one (f := ⟨f, hf2⟩) _
      (fun x ↦ (hf4 x).1) hK (fun x hx ↦ hf1 hx)) ENNReal.ofReal_lt_top
  map_mul_left_eq_self b := by
    have : ((inducedMeasure H μA μC).map (fun x ↦ b * x)).Regular :=
      Regular.map (Homeomorph.mulLeft b)
    refine MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
    rw [integral_map (by fun_prop) (by fun_prop)]
    have h (x : B) : f (b * x) = f.comp (Homeomorph.mulLeft b).toCocompactMap x := rfl
    simp only [h, integral_inducedMeasure, integrate_apply]
    rw [← integral_mul_left_eq_self _ (ψ b)⁻¹]
    congr
    ext c
    obtain ⟨b', rfl⟩ := H.isOpenQuotientMap.surjective c
    rw [← map_inv, ← map_mul, pushforward_apply, pushforward_apply]
    simp [pullback, mul_assoc]
  open_pos U hU := by
    rintro ⟨b, hb⟩
    obtain ⟨K, hK, hb, hKU⟩ := exists_compact_subset hU hb
    replace hb : b ∈ K := interior_subset hb
    obtain ⟨f, hf1, hf2, hf3, hf4⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
    have hf0 : 0 ≤ H.pushforward μA ⟨f, hf2⟩ := by
      rw [← map_zero (H.pushforward μA)]
      apply pushforward_mono
      exact fun x ↦ (hf4 x).1
    refine (lt_of_lt_of_le ?_
      (RealRMK.le_rieszMeasure_tsupport_subset (f := ⟨f, hf2⟩) _ hf4 hf3)).ne'
    rw [ENNReal.ofReal_pos]
    suffices (0 : ℝ) < pushforward H μA ⟨f, hf2⟩ (ψ b) from
      (pushforward H μA ⟨f, hf2⟩).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
        (pushforward H μA ⟨f, hf2⟩).hasCompactSupport hf0 this.ne'
    have : (Function.invFun ψ (ψ b))⁻¹ * b ∈ φ.range := by
      simp [← H.mulExact.monoidHom_ker_eq, Function.apply_invFun_apply]
    obtain ⟨a, ha⟩ := this
    replace ha : f (Function.invFun ψ (ψ b) * φ a) ≠ 0 := by simp [ha, hf1 hb]
    exact (pullback H ⟨f, hf2⟩ _).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (pullback H ⟨f, hf2⟩ _).hasCompactSupport (fun x ↦ (hf4 _).1) ha

/-- If `ψ` is injective on an open set `U`, then `U` has bounded measure. -/
@[to_additive /-- If `ψ` is injective on an open set `U`, then `U` has bounded measure. -/]
theorem inducedMeasure_lt_of_injOn (U : Set B) (hU : IsOpen U) [DiscreteTopology A]
    (h : U.InjOn ψ) :
    inducedMeasure H μA μC U ≤ μC Set.univ * μA {1} := by
  contrapose! h
  have ho : 0 < μA {1} := (isOpen_discrete {1}).measure_pos _ (Set.singleton_nonempty 1)
  have ht : μA {1} < ⊤ := isCompact_singleton.measure_lt_top
  obtain ⟨K, hKU, hK, h⟩ := Regular.innerRegular hU _ h
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  replace h : μC Set.univ * μA {1} < ENNReal.ofReal (∫ c : C, pushforward H μA ⟨f, hf2⟩ c ∂μC) :=
    lt_of_lt_of_le h ((RealRMK.rieszMeasure_le_of_eq_one (f := ⟨f, hf2⟩) _ (fun x ↦ (hf4 x).1)
      hK (fun x hx ↦ hf1 hx)))
  replace h : ∃ c : C, (μA {1}).toReal < pushforward H μA ⟨f, hf2⟩ c := by
    contrapose! h
    rcases eq_top_or_lt_top (μC Set.univ) with hC | hC
    · simp [hC, ENNReal.top_mul ho.ne']
    · have : IsFiniteMeasure μC := ⟨hC⟩
      rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_lt_top hC ht).ne, ENNReal.toReal_mul,
        ← Measure.real_def, ← smul_eq_mul, ← integral_const]
      exact integral_mono (H.pushforward μA ⟨f, hf2⟩).integrable (integrable_const _) h
  obtain ⟨c, hc⟩ := h
  contrapose! hc
  obtain ⟨b, rfl⟩ := H.isOpenQuotientMap.surjective c
  simp only [pushforward_apply, pullback_def, CompactlySupportedContinuousMap.coe_mk]
  rw [← MeasureTheory.setIntegral_support]
  have key : (Function.support fun a ↦ f (b * φ a)).Subsingleton := by
    intro a ha b hb
    simpa [H.isClosedEmbedding.injective.eq_iff] using hc (hf3 (subset_tsupport _ ha))
      (hf3 (subset_tsupport _ hb)) (by simp [H.mulExact.apply_apply_eq_one])
  obtain h | ⟨a, ha⟩ := key.eq_empty_or_singleton
  · simp [h]
  · rw [ha, integral_singleton, real_def, haar_singleton, smul_eq_mul, mul_le_iff_le_one_right]
    · exact (hf4 _).2
    · exact ENNReal.toReal_pos ho.ne' ht.ne

end TopologicalGroup.IsSES
