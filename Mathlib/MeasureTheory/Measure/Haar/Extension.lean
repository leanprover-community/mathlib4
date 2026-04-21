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
  then the induced measure on `U` is bounded by `μC Set.univ * μA {1}` (possibly infinite).

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open MeasureTheory Measure

open scoped Pointwise

namespace TopologicalGroup.IsSES

variable {A B C E : Type*} [Group A] [Group B] [Group C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  {φ : A →* B} {ψ : B →* C} (H : TopologicalGroup.IsSES φ ψ)
  [IsTopologicalGroup A] [IsTopologicalGroup B] [NormedAddCommGroup E]

/-- If `φ : A →* B` and `ψ : B →* C` define a short exact sequence of topological groups, then we
can pull back a continuous compactly supported function `f` on `B` along `φ` to the continuous
compactly supported function `a ↦ f (b * φ a)` on `A`. -/
@[to_additive /-- If `φ : A →+ B` and `ψ : B →+ C` define a short exact sequence of additive
topological groups, then we can pull back a continuous compactly supported function `f` on `B` along
`φ` to the continuous compactly supported function `a ↦ f (b + φ a)` on `A`. -/]
noncomputable abbrev pullback (f : CompactlySupportedContinuousMap B E) (b : B) :
    CompactlySupportedContinuousMap A E :=
  f.pullback_monoidHom H.isClosedEmbedding b

@[to_additive]
theorem pullback_def (f : CompactlySupportedContinuousMap B E) (b : B) (a : A) :
    pullback H f b a = f (b * φ a) :=
  f.pullback_monoidHom_def H.isClosedEmbedding b a

variable [MeasurableSpace A] [BorelSpace A] (μA : Measure A) [hμA : IsHaarMeasure μA]
  [NormedSpace ℝ E]

@[to_additive]
theorem integral_pullback_invFun_apply (f : CompactlySupportedContinuousMap B E) (b : B) :
    ∫ a, H.pullback f (Function.invFun ψ (ψ b)) a ∂μA = ∫ a, H.pullback f b a ∂μA := by
  have h : ψ ((Function.invFun ψ (ψ b))⁻¹ * b) = 1 := by simp [Function.apply_invFun_apply]
  rw [← ψ.mem_ker, H.mulExact.monoidHom_ker_eq] at h
  obtain ⟨a, ha⟩ := h
  rw [← integral_mul_left_eq_self _ a]
  simp [pullback_def, ha, mul_assoc]

variable [IsTopologicalGroup C] [LocallyCompactSpace B]

/-- If `φ : A →* B` and `ψ : B →* C` define a short exact sequence of topological groups, then we
can push forward a continuous compactly supported function on `B` to a continuous compactly
supported function on `C` by integrating over `A`. -/
@[to_additive /-- If `φ : A →+ B` and `ψ : B →+ C` define a short exact sequence of additive
topological groups, then we can push forward a continuous compactly supported function on `B` to a
continuous compactly supported function on `C` by integrating over `A`. -/]
noncomputable def pushforward :
    CompactlySupportedContinuousMap B E →ₗ[ℝ] CompactlySupportedContinuousMap C E where
  toFun f :=
  { toFun := fun c ↦ ∫ a, pullback H f (Function.invFun ψ c) a ∂μA
    hasCompactSupport' := by
      obtain ⟨K, hK, hf⟩ := exists_compact_iff_hasCompactSupport.mpr f.hasCompactSupport
      refine exists_compact_iff_hasCompactSupport.mp
        ⟨ψ '' K, hK.image H.isOpenQuotientMap.continuous, fun x hx ↦ ?_⟩
      suffices ∀ a : A, f (Function.invFun ψ x * φ a) = 0 by simp [this, pullback_def]
      refine fun a ↦ hf _ (mt (Set.mem_image_of_mem ψ) ?_)
      rwa [map_mul, Function.rightInverse_invFun H.isOpenQuotientMap.surjective,
        H.mulExact.apply_apply_eq_one, mul_one]
    continuous_toFun := by
      let := IsTopologicalGroup.rightUniformSpace B
      simp_rw [← H.isOpenQuotientMap.continuous_comp_iff, Function.comp_def,
        integral_pullback_invFun_apply, Metric.continuous_iff']
      intro b ε hε
      obtain ⟨U₀, hU₀, hb⟩ := exists_compact_mem_nhds b
      obtain ⟨K, hK, hf₀⟩ := exists_compact_iff_hasCompactSupport.mpr f.hasCompactSupport
      let S : Set A := φ ⁻¹' (U₀⁻¹ * K)
      have hSc : IsCompact S := H.isClosedEmbedding.isCompact_preimage (hU₀.inv.mul hK)
      obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ENNReal.ofReal δ * μA S < ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_toReal hSc.measure_ne_top, ← measureReal_def]
        by_cases hS' : μA.real S = 0
        · simp [hS', hε, exists_gt]
        · refine ⟨ε / 2 / μA.real S, by positivity, ?_⟩
          rwa [← ENNReal.ofReal_mul' measureReal_nonneg, ENNReal.ofReal_lt_ofReal_iff hε,
            div_mul_cancel₀ _ hS', half_lt_self_iff]
      have hS {x} (hx : x ∈ U₀) {y} (hy : y ∉ S) : H.pullback f x y = 0 := by
        contrapose! hy
        exact Set.mem_mul.mpr ⟨x⁻¹, Set.inv_mem_inv.mpr hx, x * φ y,
          not_imp_comm.mp (hf₀ (x * φ y)) hy, inv_mul_cancel_left x (φ y)⟩
      have ha := f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
      rw [uniformContinuous_iff_eventually] at ha
      obtain ⟨U, hU, hf⟩ := ha _ (Metric.dist_mem_uniformity hδ0)
      refine Filter.mem_of_superset (Filter.inter_mem
        (mul_singleton_mem_nhds_of_nhds_one b (inv_mem_nhds_one B hU)) hb) ?_
      rintro - ⟨⟨t, ht, b, rfl, -, rfl⟩, htb⟩
      have h (a) (ha : a ∈ S) : edist (H.pullback f (t * b) a) (H.pullback f b a) ≤ .ofReal δ := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (@hf ⟨t * b * φ a, b * φ a⟩ (by simpa)).le
      grw [Set.mem_setOf_eq, dist_integral_le_lintegral_edist (H.pullback f (t * b)).integrable
        (H.pullback f b).integrable, ← setLIntegral_eq_of_support_subset]
      · refine ENNReal.toReal_lt_of_lt_ofReal ((setLIntegral_mono measurable_const h).trans_lt ?_)
        rwa [lintegral_const, restrict_apply_univ]
      · intro y hy
        contrapose hy
        rw [Function.notMem_support, hS htb hy, hS (mem_of_mem_nhds hb) hy, edist_self] }
  map_add' f g := by
    ext c
    exact integral_add (pullback H f _).integrable (pullback H g _).integrable
  map_smul' x f := by
    ext c
    apply integral_smul

@[to_additive]
theorem pushforward_def (f : CompactlySupportedContinuousMap B E) (c : C) :
    pushforward H μA f c = ∫ a, pullback H f (Function.invFun ψ c) a ∂μA :=
  rfl

@[to_additive]
theorem pushforward_apply_apply (f : CompactlySupportedContinuousMap B E) (b : B) :
    pushforward H μA f (ψ b) = ∫ a, pullback H f b a ∂μA :=
  integral_pullback_invFun_apply H μA f b

@[to_additive]
theorem pushforward_mono {f g : CompactlySupportedContinuousMap B ℝ} (h : f ≤ g) :
    pushforward H μA f ≤ pushforward H μA g :=
  fun _ ↦ integral_mono (pullback H f _).integrable (pullback H g _).integrable (fun _ ↦ h _)

variable [MeasurableSpace C] [BorelSpace C] (μC : Measure C) [hμC : IsHaarMeasure μC]

/-- If `φ : A →* B` and `ψ : B →* C` define a short exact sequence of topological groups, then we
can integrate a continuous compactly supported function on `B` by integrating over `A` and `C`. -/
@[to_additive /-- If `φ : A →+ B` and `ψ : B →+ C` define a short exact sequence of additive
topological groups, then we can integrate a continuous compactly supported function on `B` by
integrating over `A` and `C`. -/]
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
theorem integrate_mono {f g : CompactlySupportedContinuousMap B ℝ} (h : f ≤ g) :
    integrate H μA μC f ≤ integrate H μA μC g :=
  integral_mono (pushforward H μA f).integrable (pushforward H μA g).integrable
    (pushforward_mono H μA h)

variable [T2Space B] [MeasurableSpace B] [BorelSpace B]

/-- If `φ : A →* B` and `ψ : B →* C` define a short exact sequence of topological groups, then we
can define a Haar measure on `B` induced by the Haar measures on `A` and `C`. -/
@[to_additive /-- If `φ : A →+ B` and `ψ : B →+ C` define a short exact sequence of additive
topological groups, then we can define a Haar measure on `B` induced by the Haar measures on `A`
and `C`. -/]
noncomputable def inducedMeasure : Measure B :=
  RealRMK.rieszMeasure ⟨integrate H μA μC, fun _ _ ↦ integrate_mono H μA μC⟩

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
    obtain ⟨f, hf1, hf2, hf3, hf4⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ K.subset_univ
    exact lt_of_le_of_lt (RealRMK.rieszMeasure_le_of_eq_one (f := ⟨f, hf2⟩) _
      (fun x ↦ (hf4 x).1) hK (fun x hx ↦ hf1 hx)) ENNReal.ofReal_lt_top
  map_mul_left_eq_self b := by
    have : ((inducedMeasure H μA μC).map (b * ·)).Regular := Regular.map (Homeomorph.mulLeft b)
    refine ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
    rw [integral_map (by fun_prop) (by fun_prop)]
    have h (x : B) : f (b * x) = f.comp (Homeomorph.mulLeft b).toCocompactMap x := rfl
    simp_rw [h, integral_inducedMeasure, integrate_apply]
    rw [← integral_mul_left_eq_self _ (ψ b)⁻¹]
    congr with c
    obtain ⟨b', rfl⟩ := H.isOpenQuotientMap.surjective c
    rw [← map_inv, ← map_mul, pushforward_apply_apply, pushforward_apply_apply]
    simp [pullback_def, mul_assoc]
  open_pos U hU := by
    rintro ⟨b, hb⟩
    obtain ⟨K, hK, hb, hKU⟩ := exists_compact_subset hU hb
    obtain ⟨f, hf1, hf2, hf3, hf4⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
    have hf0 : 0 ≤ H.pushforward μA ⟨f, hf2⟩ := by
      rw [← map_zero (H.pushforward μA)]
      apply pushforward_mono
      exact fun x ↦ (hf4 x).1
    grw [← pos_iff_ne_zero, inducedMeasure,
      ← RealRMK.le_rieszMeasure_tsupport_subset (f := ⟨f, hf2⟩) _ hf4 hf3, ENNReal.ofReal_pos]
    suffices (0 : ℝ) < pushforward H μA ⟨f, hf2⟩ (ψ b) from
      (pushforward H μA ⟨f, hf2⟩).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
        (pushforward H μA ⟨f, hf2⟩).hasCompactSupport hf0 this.ne'
    have : (Function.invFun ψ (ψ b))⁻¹ * b ∈ φ.range := by
      simp [← H.mulExact.monoidHom_ker_eq, Function.apply_invFun_apply]
    obtain ⟨a, ha⟩ := this
    replace ha : f (Function.invFun ψ (ψ b) * φ a) ≠ 0 := by simp [ha, hf1 (interior_subset hb)]
    exact (pullback H ⟨f, hf2⟩ _).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (pullback H ⟨f, hf2⟩ _).hasCompactSupport (fun x ↦ (hf4 _).1) ha

/-- If `φ : A →* B` and `ψ : B →* C` define a short exact sequence of topological groups, and if
`ψ` is injective on an open set `U`, then the induced measure on `U` is bounded above by
`μC Set.univ * μA {1}` (possibly infinite). -/
@[to_additive /-- If `φ : A →+ B` and `ψ : B →+ C` define a short exact sequence of additive
topological groups, and if `ψ` is injective on an open set `U`, then the induced measure on `U` is
bounded above by `μC Set.univ * μA {1}` (possibly infinite). -/]
theorem inducedMeasure_lt_of_injOn {U : Set B} (hU : IsOpen U) [DiscreteTopology A]
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
  obtain ⟨c, hc⟩ : ∃ c : C, (μA {1}).toReal < pushforward H μA ⟨f, hf2⟩ c := by
    contrapose! h
    rcases eq_top_or_lt_top (μC Set.univ) with hC | hC
    · simp [hC, ENNReal.top_mul ho.ne']
    · have : IsFiniteMeasure μC := ⟨hC⟩
      rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_lt_top hC ht).ne, ENNReal.toReal_mul,
        ← Measure.real_def, ← smul_eq_mul, ← integral_const]
      exact integral_mono (H.pushforward μA ⟨f, hf2⟩).integrable (integrable_const _) h
  contrapose! hc
  obtain ⟨b, rfl⟩ := H.isOpenQuotientMap.surjective c
  simp only [pushforward_apply_apply, pullback_def, CompactlySupportedContinuousMap.coe_mk]
  rw [← setIntegral_support]
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
