/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Polar coordinate change of variables for the mixed embedding of a number field

-/

section LIntegral

/-- **Tonelli's Theorem**: For `ℝ≥0∞`-valued almost everywhere measurable functions on `s ×ˢ t`,
  the integral of `f` on `s ×ˢ t` is equal to the iterated integral on `s` and `t` respectively. -/
theorem MeasureTheory.setLIntegral_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] [SFinite μ] {s : Set α} (t : Set β)
    (f : α × β → ENNReal) (hf : AEMeasurable f ((μ.prod ν).restrict (s ×ˢ t))) :
    ∫⁻ z in s ×ˢ t, f z ∂μ.prod ν = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂ν ∂μ := by
  rw [← Measure.prod_restrict, lintegral_prod _ (by rwa [Measure.prod_restrict])]

end LIntegral

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding ENNReal MeasureTheory
  MeasureTheory.Measure Real

noncomputable section realMixedSpace

abbrev realMixedSpace :=
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ)

noncomputable def mixedSpaceToRealSpace : mixedSpace K ≃ₜ realMixedSpace K :=
  (Homeomorph.refl _).prodCongr <| .piCongrRight fun _ ↦ Complex.equivRealProdCLM.toHomeomorph

@[simp]
theorem mixedSpaceToRealSpace_apply (x : mixedSpace K) :
    mixedSpaceToRealSpace K x = (x.1, fun w ↦ Complex.equivRealProd (x.2 w)) := rfl

variable [NumberField K]

open Classical in
theorem volume_preserving_mixedSpaceToRealSpace_symm :
    MeasurePreserving (mixedSpaceToRealSpace K).symm :=
  (MeasurePreserving.id _).prod <|
    volume_preserving_pi fun _ ↦  Complex.volume_preserving_equiv_real_prod.symm

open Classical in
instance : IsAddHaarMeasure (volume : Measure (realMixedSpace K)) := prod.instIsAddHaarMeasure _ _

@[simps! apply target]
def polarCoord₀ : PartialHomeomorph (realMixedSpace K) (realMixedSpace K) :=
  ((PartialHomeomorph.refl _).prod (PartialHomeomorph.pi fun _ ↦ polarCoord))

theorem polarCoord₀_source :
    (polarCoord₀ K).source = Set.univ ×ˢ (Set.univ.pi fun _ ↦ polarCoord.source) := rfl

private theorem abs_of_mem_polarCoord₀_target {x : realMixedSpace K}
    (hx : x ∈ (polarCoord₀ K).target) (w : {w // IsComplex w}) :
    |(x.2 w).1| = (x.2 w).1 :=
  abs_of_pos (hx.2 w trivial).1

open ContinuousLinearMap in
def FDerivPolarCoord₀Symm : realMixedSpace K → realMixedSpace K →L[ℝ] realMixedSpace K :=
  fun x ↦ (fst ℝ _ _).prod <| (fderivPiPolarCoordSymm x.2).comp (snd ℝ _ _)

theorem hasFDerivAt_polarCoord₀_symm (x : realMixedSpace K) :
    HasFDerivAt (polarCoord₀ K).symm (FDerivPolarCoord₀Symm K x) x := by
  classical
  exact (hasFDerivAt_id x.1).prodMap x (hasFDerivAt_pi_polarCoord_symm x.2)

open Classical in
theorem det_fderiv_polarCoord₀_symm (x : realMixedSpace K) :
    (FDerivPolarCoord₀Symm K x).det = ∏ w : {w // IsComplex w}, (x.2 w).1 := by
  have : (FDerivPolarCoord₀Symm K x).toLinearMap =
      LinearMap.prodMap (LinearMap.id) (fderivPiPolarCoordSymm x.2).toLinearMap := rfl
  rw [ContinuousLinearMap.det, this, LinearMap.prodMap_det, LinearMap.det_id, one_mul,
    ← ContinuousLinearMap.det, det_fderivPiPolarCoordSymm]

open Classical in
theorem polarCoord₀_symm_target_ae_eq_univ :
    (polarCoord₀ K).symm '' (polarCoord₀ K).target =ᵐ[volume] Set.univ := by
  rw [← Set.univ_prod_univ, volume_eq_prod, (polarCoord₀ K).symm_image_target_eq_source,
    polarCoord₀_source, ← polarCoord.symm_image_target_eq_source, ← Set.piMap_image_univ_pi]
  exact set_prod_ae_eq (by rfl) pi_polarCoord_symm_target_ae_eq_univ

open Classical in
theorem integral_comp_polarCoord₀_symm  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : realMixedSpace K → E) :
    ∫ x in (polarCoord₀ K).target, (∏ w : {w // IsComplex w}, (x.2 w).1) •
      f ((polarCoord₀ K).symm x) = ∫ x, f x := by
  rw [← setIntegral_univ (f := f), ← setIntegral_congr_set (polarCoord₀_symm_target_ae_eq_univ K)]
  convert (integral_image_eq_integral_abs_det_fderiv_smul volume
    (polarCoord₀ K).open_target.measurableSet
    (fun x _ ↦ (hasFDerivAt_polarCoord₀_symm K x).hasFDerivWithinAt)
    (polarCoord₀ K).symm.injOn f).symm using 1
  refine setIntegral_congr_fun (polarCoord₀ K).open_target.measurableSet fun x hx ↦ ?_
  simp_rw [det_fderiv_polarCoord₀_symm, Finset.abs_prod, abs_of_mem_polarCoord₀_target K hx]

open Classical in
theorem lintegral_comp_polarCoord₀_symm (f : realMixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (polarCoord₀ K).target, (∏ w : {w // IsComplex w}, .ofReal (x.2 w).1) *
      f ((polarCoord₀ K).symm x) = ∫⁻ x, f x := by
  rw [← setLIntegral_univ f, ← setLIntegral_congr (polarCoord₀_symm_target_ae_eq_univ K)]
  convert (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (polarCoord₀ K).open_target.measurableSet
    (fun x _ ↦ (hasFDerivAt_polarCoord₀_symm K x).hasFDerivWithinAt)
    (polarCoord₀ K).symm.injOn f).symm using 1
  refine setLIntegral_congr_fun (polarCoord₀ K).open_target.measurableSet ?_
  filter_upwards with x hx
  simp_rw [det_fderiv_polarCoord₀_symm, Finset.abs_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦
    abs_nonneg _), abs_of_mem_polarCoord₀_target K hx]

end realMixedSpace

section mixedSpace

variable [NumberField K]

@[simps!]
protected noncomputable def polarCoord : PartialHomeomorph (mixedSpace K) (realMixedSpace K) :=
  (PartialHomeomorph.refl _).prod (PartialHomeomorph.pi fun _ ↦ Complex.polarCoord)

theorem polarCoord_target_eq_polarCoord₀_target :
    (mixedEmbedding.polarCoord K).target = (polarCoord₀ K).target := rfl

theorem polarCoord_symm_eq :
    (mixedEmbedding.polarCoord K).symm =
      (mixedSpaceToRealSpace K).symm ∘ (polarCoord₀ K).symm := rfl

theorem normAtPlace_polarCoord_symm_of_isReal (x : realMixedSpace K) {w : InfinitePlace K}
    (hw : IsReal w) :
    normAtPlace w ((mixedEmbedding.polarCoord K).symm x) = ‖x.1 ⟨w, hw⟩‖ := by
  simp [normAtPlace_apply_of_isReal hw]

theorem normAtPlace_polarCoord_symm_of_isComplex (x : realMixedSpace K)
    {w : InfinitePlace K} (hw : IsComplex w) :
    normAtPlace w ((mixedEmbedding.polarCoord K).symm x) = ‖(x.2 ⟨w, hw⟩).1‖ := by
  simp [normAtPlace_apply_of_isComplex hw]

open Classical

protected theorem integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedSpace K → E) :
    ∫ x in (mixedEmbedding.polarCoord K).target,
      (∏ w : {w // IsComplex w}, (x.2 w).1) • f ((mixedEmbedding.polarCoord K).symm x) =
        ∫ x, f x := by
  rw [← (volume_preserving_mixedSpaceToRealSpace_symm K).integral_comp
    (mixedSpaceToRealSpace K).symm.measurableEmbedding, ← integral_comp_polarCoord₀_symm,
    polarCoord_target_eq_polarCoord₀_target, polarCoord_symm_eq, Function.comp_def]

protected theorem lintegral_comp_polarCoord_symm (f : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (mixedEmbedding.polarCoord K).target, (∏ w : {w // IsComplex w}, .ofReal (x.2 w).1) *
      f ((mixedEmbedding.polarCoord K).symm x) = ∫⁻ x, f x := by
  rw [← ( volume_preserving_mixedSpaceToRealSpace_symm K).lintegral_comp_emb
    (mixedSpaceToRealSpace K).symm.measurableEmbedding, ← lintegral_comp_polarCoord₀_symm,
    polarCoord_target_eq_polarCoord₀_target, polarCoord_symm_eq, Function.comp_def]

private theorem volume_prod_aux {s₁ : Set ({w // IsReal w} → ℝ)}
    {s₂ : Set ({w // IsComplex w} → ℂ)} :
    (mixedEmbedding.polarCoord K).target ∩ (mixedEmbedding.polarCoord K).symm ⁻¹' s₁ ×ˢ s₂ =
      s₁ ×ˢ ((Set.univ.pi fun _ ↦ Complex.polarCoord.target) ∩
              (Pi.map fun _ ↦ Complex.polarCoord.symm) ⁻¹' s₂) := by
  rw [show (mixedEmbedding.polarCoord K).symm ⁻¹' s₁ ×ˢ s₂ = s₁ ×ˢ
    (Pi.map (fun _ ↦ Complex.polarCoord.symm) ⁻¹' s₂) by rfl, mixedEmbedding.polarCoord_target,
    Set.prod_inter_prod, Set.univ_inter]

protected theorem volume_prod {s₁ : Set ({w // IsReal w} → ℝ)} {s₂ : Set ({w // IsComplex w} → ℂ)}
    (hs₁ : MeasurableSet s₁) (hs₂ : MeasurableSet s₂) :
    volume (s₁ ×ˢ s₂ : Set (mixedSpace K)) = volume s₁ *
      ∫⁻ x in (Set.univ.pi fun _ ↦ Complex.polarCoord.target) ∩
        (Pi.map fun _ ↦ Complex.polarCoord.symm) ⁻¹' s₂,
          (∏ w : {w // IsComplex w}, .ofReal (x w).1) := by
  have h_mes : MeasurableSet ((Set.univ.pi fun x ↦ Complex.polarCoord.target) ∩
      (Pi.map fun x ↦ ↑Complex.polarCoord.symm) ⁻¹' s₂) :=
    measurableSet_pi_polarCoord_target.inter <| hs₂.preimage <| measurable_pi_iff.mpr
      fun w ↦ Complex.continuous_polarCoord_symm.measurable.comp (measurable_pi_apply w)
  calc
    _ = ∫⁻ (x : realMixedSpace K), (mixedEmbedding.polarCoord K).target.indicator
          (fun p ↦ (∏ w, .ofReal (p.2 w).1) *
            (s₁ ×ˢ s₂).indicator 1 ((mixedEmbedding.polarCoord K).symm p)) x := ?_
    _ = ∫⁻ (x : realMixedSpace K), ((mixedEmbedding.polarCoord K).target ∩
          (mixedEmbedding.polarCoord K).symm ⁻¹' s₁ ×ˢ s₂).indicator
            (fun p ↦ (∏ w, .ofReal (p.2 w).1) * 1) x := ?_
    _ = ∫⁻ (x : realMixedSpace K), (s₁.indicator 1 x.1) *
          (((Set.univ.pi fun x ↦ Complex.polarCoord.target) ∩
            (Pi.map fun x ↦ ↑Complex.polarCoord.symm) ⁻¹' s₂).indicator
              (fun p ↦ 1 * ∏ w, .ofReal (p w).1) x.2) := ?_
    _ = volume s₁ * ∫⁻ x in (Set.univ.pi fun x ↦ Complex.polarCoord.target) ∩
        (Pi.map fun x ↦ ↑Complex.polarCoord.symm) ⁻¹' s₂,
          ∏ w : {w : InfinitePlace K // w.IsComplex}, ENNReal.ofReal (x w).1 := ?_
  · rw [← lintegral_indicator_one (hs₁.prod hs₂), ← mixedEmbedding.lintegral_comp_polarCoord_symm,
      ← lintegral_indicator (mixedEmbedding.polarCoord K).open_target.measurableSet]
  · congr with _
    rw [Set.inter_indicator_mul, Set.indicator_mul_left, ← Set.indicator_comp_right, Pi.one_comp,
      Pi.one_def]
  · congr with _
    rw [Set.indicator_mul_right, mul_comm, Set.indicator_mul_left, ← mul_assoc, ← Pi.one_def,
      ← Pi.one_def, ← Set.indicator_prod_one, volume_prod_aux]
  · simp_rw [one_mul, Pi.one_def]
    rw [volume_eq_prod, lintegral_prod_mul (aemeasurable_const.indicator hs₁)
      ((Measurable.aemeasurable (by fun_prop)).indicator h_mes), ← Pi.one_def,
      lintegral_indicator_one hs₁, lintegral_indicator h_mes]

end mixedSpace

noncomputable section polarSpace

abbrev polarSpace := ((InfinitePlace K) → ℝ) × ({w : InfinitePlace K // w.IsComplex} → ℝ)

open Classical MeasurableEquiv in
def measurableEquivRealMixedSpacePolarSpace : realMixedSpace K ≃ᵐ polarSpace K :=
  MeasurableEquiv.trans (prodCongr (refl _)
    (arrowProdEquivProdArrow ℝ ℝ _)) <|
    MeasurableEquiv.trans prodAssoc.symm <|
      MeasurableEquiv.trans
        (prodCongr (prodCongr (refl _)
          (arrowCongr' (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex.symm)) (refl _)))
            (refl _))
          (prodCongr (piEquivPiSubtypeProd (fun _ ↦ ℝ) _).symm (refl _))

open Classical in
def homeoRealMixedSpacePolarSpace : realMixedSpace K ≃ₜ polarSpace K :=
{ measurableEquivRealMixedSpacePolarSpace K with
  continuous_toFun := by
    change Continuous fun x : realMixedSpace K ↦  (fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2)
    refine continuous_prod_mk.mpr ⟨continuous_pi_iff.mpr fun w ↦ ?_, by fun_prop⟩
    split_ifs <;> fun_prop
  continuous_invFun := by
    change Continuous fun x : polarSpace K ↦
      (⟨fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩⟩ : realMixedSpace K)
    fun_prop }

open Classical in
theorem homeoRealMixedSpacePolarSpace_apply (x : realMixedSpace K) :
    homeoRealMixedSpacePolarSpace K x =
      ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
        (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩ := rfl

theorem homeoRealMixedSpacePolarSpace_apply_fst_of_isReal (x : realMixedSpace K)
    (w : {w // IsReal w}) :
    (homeoRealMixedSpacePolarSpace K x).1 w.1 = x.1 w := by
  simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_pos w.prop]

theorem homeoRealMixedSpacePolarSpace_apply_fst_of_isComplex (x : realMixedSpace K)
    (w : {w // IsComplex w}) :
    (homeoRealMixedSpacePolarSpace K x).1 w.1 = (x.2 w).1 := by
  simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_neg (not_isReal_iff_isComplex.mpr w.prop)]

theorem homeoRealMixedSpacePolarSpace_apply_snd (x : realMixedSpace K) (w : {w // IsComplex w}) :
    (homeoRealMixedSpacePolarSpace K x).2 w = (x.2 w).2 := rfl

@[simp]
theorem homeoRealMixedSpacePolarSpace_symm_apply (x : polarSpace K) :
    (homeoRealMixedSpacePolarSpace K).symm x = ⟨fun w ↦ x.1 w, fun w ↦ (x.1 w, x.2 w)⟩ := rfl

open Classical in
theorem volume_preserving_homeoRealMixedSpacePolarSpace [NumberField K] :
    MeasurePreserving (homeoRealMixedSpacePolarSpace K) :=
  ((MeasurePreserving.id volume).prod
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ _)).trans <|
      (volume_preserving_prodAssoc.symm).trans <|
        (((MeasurePreserving.id volume).prod (volume_preserving_arrowCongr' _
          (MeasurableEquiv.refl ℝ) (.id volume))).prod (.id volume)).trans <|
            ((volume_preserving_piEquivPiSubtypeProd
              (fun _ : InfinitePlace K ↦ ℝ) (fun w ↦ IsReal w)).symm).prod (.id volume)

@[simps!]
def polarSpaceCoord [NumberField K] : PartialHomeomorph (mixedSpace K) (polarSpace K) :=
    (mixedEmbedding.polarCoord K).transHomeomorph (homeoRealMixedSpacePolarSpace K)

open Classical in
@[simp]
theorem polarSpaceCoord_target' [NumberField K] :
    (polarSpaceCoord K).target =
      (Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ioi 0) ×ˢ
        (Set.univ.pi fun _ ↦ Set.Ioo (-π) π) := by
  ext
  simp_rw [polarSpaceCoord_target, Set.mem_preimage, homeoRealMixedSpacePolarSpace_symm_apply,
    Set.mem_prod, Set.mem_univ, true_and, Set.mem_univ_pi, Set.mem_ite_univ_left,
    not_isReal_iff_isComplex, Subtype.forall, Complex.polarCoord_target, Set.mem_prod, forall_and]

section integrals

open Classical

variable [NumberField K]

theorem integral_comp_polarSpaceCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedSpace K → E) :
    ∫ x in (polarSpaceCoord K).target,
      (∏ w : {w // IsComplex w}, x.1 w.1) • f ((polarSpaceCoord K).symm x) = ∫ x, f x := by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setIntegral_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding,
    ← mixedEmbedding.integral_comp_polarCoord_symm, polarSpaceCoord_target,
    ← Homeomorph.image_eq_preimage, Homeomorph.preimage_image, mixedEmbedding.polarCoord_target]
  simp_rw [polarSpaceCoord_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_of_isReal,
    homeoRealMixedSpacePolarSpace_apply_fst_of_isComplex, homeoRealMixedSpacePolarSpace_apply_snd]

theorem lintegral_comp_polarSpaceCoord_symm (f : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (polarSpaceCoord K).target,
      (∏ w : {w // IsComplex w}, .ofReal (x.1 w.1)) * f ((polarSpaceCoord K).symm x) =
        ∫⁻ x, f x := by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setLIntegral_comp_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding,
    ← mixedEmbedding.lintegral_comp_polarCoord_symm, polarSpaceCoord_target,
    ← Homeomorph.image_eq_preimage, Homeomorph.preimage_image, mixedEmbedding.polarCoord_target]
  simp_rw [polarSpaceCoord_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_of_isReal,
    homeoRealMixedSpacePolarSpace_apply_fst_of_isComplex, homeoRealMixedSpacePolarSpace_apply_snd]

end integrals

abbrev realSpace := InfinitePlace K → ℝ

variable {K}

def mixedSpaceOfRealSpace : realSpace K →L[ℝ] mixedSpace K := by
  refine ContinuousLinearMap.prod ?_ ?_
  · refine ContinuousLinearMap.pi fun w ↦ ?_
    refine ContinuousLinearMap.proj w.1
  · refine ContinuousLinearMap.pi fun w ↦ ?_
    refine ContinuousLinearMap.comp ?_ (ContinuousLinearMap.proj w.1)
    exact Complex.ofRealCLM

@[simp]
theorem mixedSpaceOfRealSpace_apply (x : realSpace K) :
    mixedSpaceOfRealSpace x = ⟨fun w ↦ x w.1, fun w ↦ x w.1⟩ := rfl

variable (K) in
theorem injective_mixedSpaceOfRealSpace :
    Function.Injective (mixedSpaceOfRealSpace : realSpace K → mixedSpace K) := by
  refine (injective_iff_map_eq_zero mixedSpaceOfRealSpace).mpr fun _ h ↦ ?_
  rw [mixedSpaceOfRealSpace_apply, Prod.mk_eq_zero, funext_iff, funext_iff] at h
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · exact h.1 ⟨w, hw⟩
  · exact Complex.ofReal_inj.mp <| h.2 ⟨w, hw⟩

open Classical in
abbrev normAtComplexPlaces (x : mixedSpace K) : realSpace K :=
    fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else normAtPlace w x

@[simp]
theorem normAtComplexPlaces_apply_of_isReal {x : mixedSpace K} (w : {w // IsReal w}) :
    normAtComplexPlaces x w = x.1 w := by
  rw [normAtComplexPlaces, dif_pos]

@[simp]
theorem normAtComplexPlaces_apply_of_isComplex {x : mixedSpace K} (w : {w // IsComplex w}) :
    normAtComplexPlaces x w = ‖x.2 w‖ := by
  rw [normAtComplexPlaces, dif_neg (not_isReal_iff_isComplex.mpr w.prop),
    normAtPlace_apply_of_isComplex]

theorem normAtComplexPlaces_eq_normAtComplexPlaces_iff {x y : mixedSpace K} :
    normAtComplexPlaces x = normAtComplexPlaces y ↔
      (x.1, fun w ↦ (‖x.2 w‖ : ℂ)) = (y.1, fun w ↦ (‖y.2 w‖ : ℂ)) := by
  simp [(injective_mixedSpaceOfRealSpace K).eq_iff.symm, mixedSpaceOfRealSpace]

open Classical in
abbrev realSpaceNormAtComplexPlaces (x : realSpace K) : realSpace K :=
    fun w ↦ if w.IsReal then x w else ‖x w‖

theorem realSpaceNormAtComplexPlaces_apply_of_isReal {x : realSpace K} (w : {w // IsReal w}) :
    realSpaceNormAtComplexPlaces x w = x w.1 := by
  rw [realSpaceNormAtComplexPlaces, if_pos w.prop]

theorem realSpaceNormAtComplexPlaces_apply_of_isComplex {x : realSpace K} (w : {w // IsComplex w}) :
    realSpaceNormAtComplexPlaces x w  = ‖x w.1‖ := by
  rw [realSpaceNormAtComplexPlaces, if_neg (not_isReal_iff_isComplex.mpr w.prop)]

theorem normAtComplexPlaces_mixedSpaceOfReal (x : realSpace K) :
    normAtComplexPlaces (mixedSpaceOfRealSpace x) = realSpaceNormAtComplexPlaces x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [mixedSpaceOfRealSpace_apply, normAtComplexPlaces_apply_of_isReal ⟨w, hw⟩,
      realSpaceNormAtComplexPlaces_apply_of_isReal ⟨w, hw⟩]
  · rw [mixedSpaceOfRealSpace_apply, normAtComplexPlaces_apply_of_isComplex ⟨w, hw⟩,
      realSpaceNormAtComplexPlaces_apply_of_isComplex ⟨w, hw⟩, Complex.norm_real]

theorem normMapComplex_polarSpaceCoord [NumberField K] {x : polarSpace K} :
    normAtComplexPlaces ((polarSpaceCoord K).symm x) = realSpaceNormAtComplexPlaces x.1 := by
  ext w
  simp_rw [polarSpaceCoord_symm_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtComplexPlaces_apply_of_isReal ⟨w, hw⟩,
      realSpaceNormAtComplexPlaces_apply_of_isReal ⟨w, hw⟩]
  · simp_rw [normAtComplexPlaces_apply_of_isComplex ⟨w, hw⟩,
      realSpaceNormAtComplexPlaces_apply_of_isComplex ⟨w, hw⟩, Pi.map_apply, Complex.norm_eq_abs,
      Complex.abs_polarCoord_symm, Real.norm_eq_abs]

open scoped ComplexOrder

variable {A : Set (mixedSpace K)}

open Classical in
private theorem volume_eq_two_pi_pow_mul_integral₁ (hA : ∀ x, x ∈ A ↔ ⟨x.1, fun w ↦ ‖x.2 w‖⟩ ∈ A) :
    normAtComplexPlaces '' A =
      (mixedSpaceOfRealSpace⁻¹' A) ∩
        Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ici 0 := by
  ext x
  simp_rw [Set.mem_inter_iff, Set.mem_image, Set.mem_preimage, mixedSpaceOfRealSpace_apply,
    Set.mem_univ_pi, Set.mem_ite_univ_left, not_isReal_iff_isComplex]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha₁, ha₂⟩
    refine ⟨?_, ?_⟩
    · rw [← ha₂]
      simp_rw [normAtComplexPlaces_apply_of_isReal, normAtComplexPlaces_apply_of_isComplex]
      rwa [← hA]
    · intro w hw
      rw [← ha₂, normAtComplexPlaces_apply_of_isComplex ⟨w, hw⟩]
      exact norm_nonneg _
  · rintro ⟨h₁, h₂⟩
    have hx {w : {w // IsComplex w}} : ‖x w.1‖ = x w.1 := Real.norm_of_nonneg (h₂ w.1 w.prop)
    refine ⟨⟨fun w ↦ x w, fun w ↦ ‖x w‖⟩, ?_, ?_⟩
    · simp_rw [hx]
      exact h₁
    · ext w
      obtain hw | hw := isReal_or_isComplex w
      · rw [normAtComplexPlaces_apply_of_isReal ⟨w, hw⟩]
      · rw [normAtComplexPlaces_apply_of_isComplex ⟨w, hw⟩, Complex.norm_real, norm_norm, hx]

private theorem volume_eq_two_pi_pow_mul_integral₂ (hA : ∀ x, x ∈ A ↔ ⟨x.1, fun w ↦ ‖x.2 w‖⟩ ∈ A) :
    realSpaceNormAtComplexPlaces ⁻¹' (normAtComplexPlaces '' A) = mixedSpaceOfRealSpace⁻¹' A := by
    ext x
    rw [Set.mem_preimage, Set.mem_preimage, Set.mem_image, hA]
    simp_rw [← normAtComplexPlaces_mixedSpaceOfReal, normAtComplexPlaces_eq_normAtComplexPlaces_iff]
    refine ⟨fun ⟨a, ha₁, ha₂⟩ ↦ ?_, fun h ↦ ?_⟩
    · rwa [← ha₂, ← hA]
    · exact ⟨_, h, by simp⟩

open Classical in
theorem volume_eq_two_pi_pow_mul_integral [NumberField K]
    (hA : ∀ x, x ∈ A ↔ ⟨x.1, fun w ↦ ‖x.2 w‖⟩ ∈ A) (hm : MeasurableSet A) :
    volume A = .ofReal (2 * π) ^ nrComplexPlaces K *
      ∫⁻ x in normAtComplexPlaces '' A, ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1) := by
  have hm' : MeasurableSet (realSpaceNormAtComplexPlaces ⁻¹' (normAtComplexPlaces '' A)) := by
    rw [volume_eq_two_pi_pow_mul_integral₂ hA]
    convert hm.preimage mixedSpaceOfRealSpace.measurable
  have hA' : normAtComplexPlaces ⁻¹' (normAtComplexPlaces '' A) = A := by
    refine subset_antisymm (fun x ⟨a, ha₁, ha₂⟩ ↦ ?_) (Set.subset_preimage_image _ _)
    rw [normAtComplexPlaces_eq_normAtComplexPlaces_iff] at ha₂
    rwa [hA, ← ha₂, ← hA]
  have h_ind {x} : (A.indicator 1 x : ℝ≥0∞) =
      (normAtComplexPlaces '' A).indicator 1 (normAtComplexPlaces x) := by
    simp_rw [← Set.indicator_comp_right, Function.comp_def, Pi.one_def, hA']
  rw [← lintegral_indicator_one hm]
  simp_rw [h_ind, ← lintegral_comp_polarSpaceCoord_symm, polarSpaceCoord_target']
  simp_rw [← Set.indicator_const_mul, Pi.one_apply, mul_one, normMapComplex_polarSpaceCoord]

  rw [Measure.volume_eq_prod, setLIntegral_prod]
--  rw [← Measure.prod_restrict]
--  rw [lintegral_prod _]
  · simp_rw [lintegral_const, restrict_apply MeasurableSet.univ, Set.univ_inter, volume_pi,
      Measure.pi_pi, volume_Ioo, sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ]
    rw [lintegral_mul_const' _ _ (ne_of_beq_false rfl).symm, ← volume_pi, mul_comm]
    simp_rw [← Set.indicator_comp_right, Function.comp_def]
    erw [setLIntegral_indicator hm']
    have h₁ : (realSpaceNormAtComplexPlaces⁻¹' (normAtComplexPlaces '' A) ∩
        Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ici 0) =
        normAtComplexPlaces '' A := by
      rw [volume_eq_two_pi_pow_mul_integral₂ hA, volume_eq_two_pi_pow_mul_integral₁ hA]
    have h₂ :
        (Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ioi 0 : Set (InfinitePlace K → ℝ))
          =ᵐ[volume] (Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ici 0) := by
      refine Measure.ae_eq_set_pi fun w _ ↦ ?_
      split_ifs
      · exact ae_eq_rfl
      · exact Ioi_ae_eq_Ici
    rw [setLIntegral_congr (h₁ ▸ ae_eq_set_inter ae_eq_rfl h₂), mul_comm]
  · refine (Measurable.indicator (by fun_prop) (hm'.preimage measurable_fst)).aemeasurable

abbrev normAtAllPlaces (x : mixedSpace K) : realSpace K :=
    fun w ↦ normAtPlace w x

@[simp]
theorem normAtAllPlaces_apply (x : mixedSpace K) (w : InfinitePlace K) :
    normAtAllPlaces x w = normAtPlace w x := rfl


/-- The set of points in the realSpace that are equal to `0` at a fixed place has
volume zero. -/
theorem realSpace.volume_eq_zero [NumberField K] (w : InfinitePlace K) :
    volume ({x : realSpace K | x w = 0}) = 0 := by
  let A : AffineSubspace ℝ (realSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x w = 0}, by aesop⟩, rfl⟩ (by aesop))
  convert Measure.addHaar_affineSubspace volume A fun h ↦ ?_
  simpa [A] using (h ▸ Set.mem_univ _ : 1 ∈ A)

open Classical in
theorem volume_eq_two_pow_mul_two_pi_pow_mul_integral [NumberField K]
    (hA : ∀ x, x ∈ A ↔ ⟨fun w ↦ |x.1 w|, fun w ↦ ‖x.2 w‖⟩ ∈ A) (hm : MeasurableSet A) :
    volume A = 2 ^ nrRealPlaces K * .ofReal (2 * π) ^ nrComplexPlaces K *
      ∫⁻ x in normAtAllPlaces '' A, ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1) := by
  have hA₁ (x : mixedSpace K) : x ∈ A ↔ (fun w ↦ |x.1 w|, x.2) ∈ A := by
    nth_rewrite 2 [hA]
    simp_rw [abs_abs]
    exact hA x
  have hA₂ (x : mixedSpace K) : x ∈ A ↔ ⟨x.1, fun w ↦ ‖x.2 w‖⟩ ∈ A := by
    nth_rewrite 2 [hA]
    simp_rw [Complex.norm_real, norm_norm]
    exact hA x
  rw [volume_eq_two_pow_mul_volume_plusPart _ _ hm, volume_eq_two_pi_pow_mul_integral _
    (measurableSet_plusPart hm)]
  · have : normAtAllPlaces '' A =ᵐ[volume] normAtComplexPlaces '' plusPart A := by
      have : normAtAllPlaces '' A ∩ (⋂ w : {w // IsReal w}, {x | x w.1 ≠ 0}) =
          normAtComplexPlaces '' plusPart A := by
        ext x
        simp_rw [Set.mem_inter_iff, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
        refine ⟨?_, ?_⟩
        · rintro ⟨⟨a, h₁, rfl⟩, h₂⟩
          refine ⟨⟨fun w ↦ |a.1 w|, a.2⟩, ⟨?_, ?_⟩, ?_⟩
          · rwa [← hA₁]
          · intro w
            rw [abs_pos]
            simp_rw [Set.mem_iInter,  Set.mem_setOf_eq] at h₂
            have := h₂ w
            rwa [normAtAllPlaces_apply,
              normAtPlace_apply_of_isReal w.prop, norm_ne_zero_iff] at this
          · ext w
            obtain hw | hw := isReal_or_isComplex w
            · rw [normAtAllPlaces, normAtPlace_apply_of_isReal hw, Real.norm_eq_abs,
                normAtComplexPlaces_apply_of_isReal ⟨w, hw⟩]
            · rw [normAtAllPlaces, normAtPlace_apply_of_isComplex hw,
                normAtComplexPlaces_apply_of_isComplex ⟨w, hw⟩]
        · rintro ⟨a, ⟨h₁, h₂⟩, rfl⟩
          refine ⟨⟨⟨a.1, fun w ↦ ‖a.2 w‖⟩, ?_, ?_⟩, ?_⟩
          · rwa [← hA₂]
          · ext w
            obtain hw | hw := isReal_or_isComplex w
            · rw [normAtAllPlaces, normAtPlace_apply_of_isReal hw,
                normAtComplexPlaces_apply_of_isReal ⟨w, hw⟩, Real.norm_of_nonneg (h₂ ⟨w, hw⟩).le]
            · rw [normAtAllPlaces, normAtPlace_apply_of_isComplex hw,
                normAtComplexPlaces_apply_of_isComplex ⟨w, hw⟩, Complex.norm_real, norm_norm]
          · rw [Set.mem_iInter]
            intro w
            rw [Set.mem_setOf_eq, normAtComplexPlaces_apply_of_isReal]
            exact (h₂ w).ne'
      refine ae_eq_trans (inter_ae_eq_left_of_ae_eq_univ ?_).symm (Eq.eventuallyEq this)
      simp_rw [ae_eq_univ, Set.compl_iInter, measure_iUnion_null_iff]
      intro w
      rw [show {x : realSpace K | x w.1 ≠ 0}ᶜ = {x | x w.1 = 0} by ext; simp]
      exact realSpace.volume_eq_zero w.1
    rw [mul_assoc, setLIntegral_congr this]
  · intro x
    rw [Set.mem_inter_iff, Set.mem_inter_iff]
    rw [← hA₂]
    simp
  · exact hA₁

end polarSpace

end NumberField.mixedEmbedding
