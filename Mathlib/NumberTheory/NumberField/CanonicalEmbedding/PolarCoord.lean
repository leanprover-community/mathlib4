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
  simp [normAtPlace_apply_isReal hw]

theorem normAtPlace_polarCoord_symm_of_isComplex (x : realMixedSpace K)
    {w : InfinitePlace K} (hw : IsComplex w) :
    normAtPlace w ((mixedEmbedding.polarCoord K).symm x) = ‖(x.2 ⟨w, hw⟩).1‖ := by
  simp [normAtPlace_apply_isComplex hw]

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
def polarCoord' [NumberField K] : PartialHomeomorph (mixedSpace K) (polarSpace K) :=
    (mixedEmbedding.polarCoord K).transHomeomorph (homeoRealMixedSpacePolarSpace K)

open Classical in
@[simp]
theorem polarCoord'_target' [NumberField K] :
    (polarCoord' K).target =
      (Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ioi 0) ×ˢ
        (Set.univ.pi fun _ ↦ Set.Ioo (-π) π) := by
  ext
  simp_rw [polarCoord'_target, Set.mem_preimage, homeoRealMixedSpacePolarSpace_symm_apply,
    Set.mem_prod, Set.mem_univ, true_and, Set.mem_univ_pi, Set.mem_ite_univ_left,
    not_isReal_iff_isComplex, Subtype.forall, Complex.polarCoord_target, Set.mem_prod, forall_and]

section integrals

open Classical

variable [NumberField K]

theorem integral_comp_polarCoord'_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedSpace K → E) :
    ∫ x in (mixedEmbedding.polarCoord' K).target,
      (∏ w : {w // IsComplex w}, x.1 w.1) • f ((polarCoord' K).symm x) = ∫ x, f x := by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setIntegral_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding,
    ← mixedEmbedding.integral_comp_polarCoord_symm, polarCoord'_target,
    ← Homeomorph.image_eq_preimage, Homeomorph.preimage_image, mixedEmbedding.polarCoord_target]
  simp_rw [polarCoord'_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_of_isReal,
    homeoRealMixedSpacePolarSpace_apply_fst_of_isComplex, homeoRealMixedSpacePolarSpace_apply_snd]

theorem lintegral_comp_polarCoord'_symm (f : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (mixedEmbedding.polarCoord' K).target, (∏ w : {w // IsComplex w}, .ofReal (x.1 w.1)) *
      f ((mixedEmbedding.polarCoord' K).symm x) = ∫⁻ x, f x := by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setLIntegral_comp_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding,
    ← mixedEmbedding.lintegral_comp_polarCoord_symm, polarCoord'_target,
    ← Homeomorph.image_eq_preimage, Homeomorph.preimage_image, mixedEmbedding.polarCoord_target]
  simp_rw [polarCoord'_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_of_isReal,
    homeoRealMixedSpacePolarSpace_apply_fst_of_isComplex, homeoRealMixedSpacePolarSpace_apply_snd]

end integrals

variable {K}

open Classical in
abbrev normAtComplexPlaces (x : mixedSpace K) : InfinitePlace K → ℝ :=
    fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else normAtPlace w x

theorem normAtComplexPlaces_apply_of_isReal {x : mixedSpace K} {w : InfinitePlace K}
    (hw : IsReal w) :
    normAtComplexPlaces x w = x.1 ⟨w, hw⟩ := by
  rw [normAtComplexPlaces, dif_pos hw]

theorem normAtComplexPlaces_apply_of_isComplex {x : mixedSpace K} {w : InfinitePlace K}
    (hw : IsComplex w) :
    normAtComplexPlaces x w = ‖x.2 ⟨w, hw⟩‖ := by
  rw [normAtComplexPlaces, dif_neg (not_isReal_iff_isComplex.mpr hw),
    normAtPlace_apply_isComplex hw]

theorem normAtComplexPlaces_eq_normAtComplexPlaces {x y : mixedSpace K} :
    normAtComplexPlaces x = normAtComplexPlaces y ↔
      (x.1, fun w ↦ (‖x.2 w‖ : ℂ)) = (y.1, fun w ↦ (‖y.2 w‖ : ℂ)) := sorry

open Classical in
abbrev normAtComplexPlaces₀ (x : InfinitePlace K → ℝ) : InfinitePlace K → ℝ :=
    fun w ↦ if w.IsReal then x w else ‖x w‖

theorem normAtComplexPlaces₀_apply_of_isReal {x : InfinitePlace K → ℝ} {w : InfinitePlace K}
    (hw : IsReal w) :
    normAtComplexPlaces₀ x w = x w := by
  rw [normAtComplexPlaces₀, if_pos hw]

theorem normAtComplexPlaces₀_apply_of_isComplex {x : InfinitePlace K → ℝ} {w : InfinitePlace K}
    (hw : IsComplex w) :
    normAtComplexPlaces₀ x w  = ‖x w‖ := by
  rw [normAtComplexPlaces₀, if_neg (not_isReal_iff_isComplex.mpr hw)]

theorem measurable_normAtComplexPlaces₀ :
    Measurable (normAtComplexPlaces₀ : (InfinitePlace K → ℝ) → _) := sorry

theorem normMapComplex_polarCoord' [NumberField K] {x : polarSpace K} :
    normAtComplexPlaces ((polarCoord' K).symm x) = normAtComplexPlaces₀ x.1 := by
  ext w
  simp_rw [polarCoord'_symm_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtComplexPlaces_apply_of_isReal hw, normAtComplexPlaces₀_apply_of_isReal hw]
  · simp_rw [normAtComplexPlaces_apply_of_isComplex hw, Pi.map_apply, Complex.norm_eq_abs,
      normAtComplexPlaces₀_apply_of_isComplex hw, Complex.abs_polarCoord_symm, Real.norm_eq_abs]

open Classical in
theorem volume_eq_two_pi_pow_mul_volume_normAtComplexPlaces_image [NumberField K]
  {A : Set (mixedSpace K)} (hA : ∀ x, x ∈ A ↔ (x.1, fun w ↦ ↑‖x.2 w‖) ∈ A) (hm : MeasurableSet A) :
    volume A = .ofReal (2 * π) ^ nrComplexPlaces K *
      ∫⁻ x in normAtComplexPlaces '' A, ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1) := by
  replace hA : (normAtComplexPlaces ⁻¹' (normAtComplexPlaces '' A)) = A := by
    refine subset_antisymm (fun x ⟨a, ha₁, ha₂⟩ ↦ ?_) (Set.subset_preimage_image _ _)
    rw [normAtComplexPlaces_eq_normAtComplexPlaces] at ha₂
    rwa [hA, ← ha₂, ← hA]
  have hm₁ : MeasurableSet (normAtComplexPlaces₀ ⁻¹' (normAtComplexPlaces '' A)) := by
    refine MeasurableSet.preimage ?_ measurable_normAtComplexPlaces₀
    

    sorry
  have h_ind {x} : (A.indicator 1 x : ℝ≥0∞) =
      (normAtComplexPlaces '' A).indicator 1 (normAtComplexPlaces x) := by
    rw [← Set.indicator_comp_right, Pi.one_comp, hA]
  rw [← lintegral_indicator_one hm]
  simp_rw [h_ind, ← lintegral_comp_polarCoord'_symm, polarCoord'_target']
  simp_rw [normMapComplex_polarCoord', ← Set.indicator_const_mul, Pi.one_apply, mul_one]
--  simp_rw [← Set.indicator_comp_right]
  rw [Measure.volume_eq_prod]
  rw [← Measure.prod_restrict]
  rw [lintegral_prod]
  · simp_rw [lintegral_const, restrict_apply MeasurableSet.univ, Set.univ_inter, volume_pi,
      Measure.pi_pi, volume_Ioo, sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ]
    rw [lintegral_mul_const' _ _ (ne_of_beq_false rfl).symm, ← volume_pi]
    simp_rw [← Set.indicator_comp_right, Function.comp_def]
    erw [setLIntegral_indicator hm₁]
    have h₁ : normAtComplexPlaces₀ ⁻¹' (normAtComplexPlaces '' A) ∩
        (Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ici 0) =
          normAtComplexPlaces '' A := by
      sorry
    have h₂ :
        (Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ioi 0 : Set (InfinitePlace K → ℝ))
          =ᵐ[volume] (Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ici 0) := by
      refine Measure.ae_eq_set_pi fun w _ ↦ ?_
      split_ifs
      · exact ae_eq_rfl
      · exact Ioi_ae_eq_Ici
    rw [setLIntegral_congr (h₁ ▸ ae_eq_set_inter ae_eq_rfl h₂), mul_comm]
  · refine Measurable.aemeasurable ?_
    simp_rw [← Set.indicator_comp_right]
    refine Measurable.indicator ?_ ?_
    · fun_prop
    · refine MeasurableSet.preimage ?_ measurable_fst
      exact hm₁

#exit

  let g (x : InfinitePlace K → ℝ) (w : InfinitePlace K) := if w.IsReal then x w else ‖x w‖
  have zap2 {x}: normMapComplex ((polarCoord' K).symm x) = g x.1 := sorry

include hA in
theorem toto {x} :
    (A.indicator 1 x : ℝ≥0∞) = (normMapComplex '' A).indicator 1 (normMapComplex x) := by
  rw [← Set.indicator_comp_right, hA, Pi.one_comp]






  rw [← lintegral_indicator_one]
  simp_rw [toto hA]
  rw [← lintegral_comp_polarCoord'_symm, polarCoord'_target']
  simp_rw [zap2,  ← Set.indicator_const_mul]
  rw [Measure.volume_eq_prod]
  rw [← Measure.prod_restrict]
  rw [lintegral_prod]
  simp_rw [lintegral_const, Pi.one_apply]
  simp_rw [restrict_apply sorry, Set.univ_inter, volume_pi, Measure.pi_pi, volume_Ioo,
    sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ]
  rw [lintegral_mul_const' _ _ sorry]
  simp_rw [← Set.indicator_comp_right g,
--    (fun (x : InfinitePlace K → ℝ) w ↦ if w.IsReal then x w else ‖x w‖),
    Function.comp_def, mul_one]
  rw [← volume_pi]
  have : ∫⁻ (a : InfinitePlace K → ℝ) in
    Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ioi 0,
    (g ⁻¹' (normMapComplex '' A)).indicator (fun _ ↦ ∏ x : { w : InfinitePlace K // w.IsComplex },
      ENNReal.ofReal (a ↑x)) a =
        ∫⁻ (a : InfinitePlace K → ℝ) in Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ioi 0,
      (g ⁻¹' (normMapComplex '' A)).indicator (fun a ↦ ∏ x : { w : InfinitePlace K // w.IsComplex },
      ENNReal.ofReal (a ↑x)) a := by
    congr
  rw [this]
  rw [setLIntegral_indicator]
  have hs {x : InfinitePlace K → ℝ} :
      (∀ w, IsComplex w → 0 ≤ x w) ↔ g x = x := by
    simp [funext_iff, g]
  have {a x} : (normMapComplex a = g x ∧ (∀ (i : InfinitePlace K), i.IsComplex → 0 ≤ x i))
      ↔ normMapComplex a = x := by
    refine ⟨fun ⟨h₁, _⟩ ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
    · rwa [h₁, ← hs]
    · rw [← h, eq_comm, ← hs]
      intro w _
      sorry
    · rw [← h]
      intro w _
      sorry

  have t1 : g ⁻¹' (normMapComplex '' A) ∩
      (Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ici 0) = normMapComplex '' A := by
    ext x
    simp_rw [Set.mem_inter_iff, Set.mem_univ_pi, Set.mem_ite_univ_left, not_isReal_iff_isComplex,
      Set.mem_preimage, Set.mem_Ici, Set.mem_image, ← exists_and_right, and_assoc, this]

  have t2 :
    (Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ici 0 : Set (InfinitePlace K → ℝ))
      =ᵐ[volume] (Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ioi 0) := sorry

  have t3 : g ⁻¹' (normMapComplex '' A) =ᵐ[volume] g ⁻¹' (normMapComplex '' A) := sorry

  have := ae_eq_set_inter t3 t2

  rw [t1] at this
  rw [setLIntegral_congr this.symm]
  ring
  all_goals sorry


abbrev normMap (x : mixedSpace K) : (InfinitePlace K → ℝ) := fun w ↦ normAtPlace w x

variable {A : Set (mixedSpace K)} (hA : normMap⁻¹' (normMap '' A) = A)

include hA in
omit [NumberField K] in
theorem toto {x} :
    (A.indicator 1 x : ℝ≥0∞) = (normMap '' A).indicator 1 (normMap x) := by
  rw [← Set.indicator_comp_right, hA, Pi.one_comp]

theorem zap {x} :
    normMap ((polarCoord' K).symm x) = fun w ↦ ‖x.1 w‖ := by
  ext w
  simp_rw [polarCoord'_symm_apply, normMap]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_isReal hw]
  · simp_rw [normAtPlace_apply_isComplex hw, Pi.map_apply, Complex.norm_eq_abs,
      Complex.abs_polarCoord_symm, Real.norm_eq_abs]

include hA
example :
    volume A = 0 := by
  rw [← lintegral_indicator_one]
  simp_rw [toto hA]
  rw [← lintegral_comp_polarCoord'_symm, polarCoord'_target']
  simp_rw [zap,  ← Set.indicator_const_mul]
  rw [Measure.volume_eq_prod]
  rw [← Measure.prod_restrict]
  rw [lintegral_prod]
  simp_rw [lintegral_const, Pi.one_apply]
  simp_rw [restrict_apply sorry, Set.univ_inter, volume_pi, Measure.pi_pi, volume_Ioo,
    sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ]
  rw [lintegral_mul_const' _ _ sorry]
  simp_rw [← Set.indicator_comp_right (fun (a : InfinitePlace K → ℝ) w ↦ ‖a w‖),
    Function.comp_def, mul_one]
  rw [← volume_pi]
  have : ∫⁻ (a : InfinitePlace K → ℝ) in
    Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ioi 0,
    ((fun a w ↦ ‖a w‖) ⁻¹' (normMap '' A)).indicator (fun _ ↦ ∏ x : { w : InfinitePlace K // w.IsComplex },
      ENNReal.ofReal (a ↑x)) a =
        ∫⁻ (a : InfinitePlace K → ℝ) in Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ioi 0,
      ((fun a w ↦ ‖a w‖) ⁻¹' (normMap '' A)).indicator (fun a ↦ ∏ x : { w : InfinitePlace K // w.IsComplex },
      ENNReal.ofReal (a ↑x)) a := by
    congr
  rw [this]
  rw [setLIntegral_indicator]
  have : (fun a w ↦ ‖a w‖) ⁻¹' (normMap '' A) ∩
      (Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ioi 0) = normMap '' A := by
    ext x
    simp
    refine ⟨fun ⟨⟨w, ⟨a, h1, h2⟩⟩, h3⟩ ↦ ?_, fun h ↦ ?_⟩
    ·
      sorry






end integrals

#exit

omit [NumberField K] in
@[simp]
theorem homeoRealMixedSpacePolarSpace_symm_apply (x : polarSpace K) :
    homeoRealMixedSpacePolarSpace.symm x = ⟨fun w ↦ x.1 w, fun w ↦ (x.1 w, x.2 w)⟩ := rfl

open Classical in
omit [NumberField K] in
theorem homeoRealMixedSpacePolarSpace_apply (x : realMixedSpace K) :
    homeoRealMixedSpacePolarSpace x =
      ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
        (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩ := rfl

open Classical in
theorem volume_preserving_homeoRealMixedSpacePolarSpace :
    MeasurePreserving (homeoRealMixedSpacePolarSpace (K := K)) :=
  ((MeasurePreserving.id volume).prod
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ _)).trans <|
      (volume_preserving_prodAssoc.symm).trans <|
        (((MeasurePreserving.id volume).prod (volume_preserving_arrowCongr' _
          (MeasurableEquiv.refl ℝ) (.id volume))).prod (.id volume)).trans <|
            ((volume_preserving_piEquivPiSubtypeProd
              (fun _ : InfinitePlace K ↦ ℝ) (fun w ↦ IsReal w)).symm).prod (.id volume)


open Classical MeasurableEquiv in
def aux₀ : realMixedSpace K ≃ᵐ polarSpace K :=
  MeasurableEquiv.trans (prodCongr (refl _)
    (arrowProdEquivProdArrow ℝ ℝ _)) <|
    MeasurableEquiv.trans prodAssoc.symm <|
      MeasurableEquiv.trans
        (prodCongr (prodCongr (refl _)
          (arrowCongr' (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex.symm)) (refl _)))
            (refl _))
          (prodCongr (piEquivPiSubtypeProd (fun _ ↦ ℝ) _).symm (refl _))

open Classical in
def aux : realMixedSpace K ≃ₜ polarSpace K :=
{ aux₀ K with
  continuous_toFun := by
    change Continuous fun x : realMixedSpace K ↦  (fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2)
    refine continuous_prod_mk.mpr ⟨continuous_pi_iff.mpr fun w ↦ ?_, by fun_prop⟩
    split_ifs <;> fun_prop
  continuous_invFun := by
    change Continuous fun x : polarSpace K ↦
      (⟨fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩⟩ : realMixedSpace K)
    fun_prop }

variable [NumberField K]

open Classical in
theorem volume_preserving_aux : MeasurePreserving (aux K) :=
  ((MeasurePreserving.id volume).prod
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ _)).trans <|
      (volume_preserving_prodAssoc.symm).trans <|
        (((MeasurePreserving.id volume).prod (volume_preserving_arrowCongr' _
          (MeasurableEquiv.refl ℝ) (.id volume))).prod (.id volume)).trans <|
            ((volume_preserving_piEquivPiSubtypeProd
              (fun _ : InfinitePlace K ↦ ℝ) (fun w ↦ IsReal w)).symm).prod (.id volume)

#exit

protected noncomputable def polarCoord' :
    PartialHomeomorph (mixedSpace K) (polarSpace K) :=
  (mixedSpaceToRealSpace K).transPartialHomeomorph <| (polarCoord₀ K).transHomeomorph (aux K)

theorem toto :
    (mixedEmbedding.polarCoord' K).target =
      (aux K) '' (mixedEmbedding.polarCoord K).target := sorry

open Classical in
protected theorem lintegral_comp_polarCoord_symm' (f : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (mixedEmbedding.polarCoord' K).target, (∏ w : {w // IsComplex w}, .ofReal (x.1 w.1)) *
      f ((mixedEmbedding.polarCoord' K).symm x) = ∫⁻ x, f x := by
  rw [← mixedEmbedding.lintegral_comp_polarCoord_symm]
  have := (volume_preserving_aux K).setLIntegral_comp_emb sorry
  rw [toto]
  rw [← this]
  congr
  sorry

end polarSpace

#exit

noncomputable section normSpace

open MeasurableEquiv


-- Maybe we don't want to give it a name
abbrev normSpace := (InfinitePlace K) → ℝ

def normMap (x : mixedSpace K) : normSpace K := fun w ↦ normAtPlace w x

open Classical in
def aux₀ : realMixedSpace K ≃ᵐ normSpace K × ({w : InfinitePlace K // IsComplex w} → ℝ) :=
  MeasurableEquiv.trans (prodCongr (refl _)
    (arrowProdEquivProdArrow ℝ ℝ _)) <|
    MeasurableEquiv.trans prodAssoc.symm <|
      MeasurableEquiv.trans
        (prodCongr (prodCongr (refl _)
          (arrowCongr' (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex.symm)) (refl _)))
            (refl _))
          (prodCongr (piEquivPiSubtypeProd (fun _ ↦ ℝ) _).symm (refl _))

open Classical in
def aux : realMixedSpace K ≃ₜ normSpace K × ({w : InfinitePlace K // IsComplex w} → ℝ) :=
{ aux₀ K with
  continuous_toFun := by
    change Continuous fun x : realSpace K ↦  (fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2)
    refine continuous_prod_mk.mpr ⟨continuous_pi_iff.mpr fun w ↦ ?_, by fun_prop⟩
    split_ifs <;> fun_prop
  continuous_invFun := by
    change Continuous fun x : normSpace K × ({w : InfinitePlace K // IsComplex w} → ℝ) ↦
      (⟨fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩⟩ : realSpace K)
    fun_prop }


protected noncomputable def polarCoord' :
    PartialHomeomorph (mixedSpace K) (normSpace K × ({w : InfinitePlace K // IsComplex w} → ℝ)) :=
  (mixedSpaceToRealSpace K).transPartialHomeomorph <| (polarCoord₀ K).transHomeomorph (aux K)

variable [NumberField K]

open Classical

theorem volume_preserving_aux : MeasurePreserving (aux K) :=
  ((MeasurePreserving.id volume).prod
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ _)).trans <|
      (volume_preserving_prodAssoc.symm).trans <|
        (((MeasurePreserving.id volume).prod (volume_preserving_arrowCongr' _
          (MeasurableEquiv.refl ℝ) (.id volume))).prod (.id volume)).trans <|
            ((volume_preserving_piEquivPiSubtypeProd
              (fun _ : InfinitePlace K ↦ ℝ) (fun w ↦ IsReal w)).symm).prod (.id volume)

protected noncomputable def polarCoord' :
    PartialHomeomorph (mixedSpace K) (normSpace K × ({w : InfinitePlace K // IsComplex w} → ℝ)) :=
  (mixedSpaceToRealSpace K).transPartialHomeomorph <| (polarCoord₀ K).transHomeomorph (aux K)

protected theorem lintegral_comp_polarCoord_symm' (f : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (mixedEmbedding.polarCoord' K).target, (∏ w : {w // IsComplex w}, .ofReal (x.1 w.1)) *
      f ((mixedEmbedding.polarCoord' K).symm x) = ∫⁻ x, f x := by
  sorry
--  rw [← ( volume_preserving_mixedSpaceToRealSpace_symm K).lintegral_comp_emb
--    (mixedSpaceToRealSpace K).symm.measurableEmbedding, ← lintegral_comp_polarCoord₀_symm]
--  rfl

example (s : Set (mixedSpace K)) (hs₁ : MeasurableSet s)
    (hs₂ : s = (normMap K) ⁻¹' (normMap K '' s)) :
    volume s = 2 ^ nrRealPlaces K * (2 * NNReal.pi) ^ nrComplexPlaces K  *
      ∫⁻ x in (normMap K '' s), ∏ w : {w // IsComplex w}, .ofReal (x w.1) := by
  rw [volume_eq_two_pow_mul_volume_plusPart _ _ hs₁]
  · rw [← lintegral_indicator_one]
    rw [← mixedEmbedding.lintegral_comp_polarCoord_symm', mul_assoc]
    congr





    sorry
  · intro x
    rw [hs₂]
    rw [Set.mem_preimage, Set.mem_preimage]
    have : normMap K x = normMap K (fun w ↦ |x.1 w|, x.2) := by
      ext w
      simp [normMap]
      obtain hw | hw := isReal_or_isComplex w
      · simp [normAtPlace_apply_isReal hw]
      · simp [normAtPlace_apply_isComplex hw]
    rw [this]

end normSpace


end NumberField.mixedEmbedding
