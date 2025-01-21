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
    mixedSpaceToRealSpace K x = (x.1, fun w ↦ ((x.2 w).re, (x.2 w).im)) := rfl

variable [NumberField K]

open Classical in
theorem volume_preserving_mixedSpaceToRealSpace_symm :
    MeasurePreserving (mixedSpaceToRealSpace K).symm :=
  (MeasurePreserving.id _).prod <|
    volume_preserving_pi fun _ ↦  Complex.volume_preserving_equiv_real_prod.symm

open Classical in
instance : IsAddHaarMeasure (volume : Measure (realMixedSpace K)) := prod.instIsAddHaarMeasure _ _

@[simps! target]
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
  fun x ↦ (fst ℝ _ _).prod <| (FDerivPiPolarCoordSymm x.2).comp (snd ℝ _ _)

theorem hasFDerivAt_polarCoord₀_symm (x : realMixedSpace K) :
    HasFDerivAt (polarCoord₀ K).symm (FDerivPolarCoord₀Symm K x) x := by
  classical
  exact (hasFDerivAt_id x.1).prodMap x (hasFDerivAt_pi_polarCoord_symm x.2)

open Classical in
theorem det_fderiv_polarCoord₀_symm (x : realMixedSpace K) :
    (FDerivPolarCoord₀Symm K x).det = ∏ w : {w // IsComplex w}, (x.2 w).1 := by
  have : (FDerivPolarCoord₀Symm K x).toLinearMap =
      LinearMap.prodMap (LinearMap.id) (FDerivPiPolarCoordSymm x.2).toLinearMap := rfl
  rw [ContinuousLinearMap.det, this, LinearMap.prodMap_det, LinearMap.det_id, one_mul,
    ← ContinuousLinearMap.det, det_fderiv_pi_polarCoord_symm]

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

@[simps! target]
protected noncomputable def polarCoord : PartialHomeomorph (mixedSpace K) (realMixedSpace K) :=
  (mixedSpaceToRealSpace K).transPartialHomeomorph (polarCoord₀ K)

protected theorem polarCoord_source :
    (mixedEmbedding.polarCoord K).source =
      {x : mixedSpace K | ∀ w, 0 < (x.2 w).re ∨ (x.2 w).im ≠ 0} := by
  unfold mixedEmbedding.polarCoord
  ext
  simp_rw [Homeomorph.transPartialHomeomorph_source, polarCoord₀_source, Set.mem_preimage,
    mixedSpaceToRealSpace_apply, Set.mem_prod, Set.mem_univ, true_and, Set.mem_univ_pi,
    polarCoord_source, Set.mem_union, Set.mem_setOf_eq]

protected theorem polarCoord_symm_apply (x : realMixedSpace K) :
    (mixedEmbedding.polarCoord K).symm x = (x.1, fun w ↦ Complex.polarCoord.symm (x.2 w)) := rfl

open Classical

protected theorem integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedSpace K → E) :
    ∫ x in (mixedEmbedding.polarCoord K).target,
      (∏ w : {w // IsComplex w}, (x.2 w).1) • f ((mixedEmbedding.polarCoord K).symm x) =
        ∫ x, f x := by
  rw [← (volume_preserving_mixedSpaceToRealSpace_symm K).integral_comp
    (mixedSpaceToRealSpace K).symm.measurableEmbedding, ← integral_comp_polarCoord₀_symm]
  rfl

protected theorem lintegral_comp_polarCoord_symm (f : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (mixedEmbedding.polarCoord K).target, (∏ w : {w // IsComplex w}, .ofReal (x.2 w).1) *
      f ((mixedEmbedding.polarCoord K).symm x) = ∫⁻ x, f x := by
  rw [← ( volume_preserving_mixedSpaceToRealSpace_symm K).lintegral_comp_emb
    (mixedSpaceToRealSpace K).symm.measurableEmbedding, ← lintegral_comp_polarCoord₀_symm]
  rfl

private theorem volume_prod_aux {s₁ : Set ({w // IsReal w} → ℝ)}
    {s₂ : Set ({w // IsComplex w} → ℂ)} :
    (mixedEmbedding.polarCoord K).target ∩ (mixedEmbedding.polarCoord K).symm ⁻¹' s₁ ×ˢ s₂ =
      s₁ ×ˢ ((Set.univ.pi fun _ ↦ Set.Ioi 0 ×ˢ Set.Ioo (-π) π) ∩
              (Pi.map fun _ ↦ ↑Complex.polarCoord.symm) ⁻¹' s₂) := by
  rw [show (mixedEmbedding.polarCoord K).symm ⁻¹' s₁ ×ˢ s₂ = s₁ ×ˢ
    (Pi.map (fun _ ↦ Complex.polarCoord.symm) ⁻¹' s₂) by rfl, mixedEmbedding.polarCoord_target,
    Set.prod_inter_prod, Set.univ_inter]

protected theorem volume_prod {s₁ : Set ({w // IsReal w} → ℝ)} {s₂ : Set ({w // IsComplex w} → ℂ)}
    (hs₁ : MeasurableSet s₁) (hs₂ : MeasurableSet s₂) :
    volume (s₁ ×ˢ s₂ : Set (mixedSpace K)) = volume s₁ *
      ∫⁻ x in
        (Set.univ.pi fun _ ↦ Set.Ioi 0 ×ˢ Set.Ioo (-π) π) ∩
          (Pi.map fun _ ↦ Complex.polarCoord.symm) ⁻¹' s₂,
            (∏ w : {w // IsComplex w}, .ofReal (x w).1) := by
  have h_mes : MeasurableSet ((Set.univ.pi fun x ↦ Set.Ioi 0 ×ˢ Set.Ioo (-π) π) ∩
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
    _ =  ∫⁻ (x : realMixedSpace K), (s₁.indicator 1 x.1) *
          (((Set.univ.pi fun x ↦ Set.Ioi 0 ×ˢ Set.Ioo (-π) π) ∩
            (Pi.map fun x ↦ ↑Complex.polarCoord.symm) ⁻¹' s₂).indicator
              (fun p ↦ 1 * ∏ w, .ofReal (p w).1) x.2) := ?_
    _ = volume s₁ * ∫⁻ x in (Set.univ.pi fun x ↦ Set.Ioi 0 ×ˢ Set.Ioo (-π) π) ∩
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
