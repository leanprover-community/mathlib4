/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Polar coordinate change of variables for the mixed space of a number field

We define two polar coordinate changes of variables for the mixed space `ℝ^r₁ × ℂ^r₂` associated
to a number field `K` of signature `(r₁, r₂)`. The first one is `mixedEmbedding.polarCoord` and has
value in the `realMixedSpace K` defined as `ℝ^r₁ × (ℝ ⨯ ℝ)^r₂`, the second is
`mixedEmbedding.polarSpaceCoord` and has value in the `polarSpace K` defined as `ℝ^(r₁+r₂) × ℝ^r₂`.

## Main definitions and results

* `mixedEmbedding.polarCoord`: the polar coordinate change of variables between the mixed
  space `ℝ^r₁ × ℂ^r₂` and `ℝ^r₁ × (ℝ × ℝ)^r₂` defined as the identity on the first component and
  mapping `(zᵢ)ᵢ` to `(‖zᵢ‖, Arg zᵢ)ᵢ` on the second component.

* `mixedEmbedding.integral_comp_polarCoord_symm`: the change of variables formula for
  `mixedEmbedding.polarCoord`

* `mixedEmbedding.polarSpaceCoord`: the polar coordinate change of variables between the mixed
  space `ℝ^r₁ × ℂ^r₂` and the polar space `ℝ^(r₁ + r₂) × ℝ^r₂` defined by sending `x` to
  `x w` or `‖x w‖` depending on wether `w` is real or complex for the first component, and
  to `Arg (x w)`, `w` complex, for the second component.

* `mixedEmbedding.integral_comp_polarSpaceCoord_symm`: the change of variables formula for
  `mixedEmbedding.polarSpaceCoord`

-/

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding ENNReal MeasureTheory
  MeasureTheory.Measure Real

noncomputable section realMixedSpace

/--
The real mixed space `ℝ^r₁ × (ℝ × ℝ)^r₂` with `(r₁, r₂)` the signature of `K`.
-/
abbrev realMixedSpace :=
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ)

/--
The natural homeomorphism between the mixed space `ℝ^r₁ × ℂ^r₂` and the real mixed space
`ℝ^r₁ × (ℝ × ℝ)^r₂`.
-/
noncomputable def mixedSpaceToRealMixedSpace : mixedSpace K ≃ₜ realMixedSpace K :=
  (Homeomorph.refl _).prodCongr <| .piCongrRight fun _ ↦ Complex.equivRealProdCLM.toHomeomorph

@[simp]
theorem mixedSpaceToRealMixedSpace_apply (x : mixedSpace K) :
    mixedSpaceToRealMixedSpace K x = (x.1, fun w ↦ Complex.equivRealProd (x.2 w)) := rfl

variable [NumberField K]

open scoped Classical in
theorem volume_preserving_mixedSpaceToRealMixedSpace_symm :
    MeasurePreserving (mixedSpaceToRealMixedSpace K).symm :=
  (MeasurePreserving.id _).prod <|
    volume_preserving_pi fun _ ↦  Complex.volume_preserving_equiv_real_prod.symm

open scoped Classical in
instance : IsAddHaarMeasure (volume : Measure (realMixedSpace K)) := prod.instIsAddHaarMeasure _ _

/--
The polar coordinate partial homeomorphism of `ℝ^r₁ × (ℝ × ℝ)^r₂` defined as the identity on
the first component and mapping `(rᵢ cos θᵢ, rᵢ sin θᵢ)ᵢ` to `(rᵢ, θᵢ)ᵢ` on the second component.
-/
@[simps! apply target]
def polarCoordReal : PartialHomeomorph (realMixedSpace K) (realMixedSpace K) :=
  (PartialHomeomorph.refl _).prod (PartialHomeomorph.pi fun _ ↦ polarCoord)

theorem measurable_polarCoordReal_symm :
    Measurable (polarCoordReal K).symm := by
  refine measurable_fst.prodMk <| Measurable.comp ?_ measurable_snd
  exact measurable_pi_lambda _
    fun _ ↦ continuous_polarCoord_symm.measurable.comp (measurable_pi_apply _)

theorem polarCoordReal_source :
    (polarCoordReal K).source = Set.univ ×ˢ (Set.univ.pi fun _ ↦ polarCoord.source) := rfl

private theorem abs_of_mem_polarCoordReal_target {x : realMixedSpace K}
    (hx : x ∈ (polarCoordReal K).target) (w : {w // IsComplex w}) :
    |(x.2 w).1| = (x.2 w).1 :=
  abs_of_pos (hx.2 w trivial).1

open ContinuousLinearMap in
/--
The derivative of `polarCoordReal.symm`, see `hasFDerivAt_polarCoordReal_symm`.
-/
def FDerivPolarCoordRealSymm : realMixedSpace K → realMixedSpace K →L[ℝ] realMixedSpace K :=
  fun x ↦ (fst ℝ _ _).prod <| (fderivPiPolarCoordSymm x.2).comp (snd ℝ _ _)

theorem hasFDerivAt_polarCoordReal_symm (x : realMixedSpace K) :
    HasFDerivAt (polarCoordReal K).symm (FDerivPolarCoordRealSymm K x) x := by
  classical
  exact (hasFDerivAt_id x.1).prodMap x (hasFDerivAt_pi_polarCoord_symm x.2)

open scoped Classical in
theorem det_fderivPolarCoordRealSymm (x : realMixedSpace K) :
    (FDerivPolarCoordRealSymm K x).det = ∏ w : {w // IsComplex w}, (x.2 w).1 := by
  have : (FDerivPolarCoordRealSymm K x).toLinearMap =
      LinearMap.prodMap (LinearMap.id) (fderivPiPolarCoordSymm x.2).toLinearMap := rfl
  rw [ContinuousLinearMap.det, this, LinearMap.det_prodMap, LinearMap.det_id, one_mul,
    ← ContinuousLinearMap.det, det_fderivPiPolarCoordSymm]

open scoped Classical in
theorem polarCoordReal_symm_target_ae_eq_univ :
    (polarCoordReal K).symm '' (polarCoordReal K).target =ᵐ[volume] Set.univ := by
  rw [← Set.univ_prod_univ, volume_eq_prod, (polarCoordReal K).symm_image_target_eq_source,
    polarCoordReal_source, ← polarCoord.symm_image_target_eq_source, ← Set.piMap_image_univ_pi]
  exact set_prod_ae_eq (by rfl) pi_polarCoord_symm_target_ae_eq_univ

open scoped Classical in
theorem integral_comp_polarCoordReal_symm  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : realMixedSpace K → E) :
    ∫ x in (polarCoordReal K).target, (∏ w : {w // IsComplex w}, (x.2 w).1) •
      f ((polarCoordReal K).symm x) = ∫ x, f x := by
  rw [← setIntegral_univ (f := f), ← setIntegral_congr_set
    (polarCoordReal_symm_target_ae_eq_univ K), integral_image_eq_integral_abs_det_fderiv_smul
    volume (polarCoordReal K).open_target.measurableSet
    (fun x _ ↦ (hasFDerivAt_polarCoordReal_symm K x).hasFDerivWithinAt)
    (polarCoordReal K).symm.injOn f]
  refine setIntegral_congr_fun (polarCoordReal K).open_target.measurableSet fun x hx ↦ ?_
  simp_rw [det_fderivPolarCoordRealSymm, Finset.abs_prod, abs_of_mem_polarCoordReal_target K hx]

open scoped Classical in
theorem lintegral_comp_polarCoordReal_symm (f : realMixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (polarCoordReal K).target, (∏ w : {w // IsComplex w}, .ofReal (x.2 w).1) *
      f ((polarCoordReal K).symm x) = ∫⁻ x, f x := by
  rw [← setLIntegral_univ f, ← setLIntegral_congr (polarCoordReal_symm_target_ae_eq_univ K),
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (polarCoordReal K).open_target.measurableSet
    (fun x _ ↦ (hasFDerivAt_polarCoordReal_symm K x).hasFDerivWithinAt)
    (polarCoordReal K).symm.injOn f]
  refine setLIntegral_congr_fun (polarCoordReal K).open_target.measurableSet ?_
  filter_upwards with x hx
  simp_rw [det_fderivPolarCoordRealSymm, Finset.abs_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦
    abs_nonneg _), abs_of_mem_polarCoordReal_target K hx]

end realMixedSpace

section mixedSpace

variable [NumberField K]

/--
The polar coordinate partial homeomorphism between the mixed space `ℝ^r₁ × ℂ^r₂` and
`ℝ^r₁ × (ℝ × ℝ)^r₂` defined as the identity on the first component and mapping `(zᵢ)ᵢ` to
`(‖zᵢ‖, Arg zᵢ)ᵢ` on the second component.
-/
@[simps!]
protected noncomputable def polarCoord : PartialHomeomorph (mixedSpace K) (realMixedSpace K) :=
  (PartialHomeomorph.refl _).prod (PartialHomeomorph.pi fun _ ↦ Complex.polarCoord)

theorem polarCoord_target_eq_polarCoordReal_target :
    (mixedEmbedding.polarCoord K).target = (polarCoordReal K).target := rfl

theorem polarCoord_symm_eq :
    (mixedEmbedding.polarCoord K).symm =
      (mixedSpaceToRealMixedSpace K).symm ∘ (polarCoordReal K).symm := rfl

theorem measurable_polarCoord_symm :
    Measurable (mixedEmbedding.polarCoord K).symm := by
  rw [polarCoord_symm_eq]
  exact (Homeomorph.measurable _).comp (measurable_polarCoordReal_symm K)

theorem normAtPlace_polarCoord_symm_of_isReal (x : realMixedSpace K) {w : InfinitePlace K}
    (hw : IsReal w) :
    normAtPlace w ((mixedEmbedding.polarCoord K).symm x) = ‖x.1 ⟨w, hw⟩‖ := by
  simp [normAtPlace_apply_of_isReal hw]

theorem normAtPlace_polarCoord_symm_of_isComplex (x : realMixedSpace K)
    {w : InfinitePlace K} (hw : IsComplex w) :
    normAtPlace w ((mixedEmbedding.polarCoord K).symm x) = ‖(x.2 ⟨w, hw⟩).1‖ := by
  simp [normAtPlace_apply_of_isComplex hw]

open scoped Classical in
protected theorem integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedSpace K → E) :
    ∫ x in (mixedEmbedding.polarCoord K).target,
      (∏ w : {w // IsComplex w}, (x.2 w).1) • f ((mixedEmbedding.polarCoord K).symm x) =
        ∫ x, f x := by
  rw [← (volume_preserving_mixedSpaceToRealMixedSpace_symm K).integral_comp
    (mixedSpaceToRealMixedSpace K).symm.measurableEmbedding, ← integral_comp_polarCoordReal_symm,
    polarCoord_target_eq_polarCoordReal_target, polarCoord_symm_eq, Function.comp_def]

open scoped Classical in
protected theorem lintegral_comp_polarCoord_symm (f : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (mixedEmbedding.polarCoord K).target, (∏ w : {w // IsComplex w}, .ofReal (x.2 w).1) *
      f ((mixedEmbedding.polarCoord K).symm x) = ∫⁻ x, f x := by
  rw [← ( volume_preserving_mixedSpaceToRealMixedSpace_symm K).lintegral_comp_emb
    (mixedSpaceToRealMixedSpace K).symm.measurableEmbedding, ← lintegral_comp_polarCoordReal_symm,
    polarCoord_target_eq_polarCoordReal_target, polarCoord_symm_eq, Function.comp_def]

end mixedSpace

noncomputable section polarSpace

open MeasurableEquiv

/--
The space `ℝ^(r₁+r₂) × ℝ^r₂`, it is homeomorph to the `realMixedSpace`, see
`homeoRealMixedSpacePolarSpace`.
-/
abbrev polarSpace := ((InfinitePlace K) → ℝ) × ({w : InfinitePlace K // w.IsComplex} → ℝ)

open scoped Classical in
/--
The measurable equivalence between the `realMixedSpace` and the `polarSpace`. It is actually an
homeomorphism, see `homeoRealMixedSpacePolarSpace`, but defining it in this way makes it easier
to prove that it is volume preserving, see `volume_preserving_homeoRealMixedSpacePolarSpace`.
-/
def measurableEquivRealMixedSpacePolarSpace : realMixedSpace K ≃ᵐ polarSpace K :=
  MeasurableEquiv.trans (prodCongr (refl _)
    (arrowProdEquivProdArrow ℝ ℝ _)) <|
    MeasurableEquiv.trans prodAssoc.symm <|
      MeasurableEquiv.trans
        (prodCongr (prodCongr (refl _)
          (arrowCongr' (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex.symm)) (refl _)))
            (refl _))
          (prodCongr (piEquivPiSubtypeProd (fun _ ↦ ℝ) _).symm (refl _))

open scoped Classical in
/--
The homeomorphism between the `realMixedSpace` and the `polarSpace`.
-/
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

open scoped Classical in
theorem homeoRealMixedSpacePolarSpace_apply (x : realMixedSpace K) :
    homeoRealMixedSpacePolarSpace K x =
      ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
        (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩ := rfl

theorem homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal (x : realMixedSpace K)
    (w : {w // IsReal w}) :
    (homeoRealMixedSpacePolarSpace K x).1 w.1 = x.1 w := by
  simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_pos w.prop]

theorem homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex (x : realMixedSpace K)
    (w : {w // IsComplex w}) :
    (homeoRealMixedSpacePolarSpace K x).1 w.1 = (x.2 w).1 := by
  simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_neg (not_isReal_iff_isComplex.mpr w.prop)]

theorem homeoRealMixedSpacePolarSpace_apply_snd (x : realMixedSpace K) (w : {w // IsComplex w}) :
    (homeoRealMixedSpacePolarSpace K x).2 w = (x.2 w).2 := rfl

@[simp]
theorem homeoRealMixedSpacePolarSpace_symm_apply (x : polarSpace K) :
    (homeoRealMixedSpacePolarSpace K).symm x = ⟨fun w ↦ x.1 w, fun w ↦ (x.1 w, x.2 w)⟩ := rfl

open scoped Classical in
theorem volume_preserving_homeoRealMixedSpacePolarSpace [NumberField K] :
    MeasurePreserving (homeoRealMixedSpacePolarSpace K) :=
  ((MeasurePreserving.id volume).prod
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ _)).trans <|
      (volume_preserving_prodAssoc.symm).trans <|
        (((MeasurePreserving.id volume).prod (volume_preserving_arrowCongr' _
          (MeasurableEquiv.refl ℝ) (.id volume))).prod (.id volume)).trans <|
            ((volume_preserving_piEquivPiSubtypeProd
              (fun _ : InfinitePlace K ↦ ℝ) (fun w ↦ IsReal w)).symm).prod (.id volume)

/--
The polar coordinate partial homeomorphism between the mixed space `ℝ^r₁ × ℂ^r₂` and the polar
space `ℝ^(r₁ + r₂) × ℝ^r₂` defined by sending `x` to `x w` or `‖x w‖` depending on wether `w` is
real or complex for the first component, and to `Arg (x w)`, `w` complex, for the second component.
-/
@[simps!]
def polarSpaceCoord [NumberField K] : PartialHomeomorph (mixedSpace K) (polarSpace K) :=
    (mixedEmbedding.polarCoord K).transHomeomorph (homeoRealMixedSpacePolarSpace K)

theorem measurable_polarSpaceCoord_symm [NumberField K] :
    Measurable (polarSpaceCoord K).symm := by
  rw [polarSpaceCoord, PartialHomeomorph.transHomeomorph_symm_apply]
  exact ( measurable_polarCoord_symm K).comp (Homeomorph.measurable _)

open scoped Classical in
theorem polarSpaceCoord_target' [NumberField K] :
    (polarSpaceCoord K).target =
      (Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ioi 0) ×ˢ
        (Set.univ.pi fun _ ↦ Set.Ioo (-π) π) := by
  ext
  simp_rw [polarSpaceCoord_target, Set.mem_preimage, homeoRealMixedSpacePolarSpace_symm_apply,
    Set.mem_prod, Set.mem_univ, true_and, Set.mem_univ_pi, Set.mem_ite_univ_left,
    not_isReal_iff_isComplex, Subtype.forall, Complex.polarCoord_target, Set.mem_prod, forall_and]

open scoped Classical in
theorem integral_comp_polarSpaceCoord_symm [NumberField K] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : mixedSpace K → E) :
    ∫ x in (polarSpaceCoord K).target,
      (∏ w : {w // IsComplex w}, x.1 w.1) • f ((polarSpaceCoord K).symm x) = ∫ x, f x := by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setIntegral_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding,
    ← mixedEmbedding.integral_comp_polarCoord_symm, polarSpaceCoord_target,
    ← Homeomorph.image_eq_preimage, Homeomorph.preimage_image, mixedEmbedding.polarCoord_target]
  simp_rw [polarSpaceCoord_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex, homeoRealMixedSpacePolarSpace_apply_snd]

open scoped Classical in
theorem lintegral_comp_polarSpaceCoord_symm [NumberField K] (f : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (polarSpaceCoord K).target,
      (∏ w : {w // IsComplex w}, .ofReal (x.1 w.1)) * f ((polarSpaceCoord K).symm x) =
        ∫⁻ x, f x := by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setLIntegral_comp_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding,
    ← mixedEmbedding.lintegral_comp_polarCoord_symm, polarSpaceCoord_target,
    ← Homeomorph.image_eq_preimage, Homeomorph.preimage_image, mixedEmbedding.polarCoord_target]
  simp_rw [polarSpaceCoord_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex, homeoRealMixedSpacePolarSpace_apply_snd]

end polarSpace

end NumberField.mixedEmbedding
