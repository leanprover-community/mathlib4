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
value in `realMixedSpace K` defined as `ℝ^r₁ × (ℝ ⨯ ℝ)^r₂`, the second is
`mixedEmbedding.polarSpaceCoord` and has value in `polarSpace K` defined as `ℝ^(r₁+r₂) × ℝ^r₂`.

The change of variables with the `polarSpace` is useful to compute the volumes of subsets of the
mixed space with enough symmetries, see ...

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
  ((PartialHomeomorph.refl _).prod (PartialHomeomorph.pi fun _ ↦ polarCoord))

theorem measurable_polarCoordReal_symm :
    Measurable (polarCoordReal K).symm := by
  refine measurable_fst.prod_mk <| Measurable.comp ?_ measurable_snd
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

/-- The `realSpace` associated to a number field `K` is the real vector space indexed by the
infinite places of `K`. -/
abbrev realSpace := InfinitePlace K → ℝ

variable {K}

/-- The continuous linear map from `realSpace K` to `mixedSpace K` which is the identity of real
places and the natural map `ℝ → ℂ` at complex places. -/
def mixedSpaceOfRealSpace : realSpace K →L[ℝ] mixedSpace K :=
  .prod (.pi fun w ↦ .proj w.1) (.pi fun w ↦ Complex.ofRealCLM.comp (.proj w.1))

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

open scoped Classical in
/-- The map from the `mixedSpace K` to `realSpace K` that sends the values at complex places
to their norm. -/
abbrev normAtComplexPlaces (x : mixedSpace K) : realSpace K :=
    fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else normAtPlace w x

@[simp]
theorem normAtComplexPlaces_apply_ofIsReal {x : mixedSpace K} (w : {w // IsReal w}) :
    normAtComplexPlaces x w = x.1 w := by
  rw [normAtComplexPlaces, dif_pos]

@[simp]
theorem normAtComplexPlaces_apply_ofIsComplex {x : mixedSpace K} (w : {w // IsComplex w}) :
    normAtComplexPlaces x w = ‖x.2 w‖ := by
  rw [normAtComplexPlaces, dif_neg (not_isReal_iff_isComplex.mpr w.prop),
    normAtPlace_apply_of_isComplex]

theorem normAtComplexPlaces_eq_normAtComplexPlaces_iff {x y : mixedSpace K} :
    normAtComplexPlaces x = normAtComplexPlaces y ↔
      (⟨x.1, fun w ↦ ‖x.2 w‖⟩ : mixedSpace K) = ⟨y.1, fun w ↦ ‖y.2 w‖⟩ := by
  simp [(injective_mixedSpaceOfRealSpace K).eq_iff.symm, mixedSpaceOfRealSpace]

open scoped Classical in
/-- The map on the `realSpace K` that is the identity at real places and the norm at
complex places. -/
abbrev realSpaceNormAtComplexPlaces (x : realSpace K) : realSpace K :=
    fun w ↦ if w.IsReal then x w else ‖x w‖

theorem realSpaceNormAtComplexPlaces_apply_ofIsReal {x : realSpace K} (w : {w // IsReal w}) :
    realSpaceNormAtComplexPlaces x w = x w.1 := by
  rw [realSpaceNormAtComplexPlaces, if_pos w.prop]

theorem realSpaceNormAtComplexPlaces_apply_ofIsComplex {x : realSpace K} (w : {w // IsComplex w}) :
    realSpaceNormAtComplexPlaces x w  = ‖x w.1‖ := by
  rw [realSpaceNormAtComplexPlaces, if_neg (not_isReal_iff_isComplex.mpr w.prop)]

theorem normAtComplexPlaces_mixedSpaceOfReal (x : realSpace K) :
    normAtComplexPlaces (mixedSpaceOfRealSpace x) = realSpaceNormAtComplexPlaces x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [mixedSpaceOfRealSpace_apply, normAtComplexPlaces_apply_ofIsReal ⟨w, hw⟩,
      realSpaceNormAtComplexPlaces_apply_ofIsReal ⟨w, hw⟩]
  · rw [mixedSpaceOfRealSpace_apply, normAtComplexPlaces_apply_ofIsComplex ⟨w, hw⟩,
      realSpaceNormAtComplexPlaces_apply_ofIsComplex ⟨w, hw⟩, Complex.norm_real]

theorem normMapComplex_polarSpaceCoord [NumberField K] {x : polarSpace K} :
    normAtComplexPlaces ((polarSpaceCoord K).symm x) = realSpaceNormAtComplexPlaces x.1 := by
  ext w
  simp_rw [polarSpaceCoord_symm_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtComplexPlaces_apply_ofIsReal ⟨w, hw⟩,
      realSpaceNormAtComplexPlaces_apply_ofIsReal ⟨w, hw⟩]
  · simp_rw [normAtComplexPlaces_apply_ofIsComplex ⟨w, hw⟩,
      realSpaceNormAtComplexPlaces_apply_ofIsComplex ⟨w, hw⟩, Pi.map_apply,
      Complex.norm_polarCoord_symm, Real.norm_eq_abs]

variable {A : Set (mixedSpace K)}

open scoped Classical in
private theorem volume_eq_two_pi_pow_mul_integral_aux₁
    (hA : ∀ x, x ∈ A ↔ ⟨x.1, fun w ↦ ‖x.2 w‖⟩ ∈ A) :
    normAtComplexPlaces '' A =
      (mixedSpaceOfRealSpace⁻¹' A) ∩
        Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ici 0 := by
  ext x
  simp_rw [Set.mem_inter_iff, Set.mem_image, Set.mem_preimage, mixedSpaceOfRealSpace_apply,
    Set.mem_univ_pi, Set.mem_ite_univ_left, not_isReal_iff_isComplex]
  refine ⟨fun ⟨a, ha₁, ha₂⟩ ↦ ⟨?_, fun w hw ↦ ?_⟩, fun ⟨h₁, h₂⟩ ↦
    ⟨⟨fun w ↦ x w, fun w ↦ ‖x w‖⟩, ?_, funext fun w ↦ ?_⟩⟩
  · simpa only [← ha₂, normAtComplexPlaces_apply_ofIsReal, normAtComplexPlaces_apply_ofIsComplex,
      ← hA] using ha₁
  · simpa only [← ha₂, normAtComplexPlaces_apply_ofIsComplex ⟨w, hw⟩] using norm_nonneg _
  · simpa only [← Complex.norm_real] using (hA _).mp h₁
  · obtain hw | hw := isReal_or_isComplex w
    · rw [normAtComplexPlaces_apply_ofIsReal ⟨w, hw⟩]
    · rw [normAtComplexPlaces_apply_ofIsComplex ⟨w, hw⟩, Complex.norm_real, norm_norm,
        Real.norm_of_nonneg (h₂ _ hw)]

private theorem volume_eq_two_pi_pow_mul_integral_aux₂
    (hA : ∀ x, x ∈ A ↔ ⟨x.1, fun w ↦ ‖x.2 w‖⟩ ∈ A) :
    realSpaceNormAtComplexPlaces ⁻¹' (normAtComplexPlaces '' A) = mixedSpaceOfRealSpace⁻¹' A := by
    ext x
    rw [Set.mem_preimage, Set.mem_preimage, Set.mem_image, hA]
    simp_rw [← normAtComplexPlaces_mixedSpaceOfReal, normAtComplexPlaces_eq_normAtComplexPlaces_iff]
    exact ⟨fun ⟨a, ha₁, ha₂⟩ ↦ by rwa [← ha₂, ← hA], fun h ↦ ⟨_, h, by simp⟩⟩

theorem normAtComplexPlaces_preimage_image_eq (hA : ∀ x, x ∈ A ↔ ⟨x.1, fun w ↦ ‖x.2 w‖⟩ ∈ A) :
      normAtComplexPlaces ⁻¹' (normAtComplexPlaces '' A) = A := by
  refine subset_antisymm (fun x ⟨a, ha₁, ha₂⟩ ↦ ?_) (Set.subset_preimage_image _ _)
  rwa [hA, ← normAtComplexPlaces_eq_normAtComplexPlaces_iff.mp ha₂, ← hA]

open scoped Classical in
theorem volume_eq_two_pi_pow_mul_integral [NumberField K]
    (hA : ∀ x, x ∈ A ↔ ⟨x.1, fun w ↦ ‖x.2 w‖⟩ ∈ A) (hm : MeasurableSet A) :
    volume A = .ofReal (2 * π) ^ nrComplexPlaces K *
      ∫⁻ x in normAtComplexPlaces '' A, ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1) := by
  have hm' : MeasurableSet (realSpaceNormAtComplexPlaces ⁻¹' (normAtComplexPlaces '' A)) := by
    rw [volume_eq_two_pi_pow_mul_integral_aux₂ hA]
    convert hm.preimage mixedSpaceOfRealSpace.measurable
  have h_ind {x} : (A.indicator 1 x : ℝ≥0∞) =
      (normAtComplexPlaces '' A).indicator 1 (normAtComplexPlaces x) := by
    simp_rw [← Set.indicator_comp_right, Function.comp_def, Pi.one_def,
      normAtComplexPlaces_preimage_image_eq hA]
  rw [← lintegral_indicator_one hm, ← lintegral_comp_polarSpaceCoord_symm, polarSpaceCoord_target',
    Measure.volume_eq_prod, setLIntegral_prod]
  · simp_rw [h_ind, normMapComplex_polarSpaceCoord, lintegral_const, restrict_apply
      MeasurableSet.univ, Set.univ_inter, volume_pi, Measure.pi_pi, volume_Ioo, sub_neg_eq_add,
      ← two_mul, Finset.prod_const, Finset.card_univ, ← Set.indicator_const_mul,
      ← Set.indicator_comp_right, Function.comp_def, Pi.one_apply, mul_one]
    rw [lintegral_mul_const' _ _ (ne_of_beq_false rfl).symm, mul_comm]
    erw [setLIntegral_indicator hm'] -- rw doesn't work here
    rw [volume_eq_two_pi_pow_mul_integral_aux₁ hA]
    refine congr_arg (_ * ·) <| setLIntegral_congr <| ae_eq_set_inter ?_ ?_
    · rw [← volume_eq_two_pi_pow_mul_integral_aux₁ hA, volume_eq_two_pi_pow_mul_integral_aux₂ hA]
    · refine Measure.ae_eq_set_pi fun w _ ↦ ?_
      split_ifs
      exacts [ae_eq_rfl, Ioi_ae_eq_Ici]
  · exact (Measurable.mul (by fun_prop)
      <| measurable_const.indicator <| hm.preimage (measurable_polarSpaceCoord_symm K)).aemeasurable

abbrev normAtAllPlaces (x : mixedSpace K) : realSpace K :=
    fun w ↦ normAtPlace w x

variable (K) in
theorem continuous_normAtAllPlaces :
    Continuous (normAtAllPlaces : mixedSpace K → realSpace K) :=
  continuous_pi fun _ ↦ continuous_normAtPlace _

@[simp]
theorem normAtAllPlaces_apply (x : mixedSpace K) (w : InfinitePlace K) :
    normAtAllPlaces x w = normAtPlace w x := rfl

theorem normAtAllPlaces_nonneg (x : mixedSpace K) (w : InfinitePlace K) :
    0 ≤ normAtAllPlaces x w := normAtPlace_nonneg _ _

theorem normAtPlace_mixedSpaceOfRealSpace {x : realSpace K} {w : InfinitePlace K} (hx : 0 ≤ x w) :
    normAtPlace w (mixedSpaceOfRealSpace x) = x w := by
  simp only [mixedSpaceOfRealSpace_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw, Real.norm_of_nonneg hx]
  · rw [normAtPlace_apply_of_isComplex hw, Complex.norm_of_nonneg hx]

theorem normAtAllPlaces_image_preimage_of_nonneg {s : Set (realSpace K)}
    (hs : ∀ x ∈ s, ∀ w, 0 ≤ x w) :
    normAtAllPlaces '' (normAtAllPlaces ⁻¹' s) = s := by
  rw [Set.image_preimage_eq_iff]
  rintro x hx
  refine ⟨mixedSpaceOfRealSpace x, funext fun w ↦ ?_⟩
  rw [normAtAllPlaces_apply, normAtPlace_mixedSpaceOfRealSpace (hs x hx w)]

theorem normAtAllPlaces_mixedSpaceOfRealSpace {x : realSpace K} (hx : ∀ w, 0 ≤ x w) :
    normAtAllPlaces (mixedSpaceOfRealSpace x) = x := by
  ext
  rw [normAtAllPlaces_apply, normAtPlace_mixedSpaceOfRealSpace (hx _)]

-- theorem mixedSpaceOfRealSpace_normAtAllPlaces {x : mixedSpace K} (hx : )

theorem normAtAllPlaces_normAtAllPlaces (x : mixedSpace K) :
    normAtAllPlaces (mixedSpaceOfRealSpace (normAtAllPlaces x)) = normAtAllPlaces x :=
  normAtAllPlaces_mixedSpaceOfRealSpace fun _ ↦ (normAtAllPlaces_nonneg _ _)

theorem forall_mem_iff_normAtAllPlaces_mem {s : Set (realSpace K)}
    (hs : A = normAtAllPlaces ⁻¹' s) :
    ∀ x, x ∈ A ↔ mixedSpaceOfRealSpace (normAtAllPlaces x) ∈ A := fun _ ↦ by
  rw [hs, Set.mem_preimage, Set.mem_preimage, normAtAllPlaces_normAtAllPlaces]

theorem mem_iff_normAtAllPlaces_mem_iff :
    (∀ x, x ∈ A ↔ mixedSpaceOfRealSpace (normAtAllPlaces x) ∈ A) ↔
      A = normAtAllPlaces ⁻¹' (normAtAllPlaces '' A) := by
  refine ⟨fun h ↦ ?_, fun h ↦ forall_mem_iff_normAtAllPlaces_mem h⟩
  exact subset_antisymm (Set.subset_preimage_image _ _) fun  x ⟨_, _, h₁⟩ ↦ by rwa [h, ← h₁, ← h]

/-- The set of points in the `realSpace` that are equal to `0` at a fixed place has volume zero. -/
theorem realSpace.volume_eq_zero [NumberField K] (w : InfinitePlace K) :
    volume ({x : realSpace K | x w = 0}) = 0 := by
  let A : AffineSubspace ℝ (realSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x w = 0}, by aesop⟩, rfl⟩ (by aesop))
  convert Measure.addHaar_affineSubspace volume A fun h ↦ ?_
  simpa [A] using (h ▸ Set.mem_univ _ : 1 ∈ A)

theorem volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux₁
    (hA₁ : ∀ x, x ∈ A ↔ mixedSpaceOfRealSpace (normAtAllPlaces x) ∈ A)
    (hA₂ : ∀ x, x ∈ plusPart A ↔ (x.1, fun w ↦ ↑‖x.2 w‖) ∈ plusPart A) :
    normAtAllPlaces '' A ∩ (⋂ w : {w // IsReal w}, {x | x w.1 ≠ 0}) =
      normAtComplexPlaces '' plusPart A := by
  rw [volume_eq_two_pi_pow_mul_integral_aux₁ hA₂]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image, Set.mem_pi, Set.mem_univ,
    Set.mem_ite_univ_left, not_isReal_iff_isComplex, forall_const, Set.mem_iInter, Set.mem_Ici,
    Set.mem_setOf_eq]
  refine ⟨?_, fun ⟨⟨hx₁, hx₂⟩, hx₃⟩ ↦ ⟨⟨mixedSpaceOfRealSpace x, hx₁, ?_⟩, fun w ↦ (hx₂ w).ne'⟩⟩
  · rintro ⟨⟨a, ha₁, rfl⟩, ha₂⟩
    exact ⟨⟨by rwa [← hA₁], fun w ↦ lt_of_le_of_ne' (normAtPlace_nonneg _ _) (ha₂ w)⟩,
      fun _ _ ↦ normAtPlace_nonneg _ _⟩
  · ext w
    rw [normAtAllPlaces_apply, normAtPlace_mixedSpaceOfRealSpace]
    obtain hw | hw := isReal_or_isComplex w
    · exact (hx₂ ⟨w, hw⟩).le
    · exact hx₃ w hw

open scoped Classical in
theorem volume_eq_two_pow_mul_two_pi_pow_mul_integral [NumberField K]
    (hA : ∀ x, x ∈ A ↔ mixedSpaceOfRealSpace (normAtAllPlaces x) ∈ A) (hm : MeasurableSet A) :
    volume A = 2 ^ nrRealPlaces K * .ofReal (2 * π) ^ nrComplexPlaces K *
      ∫⁻ x in normAtAllPlaces '' A, ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1) := by
  have hA₁ (x : mixedSpace K) : x ∈ A ↔ (fun w ↦ ‖x.1 w‖, x.2) ∈ A := by
    rw [hA, hA (fun w ↦ ‖x.1 w‖, x.2)]
    simp [mixedSpaceOfRealSpace_apply, normAtAllPlaces,
      normAtPlace_apply_of_isReal (Subtype.prop _), normAtPlace_apply_of_isComplex (Subtype.prop _)]
  have hA₂ (x : mixedSpace K) : x ∈ A ↔ ⟨x.1, fun w ↦ ‖x.2 w‖⟩ ∈ A := by
    rw [hA, hA ⟨x.1, fun w ↦ ‖x.2 w‖⟩]
    simp [mixedSpaceOfRealSpace_apply, normAtAllPlaces,
      normAtPlace_apply_of_isReal (Subtype.prop _), normAtPlace_apply_of_isComplex (Subtype.prop _),
      Complex.norm_real]
  have hA₃ (x : mixedSpace K) : x ∈ plusPart A ↔ (x.1, fun w ↦ ↑‖x.2 w‖) ∈ plusPart A := by
    rw [Set.mem_inter_iff, Set.mem_inter_iff, ← hA₂]
    simp
  rw [volume_eq_two_pow_mul_volume_plusPart hA₁ hm, volume_eq_two_pi_pow_mul_integral hA₃
    (measurableSet_plusPart hm), ← mul_assoc]
  refine congr_arg (_ * _ * ·) <| setLIntegral_congr ?_
  rw [← volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux₁ hA hA₃]
  refine inter_ae_eq_left_of_ae_eq_univ <| ae_eq_univ.mpr
    <| Set.compl_iInter _ ▸ measure_iUnion_null_iff.mpr fun w ↦ ?_
  rw [show {x : realSpace K | x w.1 ≠ 0}ᶜ = {x | x w.1 = 0} by ext; simp]
  exact realSpace.volume_eq_zero w.1

end polarSpace

end NumberField.mixedEmbedding
