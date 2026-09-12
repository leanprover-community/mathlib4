/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.InnerProductSpace.Complexification.Basic

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! Transfering results from C⋆-algebras to `𝕜` Hilbert spaces via complexification

In particular, we provide the continuous functional calculus for `E →L[𝕜] E`
(see `ContinuousLinearMap.instCFC` and `ContinuousLinearMap.instIsometricCFC`). -/

public section

namespace ContinuousLinearMap
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

open Complexification

protected lemma IsSelfAdjoint.norm_add_eq_max {S T : E →L[𝕜] E}
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) (h : S * T = 0) :
    ‖S + T‖ = max ‖S‖ ‖T‖ := by
  rw [← opNorm_toComplexification (S + T), map_add,
    hS.toComplexification.norm_add_eq_max hT.toComplexification
      (by simp [← toComplexification_mul, h])]
  simp

/-- `Complexification.conjugate` as a real star algebra equivalence. -/
@[expose, simps! apply] noncomputable def conjugateStarAlgEquiv :
    (Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E) ≃⋆ₐ[ℝ]
      (Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E) where
  __ := conjugate
  map_mul' := by simp
  map_star' := by simp
  map_smul' _ _ := by ext <;> simp [conj_apply]

@[simp] lemma symm_conjugateStarAlgEquiv :
    (conjugateStarAlgEquiv (𝕜 := 𝕜) (E := E)).symm = conjugateStarAlgEquiv := rfl

lemma conjugateStarAlgEquiv_comp_cfcHom_toComplexification {T : E →L[𝕜] E}
    (hT : IsSelfAdjoint T) :
    (conjugateStarAlgEquiv).toStarAlgHom.comp (cfcHom hT.toComplexification) =
      cfcHom hT.toComplexification := by
  refine symm <| cfcHom_eq_of_continuous_of_map_id hT.toComplexification _ ?_ ?_
  · eta_expand
    simp only [StarAlgHom.comp_apply, StarAlgEquiv.toStarAlgHom_apply, conjugateStarAlgEquiv_apply]
    fun_prop
  · simp [cfcHom_id hT.toComplexification]

theorem conjugate_cfcHom_toComplexification {T : E →L[𝕜] E} (hT : IsSelfAdjoint T)
    (g : C(spectrum ℝ T.toComplexification, ℝ)) :
    (cfcHom hT.toComplexification g).conjugate = cfcHom hT.toComplexification g := by
  conv_lhs => rw [← conjugateStarAlgEquiv_comp_cfcHom_toComplexification hT]
  simp

private lemma commute_cfcHom_toComplexification_algebraMapCLM_I (T : E →L[𝕜] E)
    (hT : IsSelfAdjoint T) (g : C(spectrum ℝ T.toComplexification, ℝ)) :
    (cfcHom hT.toComplexification g) ∘SL
      (algebraMapCLM 𝕜 (E →L[𝕜] E) RCLike.I).toComplexification =
        (algebraMapCLM 𝕜 (E →L[𝕜] E) RCLike.I).toComplexification ∘SL
          (cfcHom hT.toComplexification g) := by
  refine hT.toComplexification.commute_cfcHom _ ?_ g
  simp [commute_iff_eq, ContinuousLinearMap.ext_iff]

attribute [local simp] toComplexification_ofComplexification conjugate_cfcHom_toComplexification in
/-- The real star algebra homomorphism between `C(spectrum ℝ T.toComplexification, ℝ)` and
`Eₗ →L[ℝ] Eₗ`.
This is used in the continuous functional calculus. -/
private noncomputable def cfcHomAux [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {T : E →L[𝕜] E}
    (hT : IsSelfAdjoint T) : C(spectrum ℝ T.toComplexification, ℝ) →⋆ₐ[ℝ] (E →L[𝕜] E) where
  toFun g := (cfcHom hT.toComplexification g).ofComplexification
    (commute_cfcHom_toComplexification_algebraMapCLM_I _ hT _)
  map_one' := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by simp [← toComplexification_inj, hT]
  map_star' _ := by simp [← toComplexification_inj, hT, ← star_toComplexification, ← map_star]
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

private lemma toComplexification_cfcHomAux [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    {T : E →L[𝕜] E} (hT : IsSelfAdjoint T)
    (g : C(spectrum ℝ T.toComplexification, ℝ)) :
    (cfcHomAux hT g).toComplexification = cfcHom hT.toComplexification g := by
  refine toComplexification_ofComplexification ?_ (conjugate_cfcHom_toComplexification hT g)
  exact commute_cfcHom_toComplexification_algebraMapCLM_I T hT g

instance [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (a : E →L[𝕜] E) :
    CompactSpace ↑(spectrum ℝ a) := by
  rw [← spectrum_toComplexification_real]
  infer_instance

instance instCFC [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint where
  predicate_zero := IsSelfAdjoint.zero _
  spectrum_nonempty T hT := by
    rw [← spectrum_toComplexification_real]
    have : Nontrivial (Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E) :=
      toComplexification_injective.nontrivial
    exact ContinuousFunctionalCalculus.spectrum_nonempty _ hT.toComplexification
  exists_cfc_of_predicate T hT := by
    rw [← spectrum_toComplexification_real]
    refine ⟨cfcHomAux hT, ?_, fun x y hxy ↦ ?_, ?_, fun x ↦ ?_, fun x ↦ ?_⟩
    · rw [isometry_toComplexification.isEmbedding.continuous_iff]
      eta_expand
      simp only [Function.comp_apply, toComplexification_cfcHomAux]
      fun_prop
    · rwa [← toComplexification_inj, toComplexification_cfcHomAux,
        toComplexification_cfcHomAux, (cfcHom_injective hT.toComplexification).eq_iff] at hxy
    · rw [← toComplexification_inj, toComplexification_cfcHomAux, cfcHom_id ..]
    · rw [← spectrum_toComplexification_real, toComplexification_cfcHomAux]
      exact cfcHom_map_spectrum ..
    · rw [← isSelfAdjoint_toComplexification_iff, toComplexification_cfcHomAux]
      exact cfcHom_predicate ..

lemma spectralRadius_toComplexification {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) :
    spectralRadius ℂ T.toComplexification = spectralRadius 𝕜 T := by
  simp [hT.toComplexification.spectralRadius_eq_nnnorm, spectralRadius_eq_nnnorm _ hT]

instance instIsometricCFC [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    IsometricContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint where
  isometric T hT := (AddMonoidHomClass.isometry_iff_norm _).mpr fun x ↦ by
    suffices ‖cfcHom hT x‖₊ = ‖x‖₊ from congr($this)
    have : IsSelfAdjoint (cfcHom hT x) := cfcHom_predicate ..
    simp_rw [← ENNReal.coe_inj, ← spectralRadius_eq_nnnorm _ this,
      ← spectralRadius_toComplexification this,
      ← this.toComplexification.spectrumRestricts.spectralRadius_eq,
      spectralRadius, ← enorm_eq_nnnorm, ContinuousMap.enorm_eq_iSup_enorm]
    rw [← iSup_range, ← cfcHom_map_spectrum hT, spectrum_toComplexification_real]

variable (𝕜 E) in
/-- `toComplexification` as a star algebra homomorphism. -/
@[expose, simps! apply] noncomputable def toComplexificationStarAlgHom
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    (E →L[𝕜] E) →⋆ₐ[ℝ] (Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E) where
  __ := toComplexification
  map_one' := by simp
  map_mul' := by simp
  commutes' _ := by ext <;> simp
  map_star' := by simp

@[fun_prop] lemma continuous_toComplexificationStarAlgHom [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    Continuous (toComplexificationStarAlgHom 𝕜 E) := continuous_toComplexification

-- TODO: generalize `f : ℝ → ℝ` to any ring `R → R`?
@[simp] lemma toComplexification_cfc [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (f : ℝ → ℝ)
    (T : E →L[𝕜] E) : (cfc f T).toComplexification = cfc f T.toComplexification := by
  by_cases hT : IsSelfAdjoint T
  · by_cases hfT : ContinuousOn f (spectrum ℝ T)
    · simpa using (toComplexificationStarAlgHom 𝕜 E).map_cfc f T
    · simp [cfc_apply_of_not_continuousOn, hfT]
  · simp [cfc_apply_of_not_predicate, hT]

-- TODO: generalize `f : ℝ → ℝ` to any ring `R → R`?
@[simp] lemma toComplexification_cfcₙ [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (f : ℝ → ℝ)
    (T : E →L[𝕜] E) : (cfcₙ f T).toComplexification = cfcₙ f T.toComplexification := by
  by_cases hf0 : f 0 = 0
  · by_cases hT : IsSelfAdjoint T
    · by_cases hf : ContinuousOn f (quasispectrum ℝ T)
      · rw [cfcₙ_eq_cfc, cfcₙ_eq_cfc (hf := by simpa), toComplexification_cfc]
      · simp [cfcₙ_apply_of_not_continuousOn, hf]
    · simp [cfcₙ_apply_of_not_predicate, hT]
  · simp [cfcₙ_apply_of_not_map_zero, hf0]

end ContinuousLinearMap
