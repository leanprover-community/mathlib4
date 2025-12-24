/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Algebra.Equiv

import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Continuous (star-)algebra equivalences between continuous endomorphisms are (isometrically) inner

This file shows that continuous (star-)algebra equivalences between continuous endomorphisms are
isometrically inner.
See `Mathlib/LinearAlgebra/GeneralLinearGroup/AlgEquiv.lean` for the non-continuous version.
The proof is essentially the same as the non-continuous version.

# TODO:
- when `V = W`, we can state that the group homomorphism
  `(V →L[𝕜] V)ˣ →* ((V →L[𝕜] V) ≃A[𝕜] (V →L[𝕜] V))` is surjective,
  see `Module.End.mulSemiringActionToAlgEquiv_conjAct_surjective` for the non-continuous
  version of this.
-/

open ContinuousLinearMap ContinuousLinearEquiv

/-- This is the continuous version of `AlgEquiv.eq_linearEquivConjAlgEquiv`. -/
public theorem ContinuousAlgEquiv.eq_continuousLinearEquivConjContinuousAlgEquiv {𝕜 V W : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] [SeparatingDual 𝕜 V] [SeparatingDual 𝕜 W]
    [CompleteSpace V] [CompleteSpace W] (f : (V →L[𝕜] V) ≃A[𝕜] (W →L[𝕜] W)) :
    ∃ U : V ≃L[𝕜] W, f = U.conjContinuousAlgEquiv := by
  by_cases! hV : Subsingleton V
  · by_cases! hV : Subsingleton W
    · exact ⟨{ toLinearEquiv := 0 }, ext <| Subsingleton.allEq _ _⟩
    simpa using congr(f $(Subsingleton.allEq 0 1))
  simp_rw [ContinuousAlgEquiv.ext_iff, funext_iff, conjContinuousAlgEquiv_apply, ← comp_assoc,
    eq_comp_toContinuousLinearMap_symm]
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  obtain ⟨v, huv⟩ := SeparatingDual.exists_ne_zero (R := 𝕜) hu
  obtain ⟨z, hz⟩ : ∃ z : W, ¬ f (smulRight v u) z = (0 : W →L[𝕜] W) z := by
    rw [← not_forall, ← ContinuousLinearMap.ext_iff, map_eq_zero_iff, ContinuousLinearMap.ext_iff]
    exact not_forall.mpr ⟨u, huv.isUnit.smul_eq_zero.not.mpr hu⟩
  set T := apply' _ (.id 𝕜) z ∘L f.toContinuousAlgHom.toContinuousLinearMap ∘L smulRightL 𝕜 _ _ v
  have hT x : T x = f (smulRight v x) z := rfl
  have this A x : T (A x) = f A (T x) := by
    simp only [hT, ← mul_apply, ← map_mul]
    congr; ext; simp
  have surj : Function.Surjective T := fun w ↦ by
    obtain ⟨d, hd⟩ := SeparatingDual.exists_eq_one (R := 𝕜) hz
    exact ⟨f.symm (smulRight d w) u, by simp [T, this, hd]⟩
  have inj : Function.Injective T := fun x y hxy ↦ by
    have h_smul : smulRight v x = smulRight v y := by
      apply f.injective <| ContinuousLinearMap.ext fun z ↦ ?_
      obtain ⟨w, rfl⟩ := surj z
      simp [← this, hxy]
    simpa [huv.isUnit.smul_left_cancel] using congr((fun f ↦ f u) $h_smul)
  exact ⟨.ofBijective T ((LinearMapClass.ker_eq_bot _).mpr inj)
    (LinearMap.range_eq_top_of_surjective T surj), fun A ↦ (ContinuousLinearMap.ext <| this A).symm⟩

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]

/-- can't do this inline, it times out -/
noncomputable abbrev auxContinuousLinearEquiv (e : V ≃L[𝕜] W) {α α' : 𝕜} (hα : α ≠ 0)
    (hα2 : α' * α' = α⁻¹) (he : e.toContinuousLinearMap.adjoint ∘L e = α • .id 𝕜 V)
    (he' : e ∘L e.toContinuousLinearMap.adjoint = α • .id 𝕜 W) :
    V ≃L[𝕜] W where
  toFun := (α' • e.toContinuousLinearMap).toLinearMap
  invFun := (α' • e.toContinuousLinearMap.adjoint).toLinearMap
  left_inv := by
    simp only [coe_smul, Function.leftInverse_iff_comp, funext_iff, Function.comp_apply,
      LinearMap.smul_apply, ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe,
      _root_.map_smul, smul_smul, hα2, id_eq]
    simp_rw [← ContinuousLinearEquiv.coe_coe, ← comp_apply, he]
    simp [smul_smul, hα]
  right_inv := by
    simp only [coe_smul, Function.rightInverse_iff_comp, funext_iff, Function.comp_apply,
      LinearMap.smul_apply, ContinuousLinearMap.coe_coe, _root_.map_smul,
      ContinuousLinearEquiv.coe_coe, smul_smul, hα2, id_eq]
    simp_rw [← ContinuousLinearEquiv.coe_coe, ← comp_apply, he']
    simp [smul_smul, hα]
  map_add' := by simp
  map_smul' := by simp
  continuous_toFun := (α' • e.toContinuousLinearMap).continuous
  continuous_invFun := (α' • e.toContinuousLinearMap.adjoint).continuous

theorem coe_auxContinuousLinearEquiv (e : V ≃L[𝕜] W) {α α' : 𝕜} (hα : α ≠ 0) (hα2 : α' * α' = α⁻¹)
    (he : e.toContinuousLinearMap.adjoint ∘L e = α • .id 𝕜 V)
    (he' : e ∘L e.toContinuousLinearMap.adjoint = α • .id 𝕜 W) :
    (auxContinuousLinearEquiv e hα hα2 he he').toContinuousLinearMap =
      α' • e.toContinuousLinearMap := rfl

theorem adjoint_auxContinuousLinearEquiv (e : V ≃L[𝕜] W) {α α' : 𝕜} (hα : α ≠ 0)
    (hα2 : α' * α' = α⁻¹) (he : e.toContinuousLinearMap.adjoint ∘L e = α • .id 𝕜 V)
    (he' : e ∘L e.toContinuousLinearMap.adjoint = α • .id 𝕜 W)
    (hαa : starRingEnd 𝕜 α' = α') :
    adjoint (auxContinuousLinearEquiv e hα hα2 he he').toContinuousLinearMap =
      α' • e.toContinuousLinearMap.adjoint := by
  ext x
  apply ext_inner_left 𝕜 fun y ↦ ?_
  simp [auxContinuousLinearEquiv, adjoint_inner_right, inner_smul_left, inner_smul_right, hαa]

/-- can't do this inline either, it times out -/
noncomputable abbrev auxIsometry (e : V ≃L[𝕜] W) {α α' : 𝕜} (hα : α ≠ 0) (hα2 : α' * α' = α⁻¹)
    (he : e.toContinuousLinearMap.adjoint ∘L e = α • .id 𝕜 V)
    (he' : e ∘L e.toContinuousLinearMap.adjoint = α • .id 𝕜 W)
    (hαa : starRingEnd 𝕜 α' = α') :
    V ≃ₗᵢ[𝕜] W where
  __ := auxContinuousLinearEquiv e hα hα2 he he' |>.toLinearEquiv
  norm_map' := by
    rw [ContinuousLinearEquiv.coe_toLinearEquiv, ← ContinuousLinearEquiv.coe_coe,
      norm_map_iff_adjoint_comp_self, adjoint_auxContinuousLinearEquiv _ _ _ _ _ hαa,
      coe_auxContinuousLinearEquiv]
    simp only [comp_smulₛₗ, RingHom.id_apply, smul_comp, smul_smul, hα2]
    simp [he, smul_smul, hα, one_def]

theorem coe_auxIsometry (e : V ≃L[𝕜] W) {α α' : 𝕜} (hα : α ≠ 0) (hα2 : α' * α' = α⁻¹)
    (he : e.toContinuousLinearMap.adjoint ∘L e = α • .id 𝕜 V)
    (he' : e ∘L e.toContinuousLinearMap.adjoint = α • .id 𝕜 W)
    (hαa : starRingEnd 𝕜 α' = α') :
    (auxIsometry e hα hα2 he he' hαa).toContinuousLinearEquiv.toContinuousLinearMap =
      α' • e.toContinuousLinearMap := rfl

theorem coe_symm_auxIsometry (e : V ≃L[𝕜] W) {α α' : 𝕜} (hα : α ≠ 0) (hα2 : α' * α' = α⁻¹)
    (he : e.toContinuousLinearMap.adjoint ∘L e = α • .id 𝕜 V)
    (he' : e ∘L e.toContinuousLinearMap.adjoint = α • .id 𝕜 W)
    (hαa : starRingEnd 𝕜 α' = α') :
    (auxIsometry e hα hα2 he he' hαa).toContinuousLinearEquiv.symm.toContinuousLinearMap =
      α'⁻¹ • e.symm.toContinuousLinearMap := by
  ext y
  apply (auxIsometry e hα hα2 he he' hαa).toContinuousLinearEquiv.injective
  simp [smul_smul, inv_mul_cancel₀ (a := α') (by grind)]

open ComplexOrder

public theorem StarAlgEquiv.coe_eq_linearIsometryEquiv_conjugate
    (f : (V →L[𝕜] V) ≃⋆ₐ[𝕜] (W →L[𝕜] W)) (hf : Continuous f) :
    ∃ U : V ≃ₗᵢ[𝕜] W,
      ⇑f = fun x ↦ U.toContinuousLinearEquiv ∘L x ∘L U.symm.toContinuousLinearEquiv := by
  by_cases! hV : Subsingleton V
  · by_cases! hV : Subsingleton W
    · use { toLinearEquiv := 0, norm_map' _ := by simp [Subsingleton.eq_zero] }
      exact Subsingleton.allEq _ _
    simpa using congr(f $(Subsingleton.allEq 0 1))
  obtain ⟨y, hy⟩ := (ContinuousAlgEquiv.ofAlgEquiv f.toAlgEquiv hf
    (f.toAlgEquiv.toLinearEquiv.continuous_symm hf)).eq_continuousLinearEquivConjContinuousAlgEquiv
  have (x : V →L[𝕜] V) : adjoint (f x) = f (adjoint x) := map_star _ _ |>.symm
  rw [ContinuousAlgEquiv.ext_iff] at hy
  simp_rw [← StarAlgEquiv.coe_toAlgEquiv, ContinuousAlgEquiv.coe_ofAlgEquiv f.toAlgEquiv hf _ ▸ hy,
    conjContinuousAlgEquiv_apply,  adjoint_comp] at this
  replace this (x : V →L[𝕜] V) : adjoint y.toContinuousLinearMap ∘L y ∘L adjoint x ∘L y.symm =
      adjoint x ∘L adjoint y.toContinuousLinearMap := by
    simp_rw [← this x, ← comp_assoc, ← adjoint_comp]
    simp
  replace this (x : V →L[𝕜] V) : Commute x (adjoint y.toContinuousLinearMap ∘L y) := by
    specialize this (adjoint x)
    simp only [adjoint_adjoint] at this
    simp_rw [Commute, SemiconjBy, mul_def, ← comp_assoc, ← this, comp_assoc]
    simp
  replace this :
      (adjoint y.toContinuousLinearMap ∘L y) ∈ Subalgebra.centralizer 𝕜 (⊤ : Set (V →L[𝕜] V)) := by
    rw [Subalgebra.mem_centralizer_iff]
    exact fun _ _ ↦ this _
  simp only [Set.top_eq_univ, Subalgebra.centralizer_univ, Algebra.IsCentral.center_eq_bot] at this
  obtain ⟨α, hα⟩ := this
  simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId, Algebra.algebraMap_eq_smul_one] at hα
  have this : IsUnit (adjoint y.toContinuousLinearMap ∘L y) := isUnit_iff_exists.mpr
    ⟨y.symm ∘L adjoint y.symm.toContinuousLinearMap, by
        simp [mul_def, ← comp_assoc, comp_assoc _ _ (adjoint y.toContinuousLinearMap),
          ← adjoint_comp, one_def, comp_assoc _ y.toContinuousLinearMap]⟩
  have thisα : α = RCLike.re α := by
    have this10 := by simpa [IsSelfAdjoint, ← hα, one_def, star_eq_adjoint] using
      IsSelfAdjoint.adjoint_conj (IsSelfAdjoint.one (W →L[𝕜] W)) y.toContinuousLinearMap
    rwa [← one_def, (smul_left_injective 𝕜 one_ne_zero).eq_iff, RCLike.conj_eq_iff_re,
      eq_comm] at this10
  have thisα' : α ≠ 0 := fun h ↦ by simp [h, ← hα] at this
  have this2 : 0 ≤ α := by
    have this1 := thisα.symm ▸ (nonneg_iff_isPositive _ |>.mpr
      (thisα ▸ hα ▸ isPositive_adjoint_comp_self y.toContinuousLinearMap))
    rw [← LinearMap.IsPositive.isPositive_smul_iff (E := V) isPositive_one]
    · exact (nonneg_iff_isPositive _).mp this1
    · exact one_ne_zero' (V →ₗ[𝕜] V)
  replace this2 := RCLike.ofReal_pos.mp <| thisα ▸ (lt_of_le_of_ne' this2 thisα')
  have thisU : y.toContinuousLinearMap ∘L adjoint y.toContinuousLinearMap =
      α • ContinuousLinearMap.id 𝕜 _ := by
        have := by simpa [one_def, comp_assoc] using congr($hα ∘L y.symm.toContinuousLinearMap)
        ext
        apply_fun y.symm using y.symm.injective
        simp [← this]
  set αa := (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜)
  have αa2 : αa * αa = α⁻¹ := by
    simp_rw [αa, ← RCLike.ofReal_mul, ← Real.rpow_add this2]
    rw [thisα]
    norm_num
    simp [Real.rpow_neg_one]
  set U := auxIsometry y thisα' αa2 hα.symm thisU (by simp [αa])
  use U
  have la : αa⁻¹ * αa = 1 := by
    simp only [one_div, αa]
    exact inv_mul_cancel₀ (by
      simp only [ne_eq, map_eq_zero]
      rw [Real.rpow_eq_zero this2.le (by simp)]
      exact ne_of_gt this2)
  simp [U, coe_auxIsometry, coe_symm_auxIsometry, smul_smul, la, ← conjContinuousAlgEquiv_apply,
    ← hy]

/- Remove instance when we have `StarOrderedRing (V →L[𝕜] V)` since
this then becomes an instance from `StarRingEquivClass.instOrderIsoClass`. -/
instance (priority := 100) {F : Type*} [EquivLike F (V →L[𝕜] V) (W →L[𝕜] W)]
    [NonUnitalAlgEquivClass F 𝕜 _ _] [StarHomClass F _ _] [ContinuousMapClass F _ _] :
    OrderIsoClass F _ _ where
  map_le_map_iff f x y := by
    obtain ⟨U, hU⟩ := StarAlgEquiv.coe_eq_linearIsometryEquiv_conjugate
      (StarAlgEquivClass.toStarAlgEquiv f : _ ≃⋆ₐ[𝕜] _) (map_continuous f)
    simp_rw [LinearIsometryEquiv.toContinuousLinearEquiv_symm, funext_iff,
      fun x ↦ show StarAlgEquivClass.toStarAlgEquiv f x = f x by rfl] at hU
    simp_rw [le_def, ← _root_.map_sub, ← isPositive_toLinearMap_iff, hU]
    exact LinearMap.isPositive_linearIsometryEquiv_conj_iff U
