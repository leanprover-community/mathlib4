/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Sequences


/-!
# Continuous (star-)algebra equivalences between continuous endomorphisms are (isometrically) inner

This file shows that continuous (star-)algebra equivalences between continuous endomorphisms are
(isometrically) inner.
See `Mathlib/LinearAlgebra/GeneralLinearGroup/AlgEquiv.lean` for the non-continuous version.
The proof follows the same idea as the non-continuous version.

### TODO:
- when `V = W`, we can state that the group homomorphism
  `(V →L[𝕜] V)ˣ →* ((V →L[𝕜] V) ≃A[𝕜] (V →L[𝕜] V))` is surjective,
  see `Module.End.mulSemiringActionToAlgEquiv_conjAct_surjective` for the non-continuous
  version of this.
-/

open ContinuousLinearMap ContinuousLinearEquiv

section
variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] [SeparatingDual 𝕜 V]
  [SeparatingDual 𝕜 W]

/-- This is the continuous version of `AlgEquiv.eq_linearEquivConjAlgEquiv`. -/
public theorem ContinuousAlgEquiv.eq_continuousLinearEquivConjContinuousAlgEquiv
    (f : (V →L[𝕜] V) ≃A[𝕜] (W →L[𝕜] W)) :
    ∃ U : V ≃L[𝕜] W, f = U.conjContinuousAlgEquiv := by
  /- The proof goes as follows:
    We want to show the existence of a continuous linear equivalence `U : V ≃L[𝕜] W` such that
    `f A (U x) = U (A x)` for all `A : V →L[𝕜] V` and `x : V`.
    Assume nontriviality of `V`, and let `(u : V) ≠ 0`. Let `v` be a strong dual on `V` such that
    `v u ≠ 0` (exists since it has a separating dual).
    Let `z : W` such that `f (smulRight v u) z ≠ 0`.
    Then we construct a bijective continuous linear map `T : V →L[𝕜] W`
    given by `x ↦ f (smulRight v x) z` and so satisfies `T (A x) = f A (T x)` for all
    `A : V →L[𝕜] V` and `x : V`. So it remains to show that this map has a continuous inverse.
    Let `d` be a strong dual on `W` such that `d ((f (smulRight v u)) z) = 1` (exists since it has
    a separating dual).
    We then construct a right-inverse continuous linear map `T' : W →L[𝕜] V` given by
    `x ↦ f.symm (smulRight d x) u`.
    And so it follows that `T` is also a continuous linear equivalence. -/
  by_cases! hV : Subsingleton V
  · by_cases! hV : Subsingleton W
    · exact ⟨{ toLinearEquiv := 0 }, ext <| Subsingleton.allEq _ _⟩
    simpa using congr(f $(Subsingleton.allEq 0 1))
  simp_rw [ContinuousAlgEquiv.ext_iff, funext_iff, conjContinuousAlgEquiv_apply, ← comp_assoc,
    eq_comp_toContinuousLinearMap_symm]
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  obtain ⟨v, huv⟩ := SeparatingDual.exists_ne_zero (R := 𝕜) hu
  obtain ⟨z, hz⟩ : ∃ z : W, ¬ f (smulRight v u) z = (0 : W →L[𝕜] W) z := by
    simp_rw [← not_forall, ← ContinuousLinearMap.ext_iff, map_eq_zero_iff,
      ContinuousLinearMap.ext_iff, not_forall, smulRight_apply, zero_apply,
      smul_eq_zero_iff_left hu]
    exact ⟨u, huv⟩
  set T := apply' _ (.id 𝕜) z ∘L f.toContinuousAlgHom.toContinuousLinearMap ∘L smulRightL 𝕜 _ _ v
  have hT x : T x = f (smulRight v x) z := rfl
  have this A x : T (A x) = f A (T x) := by
    simp only [hT, ← mul_apply, ← map_mul]
    congr; ext; simp
  have ⟨d, hd⟩ := SeparatingDual.exists_eq_one (R := 𝕜) hz
  have surj : Function.Surjective T := fun w ↦ ⟨f.symm (smulRight d w) u, by simp [T, this, hd]⟩
  have inj : Function.Injective T := fun x y hxy ↦ by
    have h_smul : smulRight v x = smulRight v y := by
      apply f.injective <| ContinuousLinearMap.ext fun z ↦ ?_
      obtain ⟨w, rfl⟩ := surj z
      simp [← this, hxy]
    simpa [huv.isUnit.smul_left_cancel] using congr((fun f ↦ f u) $h_smul)
  set Tₗ : V ≃ₗ[𝕜] W := .ofBijective T.toLinearMap ⟨inj, surj⟩
  set T' := apply' _ (.id 𝕜) u ∘L f.symm.toContinuousAlgHom.toContinuousLinearMap ∘L
    smulRightL 𝕜 _ _ d
  set TL : V ≃L[𝕜] W := { Tₗ with
    continuous_toFun := T.continuous
    continuous_invFun := by
      change Continuous Tₗ.symm.toLinearMap
      suffices T'.toLinearMap = Tₗ.symm from this ▸ T'.continuous
      simp [LinearMap.ext_iff, ← Tₗ.injective.eq_iff, T', this, hT, hd, Tₗ] }
  exact ⟨TL, fun A ↦ (ContinuousLinearMap.ext <| this A).symm⟩

variable (𝕜 V W) in
public theorem ContinuousLinearEquiv.conjContinuousAlgEquiv_surjective :
    Function.Surjective (conjContinuousAlgEquiv (𝕜 := 𝕜) (G := V) (H := W)) :=
  fun f ↦ f.eq_continuousLinearEquivConjContinuousAlgEquiv.imp fun _ h ↦ h.symm

end

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]

section auxiliaryDefs

variable (e : V ≃L[𝕜] W) {α α' : 𝕜} (hα : α ≠ 0)
  (hα2 : α' * α' = α⁻¹) (he : e.toContinuousLinearMap.adjoint ∘L e = α • .id 𝕜 V)
  (he' : e ∘L e.toContinuousLinearMap.adjoint = α • .id 𝕜 W)
include hα hα2 he he'

/-- Scalar multiple of a continuous linear equivalence (given certain properties are satisfied). -/
noncomputable abbrev auxContinuousLinearEquiv :
    V ≃L[𝕜] W where
  toLinearMap := (α' • e.toContinuousLinearMap).toLinearMap
  invFun := (α' • e.toContinuousLinearMap.adjoint).toLinearMap
  left_inv x := by
    have := by simpa using congr($he x)
    simp [smul_smul, hα2, this, hα, ← mul_assoc]
  right_inv x := by
    have := by simpa using congr($he' x)
    simp [smul_smul, hα2, this, hα, ← mul_assoc]
  continuous_toFun := (α' • e.toContinuousLinearMap).continuous
  continuous_invFun := (α' • e.toContinuousLinearMap.adjoint).continuous

@[simp] theorem coe_auxContinuousLinearEquiv :
    (auxContinuousLinearEquiv e hα hα2 he he').toContinuousLinearMap =
      α' • e.toContinuousLinearMap := rfl

/-- Construct an isometry linear equivalence from a continuous linear equivalence
and that its adjoint is a real-scalar multiple of its inverse. -/
noncomputable abbrev auxIsometry (hαa : starRingEnd 𝕜 α' = α') :
    V ≃ₗᵢ[𝕜] W where
  __ := auxContinuousLinearEquiv e hα hα2 he he' |>.toLinearEquiv
  norm_map' := by
    rw [ContinuousLinearEquiv.coe_toLinearEquiv, ← ContinuousLinearEquiv.coe_coe,
      norm_map_iff_adjoint_comp_self, coe_auxContinuousLinearEquiv,
      MulActionSemiHomClass.map_smulₛₗ]
    simp only [hαa, comp_smulₛₗ, RingHom.id_apply, smul_comp, smul_smul, hα2]
    simp [he, smul_smul, hα, one_def]

@[simp] theorem coe_auxIsometry (hαa : starRingEnd 𝕜 α' = α') :
    (auxIsometry e hα hα2 he he' hαa).toContinuousLinearEquiv.toContinuousLinearMap =
      α' • e.toContinuousLinearMap := rfl

@[simp] theorem coe_symm_auxIsometry (hαa : starRingEnd 𝕜 α' = α') :
    (auxIsometry e hα hα2 he he' hαa).toContinuousLinearEquiv.symm.toContinuousLinearMap =
      α'⁻¹ • e.symm.toContinuousLinearMap := by
  ext y
  apply (auxIsometry e hα hα2 he he' hαa).toContinuousLinearEquiv.injective
  simp [smul_smul, inv_mul_cancel₀ (a := α') (by grind)]

end auxiliaryDefs

open ComplexOrder

/-- The ⋆-algebra equivalence version of
`ContinuousAlgEquiv.eq_continuousLinearEquivConjContinuousAlgEquiv`.

TODO: remove the hypothesis `Continuous f`, as star-algebra equivalences between endomorphisms are
automatically continuous. -/
public theorem StarAlgEquiv.eq_linearIsometryEquivConjStarAlgEquiv
    (f : (V →L[𝕜] V) ≃⋆ₐ[𝕜] (W →L[𝕜] W)) (hf : Continuous f) :
    ∃ U : V ≃ₗᵢ[𝕜] W, f = U.conjStarAlgEquiv := by
  -- Assume nontriviality of `V`.
  by_cases! Subsingleton V
  · by_cases! Subsingleton W
    · use { toLinearEquiv := 0, norm_map' _ := by simp [Subsingleton.eq_zero] }
      exact ext fun _ ↦ Subsingleton.allEq _ _
    simpa using congr(f $(Subsingleton.allEq 0 1))
  /- By `ContinuousAlgEquiv.eq_continuousLinearEquivConjContinuousAlgEquiv`,
    we know there exists a continuous linear equivalence `y : V ≃L[𝕜] W` such that
    `f = y.conjAlgEquiv`.
    Our goal will be to construct an isometry from `y`. We do this by first showing
    `adjoint y ∘ y` is in the center of the endomorphisms, and as the algebra of endomorphisms
    are central, `adjoint y ∘ y` is a scalar multiple of the identity. -/
  obtain ⟨y, hy⟩ := (ContinuousAlgEquiv.mk f.toAlgEquiv hf
    (f.toAlgEquiv.toLinearEquiv.continuous_symm hf)).eq_continuousLinearEquivConjContinuousAlgEquiv
  have (x : V →L[𝕜] V) : adjoint (f x) = f (adjoint x) := map_star _ _ |>.symm
  rw [ContinuousAlgEquiv.ext_iff] at hy
  simp_rw [← StarAlgEquiv.coe_toAlgEquiv, ContinuousAlgEquiv.coe_mk f.toAlgEquiv hf _ ▸ hy,
    conjContinuousAlgEquiv_apply,  adjoint_comp] at this
  replace this (x : V →L[𝕜] V) : adjoint y.toContinuousLinearMap ∘L y ∘L adjoint x ∘L y.symm =
      adjoint x ∘L adjoint y.toContinuousLinearMap := by
    simp_rw [← this x, ← comp_assoc, ← adjoint_comp]
    simp
  replace this (x : V →L[𝕜] V) : Commute x (adjoint y.toContinuousLinearMap ∘L y) := by
    simp_rw [commute_iff_eq, mul_def, ← comp_assoc, ← (adjoint_adjoint x ▸ this _), comp_assoc]
    simp
  -- Let `α : 𝕜` be that scalar, i.e., `adjoint y ∘ y = α • id`. This scalar is clearly real.
  obtain ⟨α, hα⟩ := by simpa using (Subalgebra.mem_center_iff (R := 𝕜)).mpr fun _ ↦ this _
  simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId, Algebra.algebraMap_eq_smul_one] at hα
  have : IsUnit (adjoint y.toContinuousLinearMap ∘L y) :=
    isUnit_iff_exists.mpr ⟨y.symm ∘L adjoint y.symm.toContinuousLinearMap, by
      simp [mul_def, ← comp_assoc, comp_assoc _ _ (adjoint y.toContinuousLinearMap),
        ← adjoint_comp, one_def, comp_assoc _ y.toContinuousLinearMap]⟩
  have hα_re : α = RCLike.re α := by
    have := by simpa [IsSelfAdjoint, ← hα, one_def, star_eq_adjoint] using
      (IsSelfAdjoint.one (W →L[𝕜] W)).adjoint_conj y.toContinuousLinearMap
    rwa [← one_def, (smul_left_injective 𝕜 one_ne_zero).eq_iff, RCLike.conj_eq_iff_re,
      eq_comm] at this
  --  Also, as `adjoint y ∘ y` is invertible, we get `α ≠ 0`.
  have hα_ne_zero : α ≠ 0 := fun h ↦ by simp [h, ← hα] at this
  -- As `adjoint y ∘ y` is positive, we then get `0 < α`.
  have hα_nonneg : 0 ≤ α := by
    have := hα_re.symm ▸ (nonneg_iff_isPositive _ |>.mpr
      (hα_re ▸ hα ▸ isPositive_adjoint_comp_self y.toContinuousLinearMap))
    rw [← LinearMap.isPositive_one.isPositive_smul_iff (E := V) (one_ne_zero' (V →ₗ[𝕜] V))]
    exact (nonneg_iff_isPositive _).mp this
  have hα_pos := RCLike.ofReal_pos.mp <| hα_re ▸ (lt_of_le_of_ne' hα_nonneg hα_ne_zero)
  -- We also get `y ∘ adjoint y = α • id`.
  have h_comp_adjoint : y.toContinuousLinearMap ∘L adjoint y.toContinuousLinearMap =
      α • ContinuousLinearMap.id 𝕜 _ := by
    ext x
    simpa using congr(y (($hα ∘L y.symm.toContinuousLinearMap) x)).symm
  -- Finally, we construct our isometry `1/√(re α) • y`.
  set β := (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜)
  have hβ : β * β = α⁻¹ := by
    rw [hα_re]
    norm_num [β, ← RCLike.ofReal_mul, ← Real.rpow_add hα_pos, Real.rpow_neg_one]
  set U := auxIsometry y hα_ne_zero hβ hα.symm h_comp_adjoint (by simp [β])
  use U
  have hβ₂ : β⁻¹ * β = 1 := by
    refine inv_mul_cancel₀ ?_
    simp only [β, ne_eq, map_eq_zero]
    rw [Real.rpow_eq_zero hα_pos.le (by simp)]
    exact ne_of_gt hα_pos
  ext
  simp [U.conjStarAlgEquiv_apply, U, smul_smul, hβ₂, ← conjContinuousAlgEquiv_apply, ← hy]

/- TODO: Remove instance when we have `StarOrderedRing (V →L[𝕜] V)` since
this then becomes an instance from `StarRingEquivClass.instOrderIsoClass`. -/
public instance (priority := 100) {F : Type*} [EquivLike F (V →L[𝕜] V) (W →L[𝕜] W)]
    [NonUnitalAlgEquivClass F 𝕜 _ _] [StarHomClass F _ _] [ContinuousMapClass F _ _] :
    OrderIsoClass F _ _ where
  map_le_map_iff f x y := by
    obtain ⟨U, hU⟩ := StarAlgEquiv.eq_linearIsometryEquivConjStarAlgEquiv
      (StarAlgEquivClass.toStarAlgEquiv f : _ ≃⋆ₐ[𝕜] _) (map_continuous f)
    have this a : f a = U.conjStarAlgEquiv a := by simpa using congr($hU a)
    simp_rw [le_def, ← _root_.map_sub, ← isPositive_toLinearMap_iff, this]
    exact LinearMap.isPositive_linearIsometryEquiv_conj_iff U
