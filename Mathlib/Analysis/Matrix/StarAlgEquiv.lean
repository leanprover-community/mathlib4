/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Topology.Algebra.Algebra.Equiv

import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv

/-!

# Star algebra equivalences on matrices are unitarily inner

-/

open scoped ComplexOrder

variable {𝕜 A B F : Type*} [RCLike 𝕜] [Ring A] [Algebra 𝕜 A] [StarRing A] [StarModule 𝕜 A]
  [PartialOrder A] [StarOrderedRing A] [Star B] [FunLike F B A] [StarHomClass F B A]

/-- Given ⋆-homomorphisms `f` and `g`, where the centralizer of the range of `f` is trivial,
`f` and `g` differ by a unit iff they differ by a unitary. -/
public theorem StarHom.coe_eq_units_conjugate_iff_coe_eq_unitary_conjugate
    (f g : F) (hf : Subalgebra.centralizer 𝕜 (Set.range f) = ⊥) :
    (∃ (x : Aˣ), ⇑g = fun b ↦ ↑x * f b * ↑x⁻¹) ↔
    ∃ (u : unitary A), ⇑g = fun b ↦ u * f b * (star u : A) := by
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨u, hu⟩ ↦ ⟨Unitary.toUnits u, hu⟩⟩
  nontriviality A
  have (x : B) : star (g x) = g (star x) := map_star _ _ |>.symm
  simp_rw [hy, star_mul] at this
  replace this (x : B) : star (y : A) * (y : A) * star (f x) * ↑y⁻¹ = star (f x) * star ↑y := by
    simp_rw [mul_assoc, ← mul_assoc (y : A), ← map_star f, ← this, ← mul_assoc,
      ← star_mul, Units.inv_mul, mul_one, map_star, star_mul]
  replace this (x : B) : Commute (f x) (star ↑y * y) := by
    specialize this (star x)
    simp only [map_star, star_star] at this
    simp_rw [Commute, SemiconjBy, ← mul_assoc, ← this, mul_assoc, Units.inv_mul, mul_one]
  replace this (x : A) (hx : x ∈ Set.range f) : Commute x (star ↑y * y) :=
    have ⟨a, ha⟩ := hx
    ha ▸ this _
  simp_rw [Commute, SemiconjBy, ← Subalgebra.mem_centralizer_iff 𝕜, hf] at this
  obtain ⟨α, hα⟩ := this
  simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId, Algebra.algebraMap_eq_smul_one] at hα
  have this : IsUnit (star (y : A) * y) := isUnit_iff_exists.mpr
    ⟨y⁻¹ * star ((y⁻¹ : Aˣ) : A), by simp [← mul_assoc, ← star_mul, mul_assoc _ _ (star (y : A))]⟩
  have thisα : α = RCLike.re α := by
    have this10 := by simpa [IsSelfAdjoint, ← hα] using IsSelfAdjoint.star_mul_self (y : A)
    rwa [(smul_left_injective _ one_ne_zero).eq_iff, RCLike.conj_eq_iff_re, eq_comm] at this10
  have thisα' : α ≠ 0 := fun h ↦ by simp [h, ← hα] at this
  have this2 : 0 ≤ α := by
    rw [thisα, RCLike.ofReal_nonneg]
    by_contra! this2
    exact one_ne_zero <| (IsUnit.mk0 _ thisα').smul_eq_zero.mp (thisα.symm ▸ le_antisymm
      (smul_zero (RCLike.re α : 𝕜) (A := A) ▸ smul_le_smul_of_nonpos_left zero_le_one
        (by simpa using this2.le))
      (thisα ▸ hα ▸ star_mul_self_nonneg (y : A)))
  replace this2 := RCLike.ofReal_pos.mp <| thisα ▸ (lt_of_le_of_ne' this2 thisα')
  have thisU : y * star (y : A) = α • (1 : A) := by simp [← Units.mul_left_inj y, mul_assoc, ← hα]
  set αa := (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜)
  have isU : αa • (y : A) ∈ unitary A := by
    simp_rw [Unitary.mem_iff, star_smul, RCLike.star_def, smul_mul_smul, αa, RCLike.conj_ofReal,
      ← RCLike.ofReal_mul, ← Real.rpow_add this2, ← hα, thisU]
    norm_num
    nth_rw 2 [thisα]
    simp [smul_smul, ← RCLike.ofReal_mul, ← Real.rpow_add_one (NeZero.of_pos this2).out]
  set U : unitary A := ⟨_, isU⟩
  have Uinv : ((((RCLike.re α : ℝ) ^ ((1 / 2 : ℝ)) : ℝ) : 𝕜) • ((y⁻¹ : Aˣ) : A)) =
      (U⁻¹ : unitary A) := by
    rw [← neg_neg (1 / 2 : ℝ), Real.rpow_neg_eq_inv_rpow, Real.inv_rpow this2.le]
    set α' : 𝕜ˣ := Units.mk0 αa <| by
      simp only [one_div, ne_eq, map_eq_zero, αa]
      rw [Real.rpow_eq_zero this2.le (by simp)]
      exact ne_of_gt this2
    rw [RCLike.ofReal_inv, show ↑(RCLike.re α ^ (-(1 / 2 : ℝ))) = αa by rfl]
    have := by simpa only [Units.val_smul] using congr(($(Units.smul_inv α' y) : A))
    rw [show α' • y = Unitary.toUnits U by ext; simp [α', αa, U]] at this
    rw [show ((U⁻¹ : unitary A) : A) = ((Unitary.toUnits U)⁻¹ : Aˣ) by rfl, this]
    congr
  use U
  rw [← Unitary.coe_star, Unitary.star_eq_inv, ← Uinv]
  simp [αa, Algebra.smul_mul_assoc, U, smul_smul, ← RCLike.ofReal_mul, ← Real.rpow_add this2, hy]

section
open Matrix
variable {n : Type*} [Fintype n]

-- TODO: wait for other PR
proof_wanted Matrix.AlgEquiv.coe_eq_conjugate {m : Type*} [Fintype m] [DecidableEq m]
    [DecidableEq n] {K : Type*} [Field K] (f : Matrix m m K ≃ₐ[K] Matrix n n K) :
    ∃ (U : Matrix n m K) (V : Matrix m n K) (hUV : U * V = 1), ⇑f = fun x ↦ U * x * V

-- TODO: change `Matrix` to any central and simple finite algebra
-- and then also add the `AlgHom` version of this
-- and then also move this file outside of the `Matrix` folder
public theorem AlgEquiv.eq_mulSemiringActionToAlgEquiv_conjAct [DecidableEq n] {K : Type*} [Field K]
    (f : Matrix n n K ≃ₐ[K] Matrix n n K) :
    ∃ U : GL n K, f = MulSemiringAction.toAlgEquiv K (G := ConjAct (GL n K)) _ U := by
  obtain ⟨U, hU⟩ := ((toLinAlgEquiv'.symm.trans f).trans toLinAlgEquiv').eq_linearEquivConjAlgEquiv
  use GeneralLinearGroup.toLin.symm (.ofLinearEquiv U)
  ext1 x
  have := by simpa using congr((toLinAlgEquiv'.trans $hU).trans toLinAlgEquiv'.symm x)
  simp only [this, LinearMap.toMatrixAlgEquiv', toLinAlgEquiv', AlgEquiv.ofLinearEquiv_symm,
    LinearMap.toMatrix'_symm, AlgEquiv.ofLinearEquiv_apply, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', ← mul_assoc,
    MulSemiringAction.toAlgEquiv_apply, ConjAct.units_smul_def, coe_units_inv]
  congr
  refine (inv_eq_right_inv ?_).symm
  simp [ConjAct.ofConjAct, GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.ofLinearEquiv,
    LinearMap.toMatrixAlgEquiv', ← LinearMap.toMatrix'_comp]

open ComplexOrder MatrixOrder

-- TODO: change `Matrix` to any central, simple and star-ordered finite algebra
-- and then also add the `StarAlgHom` version of this
public theorem StarAlgEquiv.eq_unitaryConjStarAlgAut [DecidableEq n]
    (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) :
    ∃ U : unitaryGroup n 𝕜, f = Unitary.conjStarAlgAut 𝕜 _ U := by
  obtain ⟨g, hg⟩ := f.toAlgEquiv.eq_mulSemiringActionToAlgEquiv_conjAct
  have := StarHom.coe_eq_units_conjugate_iff_coe_eq_unitary_conjugate (𝕜 := 𝕜) 1 f (by simp)
  obtain ⟨U, hU⟩ := this.mp ⟨g, congr($hg)⟩
  exact ⟨U, StarAlgEquiv.ext <| congrFun hU⟩

end

theorem ContinuousLinearEquiv.eq_comp_toContinuousLinearMap_symm
    {R₁ R₂ R₃ M₁ M₂ M₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid M₃] {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂}
    {module_M₃ : Module R₃ M₃} [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]
    {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} {σ₁₃ : R₁ →+* R₃}
    {σ₂₃ : R₂ →+* R₃} {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] {e₁₂ : M₁ ≃SL[σ₁₂] M₂} [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃]
    (f : M₂ →SL[σ₂₃] M₃) (g : M₁ →SL[σ₁₃] M₃) :
    f = g.comp e₁₂.symm.toContinuousLinearMap ↔ f.comp e₁₂.toContinuousLinearMap = g := by
  aesop

/-- Interpret a `ContinuousAlgHom` as a `ContinuousLinearMap`. -/
def ContinuousAlgHom.toContinuousLinearMap {R A B : Type*} [CommSemiring R] [Semiring A]
    [TopologicalSpace A] [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
    (e : A →A[R] B) : A →L[R] B :=
  { e with map_smul' := by simp }

/-- Interpret a `ContinuousAlgEquiv` as a `ContinuousLinearMap`. -/
abbrev ContinuousAlgEquiv.toContinuousLinearMap {R A B : Type*} [CommSemiring R] [Semiring A]
    [TopologicalSpace A] [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
    (e : A ≃A[R] B) : A →L[R] B := e.toContinuousAlgHom.toContinuousLinearMap

@[simp] theorem ContinuousAlgEquiv.coe_toContinuousLinearMap {R A B : Type*} [CommSemiring R]
    [Semiring A] [TopologicalSpace A] [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
    (e : A ≃A[R] B) : ⇑e.toContinuousLinearMap = e := rfl

open ContinuousLinearMap

theorem ContinuousAlgEquiv.coe_eq_conjugate {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]
    [SeparatingDual 𝕜 V] [SeparatingDual 𝕜 W] [CompleteSpace V] [CompleteSpace W]
    (f : (V →L[𝕜] V) ≃A[𝕜] (W →L[𝕜] W)) :
    ∃ U : V ≃L[𝕜] W, ⇑f = fun x ↦ U ∘L x ∘L U.symm := by
  /- basically copied the same proof as the linear one -/
  by_cases! hV : Subsingleton V
  · by_cases! hV : Subsingleton W
    · use { toLinearEquiv := 0, continuous_invFun := by fun_prop }
      exact Subsingleton.allEq _ _
    simpa using congr(f $(Subsingleton.allEq 0 1))
  simp_rw [funext_iff, ← comp_assoc, ContinuousLinearEquiv.eq_comp_toContinuousLinearMap_symm]
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  obtain ⟨v, huv⟩ := SeparatingDual.exists_ne_zero (R := 𝕜) hu
  obtain ⟨z, hz⟩ : ∃ z : W, ¬ f (smulRight v u) z = (0 : W →L[𝕜] W) z := by
    rw [← not_forall, ← ContinuousLinearMap.ext_iff, EmbeddingLike.map_eq_zero_iff,
      ContinuousLinearMap.ext_iff]
    exact not_forall.mpr ⟨u, huv.isUnit.smul_eq_zero.not.mpr hu⟩
  set T := ContinuousLinearMap.apply' _ (.id 𝕜) z ∘L f.toContinuousLinearMap ∘L smulRightL 𝕜 _ _ v
  have hT x : T x = f (smulRight v x) z := rfl
  have this A x : T (A x) = f A (T x) := by
    simp only [hT, ← ContinuousLinearMap.mul_apply, ← map_mul]
    congr; ext; simp
  have surj : Function.Surjective T := fun w ↦ by
    obtain ⟨d, hd⟩ := SeparatingDual.exists_eq_one (R := 𝕜) hz
    exact ⟨f.symm (smulRight d w) u, by simp [T, this, hd]⟩
  have inj : Function.Injective T := fun x y hxy ↦ by
    have h_smul : smulRightL 𝕜 _ _ v x = smulRightL 𝕜 _ _ v y := by
      apply f.injective <| ContinuousLinearMap.ext fun z ↦ ?_
      obtain ⟨w, rfl⟩ := surj z
      simp [← this, hxy]
    simpa [huv.isUnit.smul_left_cancel] using congr((fun f ↦ f u) $h_smul)
  exact ⟨.ofBijective T ((LinearMapClass.ker_eq_bot _).mpr inj)
    (LinearMap.range_eq_top_of_surjective T surj), fun A ↦ (ContinuousLinearMap.ext <| this A).symm⟩

/-- Interpret a ⋆-algebra equivalence as a continuous algebra equivalence when it is continuous. -/
abbrev StarAlgEquiv.toContinuousAlgEquiv {R A B : Type*} [CommSemiring R] [Semiring A]
    [TopologicalSpace A] [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
    [Star R] [Star A] [Star B] (e : A ≃⋆ₐ[R] B) (he : Continuous e) (he' : Continuous e.symm) :
    A ≃A[R] B :=
  { e.toAlgEquiv with continuous_toFun := he, continuous_invFun := he' }

@[simp] theorem StarAlgEquiv.coe_toContinuousAlgEquiv {R A B : Type*} [CommSemiring R] [Semiring A]
    [TopologicalSpace A] [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
    [Star R] [Star A] [Star B] (e : A ≃⋆ₐ[R] B) (he : Continuous e) (he' : Continuous e.symm) :
    ⇑(e.toContinuousAlgEquiv he he') = e := rfl

theorem StarAlgEquiv.eq_unitaryConjStarAlgAut_symm_unitaryLinearIsometryEquiv
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (f : (V →L[ℂ] V) ≃⋆ₐ[ℂ] (V →L[ℂ] V)) (hf : Continuous f) (hf' : Continuous f.symm) :
    ∃ U : V ≃ₗᵢ[ℂ] V, f = Unitary.conjStarAlgAut ℂ _
      ((Unitary.linearIsometryEquiv (𝕜 := ℂ)).symm U) := by
  obtain ⟨g, hg⟩ := f.toContinuousAlgEquiv hf hf' |>.coe_eq_conjugate
  obtain ⟨U, hU⟩ := StarHom.coe_eq_units_conjugate_iff_coe_eq_unitary_conjugate (𝕜 := ℂ)
    1 f (by simp) |>.mp ⟨g.toUnit, congr($hg)⟩
  exact ⟨Unitary.linearIsometryEquiv U, StarAlgEquiv.ext <| congrFun hU⟩

theorem ContinuousLinearEquiv.isometry_iff_adjoint_eq_symm
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W] (e : V ≃L[𝕜] W) :
    Isometry e ↔ adjoint e.toContinuousLinearMap = e.symm.toContinuousLinearMap := by
  simp_rw [AddMonoidHomClass.isometry_iff_norm, ← coe_coe, norm_map_iff_adjoint_comp_self]
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun x ↦ by simpa using congr($h (e.symm x)), fun h ↦ ?_⟩
  simp [h, one_def]

/-- can't do this inline, it times out -/
noncomputable abbrev aux_isometry
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]
    (e : V ≃L[𝕜] W) {α α' : 𝕜} (hα : α ≠ 0) (hα2 : α' * α' = α⁻¹)
    (he : e.toContinuousLinearMap.adjoint ∘L e = α • .id 𝕜 V)
    (he' : e ∘L e.toContinuousLinearMap.adjoint = α • .id 𝕜 W) :
    V ≃L[𝕜] W where
  toFun := (α' • e.toContinuousLinearMap).toLinearMap
  invFun := (α' • e.toContinuousLinearMap.adjoint).toLinearMap
  left_inv := by
    simp only [coe_smul, Function.leftInverse_iff_comp, funext_iff, Function.comp_apply,
      LinearMap.smul_apply, coe_coe, ContinuousLinearEquiv.coe_coe, map_smul, smul_smul, hα2, id_eq]
    simp_rw [← ContinuousLinearEquiv.coe_coe, ← comp_apply, he]
    simp [smul_smul, hα]
  right_inv := by
    simp only [coe_smul, Function.rightInverse_iff_comp, funext_iff, Function.comp_apply,
      LinearMap.smul_apply, coe_coe, map_smul, ContinuousLinearEquiv.coe_coe, smul_smul, hα2, id_eq]
    simp_rw [← ContinuousLinearEquiv.coe_coe, ← comp_apply, he']
    simp [smul_smul, hα]
  map_add' := by simp
  map_smul' := by simp
  continuous_toFun := (α' • e.toContinuousLinearMap).continuous
  continuous_invFun := (α' • e.toContinuousLinearMap.adjoint).continuous

theorem adjoint_aux_isometry
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]
    (e : V ≃L[𝕜] W) {α α' : 𝕜} (hα : α ≠ 0) (hα2 : α' * α' = α⁻¹)
    (he : e.toContinuousLinearMap.adjoint ∘L e = α • .id 𝕜 V)
    (he' : e ∘L e.toContinuousLinearMap.adjoint = α • .id 𝕜 W)
    (hαa : starRingEnd 𝕜 α' = α') :
    adjoint (aux_isometry e hα hα2 he he').toContinuousLinearMap =
      α' • e.toContinuousLinearMap.adjoint := by
  ext x
  apply ext_inner_left 𝕜 fun y ↦ ?_
  simp [aux_isometry, adjoint_inner_right, inner_smul_left, inner_smul_right, hαa]

/-- can't do this inline either, it times out -/
noncomputable abbrev aux_isometry'
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]
    (e : V ≃L[𝕜] W) {α α' : 𝕜} (hα : α ≠ 0) (hα2 : α' * α' = α⁻¹)
    (he : e.toContinuousLinearMap.adjoint ∘L e = α • .id 𝕜 V)
    (he' : e ∘L e.toContinuousLinearMap.adjoint = α • .id 𝕜 W)
    (hαa : starRingEnd 𝕜 α' = α') :
    V ≃ₗᵢ[𝕜] W where
  __ := aux_isometry e hα hα2 he he' |>.toLinearEquiv
  norm_map' _ := by
    have heI : Isometry (aux_isometry e hα hα2 he he') := by
      rw [ContinuousLinearEquiv.isometry_iff_adjoint_eq_symm]
      exact adjoint_aux_isometry e hα hα2 he he' hαa
    simpa using heI.norm_map_of_map_zero (by simp) _

theorem coe_aux_isometry' {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]
    (e : V ≃L[𝕜] W) {α α' : 𝕜} (hα : α ≠ 0) (hα2 : α' * α' = α⁻¹)
    (he : e.toContinuousLinearMap.adjoint ∘L e = α • .id 𝕜 V)
    (he' : e ∘L e.toContinuousLinearMap.adjoint = α • .id 𝕜 W)
    (hαa : starRingEnd 𝕜 α' = α') :
    (aux_isometry' e hα hα2 he he' hαa).toContinuousLinearEquiv.toContinuousLinearMap =
      α' • e.toContinuousLinearMap := rfl

theorem coe_symm_aux_isometry' {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]
    (e : V ≃L[𝕜] W) {α α' : 𝕜} (hα : α ≠ 0) (hα2 : α' * α' = α⁻¹)
    (he : e.toContinuousLinearMap.adjoint ∘L e = α • .id 𝕜 V)
    (he' : e ∘L e.toContinuousLinearMap.adjoint = α • .id 𝕜 W)
    (hαa : starRingEnd 𝕜 α' = α') :
    (aux_isometry' e hα hα2 he he' hαa).toContinuousLinearEquiv.symm.toContinuousLinearMap =
      α'⁻¹ • e.symm.toContinuousLinearMap := by
  ext y
  apply (aux_isometry' e hα hα2 he he' hαa).toContinuousLinearEquiv.injective
  simp [smul_smul, inv_mul_cancel₀ (a := α') (by grind)]

theorem LinearMap.IsSymmetric.isSymmetric_smul_iff {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] {f : V →ₗ[𝕜] V} (hf : f.IsSymmetric) (hf' : f ≠ 0) (α : 𝕜) :
    (α • f).IsSymmetric ↔ starRingEnd 𝕜 α = α := by
  refine ⟨fun h ↦ ?_, hf.smul⟩
  simp only [IsSymmetric, smul_apply, inner_smul_left, inner_smul_right, hf _ _,
    mul_eq_mul_right_iff, forall_or_left] at h
  have : f = 0 ↔ ∀ x y, inner 𝕜 x (f y) = inner 𝕜 x ((0 : V →ₗ[𝕜] V) y) := by
    rw [forall_comm]
    simp_rw [LinearMap.ext_iff, ← ext_iff_inner_left 𝕜]
  simp_rw [← (by simpa using this), hf', or_false] at h
  exact h

theorem ContinuousLinearMap.IsPositive.isPositive_smul_iff {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] {f : V →L[𝕜] V} (hf : f.IsPositive) (hf' : f ≠ 0) (α : 𝕜) :
    (α • f).IsPositive ↔ 0 ≤ α := by
  simp only [IsPositive, coe_smul, hf.isSymmetric.isSymmetric_smul_iff (by exact_mod_cast hf'),
    reApplyInnerSelf, coe_smul', Pi.smul_apply, inner_smul_left]
  refine ⟨fun ⟨h1, h2⟩ ↦ ?_, fun h ↦ ?_⟩
  · have : (RCLike.re α : 𝕜) = α := RCLike.conj_eq_iff_re.mp h1
    apply RCLike.re_nonneg_of_nonneg h1 |>.mp
    rw [h1, ← this] at h2
    simp only [RCLike.re_ofReal_mul, mul_nonneg_iff] at h2
    have := by simpa [reApplyInnerSelf] using fun x ↦ hf.2 x
    simp only [this, and_true, forall_or_left] at h2
    obtain (h | h) := h2
    · exact h
    · rw [forall_and_left] at h
      have := hf.isSymmetric.inner_map_self_eq_zero.not.mpr (by exact_mod_cast hf')
      simp_rw [RCLike.ext_iff (K := 𝕜), forall_and] at this
      simp only [coe_coe, map_zero] at this
      have this' := by simpa using hf.isSymmetric.im_inner_apply_self
      simp_rw [this', forall_true_iff, and_true] at this
      grind
  · rw [RCLike.nonneg_iff] at h
    simp_all only [ne_eq, RCLike.conj_eq_iff_im, RCLike.mul_re, RCLike.conj_re, RCLike.conj_im,
      neg_zero, zero_mul, sub_zero, true_and]
    intro x
    exact mul_nonneg h.1 (hf.2 _)

set_option maxHeartbeats 200400 in
-- :FIXME: slow proof
theorem ContinuousStarAlgEquiv.coe_eq_conjugate'
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]
    (f : (V →L[𝕜] V) ≃⋆ₐ[𝕜] (W →L[𝕜] W)) (hf : Continuous f) (hf' : Continuous f.symm) :
    ∃ U : V ≃ₗᵢ[𝕜] W, ⇑f =
      fun x ↦ U.toContinuousLinearEquiv ∘L x ∘L U.symm.toContinuousLinearEquiv := by
  obtain ⟨y, hy⟩ := f.toContinuousAlgEquiv hf hf' |>.coe_eq_conjugate
  by_cases! hV : Subsingleton V
  · by_cases! hV : Subsingleton W
    · use { toLinearEquiv := 0, norm_map' _ := by simp [Subsingleton.eq_zero] }
      exact Subsingleton.allEq _ _
    simpa using congr(f $(Subsingleton.allEq 0 1))
  have (x : V →L[𝕜] V) : adjoint (f x) = f (adjoint x) := map_star _ _ |>.symm
  simp_rw [(StarAlgEquiv.coe_toContinuousAlgEquiv _ hf _ ▸ hy), adjoint_comp] at this
  replace this (x : V →L[𝕜] V) : adjoint y.toContinuousLinearMap ∘L y.toContinuousLinearMap ∘L
      adjoint x ∘L y.symm.toContinuousLinearMap = adjoint x ∘L
        adjoint y.toContinuousLinearMap := by
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
    rw [← ContinuousLinearMap.IsPositive.isPositive_smul_iff (V := V) isPositive_one]
    · exact (nonneg_iff_isPositive _).mp this1
    · exact one_ne_zero' (V →L[𝕜] V)
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
  set U := aux_isometry' y thisα' αa2 hα.symm thisU (by simp [αa])
  use U
  have la : αa⁻¹ * αa = 1 := by
    simp only [one_div, αa]
    exact inv_mul_cancel₀ (by
      simp only [ne_eq, map_eq_zero]
      rw [Real.rpow_eq_zero this2.le (by simp)]
      exact ne_of_gt this2)
  simp [U, coe_aux_isometry', coe_symm_aux_isometry', smul_smul, la, ← hy]
