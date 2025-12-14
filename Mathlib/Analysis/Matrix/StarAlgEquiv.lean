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

import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
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

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

-- TODO: change `Matrix` to any central and simple finite algebra
-- and then also add the `AlgHom` version of this
-- and then also move this file outside of the `Matrix` folder
public theorem AlgEquiv.eq_mulSemiringActionToAlgEquiv_conjAct {K : Type*} [Field K]
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

-- TODO: change `Matrix` to any central, simple and star-ordered finite algebra
-- and then also add the `StarAlgHom` version of this
open ComplexOrder MatrixOrder in
public theorem StarAlgEquiv.eq_unitaryConjStarAlgAut (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) :
    ∃ U : unitaryGroup n 𝕜, f = Unitary.conjStarAlgAut 𝕜 _ U := by
  obtain ⟨g, hg⟩ := f.toAlgEquiv.eq_mulSemiringActionToAlgEquiv_conjAct
  have := StarHom.coe_eq_units_conjugate_iff_coe_eq_unitary_conjugate (𝕜 := 𝕜) 1 f (by simp)
  obtain ⟨U, hU⟩ := this.mp ⟨g, congr($hg)⟩
  exact ⟨U, StarAlgEquiv.ext <| congrFun hU⟩
