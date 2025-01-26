/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/

import Mathlib.LinearAlgebra.ExteriorPower.InducedForm
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.WedgeProduct

/-!
Documentation
-/
/-
Hodge star operator or Hodge star is a linear map defined on the exterior algebra of a
finite-dimensional oriented vector space endowed with a nondegenerate symmetric bilinear form.

α = ⋀ α_i , β = ⋀ β_i ∈ ⋀ᵏ V
⟨α , β⟩ = det( ⟨α_i , β_j⟩ )

{e_i} orthonormal basis for V
ω = ⋀ e_i
α ∧ ⋆β = ⟨α , β⟩ ω
-/

open Module

namespace exteriorPower

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

variable (B : LinearMap.BilinForm F V)
local notation "⟪" v ", " w "⟫" => exteriorPower.BilinForm B _ v w

variable (vol : ⋀[F]^(finrank F V) V)
variable (volNormOne : exteriorPower.BilinForm B _ vol vol = 1)

noncomputable def equivOfVol : ⋀[F]^(finrank F V) V ≃ₗ[F] F where
  toFun := fun v ↦ ⟪vol, v⟫
  invFun := fun f ↦ f • vol
  left_inv := by
    intro v
    have rank_one : finrank F (⋀[F]^(finrank F V) V) = 1 := by
      rw [finrank_eq F, Nat.choose_self]
    obtain ⟨w, _, hw⟩ := finrank_eq_one_iff'.mp rank_one
    obtain ⟨cv, hv⟩ := hw v
    obtain ⟨cvol, hvol⟩ := hw vol
    dsimp
    rw [← hv]
    nth_rw 2 [← hvol]
    rw [LinearMap.BilinForm.smul_right]
    rw [← smul_assoc]
    nth_rw 1 [smul_eq_mul]
    rw [mul_assoc]
    nth_rw 2 [mul_comm]
    rw [← LinearMap.BilinForm.smul_right, hvol, volNormOne]
    simp
  right_inv := by
    intro f
    simp only [map_smul, smul_eq_mul, volNormOne, mul_one]
  map_add' := map_add _
  map_smul' := map_smul _

noncomputable def HodgePairing {k : ℕ} (hk : k ≤ finrank F V) :
  ⋀[F]^k V →ₗ[F] ⋀[F]^(finrank F V - k) V →ₗ[F] F where
  toFun α:= {
    toFun := fun β ↦ equivOfVol B vol volNormOne <| WedgeProduct (Nat.add_sub_of_le hk) α β
    map_add' := by simp only [map_add, implies_true]
    map_smul' := by simp only [map_smul, smul_eq_mul, RingHom.id_apply, implies_true] }
  map_add' := by
    intro x y
    ext β
    simp only [map_add, LinearMap.add_apply, LinearMap.compAlternatingMap_apply, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_compAlternatingMap, AlternatingMap.add_apply]
  map_smul' := by
    intro a x
    ext β
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, LinearMap.compAlternatingMap_apply,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_compAlternatingMap,
      AlternatingMap.smul_apply]

variable (hN : B.Nondegenerate)

noncomputable def HodgeStar {k : ℕ} (hk : k ≤ finrank F V) :
  ⋀[F]^k V →ₗ[F] ⋀[F]^(finrank F V - k) V where
  toFun α := (LinearMap.BilinForm.toDual (exteriorPower.BilinForm B _)
    (bilin_nondegen B (finrank F V - k) hN)).symm <| TensorProduct.rid F
    (Dual F (⋀[F]^(finrank F V - k) V)) <| (dualTensorHomEquiv F (⋀[F]^(finrank F V - k) V) F).symm
    (HodgePairing B vol volNormOne hk α)
  map_add' := by
    intro x y
    rw [← map_add, LinearEquiv.symm_apply_eq, LinearEquiv.apply_symm_apply, map_add, map_add]
    rw [← LinearEquiv.eq_symm_apply, map_add]
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  map_smul' := by
    intro a x
    dsimp
    rw [← map_smul, EquivLike.apply_eq_iff_eq, ← LinearEquiv.eq_symm_apply]
    rw [map_smul (TensorProduct.rid F (Dual F ↥(⋀[F]^(finrank F V - k) V))).symm a]
    rw [LinearEquiv.symm_apply_apply, map_smul, map_smul]

variable {k : ℕ} (hk : k ≤ finrank F V)
#check HodgeStar B vol volNormOne hN hk

end exteriorPower
