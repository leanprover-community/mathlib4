/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/

import Mathlib.LinearAlgebra.ExteriorPower.InducedForm
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

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
--variable (B : LinearMap.BilinForm F V)

--noncomputable abbrev n : ℕ := Module.finrank F V

#check Module.finrank F V
#check LinearMap.BilinForm.toDual

variable {k : ℕ} in
#check dualTensorHomEquiv F (⋀[F]^(finrank F V - k) V) (⋀[F]^(finrank F V) V)

#check fun (α β : ExteriorAlgebra F V) ↦ α * β

variable (B : LinearMap.BilinForm F V)
local notation "⟪" v ", " w "⟫" => exteriorPower.BilinForm B _ v w

variable (vol : ⋀[F]^(finrank F V) V)

noncomputable def volumeEquiv (h : ⟪vol, vol⟫ = 1) : ⋀[F]^(finrank F V) V ≃ₗ[F] F where
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
    rw [← LinearMap.BilinForm.smul_right, hvol, h]
    simp
  right_inv := by
    intro f
    simp only [map_smul, smul_eq_mul, h, mul_one]
  map_add' := sorry
  map_smul' := sorry

#check TensorProduct.rid
variable (hVol : ⟪vol, vol⟫ = 1)
--def Wedge {k : ℕ} (α : ⋀[F]^k V) := (fun (β : ExteriorAlgebra F V) ↦ α * β)
def Wedge {k : ℕ} (α : ⋀[F]^k V) : ⋀[F]^(finrank F V - k) V →ₗ[F] ⋀[F]^(finrank F V) V := sorry

variable (hN : B.Nondegenerate)
variable (k : ℕ) in
#check LinearEquiv.rTensor ((⋀[F]^(finrank F V) V))
  (LinearMap.BilinForm.toDual (exteriorPower.BilinForm B _) (bilin_nondegen B (finrank F V - k) hN))

#check volumeEquiv B vol hVol
variable (k : ℕ) in
#check LinearEquiv.lTensor (R := F) (⋀[F]^(finrank F V - k) V) (volumeEquiv B vol hVol)

noncomputable def HodgeStar {k : ℕ} := fun (α : ⋀[F]^k V) ↦
  TensorProduct.rid F (⋀[F]^(finrank F V - k) V)
  (LinearEquiv.lTensor (R := F) (⋀[F]^(finrank F V - k) V) (volumeEquiv B vol hVol)
  ((LinearEquiv.rTensor ((⋀[F]^(finrank F V) V))
  (LinearMap.BilinForm.toDual (exteriorPower.BilinForm B _)
  (bilin_nondegen B (finrank F V - k) hN))).symm
  ((dualTensorHomEquiv F (⋀[F]^(finrank F V - k) V) (⋀[F]^(finrank F V) V)).symm
  (Wedge α))))

#check HodgeStar

end exteriorPower
