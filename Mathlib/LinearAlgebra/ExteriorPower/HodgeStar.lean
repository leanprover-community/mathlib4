/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/

import Mathlib.LinearAlgebra.ExteriorPower.InducedForm
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.WedgeProduct
import Mathlib.LinearAlgebra.PerfectPairing.Basic

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

variable {k : ℕ} (hk : k ≤ finrank F V) in
#check WedgeProduct (R := F) (M := V) (Nat.add_sub_of_le hk)


#check LinearEquiv.injective
#check Function.Injective.comp
#check Function.Injective.injective_linearMapComp_left

noncomputable def HodgePairing' {k : ℕ} (hk : k ≤ finrank F V) :
  PerfectPairing F (⋀[F]^k V) (⋀[F]^(finrank F V - k) V) := PerfectPairing.mkOfInjective
    ((WedgeProduct (R := F) (M := V) (Nat.add_sub_of_le hk)).compr₂ (equivOfVol B vol volNormOne))
    (by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro α h

      sorry)
    ( by

      sorry)

variable (hN : B.Nondegenerate)

theorem hodge_pair_def {k : ℕ} (hk : k ≤ finrank F V) (α : ⋀[F]^k V)
  (β : ⋀[F]^(finrank F V - k) V) :
  HodgePairing B vol volNormOne hk α β = ⟪vol, WedgeProduct (Nat.add_sub_of_le hk) α β⟫ := by rfl

noncomputable def HodgeStar {k : ℕ} (hk : k ≤ finrank F V) :
  ⋀[F]^k V →ₗ[F] ⋀[F]^(finrank F V - k) V where
  toFun α := (LinearMap.BilinForm.toDual (exteriorPower.BilinForm B _)
    (bilin_nondegen B (finrank F V - k) hN)).symm (HodgePairing B vol volNormOne hk α)
  map_add' := by
    simp only [map_add, implies_true]
  map_smul' := by
    simp only [map_smul, RingHom.id_apply, implies_true]

variable {k : ℕ} (hk : k ≤ finrank F V)

local notation "HStar"  => HodgeStar B vol volNormOne hN hk
local notation "⟪" v ", " w "⟫" => exteriorPower.BilinForm B k v w

theorem hodge_def (α : ⋀[F]^k V) :
  exteriorPower.BilinForm B (finrank F V - k) (HStar α) =
  HodgePairing B vol volNormOne hk α := by
  unfold HodgeStar
  dsimp
  ext γ
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.BilinForm.apply_toDual_symm_apply]

theorem hodge_invariant (α β : ⋀[F]^k V) : ⟪HStar α, HStar β⟫ =
  exteriorPower.BilinForm B k α β := by
  rw [hodge_def]

  sorry

theorem hodge_property (α β : ⋀[F]^k V) : WedgeProduct (Nat.add_sub_of_le hk) α (HStar β) =
  exteriorPower.BilinForm B k α β • vol := by
  apply LinearEquiv.injective (equivOfVol B vol volNormOne)
  unfold equivOfVol
  simp only [map_smul, smul_eq_mul]
  dsimp
  rw [volNormOne, mul_one]
  rw [← hodge_pair_def B vol volNormOne hk]
  rw [← hodge_def B vol volNormOne hN hk]
  exact hodge_invariant B vol volNormOne hN hk α β

end exteriorPower
