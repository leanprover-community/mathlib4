/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

! This file was ported from Lean 3 source module number_theory.modular_forms.congruence_subgroups
! leanprover-community/mathlib commit ae690b0c236e488a0043f6faa8ce3546e7f2f9c5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Zmod.Basic
import Mathbin.GroupTheory.GroupAction.ConjAct
import Mathbin.GroupTheory.Subgroup.Pointwise
import Mathbin.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Congruence subgroups

This defines congruence subgroups of `SL(2, ℤ)` such as `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` for `N` a
natural number.

It also contains basic results about congruence subgroups.

-/


-- mathport name: «exprSL( , )»
local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToFun

-- mathport name: «expr↑ₘ »
local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) _) _

open Matrix.SpecialLinearGroup Matrix

variable (N : ℕ)

-- mathport name: «exprSLMOD( )»
local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

@[simp]
theorem SL_reduction_mod_hom_val (N : ℕ) (γ : SL(2, ℤ)) :
    ∀ i j : Fin 2, (SLMOD(N) γ : Matrix (Fin 2) (Fin 2) (ZMod N)) i j = ((↑ₘγ i j : ℤ) : ZMod N) :=
  fun i j => rfl
#align SL_reduction_mod_hom_val SL_reduction_mod_hom_val

/-- The full level `N` congruence subgroup of `SL(2, ℤ)` of matrices that reduce to the identity
modulo `N`.-/
def gamma (N : ℕ) : Subgroup SL(2, ℤ) :=
  SLMOD(N).ker
#align Gamma gamma

theorem gamma_mem' (N : ℕ) (γ : SL(2, ℤ)) : γ ∈ gamma N ↔ SLMOD(N) γ = 1 :=
  Iff.rfl
#align Gamma_mem' gamma_mem'

@[simp]
theorem gamma_mem (N : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ gamma N ↔
      ((↑ₘγ 0 0 : ℤ) : ZMod N) = 1 ∧
        ((↑ₘγ 0 1 : ℤ) : ZMod N) = 0 ∧
          ((↑ₘγ 1 0 : ℤ) : ZMod N) = 0 ∧ ((↑ₘγ 1 1 : ℤ) : ZMod N) = 1 :=
  by
  rw [gamma_mem']
  constructor
  · intro h
    simp [← SL_reduction_mod_hom_val N γ, h]
  · intro h
    ext
    rw [SL_reduction_mod_hom_val N γ]
    fin_cases i <;> fin_cases j
    all_goals simp_rw [h]; rfl
#align Gamma_mem gamma_mem

theorem gamma_normal (N : ℕ) : Subgroup.Normal (gamma N) :=
  SLMOD(N).normal_ker
#align Gamma_normal gamma_normal

theorem gamma_one_top : gamma 1 = ⊤ := by
  ext
  simp
#align Gamma_one_top gamma_one_top

theorem gamma_zero_bot : gamma 0 = ⊥ := by
  ext
  simp only [gamma_mem, coe_coe, coe_matrix_coe, Int.coe_castRingHom, map_apply, Int.cast_id,
    Subgroup.mem_bot]
  constructor
  · intro h
    ext
    fin_cases i <;> fin_cases j
    any_goals simp [h]
  · intro h
    simp [h]
#align Gamma_zero_bot gamma_zero_bot

/-- The congruence subgroup of `SL(2, ℤ)` of matrices whose lower left-hand entry reduces to zero
modulo `N`. -/
def gamma0 (N : ℕ) : Subgroup SL(2, ℤ)
    where
  carrier := { g : SL(2, ℤ) | ((↑ₘg 1 0 : ℤ) : ZMod N) = 0 }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq]
    have h := (Matrix.two_mul_expl a.1 b.1).2.2.1
    simp only [coe_coe, coe_matrix_coe, coe_mul, Int.coe_castRingHom, map_apply, Set.mem_setOf_eq,
      Subtype.val_eq_coe, mul_eq_mul] at *
    rw [h]
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Subtype.val_eq_coe]
    rw [SL2_inv_expl a]
    simp only [Subtype.val_eq_coe, cons_val_zero, cons_val_one, head_cons, coe_coe, coe_matrix_coe,
      coe_mk, Int.coe_castRingHom, map_apply, Int.cast_neg, neg_eq_zero, Set.mem_setOf_eq] at *
    exact ha
#align Gamma0 gamma0

@[simp]
theorem gamma0_mem (N : ℕ) (A : SL(2, ℤ)) : A ∈ gamma0 N ↔ ((↑ₘA 1 0 : ℤ) : ZMod N) = 0 :=
  Iff.rfl
#align Gamma0_mem gamma0_mem

theorem gamma0_det (N : ℕ) (A : gamma0 N) : (A.1.1.det : ZMod N) = 1 := by simp [A.1.property]
#align Gamma0_det gamma0_det

/-- The group homomorphism from `Gamma0` to `zmod N` given by mapping a matrix to its lower
right-hand entry. -/
def gamma0Map (N : ℕ) : gamma0 N →* ZMod N
    where
  toFun g := ((↑ₘg 1 1 : ℤ) : ZMod N)
  map_one' := by simp
  map_mul' := by
    intro A B
    have := (two_mul_expl A.1.1 B.1.1).2.2.2
    simp only [coe_coe, Subgroup.coe_mul, coe_matrix_coe, coe_mul, Int.coe_castRingHom, map_apply,
      Subtype.val_eq_coe, mul_eq_mul] at *
    rw [this]
    have ha := A.property
    simp only [Int.cast_add, Int.cast_mul, add_left_eq_self, Subtype.val_eq_coe, gamma0_mem,
      coe_coe, coe_matrix_coe, Int.coe_castRingHom, map_apply] at *
    rw [ha]
    simp
#align Gamma_0_map gamma0Map

/-- The congruence subgroup `Gamma1` (as a subgroup of `Gamma0`) of matrices whose bottom
row is congruent to `(0,1)` modulo `N`.-/
def gamma1' (N : ℕ) : Subgroup (gamma0 N) :=
  (gamma0Map N).ker
#align Gamma1' gamma1'

@[simp]
theorem Gamma1_mem' (N : ℕ) (γ : gamma0 N) : γ ∈ gamma1' N ↔ (gamma0Map N) γ = 1 :=
  Iff.rfl
#align Gamma1_mem' Gamma1_mem'

theorem Gamma1_to_gamma0_mem (N : ℕ) (A : gamma0 N) :
    A ∈ gamma1' N ↔
      ((↑ₘA 0 0 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 1 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 0 : ℤ) : ZMod N) = 0 :=
  by
  constructor
  · intro ha
    have hA := A.property
    rw [gamma0_mem] at hA
    have adet := gamma0_det N A
    rw [Matrix.det_fin_two] at adet
    simp only [gamma0Map, coe_coe, coe_matrix_coe, Int.coe_castRingHom, map_apply, Gamma1_mem',
      MonoidHom.coe_mk, Subtype.val_eq_coe, Int.cast_sub, Int.cast_mul] at *
    rw [hA, ha] at adet
    simp only [mul_one, MulZeroClass.mul_zero, sub_zero] at adet
    simp only [adet, hA, ha, eq_self_iff_true, and_self_iff]
  · intro ha
    simp only [Gamma1_mem', gamma0Map, MonoidHom.coe_mk, coe_coe, coe_matrix_coe,
      Int.coe_castRingHom, map_apply]
    exact ha.2.1
#align Gamma1_to_Gamma0_mem Gamma1_to_gamma0_mem

/-- The congruence subgroup `Gamma1` of `SL(2, ℤ)` consisting of matrices whose bottom
row is congruent to `(0,1)` modulo `N`. -/
def gamma1 (N : ℕ) : Subgroup SL(2, ℤ) :=
  Subgroup.map ((gamma0 N).Subtype.comp (gamma1' N).Subtype) ⊤
#align Gamma1 gamma1

@[simp]
theorem gamma1_mem (N : ℕ) (A : SL(2, ℤ)) :
    A ∈ gamma1 N ↔
      ((↑ₘA 0 0 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 1 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 0 : ℤ) : ZMod N) = 0 :=
  by
  constructor
  · intro ha
    simp_rw [gamma1, Subgroup.mem_map] at ha
    simp at ha
    obtain ⟨⟨x, hx⟩, hxx⟩ := ha
    rw [Gamma1_to_gamma0_mem] at hx
    rw [← hxx]
    convert hx
  · intro ha
    simp_rw [gamma1, Subgroup.mem_map]
    have hA : A ∈ gamma0 N := by simp [ha.right.right, gamma0_mem, Subtype.val_eq_coe]
    have HA : (⟨A, hA⟩ : gamma0 N) ∈ gamma1' N :=
      by
      simp only [Gamma1_to_gamma0_mem, Subgroup.coe_mk, coe_coe, coe_matrix_coe,
        Int.coe_castRingHom, map_apply]
      exact ha
    refine' ⟨(⟨(⟨A, hA⟩ : gamma0 N), HA⟩ : (gamma1' N : Subgroup (gamma0 N))), _⟩
    simp
#align Gamma1_mem gamma1_mem

theorem gamma1_in_gamma0 (N : ℕ) : gamma1 N ≤ gamma0 N :=
  by
  intro x HA
  simp only [gamma0_mem, gamma1_mem, coe_coe, coe_matrix_coe, Int.coe_castRingHom, map_apply] at *
  exact HA.2.2
#align Gamma1_in_Gamma0 gamma1_in_gamma0

section CongruenceSubgroup

/-- A congruence subgroup is a subgroup of `SL(2, ℤ)` which contains some `Gamma N` for some
`(N : ℕ+)`. -/
def IsCongruenceSubgroup (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∃ N : ℕ+, gamma N ≤ Γ
#align is_congruence_subgroup IsCongruenceSubgroup

theorem isCongruenceSubgroup_trans (H K : Subgroup SL(2, ℤ)) (h : H ≤ K)
    (h2 : IsCongruenceSubgroup H) : IsCongruenceSubgroup K :=
  by
  obtain ⟨N, hN⟩ := h2
  refine' ⟨N, le_trans hN h⟩
#align is_congruence_subgroup_trans isCongruenceSubgroup_trans

theorem gamma_is_cong_sub (N : ℕ+) : IsCongruenceSubgroup (gamma N) :=
  ⟨N, by simp only [le_refl]⟩
#align Gamma_is_cong_sub gamma_is_cong_sub

theorem gamma1_is_congruence (N : ℕ+) : IsCongruenceSubgroup (gamma1 N) :=
  by
  refine' ⟨N, _⟩
  intro A hA
  simp only [gamma1_mem, gamma_mem] at *
  simp only [hA, eq_self_iff_true, and_self_iff]
#align Gamma1_is_congruence gamma1_is_congruence

theorem gamma0_is_congruence (N : ℕ+) : IsCongruenceSubgroup (gamma0 N) :=
  isCongruenceSubgroup_trans _ _ (gamma1_in_gamma0 N) (gamma1_is_congruence N)
#align Gamma0_is_congruence gamma0_is_congruence

end CongruenceSubgroup

section Conjugation

open Pointwise

theorem gamma_cong_eq_self (N : ℕ) (g : ConjAct SL(2, ℤ)) : g • gamma N = gamma N := by
  apply Subgroup.Normal.conjAct (gamma_normal N)
#align Gamma_cong_eq_self gamma_cong_eq_self

theorem conj_cong_is_cong (g : ConjAct SL(2, ℤ)) (Γ : Subgroup SL(2, ℤ))
    (h : IsCongruenceSubgroup Γ) : IsCongruenceSubgroup (g • Γ) :=
  by
  obtain ⟨N, HN⟩ := h
  refine' ⟨N, _⟩
  rw [← gamma_cong_eq_self N g, Subgroup.pointwise_smul_le_pointwise_smul_iff]
  exact HN
#align conj_cong_is_cong conj_cong_is_cong

end Conjugation

