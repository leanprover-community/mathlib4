/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

#align_import number_theory.modular_forms.congruence_subgroups from "leanprover-community/mathlib"@"ae690b0c236e488a0043f6faa8ce3546e7f2f9c5"

/-!
# Congruence subgroups

This defines congruence subgroups of `SL(2, ℤ)` such as `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` for `N` a
natural number.

It also contains basic results about congruence subgroups.

-/


local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

attribute [-instance] Matrix.SpecialLinearGroup.instCoeFun

local notation:1024 "↑ₘ" A:1024 => ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)

open Matrix.SpecialLinearGroup Matrix

variable (N : ℕ)

local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

set_option linter.uppercaseLean3 false

@[simp]
theorem SL_reduction_mod_hom_val (N : ℕ) (γ : SL(2, ℤ)) :
    ∀ i j : Fin 2, (SLMOD(N) γ : Matrix (Fin 2) (Fin 2) (ZMod N)) i j = ((↑ₘγ i j : ℤ) : ZMod N) :=
  fun _ _ => rfl
#align SL_reduction_mod_hom_val SL_reduction_mod_hom_val

/-- The full level `N` congruence subgroup of `SL(2, ℤ)` of matrices that reduce to the identity
modulo `N`. -/
def Gamma (N : ℕ) : Subgroup SL(2, ℤ) :=
  SLMOD(N).ker
#align Gamma Gamma

theorem Gamma_mem' (N : ℕ) (γ : SL(2, ℤ)) : γ ∈ Gamma N ↔ SLMOD(N) γ = 1 :=
  Iff.rfl
#align Gamma_mem' Gamma_mem'

@[simp]
theorem Gamma_mem (N : ℕ) (γ : SL(2, ℤ)) : γ ∈ Gamma N ↔ ((↑ₘγ 0 0 : ℤ) : ZMod N) = 1 ∧
    ((↑ₘγ 0 1 : ℤ) : ZMod N) = 0 ∧ ((↑ₘγ 1 0 : ℤ) : ZMod N) = 0 ∧ ((↑ₘγ 1 1 : ℤ) : ZMod N) = 1 := by
  rw [Gamma_mem']
  constructor
  · intro h
    simp [← SL_reduction_mod_hom_val N γ, h]
  · intro h
    ext i j
    rw [SL_reduction_mod_hom_val N γ]
    fin_cases i <;> fin_cases j <;> simp only [h]
    exacts [h.1, h.2.1, h.2.2.1, h.2.2.2]
#align Gamma_mem Gamma_mem

theorem Gamma_normal (N : ℕ) : Subgroup.Normal (Gamma N) :=
  SLMOD(N).normal_ker
#align Gamma_normal Gamma_normal

theorem Gamma_one_top : Gamma 1 = ⊤ := by
  ext
  simp [eq_iff_true_of_subsingleton]
#align Gamma_one_top Gamma_one_top

theorem Gamma_zero_bot : Gamma 0 = ⊥ := by
  ext
  simp only [Gamma_mem, coe_matrix_coe, Int.coe_castRingHom, map_apply, Int.cast_id,
    Subgroup.mem_bot]
  constructor
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [h]
    exacts [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · intro h
    simp [h]
#align Gamma_zero_bot Gamma_zero_bot

lemma ModularGroup_T_pow_mem_Gamma (N M : ℤ) (hNM : N ∣ M) :
    (ModularGroup.T ^ M) ∈ _root_.Gamma (Int.natAbs N) := by
  simp only [Gamma_mem, Fin.isValue, ModularGroup.coe_T_zpow, of_apply, cons_val', cons_val_zero,
    empty_val', cons_val_fin_one, Int.cast_one, cons_val_one, head_cons, head_fin_const,
    Int.cast_zero, and_self, and_true, true_and]
  refine Iff.mpr (ZMod.intCast_zmod_eq_zero_iff_dvd M (Int.natAbs N)) ?_
  simp only [Int.natCast_natAbs, abs_dvd, hNM]

/-- The congruence subgroup of `SL(2, ℤ)` of matrices whose lower left-hand entry reduces to zero
modulo `N`. -/
def Gamma0 (N : ℕ) : Subgroup SL(2, ℤ) where
  carrier := { g : SL(2, ℤ) | ((↑ₘg 1 0 : ℤ) : ZMod N) = 0 }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq]
    have h := (Matrix.two_mul_expl a.1 b.1).2.2.1
    simp only [coe_matrix_coe, coe_mul, Int.coe_castRingHom, map_apply, Set.mem_setOf_eq] at *
    rw [h]
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq]
    rw [SL2_inv_expl a]
    simp only [cons_val_zero, cons_val_one, head_cons, coe_matrix_coe,
      coe_mk, Int.coe_castRingHom, map_apply, Int.cast_neg, neg_eq_zero, Set.mem_setOf_eq] at *
    exact ha
#align Gamma0 Gamma0

@[simp]
theorem Gamma0_mem (N : ℕ) (A : SL(2, ℤ)) : A ∈ Gamma0 N ↔ ((↑ₘA 1 0 : ℤ) : ZMod N) = 0 :=
  Iff.rfl
#align Gamma0_mem Gamma0_mem

theorem Gamma0_det (N : ℕ) (A : Gamma0 N) : (A.1.1.det : ZMod N) = 1 := by simp [A.1.property]
#align Gamma0_det Gamma0_det

/-- The group homomorphism from `Gamma0` to `ZMod N` given by mapping a matrix to its lower
right-hand entry. -/
def Gamma0Map (N : ℕ) : Gamma0 N →* ZMod N where
  toFun g := ((↑ₘg 1 1 : ℤ) : ZMod N)
  map_one' := by simp
  map_mul' := by
    intro A B
    have := (two_mul_expl A.1.1 B.1.1).2.2.2
    simp only [Subgroup.coe_mul, coe_matrix_coe, coe_mul, Int.coe_castRingHom, map_apply] at *
    rw [this]
    have ha := A.property
    simp only [Int.cast_add, Int.cast_mul, add_left_eq_self, Gamma0_mem,
      coe_matrix_coe, Int.coe_castRingHom, map_apply] at *
    rw [ha]
    simp
#align Gamma_0_map Gamma0Map

/-- The congruence subgroup `Gamma1` (as a subgroup of `Gamma0`) of matrices whose bottom
row is congruent to `(0,1)` modulo `N`. -/
def Gamma1' (N : ℕ) : Subgroup (Gamma0 N) :=
  (Gamma0Map N).ker
#align Gamma1' Gamma1'

@[simp, nolint simpNF] -- Porting note: linter failed to synth `CommMonoid { x // x ∈ Gamma0 N }`
theorem Gamma1_mem' (N : ℕ) (γ : Gamma0 N) : γ ∈ Gamma1' N ↔ (Gamma0Map N) γ = 1 :=
  Iff.rfl
#align Gamma1_mem' Gamma1_mem'

theorem Gamma1_to_Gamma0_mem (N : ℕ) (A : Gamma0 N) : A ∈ Gamma1' N ↔
    ((↑ₘA 0 0 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 1 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 0 : ℤ) : ZMod N) = 0 := by
  constructor
  · intro ha
    have hA := A.property
    rw [Gamma0_mem] at hA
    have adet := Gamma0_det N A
    rw [Matrix.det_fin_two] at adet
    simp only [Gamma0Map, coe_matrix_coe, Int.coe_castRingHom, map_apply, Gamma1_mem',
      MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_sub, Int.cast_mul] at *
    rw [hA, ha] at adet
    simp only [mul_one, mul_zero, sub_zero] at adet
    simp only [adet, hA, ha, eq_self_iff_true, and_self_iff]
  · intro ha
    simp only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, coe_matrix_coe,
      Int.coe_castRingHom, map_apply]
    exact ha.2.1
#align Gamma1_to_Gamma0_mem Gamma1_to_Gamma0_mem

/-- The congruence subgroup `Gamma1` of `SL(2, ℤ)` consisting of matrices whose bottom
row is congruent to `(0,1)` modulo `N`. -/
def Gamma1 (N : ℕ) : Subgroup SL(2, ℤ) :=
  Subgroup.map ((Gamma0 N).subtype.comp (Gamma1' N).subtype) ⊤
#align Gamma1 Gamma1

@[simp]
theorem Gamma1_mem (N : ℕ) (A : SL(2, ℤ)) : A ∈ Gamma1 N ↔
    ((↑ₘA 0 0 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 1 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 0 : ℤ) : ZMod N) = 0 := by
  constructor
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map] at ha
    obtain ⟨⟨x, hx⟩, hxx⟩ := ha
    rw [Gamma1_to_Gamma0_mem] at hx
    simp only [Subgroup.mem_top, true_and] at hxx
    rw [← hxx]
    convert hx
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map]
    have hA : A ∈ Gamma0 N := by simp [ha.right.right, Gamma0_mem]
    have HA : (⟨A, hA⟩ : Gamma0 N) ∈ Gamma1' N := by
      simp only [Gamma1_to_Gamma0_mem, Subgroup.coe_mk, coe_matrix_coe,
        Int.coe_castRingHom, map_apply]
      exact ha
    refine ⟨(⟨(⟨A, hA⟩ : Gamma0 N), HA⟩ : (Gamma1' N : Subgroup (Gamma0 N))), ?_⟩
    simp
#align Gamma1_mem Gamma1_mem

theorem Gamma1_in_Gamma0 (N : ℕ) : Gamma1 N ≤ Gamma0 N := by
  intro x HA
  simp only [Gamma0_mem, Gamma1_mem, coe_matrix_coe, Int.coe_castRingHom, map_apply] at *
  exact HA.2.2
#align Gamma1_in_Gamma0 Gamma1_in_Gamma0

section CongruenceSubgroup

/-- A congruence subgroup is a subgroup of `SL(2, ℤ)` which contains some `Gamma N` for some
`(N : ℕ+)`. -/
def IsCongruenceSubgroup (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∃ N : ℕ+, Gamma N ≤ Γ
#align is_congruence_subgroup IsCongruenceSubgroup

theorem isCongruenceSubgroup_trans (H K : Subgroup SL(2, ℤ)) (h : H ≤ K)
    (h2 : IsCongruenceSubgroup H) : IsCongruenceSubgroup K := by
  obtain ⟨N, hN⟩ := h2
  exact ⟨N, le_trans hN h⟩
#align is_congruence_subgroup_trans isCongruenceSubgroup_trans

theorem Gamma_is_cong_sub (N : ℕ+) : IsCongruenceSubgroup (Gamma N) :=
  ⟨N, by simp only [le_refl]⟩
#align Gamma_is_cong_sub Gamma_is_cong_sub

theorem Gamma1_is_congruence (N : ℕ+) : IsCongruenceSubgroup (Gamma1 N) := by
  refine ⟨N, ?_⟩
  intro A hA
  simp only [Gamma1_mem, Gamma_mem] at *
  simp only [hA, eq_self_iff_true, and_self_iff]
#align Gamma1_is_congruence Gamma1_is_congruence

theorem Gamma0_is_congruence (N : ℕ+) : IsCongruenceSubgroup (Gamma0 N) :=
  isCongruenceSubgroup_trans _ _ (Gamma1_in_Gamma0 N) (Gamma1_is_congruence N)
#align Gamma0_is_congruence Gamma0_is_congruence

end CongruenceSubgroup

section Conjugation

open Pointwise

theorem Gamma_cong_eq_self (N : ℕ) (g : ConjAct SL(2, ℤ)) : g • Gamma N = Gamma N := by
  apply Subgroup.Normal.conjAct (Gamma_normal N)
#align Gamma_cong_eq_self Gamma_cong_eq_self

theorem conj_cong_is_cong (g : ConjAct SL(2, ℤ)) (Γ : Subgroup SL(2, ℤ))
    (h : IsCongruenceSubgroup Γ) : IsCongruenceSubgroup (g • Γ) := by
  obtain ⟨N, HN⟩ := h
  refine ⟨N, ?_⟩
  rw [← Gamma_cong_eq_self N g, Subgroup.pointwise_smul_le_pointwise_smul_iff]
  exact HN
#align conj_cong_is_cong conj_cong_is_cong

end Conjugation
