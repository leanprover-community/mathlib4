/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Congruence subgroups

This defines congruence subgroups of `SL(2, ℤ)` such as `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` for `N` a
natural number.

It also contains basic results about congruence subgroups.

-/

open Matrix.SpecialLinearGroup Matrix

open scoped MatrixGroups ModularGroup

variable (N : ℕ)

local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

@[simp]
theorem SL_reduction_mod_hom_val (γ : SL(2, ℤ)) (i j : Fin 2):
    SLMOD(N) γ i j = (γ i j : ZMod N) :=
  rfl

namespace CongruenceSubgroup

/-- The full level `N` congruence subgroup of `SL(2, ℤ)` of matrices that reduce to the identity
modulo `N`. -/
def Gamma : Subgroup SL(2, ℤ) :=
  SLMOD(N).ker

@[inherit_doc] scoped notation  "Γ(" n ")"  => Gamma n

theorem Gamma_mem' {N} {γ : SL(2, ℤ)} : γ ∈ Gamma N ↔ SLMOD(N) γ = 1 :=
  Iff.rfl

@[simp]
theorem Gamma_mem {N} {γ : SL(2, ℤ)} : γ ∈ Gamma N ↔ (γ 0 0 : ZMod N) = 1 ∧
    (γ 0 1 : ZMod N) = 0 ∧ (γ 1 0 : ZMod N) = 0 ∧ (γ 1 1 : ZMod N) = 1 := by
  rw [Gamma_mem']
  constructor
  · intro h
    simp [← SL_reduction_mod_hom_val N γ, h]
  · intro h
    ext i j
    rw [SL_reduction_mod_hom_val N γ]
    fin_cases i <;> fin_cases j <;> simp only [h]
    exacts [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem Gamma_normal : Subgroup.Normal (Gamma N) :=
  SLMOD(N).normal_ker

theorem Gamma_one_top : Gamma 1 = ⊤ := by
  ext
  simp [eq_iff_true_of_subsingleton]

lemma mem_Gamma_one (γ : SL(2, ℤ)) : γ ∈ Γ(1) := by
  simp only [Gamma_one_top, Subgroup.mem_top]

theorem Gamma_zero_bot : Gamma 0 = ⊥ := rfl

lemma ModularGroup_T_pow_mem_Gamma (N M : ℤ) (hNM : N ∣ M) :
    (ModularGroup.T ^ M) ∈ Gamma (Int.natAbs N) := by
  simp only [Gamma_mem, Fin.isValue, ModularGroup.coe_T_zpow, of_apply, cons_val', cons_val_zero,
    empty_val', cons_val_fin_one, Int.cast_one, cons_val_one, head_cons, head_fin_const,
    Int.cast_zero, and_self, and_true, true_and]
  refine Iff.mpr (ZMod.intCast_zmod_eq_zero_iff_dvd M (Int.natAbs N)) ?_
  simp only [Int.natCast_natAbs, abs_dvd, hNM]

/-- The congruence subgroup of `SL(2, ℤ)` of matrices whose lower left-hand entry reduces to zero
modulo `N`. -/
def Gamma0 : Subgroup SL(2, ℤ) where
  carrier := { g | (g 1 0 : ZMod N) = 0 }
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

@[simp]
theorem Gamma0_mem {N} {A : SL(2, ℤ)} : A ∈ Gamma0 N ↔ (A 1 0 : ZMod N) = 0 :=
  Iff.rfl

/-- The group homomorphism from `CongruenceSubgroup.Gamma0` to `ZMod N` given by
mapping a matrix to its lower right-hand entry. -/
def Gamma0Map (N : ℕ) : Gamma0 N →* ZMod N where
  toFun g := g.1 1 1
  map_one' := by simp
  map_mul' := by
    rintro ⟨A, hA⟩ ⟨B, _⟩
    simp only [MulMemClass.mk_mul_mk, Fin.isValue, coe_mul, (two_mul_expl A.1 B).2.2.2,
      Int.cast_add, Int.cast_mul, Gamma0_mem.mp hA, zero_mul, zero_add]

/-- The congruence subgroup `Gamma1` (as a subgroup of `Gamma0`) of matrices whose bottom
row is congruent to `(0, 1)` modulo `N`. -/
def Gamma1' (N : ℕ) : Subgroup (Gamma0 N) :=
  (Gamma0Map N).ker

@[simp]
theorem Gamma1_mem' {N} {γ : Gamma0 N} : γ ∈ Gamma1' N ↔ Gamma0Map N γ = 1 :=
  Iff.rfl

theorem Gamma1_to_Gamma0_mem {N} (A : Gamma0 N) :
    A ∈ Gamma1' N ↔
    ((A.1 0 0 : ℤ) : ZMod N) = 1 ∧ ((A.1 1 1 : ℤ) : ZMod N) = 1
      ∧ ((A.1 1 0 : ℤ) : ZMod N) = 0 := by
  constructor
  · intro ha
    have adet : (A.1.1.det : ZMod N) = 1 := by simp only [A.1.property, Int.cast_one]
    rw [Matrix.det_fin_two] at adet
    simp only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_sub,
      Int.cast_mul] at *
    simpa only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_sub,
      Int.cast_mul, ha, Gamma0_mem.mp A.property, and_self_iff, and_true, mul_one, mul_zero,
      sub_zero] using adet
  · intro ha
    simp only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, coe_matrix_coe,
      Int.coe_castRingHom, map_apply]
    exact ha.2.1

/-- The congruence subgroup `Gamma1` of `SL(2, ℤ)` consisting of matrices
whose bottom row is congruent to `(0,1)` modulo `N`. -/
def Gamma1 (N : ℕ) : Subgroup SL(2, ℤ) :=
  Subgroup.map ((Gamma0 N).subtype.comp (Gamma1' N).subtype) ⊤

@[simp]
theorem Gamma1_mem (N : ℕ) (A : SL(2, ℤ)) : A ∈ Gamma1 N ↔
    (A 0 0 : ZMod N) = 1 ∧ (A 1 1 : ZMod N) = 1 ∧ (A 1 0 : ZMod N) = 0 := by
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

theorem Gamma1_in_Gamma0 (N : ℕ) : Gamma1 N ≤ Gamma0 N := by
  intro x HA
  simp only [Gamma0_mem, Gamma1_mem, coe_matrix_coe, Int.coe_castRingHom, map_apply] at *
  exact HA.2.2

section CongruenceSubgroups

/-- A congruence subgroup is a subgroup of `SL(2, ℤ)` which contains some `Gamma N` for some
`(N : ℕ+)`. -/
def IsCongruenceSubgroup (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∃ N : ℕ+, Gamma N ≤ Γ

theorem isCongruenceSubgroup_trans (H K : Subgroup SL(2, ℤ)) (h : H ≤ K)
    (h2 : IsCongruenceSubgroup H) : IsCongruenceSubgroup K := by
  obtain ⟨N, hN⟩ := h2
  exact ⟨N, le_trans hN h⟩

theorem Gamma_is_cong_sub (N : ℕ+) : IsCongruenceSubgroup (Gamma N) :=
  ⟨N, by simp only [le_refl]⟩

theorem Gamma1_is_congruence (N : ℕ+) : IsCongruenceSubgroup (Gamma1 N) := by
  refine ⟨N, ?_⟩
  intro A hA
  simp only [Gamma1_mem, Gamma_mem] at *
  simp only [hA, eq_self_iff_true, and_self_iff]

theorem Gamma0_is_congruence (N : ℕ+) : IsCongruenceSubgroup (Gamma0 N) :=
  isCongruenceSubgroup_trans _ _ (Gamma1_in_Gamma0 N) (Gamma1_is_congruence N)

end CongruenceSubgroups

section Conjugation

open Pointwise

theorem Gamma_cong_eq_self (N : ℕ) (g : ConjAct SL(2, ℤ)) : g • Gamma N = Gamma N := by
  apply Subgroup.Normal.conjAct (Gamma_normal N)

theorem conj_cong_is_cong (g : ConjAct SL(2, ℤ)) (Γ : Subgroup SL(2, ℤ))
    (h : IsCongruenceSubgroup Γ) : IsCongruenceSubgroup (g • Γ) := by
  obtain ⟨N, HN⟩ := h
  refine ⟨N, ?_⟩
  rw [← Gamma_cong_eq_self N g, Subgroup.pointwise_smul_le_pointwise_smul_iff]
  exact HN

end Conjugation

end CongruenceSubgroup
