/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Matrices with fixed determinant

This file defines the type of matrices with fixed determinant `m` and proves some basic results
about them.
-/

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

/--The set of matrices with fixed determinant `m`. -/
def FixedDetMatrices (m : R) := { A : Matrix n n R // A.det = m }

namespace FixedDetMatrices

lemma ext' (m : R) {A B : FixedDetMatrices n R m} (h : A.1 = B.1) : A = B := by
  cases A; cases B
  congr

@[ext]
lemma ext (m : R) {A B : FixedDetMatrices n R m} (h : ∀ i j , A.1 i j = B.1 i j) : A = B := by
  apply ext'
  ext i j
  apply h

open ModularGroup Matrix SpecialLinearGroup MatrixGroups

local notation:1024 "↑ₘ" A:1024 => ((A : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)

local notation:1024 "Δ" m : 1024 => (FixedDetMatrices (Fin 2) ℤ m)

lemma S_pow_two : ↑ₘ(S ^ 2) = -1 := by
  simp only [S, Int.reduceNeg, pow_two, coe_mul, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
    vecMul_cons, head_cons, zero_smul, tail_cons, neg_smul, one_smul, neg_cons, neg_zero, neg_empty,
    empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply]
  exact Eq.symm (eta_fin_two (-1))

lemma S_mul_self : (S.1 * S.1) = -1 := by
  rw [← pow_two]
  exact S_pow_two

/--Set of representatives for the orbits under `S` and `T`. -/
def reps (m : ℤ) : Set (Δ m) :=
  { A : Δ m | (A.1 1 0) = 0 ∧ 0 < A.1 0 0 ∧ 0 ≤ A.1 0 1 ∧ |(A.1 0 1)| < |(A.1 1 1)|}

variable (m : ℤ) (g : SpecialLinearGroup n R) (A : Δ m) (R : Type*) [CommRing R]

instance (m : outParam R) : HSMul (SpecialLinearGroup n R) (FixedDetMatrices n R m)
  ((FixedDetMatrices n R m)) :=
{ hSMul := fun g A => ⟨g * A.1, by simp only [det_mul, SpecialLinearGroup.det_coe, A.2, one_mul]⟩}

lemma smul_def (m : R) (g : SpecialLinearGroup n R) (A : (FixedDetMatrices n R m)) : g • A =
    ⟨g * A.1, by simp only [det_mul, SpecialLinearGroup.det_coe, A.2, one_mul]⟩ := rfl

instance (m : R) : MulAction (SpecialLinearGroup n R) (FixedDetMatrices n R m) where
  smul := fun g A => g • A
  one_smul := by intro b; rw [smul_def]; simp
  mul_smul := by
      intro x y b
      simp_rw [smul_def, ← mul_assoc]
      rfl

lemma smul_coe (m : R) (g : SpecialLinearGroup n R) (A : (FixedDetMatrices n R m)) :
    (g • A).1 = g * A.1 := by
  rw [smul_def]

lemma aux1 (m : ℤ) (A : Δ m) : A.1 0 0 -( A.1 1 0)*(A.1 0 0/ A.1 1 0)= A.1 0 0 % A.1 1 0 := by
  simp only [Int.cast_id, Fin.isValue]
  exact Eq.symm (Int.emod_def (A.1 0 0) (A.1 1 0))

/--Reduction step for matrices in `Δ m` which moves the matrices towards `reps`.-/
def reduce_step (A : Δ m) : Δ m := S • ( (T^(-((A.1 0 0)/(A.1 1 0)))) • A)

lemma reduce_aux (m : ℤ) (A : Δ m) (h : Int.natAbs (A.1 1 0) ≠ 0) :
    Int.natAbs ((reduce_step m A).1 1 0) < Int.natAbs (A.1 1 0) := by
  simp_rw [reduce_step, smul_coe, coe_T_zpow, S]
  simp only [Int.reduceNeg, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, empty_mul,
    Equiv.symm_apply_apply, vecMul_cons, vecHead, cons_val_zero, zero_smul, vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, cons_val_one, cons_val_fin_one, neg_smul, one_smul,
    empty_vecMul, add_zero, zero_add, of_apply, cons_val', Pi.neg_apply, vecMul, cons_dotProduct,
    zero_mul, one_mul, dotProduct_empty, mul_comm, mul_neg, ← Int.sub_eq_add_neg, (aux1 m A),
    empty_val']
  zify
  apply le_trans _ (Int.emod_lt (A.1 0 0) (Int.natAbs_ne_zero.mp h))
  simp only [Fin.isValue, Int.cast_id, add_le_add_iff_right]
  rw [abs_eq_self.mpr (Int.emod_nonneg (A.1 0 0) (Int.natAbs_ne_zero.mp h))]

/--Reduction lemma for integral FixedDetMatrices. -/
@[elab_as_elim]
def reduce_rec {C : Δ m → Sort*} (h0 : ∀ A : Δ m, Int.natAbs (A.1 1 0) = 0 → C A)
  (h1 : ∀ A : Δ m, Int.natAbs ((A.1 1 0)) ≠ 0 → C (reduce_step m A) → C A) :
    ∀ A, C A := fun A => by
  by_cases h : Int.natAbs (A.1 1 0) = 0
  · apply h0 _ h
  · exact h1 A h (reduce_rec h0 h1 (reduce_step m A))
  termination_by A => Int.natAbs (A.1 1 0)
  decreasing_by
    apply reduce_aux m A
    simp only [Int.cast_id, Fin.isValue, ne_eq, Int.natAbs_eq_zero]
    rw [@Int.natAbs_eq_zero] at h
    exact h

set_option linter.unusedVariables false in
/--Map from `Δ m → Δ m` which reduces a FixedDetMatrix towards a representative element in reps. -/
def reduce : Δ m → Δ m := fun A => by
  if h : Int.natAbs (A.1 1 0) = 0 then
    if ha : 0 < A.1 0 0 then exact (T^(-(A.1 0 1/A.1 1 1))) • A else exact
      (T^(-(-A.1 0 1/ -A.1 1 1))) • ( S • ( S • A))
  else
    exact reduce (reduce_step m A)
  termination_by b => Int.natAbs (b.1 1 0)
  decreasing_by
      apply reduce_aux m
      simp only [Int.cast_id, Fin.isValue, ne_eq, Int.natAbs_eq_zero]
      rw [@Int.natAbs_eq_zero] at h
      exact h

lemma reduce_eqn1 (A : Δ m) (hc : Int.natAbs (A.1 1 0) = 0) (ha : 0 < A.1 0 0) :
    reduce m A = (T^(-(A.1 0 1/A.1 1 1))) • A := by
  rw [reduce]
  simp only [Int.cast_id, Fin.isValue, Int.natAbs_eq_zero, zpow_neg, Int.ediv_neg, neg_neg,
    dite_eq_ite] at *
  simp_rw [if_pos hc, if_pos ha]

lemma reduce_eqn2 (A : Δ m) (hc : Int.natAbs (A.1 1 0) = 0) (ha : ¬ 0 < A.1 0 0) :
    reduce m A = (T^(-(-A.1 0 1/ -A.1 1 1))) • ( S • ( S • A)) := by
  rw [reduce]
  simp only [Int.cast_id, Fin.isValue, Int.natAbs_eq_zero, zpow_neg, Int.ediv_neg, neg_neg,
    dite_eq_ite] at *
  simp_rw [if_pos hc, if_neg ha]

lemma reduce_eqn3 (A : Δ m) (hc : ¬ Int.natAbs (A.1 1 0) = 0) :
    reduce m A = reduce m (reduce_step m A) := by
  rw [reduce]
  simp only [Int.cast_id, Fin.isValue, Int.natAbs_eq_zero, zpow_neg, Int.ediv_neg, neg_neg,
    dite_eq_ite] at *
  simp_rw [if_neg hc]

lemma A_d_ne_zero (A : Δ m) (ha : A.1 1 0 = 0) (hm : m ≠ 0) : A.1 1 1 ≠ 0 := by
  have := A.2
  rw [det_fin_two, ha] at this
  simp only [Int.cast_id, Fin.isValue, mul_zero, sub_zero] at this
  aesop

lemma A_a_ne_zero (A : Δ m) (ha : A.1 1 0 = 0) (hm : m ≠ 0) : A.1 0 0 ≠ 0 := by
  have := A.2
  rw [@det_fin_two, ha] at this
  simp only [Int.cast_id, Fin.isValue, mul_zero, sub_zero] at this
  aesop

lemma A_b_eq_zero (A : Δ m) (ha : A.1 1 0 = 0) : A.1 0 0 * A.1 1 1 = m := by
  have := A.2
  rw [@det_fin_two, ha] at this
  simp only [Int.cast_id, Fin.isValue, mul_zero, sub_zero] at this
  aesop

lemma reduce_mem_reps (m : ℤ) (hm : m ≠ 0) : ∀ A : Δ m, reduce m A ∈ reps m := by
  apply reduce_rec
  · intro A h
    by_cases h1 : 0 < A.1 0 0
    rw [reduce_eqn1 _ _ h h1, reps]
    simp only [Int.cast_id, Fin.isValue, zpow_neg, Set.mem_setOf_eq]
    rw [smul_coe]
    simp [coe_T_zpow, vecMul, vecHead, vecTail]
    refine ⟨ Int.natAbs_eq_zero.mp h, by simp at h; rw [h]; simp [h1], by
      apply Int.ediv_mul_le; apply A_d_ne_zero _ _ (by simpa using h) hm, by
      rw [mul_comm, ← @Int.sub_eq_add_neg, (Int.emod_def (A.1 0 1) (A.1 1 1)).symm]
      apply le_trans _ (Int.emod_lt (A.1 0 1) (by apply A_d_ne_zero _ _ (by simpa using h) hm))
      rw [abs_eq_self.mpr ( Int.emod_nonneg (A.1 0 1) (A_d_ne_zero _ _ (by simpa using h) hm))]⟩
    rw [reduce_eqn2 _ _ h h1, reps]
    simp only [Int.cast_id, Fin.isValue, Int.ediv_neg, neg_neg, smul_def, ← mul_assoc, coe_T_zpow,
      cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, empty_mul, Equiv.symm_apply_apply,
      vecMul_vecMul, Set.mem_setOf_eq, of_apply, cons_val', vecMul, cons_dotProduct, vecHead,
      one_mul, vecTail, Function.comp_apply, Fin.succ_zero_eq_one, dotProduct_empty, add_zero,
      zero_mul, zero_add, empty_val', cons_val_fin_one, cons_val_one, cons_val_zero]
    rw [← pow_two]
    have := S_pow_two
    simp only [coe_pow] at this
    rw [this]
    simp only [Fin.isValue, neg_mul, one_mul, neg_apply, neg_eq_zero, mul_neg,
      lt_add_neg_iff_add_lt, zero_add, le_add_neg_iff_add_le, abs_neg]
    refine ⟨Int.natAbs_eq_zero.mp h, by
        simp only [ne_eq, Int.cast_id, Fin.isValue, Int.natAbs_eq_zero, not_lt] at *
        rw [h]
        simp only [Fin.isValue, mul_zero, Left.neg_pos_iff]
        rw [Int.lt_iff_le_and_ne]
        refine ⟨h1, by apply A_a_ne_zero _ _ (by simpa using h) hm⟩, by
        apply Int.ediv_mul_le; apply A_d_ne_zero _ _ (by simpa using h) hm, by
        rw [mul_comm, ← @Int.sub_eq_add_neg, (Int.emod_def (-A.1 0 1) (A.1 1 1)).symm]
        apply le_trans _ (Int.emod_lt (-A.1 0 1) (by apply A_d_ne_zero _ _ (by simpa using h) hm))
        rw [abs_eq_self.mpr (Int.emod_nonneg (-A.1 0 1) (A_d_ne_zero _ _ (by simpa using h) hm))]⟩
  · exact fun A h1 h2 ↦ Eq.mpr (id (congrArg (fun _a ↦ _a ∈ reps m) (reduce_eqn3 m A h1))) h2

lemma S_smul_four (A : Δ m) : (S • ( S • (S • ( S • A)))) = A := by
  simp_rw [smul_def, ← mul_assoc, S_mul_self]
  simp only [Int.cast_id, neg_mul, one_mul]
  simp_rw [S_mul_self]
  simp only [neg_mul, one_mul, neg_neg, Subtype.coe_eta]

lemma T_S_rel (A : Δ m) : (S • S • S • T • S • T • S • A) = T⁻¹ • A := by
  have : S • S • S • T • S • T • S = T⁻¹ := by
    simp_rw [smul_eq_mul]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals {rfl}
  simp_rw [← this, ← smul_assoc]

@[elab_as_elim]
theorem induction_on {C : Δ m → Prop} (A : Δ m) (hm : m ≠ 0)
  (h0 : ∀ A : Δ m, A.1 1 0 = 0 → A.1 0 0 * A.1 1 1 = m → 0 < A.1 0 0 → 0 ≤ A.1 0 1 →
    Int.natAbs (A.1 0 1) < Int.natAbs (A.1 1 1) → C A) (hS : ∀ B, C B → C (S • B))
      (hT : ∀ B, C B → C (T • B)) : C A := by
  have hS' : ∀ B, C (S • B) → C B := by
    intro B ih
    rw [← (S_smul_four m B)]
    apply hS _ (hS _ (hS _ ih))
  have hT_inv : ∀ B, C B → C (T⁻¹ • B) := by
    intro B ih
    have h := (hS _ $ hS _ $ hS _ $ hT _ $ hS _ $ hT _ $ hS _ ih)
    rw [T_S_rel m B] at h
    exact h
  have hT' : ∀ B, C (T • B) → C B := by
    intro B ih
    have h := hT_inv (T • B) ih
    simpa using h
  have hT_pow' : ∀ B (n : ℤ), C ((T^n) • B) → C B := by
    intro B n
    induction' n using Int.induction_on with n hn m hm
    · simp only [ne_eq, Int.cast_id, Fin.isValue, zpow_zero, one_smul, imp_self] at *
    ·   intro h
        rw [add_comm, zpow_add, ← smul_eq_mul] at h
        simp only [zpow_one] at h
        rw [smul_assoc] at h
        exact hn $ hT' _ h
    · rw [sub_eq_neg_add, zpow_add, zpow_neg_one]
      intro h
      apply hm
      have := hT _ h
      rw [smul_def] at this
      convert this
      simp only [zpow_neg, zpow_natCast, smul_def, Int.cast_id, coe_inv, coe_pow, adjugate_pow, ←
        mul_assoc, ← coe_mul, mul_inv_cancel T, one_mul]
  have h_reduce : C (reduce m A) := by
    rcases reduce_mem_reps m hm A with ⟨H1, H2, H3, H4⟩
    apply h0 _ H1 ?_ H2 H3
    · zify
      apply H4
    · apply A_b_eq_zero _ _ H1
  suffices ∀ A : Δ m, C (reduce m A) → C A from this _ h_reduce
  apply reduce_rec
  · intro A h
    by_cases h1 : 0 < A.1 0 0
    · rw [reduce_eqn1 _ _ h h1]
      intro h
      apply hT_pow' A (-(A.1 0 1 / A.1 1 1)) h
    · rw [reduce_eqn2 _ _ h h1]
      intro h
      exact hS' _ $ hS' _ (hT_pow' _ _ h)
  intro A hc ih hA
  rw [reduce_eqn3 _ _ hc] at hA
  exact hT_pow' _ _ $ hS' _ (ih hA)

/--The subngroup of `SL(2,ℤ)` generated by `S` and `T`-/
def S_T_subgroup := Subgroup.closure {S, T}

lemma S_mem_S_T_subgroup : S ∈ S_T_subgroup := by
  apply Subgroup.subset_closure
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]

lemma T_mem_S_T_subgroup : T ∈ S_T_subgroup := by
  apply Subgroup.subset_closure
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]

lemma S_smul_mem_S_T_subgroup (B : Δ 1) (hB : B ∈ S_T_subgroup) : (S • B) ∈ S_T_subgroup := by
  rw [smul_eq_mul]
  apply Subgroup.mul_mem _ (S_mem_S_T_subgroup) (hB)

lemma T_smul_mem_S_T_subgroup (B : Δ 1) (hB : B ∈ S_T_subgroup) : (T • B) ∈ S_T_subgroup := by
  rw [smul_eq_mul]
  apply Subgroup.mul_mem _ (T_mem_S_T_subgroup) (hB)

lemma det_one_mem_G : ∀ A : Δ 1, A ∈ S_T_subgroup := by
  intro A
  induction A using (induction_on 1 )
  exact Int.one_ne_zero
  next A a1 a2 a4 a5 a6 =>
    have : A = (1 : SL(2,ℤ)) := by
      ext i j
      fin_cases i; fin_cases j
      · simp only [Int.cast_id, Fin.zero_eta, Fin.isValue, coe_one, one_apply_eq]
        have := Int.mul_eq_one_iff_eq_one_or_neg_one.mp (A_b_eq_zero 1 A a1)
        aesop
      · simp only [Int.cast_id, Fin.zero_eta, Fin.isValue, Fin.mk_one, coe_one, ne_eq, zero_ne_one,
        not_false_eq_true, one_apply_ne]
        have := Int.mul_eq_one_iff_eq_one_or_neg_one.mp (A_b_eq_zero 1 A a1)
        aesop
      fin_cases j
      · simp only [Int.cast_id, Fin.mk_one, Fin.isValue, Fin.zero_eta, a1, coe_one, ne_eq,
        one_ne_zero, not_false_eq_true, one_apply_ne]
      · simp only [Int.cast_id, Fin.mk_one, Fin.isValue, coe_one, one_apply_eq]
        have := Int.mul_eq_one_iff_eq_one_or_neg_one.mp (A_b_eq_zero 1 A a1)
        aesop
    rw [this]
    exact Subgroup.one_mem S_T_subgroup
  next B hb => apply (S_smul_mem_S_T_subgroup B) hb
  next B hb => apply (T_smul_mem_S_T_subgroup B) hb

lemma SL2Z_generators : S_T_subgroup = (⊤ : Subgroup (SL(2,ℤ))) := by
    refine (Subgroup.eq_top_iff' S_T_subgroup).mpr (fun _ => det_one_mem_G _)

end FixedDetMatrices
