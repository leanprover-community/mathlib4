/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Int.Interval

/-!
# Matrices with fixed determinant

This file defines the type of matrices with fixed determinant `m` and proves some basic results
about them.

Note: Some of this was done originally in Lean 3 in the
kbb (https://github.com/kim-em/kbb/tree/master) repository, so credit to those authors.
-/

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

/--The subtype of matrices with fixed determinant `m`. -/
def FixedDetMatrix (m : R) := { A : Matrix n n R // A.det = m }

namespace FixedDetMatrices

open Matrix hiding mul_smul
open ModularGroup SpecialLinearGroup MatrixGroups

/--Extensionality theorem for `FixedDetMatrix` with respect to the underlying matrix, not
entriwise. -/
lemma ext' {m : R} {A B : FixedDetMatrix n R m} (h : A.1 = B.1) : A = B := by
  cases A; cases B
  congr

@[ext]
lemma ext {m : R} {A B : FixedDetMatrix n R m} (h : ∀ i j , A.1 i j = B.1 i j) : A = B := by
  apply ext'
  ext i j
  apply h

instance (m : R) : SMul (SpecialLinearGroup n R) (FixedDetMatrix n R m) where
  smul g A := ⟨g * A.1, by simp only [det_mul, SpecialLinearGroup.det_coe, A.2, one_mul]⟩

lemma smul_def (m : R) (g : SpecialLinearGroup n R) (A : (FixedDetMatrix n R m)) :
    g • A = ⟨g * A.1, by simp only [det_mul, SpecialLinearGroup.det_coe, A.2, one_mul]⟩ :=
  rfl

instance (m : R) : MulAction (SpecialLinearGroup n R) (FixedDetMatrix n R m) where
  one_smul b := by rw [smul_def]; simp only [coe_one, one_mul, Subtype.coe_eta]
  mul_smul x y b := by simp_rw [smul_def, ← mul_assoc, coe_mul]

lemma smul_coe (m : R) (g : SpecialLinearGroup n R) (A : FixedDetMatrix n R m) :
    (g • A).1 = g * A.1 := by
  rw [smul_def]

section IntegralFixedDetMatrices

local notation:1024 "Δ" m : 1024 => (FixedDetMatrix (Fin 2) ℤ m)

variable {m : ℤ}

/--Set of representatives for the orbits under `S` and `T`. -/
def reps (m : ℤ) : Set (Δ m) :=
  {A : Δ m | (A.1 1 0) = 0 ∧ 0 < A.1 0 0 ∧ 0 ≤ A.1 0 1 ∧ |(A.1 0 1)| < |(A.1 1 1)|}

/--Reduction step for matrices in `Δ m` which moves the matrices towards `reps`.-/
def reduceStep (A : Δ m) : Δ m := S • (T ^ (-(A.1 0 0 / A.1 1 0))) • A

private lemma reduce_aux {A : Δ m} (h : (A.1 1 0) ≠ 0) :
    |((reduceStep A).1 1 0)| < |(A.1 1 0)| := by
  suffices ((reduceStep A).1 1 0) = A.1 0 0 % A.1 1 0 by
    rw [this, abs_eq_self.mpr (Int.emod_nonneg (A.1 0 0) h)]
    exact Int.emod_lt (A.1 0 0) h
  simp_rw [Int.emod_def, sub_eq_add_neg, reduceStep, smul_coe, coe_T_zpow, S]
  norm_num [vecMul, vecHead, vecTail, mul_comm]

/--Reduction lemma for integral FixedDetMatrices. -/
@[elab_as_elim]
def reduce_rec {C : Δ m → Sort*}
    (base : ∀ A : Δ m, (A.1 1 0) = 0 → C A)
    (step : ∀ A : Δ m, (A.1 1 0) ≠ 0 → C (reduceStep A) → C A) :
    ∀ A, C A := fun A => by
  by_cases h : (A.1 1 0) = 0
  · exact base _ h
  · exact step A h (reduce_rec base step (reduceStep A))
  termination_by A => Int.natAbs (A.1 1 0)
  decreasing_by
    zify
    exact reduce_aux h

/--Map from `Δ m → Δ m` which reduces a FixedDetMatrix towards a representative element in reps. -/
def reduce : Δ m → Δ m := fun A ↦
  if (A.1 1 0) = 0 then
    if 0 < A.1 0 0 then (T ^ (-(A.1 0 1 / A.1 1 1))) • A else
      (T ^ (-(-A.1 0 1 / -A.1 1 1))) • (S • (S • A)) --the -/- don't cancel with ℤ divs.
  else
    reduce (reduceStep A)
  termination_by b => Int.natAbs (b.1 1 0)
  decreasing_by
    next a h =>
    zify
    exact reduce_aux h

lemma reduce_of_pos {A : Δ m} (hc : (A.1 1 0) = 0) (ha : 0 < A.1 0 0) :
    reduce A = (T ^ (-(A.1 0 1 / A.1 1 1))) • A := by
  rw [reduce]
  simp only [zpow_neg, Int.ediv_neg, neg_neg] at *
  simp_rw [if_pos hc, if_pos ha]

lemma reduce_of_not_pos {A : Δ m} (hc : (A.1 1 0) = 0) (ha : ¬ 0 < A.1 0 0) :
    reduce A = (T ^ (-(-A.1 0 1 / -A.1 1 1))) • (S • (S • A)) := by
  rw [reduce]
  simp only [abs_eq_zero, zpow_neg, Int.ediv_neg, neg_neg] at *
  simp_rw [if_pos hc, if_neg ha]

@[simp]
lemma reduce_reduceStep {A : Δ m} (hc : (A.1 1 0) ≠ 0) :
    reduce (reduceStep A) = reduce A := by
  symm
  rw [reduce, if_neg hc]

private lemma A_c_eq_zero {A : Δ m} (ha : A.1 1 0 = 0) : A.1 0 0 * A.1 1 1 = m := by
  simpa only [det_fin_two, ha, mul_zero, sub_zero] using A.2

private lemma A_d_ne_zero {A : Δ m} (ha : A.1 1 0 = 0) (hm : m ≠ 0) : A.1 1 1 ≠ 0 :=
  right_ne_zero_of_mul (A_c_eq_zero (ha) ▸ hm)

private lemma A_a_ne_zero {A : Δ m} (ha : A.1 1 0 = 0) (hm : m ≠ 0) : A.1 0 0 ≠ 0 :=
  left_ne_zero_of_mul (A_c_eq_zero ha ▸ hm)

/--An auxiliary result bounding the size of the entries of the representatives in `reps`. -/
lemma reps_entries_le_m' {A : Δ m} (h : A ∈ reps m) (i j : Fin 2) :
    A.1 i j ∈ Finset.Icc (-|m|) |m| := by
  suffices |A.1 i j| ≤ |m| from Finset.mem_Icc.mpr <| abs_le.mp this
  obtain ⟨h10, h00, h01, h11⟩ := h
  have h1 : 0 < |A.1 1 1| := (abs_nonneg _).trans_lt h11
  have h2 : 0 < |A.1 0 0| := abs_pos.mpr h00.ne'
  fin_cases i <;> fin_cases j
  · simpa only [← abs_mul, A_c_eq_zero h10] using (le_mul_iff_one_le_right h2).mpr h1
  · simpa only [← abs_mul, A_c_eq_zero h10] using h11.le.trans (le_mul_of_one_le_left h1.le h2)
  · simp_all
  · simpa only [← abs_mul, A_c_eq_zero h10] using (le_mul_iff_one_le_left h1).mpr h2

@[simp]
lemma reps_zero_empty : reps 0 = ∅ := by
  rw [reps, Set.eq_empty_iff_forall_not_mem]
  rintro A ⟨h₁, h₂, -, h₄⟩
  suffices |A.1 0 1| < 0 by linarith [abs_nonneg (A.1 0 1)]
  have := A_c_eq_zero h₁
  simp_all [h₂.ne']

noncomputable instance repsFintype (k : ℤ) : Fintype (reps k) := by
  let H := Finset.Icc (-|k|) |k|
  let H4 := Fin 2 → Fin 2 → H
  apply Fintype.ofInjective (β := H4) (f := fun M i j ↦ ⟨M.1.1 i j, reps_entries_le_m' M.2 i j⟩)
  intro M N h
  ext i j
  simpa only [Subtype.mk.injEq] using congrFun₂ h i j

@[simp]
lemma S_smul_four (A : Δ m) : S • S • S • S • A = A := by
  simp only [smul_def, ← mul_assoc, S_mul_S_eq, neg_mul, one_mul, mul_neg, neg_neg, Subtype.coe_eta]

@[simp]
lemma T_S_rel_smul (A : Δ m) : S • S • S • T • S • T • S • A = T⁻¹ • A := by
  simp_rw [← T_S_rel, ← smul_assoc]

lemma reduce_mem_reps {m : ℤ} (hm : m ≠ 0) (A : Δ m) : reduce A ∈ reps m := by
  induction A using reduce_rec with
  | step A h1 h2 => simpa only [reduce_reduceStep h1] using h2
  | base A h =>
    have hd := A_d_ne_zero h hm
    by_cases h1 : 0 < A.1 0 0
    · simp only [reduce_of_pos h h1]
      have h2 := Int.emod_def (A.1 0 1) (A.1 1 1)
      have h4 := Int.ediv_mul_le (A.1 0 1) hd
      set n : ℤ := A.1 0 1 / A.1 1 1
      have h3 := Int.emod_lt (A.1 0 1) hd
      rw [← abs_eq_self.mpr <| Int.emod_nonneg _ hd] at h3
      simp only [smul_def, Fin.isValue, coe_T_zpow]
      suffices A.1 1 0 = 0 ∧ n * A.1 1 0 < A.1 0 0 ∧
          n * A.1 1 1 ≤ A.1 0 1 ∧ |A.1 0 1 + -(n * A.1 1 1)| < |A.1 1 1| by
        simpa only [reps, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, empty_mul,
          Equiv.symm_apply_apply, Set.mem_setOf_eq, of_apply, cons_val', vecMul, cons_dotProduct,
          vecHead, one_mul, vecTail, Function.comp_apply, Fin.succ_zero_eq_one, neg_mul,
          dotProduct_empty, add_zero, zero_mul, zero_add, empty_val', cons_val_fin_one,
          cons_val_one, cons_val_zero, lt_add_neg_iff_add_lt, le_add_neg_iff_add_le]
      simp_all only [h, mul_comm n, zero_mul, ← sub_eq_add_neg, ← h2,
        Fin.isValue, h1, h3, and_true, true_and]
    · simp only [reps, Fin.isValue, reduce_of_not_pos h h1, Int.ediv_neg, neg_neg, smul_def, ←
        mul_assoc, S_mul_S_eq, neg_mul, one_mul, coe_T_zpow, mul_neg, cons_mul, Nat.succ_eq_add_one,
        Nat.reduceAdd, empty_mul, Equiv.symm_apply_apply, neg_of, neg_cons, neg_empty,
        Set.mem_setOf_eq, of_apply, cons_val', Pi.neg_apply, vecMul, cons_dotProduct, vecHead,
        vecTail, Function.comp_apply, Fin.succ_zero_eq_one, h, mul_zero, dotProduct_empty, add_zero,
        zero_mul, neg_zero, empty_val', cons_val_fin_one, cons_val_one, cons_val_zero, lt_neg,
        neg_add_rev, zero_add, le_add_neg_iff_add_le, ← le_neg, abs_neg, true_and]
      refine ⟨?_, Int.ediv_mul_le _ hd, ?_⟩
      · simp only [Int.lt_iff_le_and_ne]
        exact ⟨not_lt.mp h1, A_a_ne_zero h hm⟩
      · rw [mul_comm, add_comm, ← Int.sub_eq_add_neg, ← Int.emod_def,
         abs_eq_self.mpr <| Int.emod_nonneg _ hd]
        exact Int.emod_lt _ hd

variable {C : Δ m → Prop}

private lemma prop_red_S (hS : ∀ B, C B → C (S • B)) (B) : C (S • B) ↔ C B := by
  refine ⟨?_, hS _⟩
  intro ih
  rw [← (S_smul_four B)]
  solve_by_elim

private lemma prop_red_T (hS : ∀ B, C B → C (S • B)) (hT : ∀ B, C B → C (T • B)) (B) :
    C (T • B) ↔ C B := by
  refine ⟨?_, hT _⟩
  intro ih
  rw [show B = T⁻¹ • T • B by simp, ← T_S_rel_smul]
  solve_by_elim (config := {maxDepth := 10})

private lemma prop_red_T_pow (hS : ∀ B, C B → C (S • B)) (hT : ∀ B, C B → C (T • B)) :
     ∀ B (n : ℤ), C (T^n • B) ↔ C B := by
  intro B n
  induction' n using Int.induction_on with n hn m hm
  · simp only [zpow_zero, one_smul, imp_self]
  · simpa only [add_comm (n:ℤ), zpow_add _ 1, ← smul_eq_mul, zpow_one, smul_assoc, prop_red_T hS hT]
  · rwa [sub_eq_neg_add, zpow_add, zpow_neg_one, ← prop_red_T hS hT, mul_smul, smul_inv_smul]

@[elab_as_elim]
theorem induction_on {C : Δ m → Prop} {A : Δ m} (hm : m ≠ 0)
    (h0 : ∀ A : Δ m, A.1 1 0 = 0 → 0 < A.1 0 0 → 0 ≤ A.1 0 1 → |(A.1 0 1)| < |(A.1 1 1)| → C A)
    (hS : ∀ B, C B → C (S • B)) (hT : ∀ B, C B → C (T • B)) : C A := by
  have h_reduce : C (reduce A) := by
    rcases reduce_mem_reps hm A with ⟨H1, H2, H3, H4⟩
    exact h0 _ H1 H2 H3 H4
  suffices ∀ A : Δ m, C (reduce A) → C A from this _ h_reduce
  apply reduce_rec
  · intro A h
    by_cases h1 : 0 < A.1 0 0
    · simp only [reduce_of_pos h h1, prop_red_T_pow hS hT, imp_self]
    · simp only [reduce_of_not_pos h h1, prop_red_T_pow hS hT, prop_red_S hS, imp_self]
  intro A hc ih hA
  rw [← reduce_reduceStep hc] at hA
  simpa only [reduceStep, prop_red_S hS, prop_red_T_pow hS hT] using ih hA

end IntegralFixedDetMatrices

end FixedDetMatrices
