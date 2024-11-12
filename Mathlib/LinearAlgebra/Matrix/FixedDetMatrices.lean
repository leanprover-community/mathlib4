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

namespace FixedDetMatrix

open ModularGroup Matrix SpecialLinearGroup MatrixGroups

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

variable (m : ℤ)

/--Set of representatives for the orbits under `S` and `T`. -/
def reps : Set (Δ m) :=
  { A : Δ m | (A.1 1 0) = 0 ∧ 0 < A.1 0 0 ∧ 0 ≤ A.1 0 1 ∧ |(A.1 0 1)| < |(A.1 1 1)|}

/--Reduction step for matrices in `Δ m` which moves the matrices towards `reps`.-/
def reduce_step (A : Δ m) : Δ m := S • (T ^ (-(A.1 0 0 / A.1 1 0))) • A

private lemma reduce_aux (m : ℤ) (A : Δ m) (h : |(A.1 1 0)| ≠ 0) :
    |((reduce_step m A).1 1 0)| < |(A.1 1 0)| := by
  simp_rw [reduce_step, smul_coe, coe_T_zpow, S]
  simp only [Int.reduceNeg, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, empty_mul,
    Equiv.symm_apply_apply, vecMul_cons, vecHead, cons_val_zero, zero_smul, vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, cons_val_one, cons_val_fin_one, neg_smul, one_smul,
    empty_vecMul, add_zero, zero_add, of_apply, cons_val', Pi.neg_apply, vecMul, cons_dotProduct,
    zero_mul, one_mul, dotProduct_empty, mul_comm, mul_neg, ← Int.sub_eq_add_neg,
    Eq.symm (Int.emod_def (A.1 0 0) (A.1 1 0)), empty_val']
  apply le_trans _ (Int.emod_lt (A.1 0 0) (abs_ne_zero.mp h))
  simp only [Fin.isValue, Int.cast_id, add_le_add_iff_right]
  rw [abs_eq_self.mpr (Int.emod_nonneg (A.1 0 0) (abs_ne_zero.mp h))]

/--Reduction lemma for integral FixedDetMatrices. -/
@[elab_as_elim]
def reduce_rec {C : Δ m → Sort*} (h0 : ∀ A : Δ m, |(A.1 1 0)| = 0 → C A)
    (h1 : ∀ A : Δ m, |(A.1 1 0)| ≠ 0 → C (reduce_step m A) → C A) :
    ∀ A, C A := fun A => by
  by_cases h : |(A.1 1 0)| = 0
  · apply h0 _ h
  · exact h1 A h (reduce_rec h0 h1 (reduce_step m A))
  termination_by A => Int.natAbs (A.1 1 0)
  decreasing_by
    zify
    apply reduce_aux m A
    simpa only [Fin.isValue, ne_eq, abs_eq_zero] using h

/--Map from `Δ m → Δ m` which reduces a FixedDetMatrix towards a representative element in reps. -/
def reduce : Δ m → Δ m := fun A => by
  if |(A.1 1 0)| = 0 then
    if  0 < A.1 0 0 then exact (T ^ (-(A.1 0 1/A.1 1 1))) • A else exact
      (T ^ (-(-A.1 0 1/ -A.1 1 1))) • ( S • ( S • A)) --the -/- don't cancel with ℤ divs.
  else
    exact reduce (reduce_step m A)
  termination_by b => Int.natAbs (b.1 1 0)
  decreasing_by
      next a h =>
      zify
      apply reduce_aux m
      simpa only [Fin.isValue, ne_eq, abs_eq_zero] using h

lemma reduce_eqn1 (A : Δ m) (hc : |(A.1 1 0)| = 0) (ha : 0 < A.1 0 0) :
    reduce m A = (T ^ (-(A.1 0 1/A.1 1 1))) • A := by
  rw [reduce]
  simp only [Fin.isValue, abs_eq_zero, zpow_neg, Int.ediv_neg, neg_neg, dite_eq_ite] at *
  simp_rw [if_pos hc, if_pos ha]

lemma reduce_eqn2 (A : Δ m) (hc : |(A.1 1 0)| = 0) (ha : ¬ 0 < A.1 0 0) :
    reduce m A = (T ^ (-(-A.1 0 1/ -A.1 1 1))) • ( S • ( S • A)) := by
  rw [reduce]
  simp only [Int.cast_id, Fin.isValue, zpow_neg, Int.ediv_neg, neg_neg,
    dite_eq_ite] at *
  simp_rw [if_pos hc, if_neg ha]

lemma reduce_eqn3 (A : Δ m) (hc : ¬ |(A.1 1 0)| = 0) :
    reduce m A = reduce m (reduce_step m A) := by
  rw [reduce]
  simp only [Int.cast_id, Fin.isValue, zpow_neg, Int.ediv_neg, neg_neg,
    dite_eq_ite] at *
  simp_rw [if_neg hc]

private lemma A_d_ne_zero (A : Δ m) (ha : A.1 1 0 = 0) (hm : m ≠ 0) : A.1 1 1 ≠ 0 := by
  have := A.2
  rw [det_fin_two, ha] at this
  aesop

private lemma A_a_ne_zero (A : Δ m) (ha : A.1 1 0 = 0) (hm : m ≠ 0) : A.1 0 0 ≠ 0 := by
  have := A.2
  rw [det_fin_two, ha] at this
  aesop

private lemma A_c_eq_zero (A : Δ m) (ha : A.1 1 0 = 0) : A.1 0 0 * A.1 1 1 = m := by
  have := A.2
  rw [det_fin_two, ha] at this
  aesop

/--An auxiliary result bounding the size of the entries of the representatives in `reps`. -/
lemma reps_entries_le_m' (hm : m ≠ 0) (A : Δ m) (h : A ∈ reps m) (i j : Fin 2) :
    A.1 i j ∈ Finset.Icc (-|m|) |m|:= by
  have h1 : 0 < |A.1 1 1| := Eq.mpr (id (congrArg (fun _a ↦ _a) (propext abs_pos)))
    (A_d_ne_zero m A h.left hm)
  have h2 : 0 < |A.1 0 0| := Eq.mpr (id (congrArg (fun _a ↦ _a) (propext abs_pos)))
    (A_a_ne_zero m A h.left hm)
  fin_cases i <;> fin_cases j
  · simp only [← A_c_eq_zero m A h.1, Fin.zero_eta, Fin.isValue, Finset.mem_Icc, abs_mul]
    constructor
    · rw [neg_le]
      apply (le_trans (neg_le_abs (A.1 0 0)) ((le_mul_iff_one_le_right h2).mpr h1))
    · exact le_trans (le_abs_self (A.1 0 0)) ((le_mul_iff_one_le_right h2).mpr h1)
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Finset.mem_Icc]
    constructor
    · have := abs_pos.mpr hm
      have := h.2.2.1
      omega
    · simp_rw [← A_c_eq_zero m A h.1, abs_mul]
      apply le_trans (le_abs_self (A.1 0 1)) (le_trans h.2.2.2.le (le_mul_of_one_le_left h1.le h2))
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, h.1, Finset.mem_Icc, Left.neg_nonpos_iff,
    abs_nonneg, and_self]
  · simp only [Fin.mk_one, Fin.isValue, ← A_c_eq_zero m A h.1, abs_mul, Finset.mem_Icc]
    constructor
    · rw [neg_le]
      apply le_trans (neg_le_abs (A.1 1 1)) ((le_mul_iff_one_le_left h1).mpr h2)
    · exact le_trans (le_abs_self (A.1 1 1)) ((le_mul_iff_one_le_left h1).mpr h2)

lemma reps_zero_empty : (reps 0) = ∅ := by
  rw [reps]
  ext A
  constructor
  · intro h
    have := A_c_eq_zero 0 _ h.1
    simp only [Fin.isValue, Set.mem_setOf_eq, mul_eq_zero, Set.mem_empty_iff_false] at *
    rcases this with hl | hr
    · exfalso
      simp only [hl, Fin.isValue, lt_self_iff_false, false_and, and_false] at h
    · simp only [hr, Fin.isValue, abs_zero] at h
      exact Lean.Omega.Int.le_lt_asymm (abs_nonneg (A.1 0 1)) (h.2.2.2)
  · simp only [Set.mem_empty_iff_false, Fin.isValue, Set.mem_setOf_eq, false_implies]

noncomputable instance reps_fintype (k : ℤ) : Fintype (reps k) := by
  by_cases hk : k ≠ 0
  · let H := Finset.Icc (-|k|) |k|
    let H4 :=  H × H × H × H
    apply Fintype.ofInjective (β := H4) (f := fun (M : reps k) =>
      ⟨⟨M.1.1 0 0,  reps_entries_le_m' k hk M M.2 0 0⟩,
        ⟨M.1.1 0 1, reps_entries_le_m' k hk M M.2 0 1⟩,
          ⟨M.1.1 1 0, reps_entries_le_m' k hk M M.2 1 0⟩,
            ⟨M.1.1 1 1, reps_entries_le_m' k hk M M.2 1 1⟩⟩)
    intro M N h
    ext i j
    rw [Prod.ext_iff] at h
    simp only [Fin.isValue, Subtype.mk.injEq, Prod.mk.injEq] at h
    fin_cases i <;> fin_cases j --is there an easy way to golf this?
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · simp only [ne_eq, Decidable.not_not] at hk
    rw [hk, reps_zero_empty]
    exact Set.fintypeEmpty

lemma reduce_mem_reps (m : ℤ) (hm : m ≠ 0) : ∀ A : Δ m, reduce m A ∈ reps m := by
  apply reduce_rec
  · intro A h
    by_cases h1 : 0 < A.1 0 0
    · simp only [reps, Fin.isValue, reduce_eqn1 m A h h1, zpow_neg, Set.mem_setOf_eq, smul_coe,
      coe_inv, coe_T_zpow, adjugate_fin_two_of, neg_zero, cons_mul, Nat.succ_eq_add_one,
      Nat.reduceAdd, empty_mul, Equiv.symm_apply_apply, of_apply, cons_val', vecMul,
      cons_dotProduct, vecHead, one_mul, vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      neg_mul, dotProduct_empty, add_zero, zero_mul, zero_add, empty_val', cons_val_fin_one,
      cons_val_one, cons_val_zero, lt_add_neg_iff_add_lt, le_add_neg_iff_add_le]
      refine ⟨abs_eq_zero.mp h, ?_, ?_, ?_⟩
      · rw [abs_eq_zero.mp h]; simp only [Fin.isValue, mul_zero, h1]
      · apply Int.ediv_mul_le; apply A_d_ne_zero m A (by simpa only [abs_eq_zero] using h) hm
      · rw [mul_comm, ← @Int.sub_eq_add_neg, (Int.emod_def (A.1 0 1) (A.1 1 1)).symm]
        apply le_trans _ (Int.emod_lt (A.1 0 1) (A_d_ne_zero m A (by simpa using h) hm))
        rw [abs_eq_self.mpr (Int.emod_nonneg (A.1 0 1) (A_d_ne_zero m A (by simpa using h) hm))]
    · simp only [reps, Fin.isValue, reduce_eqn2 m A h h1, Int.ediv_neg, neg_neg, smul_def, ←
      mul_assoc, S_mul_S_eq, neg_mul, one_mul, coe_T_zpow, mul_neg, cons_mul, Nat.succ_eq_add_one,
      Nat.reduceAdd, empty_mul, Equiv.symm_apply_apply, neg_of, neg_cons, neg_empty,
      Set.mem_setOf_eq, of_apply, cons_val', Pi.neg_apply, vecMul, cons_dotProduct, vecHead,
      vecTail, Function.comp_apply, Fin.succ_zero_eq_one, dotProduct_empty, add_zero, neg_add_rev,
      zero_mul, zero_add, empty_val', cons_val_fin_one, cons_val_one, neg_eq_zero, cons_val_zero,
      lt_add_neg_iff_add_lt, le_add_neg_iff_add_le, abs_neg]
      refine ⟨abs_eq_zero.mp h, ?_, ?_,?_⟩
      · simp only [Fin.isValue, abs_eq_zero.mp h, mul_zero, neg_zero, Int.lt_iff_le_and_ne, ne_eq]
        refine ⟨not_lt.mp h1, A_a_ne_zero m A (by simpa using h) hm⟩
      · rw [le_neg]
        apply Int.ediv_mul_le; apply A_d_ne_zero m A (by simpa using h) hm
      · rw [mul_comm, add_comm, ← @Int.sub_eq_add_neg, (Int.emod_def (-A.1 0 1) (A.1 1 1)).symm]
        apply le_trans _ (Int.emod_lt (-A.1 0 1) (A_d_ne_zero m A (by simpa using h) hm))
        rw [abs_eq_self.mpr (Int.emod_nonneg (-A.1 0 1) (A_d_ne_zero m A (by simpa using h) hm))]
  · exact fun A h1 h2 ↦ Eq.mpr (id (congrArg (fun _a ↦ _a ∈ reps m) (reduce_eqn3 m A h1))) h2

lemma S_smul_four (A : Δ m) : (S • ( S • (S • ( S • A)))) = A := by
  simp only [smul_def, ← mul_assoc, S_mul_S_eq, neg_mul, one_mul, mul_neg, neg_neg, Subtype.coe_eta]

lemma T_S_rel (A : Δ m) : (S • S • S • T • S • T • S • A) = T⁻¹ • A := by
  have : S • S • S • T • S • T • S = T⁻¹ := by
    rw [smul_eq_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  simp_rw [← this, ← smul_assoc]

private lemma prop_red1 {C : Δ m → Prop} (hS : ∀ B, C B → C (S • B)) : ∀ B, C (S • B) → C B := by
  intro B ih
  rw [← (S_smul_four m B)]
  apply hS _ (hS _ (hS _ ih))

private lemma prop_red2 {C : Δ m → Prop} (hS : ∀ B, C B → C (S • B)) (hT : ∀ B, C B → C (T • B)) :
    ∀ B, C B → C (T⁻¹ • B) := by
  intro B ih
  have h := (hS _ <| hS _ <| hS _ <| hT _ <| hS _ <| hT _ <| hS _ ih)
  rw [T_S_rel m B] at h
  exact h

private lemma prop_red3 {C : Δ m → Prop} (hS : ∀ B, C B → C (S • B)) (hT : ∀ B, C B → C (T • B)) :
    ∀ B, C (T • B) → C B := by
  intro B ih
  have h := (prop_red2 _ hS hT) (T • B) ih
  simpa using h

private lemma prop_red4 {C : Δ m → Prop} (hS : ∀ B, C B → C (S • B)) (hT : ∀ B, C B → C (T • B)) :
     ∀ B (n : ℤ), C (T^n • B) → C B := by
  intro B n
  induction' n using Int.induction_on with n hn m hm
  · simp only [zpow_zero, one_smul, imp_self]
  · intro h
    rw [add_comm, zpow_add, ← smul_eq_mul, zpow_one, smul_assoc] at h
    exact hn <| (prop_red3 _ hS hT) _ h
  · rw [sub_eq_neg_add, zpow_add, zpow_neg_one]
    intro h
    apply hm
    have := hT _ h
    rw [smul_def] at this
    convert this
    simp only [zpow_neg, zpow_natCast, smul_def, Int.cast_id, coe_inv, coe_pow, adjugate_pow, ←
      mul_assoc, ← coe_mul, mul_inv_cancel T, one_mul]

@[elab_as_elim]
theorem induction_on {C : Δ m → Prop} (A : Δ m) (hm : m ≠ 0)
    (h0 : ∀ A : Δ m, A.1 1 0 = 0 → A.1 0 0 * A.1 1 1 = m → 0 < A.1 0 0 → 0 ≤ A.1 0 1 →
      |(A.1 0 1)| < |(A.1 1 1)| → C A)
    (hS : ∀ B, C B → C (S • B)) (hT : ∀ B, C B → C (T • B)) : C A := by
  have h_reduce : C (reduce m A) := by
    rcases reduce_mem_reps m hm A with ⟨H1, H2, H3, H4⟩
    apply h0 _ H1 ?_ H2 H3
    · apply H4
    · apply A_c_eq_zero _ _ H1
  suffices ∀ A : Δ m, C (reduce m A) → C A from this _ h_reduce
  apply reduce_rec
  · intro A h
    by_cases h1 : 0 < A.1 0 0
    · rw [reduce_eqn1 _ _ h h1]
      intro h
      apply (prop_red4 _ hS hT) A (-(A.1 0 1 / A.1 1 1)) h
    · rw [reduce_eqn2 _ _ h h1]
      intro h
      exact (prop_red1 _ hS) _ <| (prop_red1 _ hS) _ ((prop_red4 _ hS hT) _ _ h)
  intro A hc ih hA
  rw [reduce_eqn3 _ _ hc] at hA
  exact (prop_red4 _ hS hT) _ _ <| (prop_red1 _ hS) _ (ih hA)

end IntegralFixedDetMatrices

end FixedDetMatrix
