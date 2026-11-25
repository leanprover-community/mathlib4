/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johnathon Kyle Armstrong
-/
module

public import Mathlib.GroupTheory.Coxeter.ReflectionSystem
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Generalized Howlett's Formula for Reflection Systems

This file proves Howlett's formula for the principal (Coxeter) element
`w = s_0 * s_1 * ... * s_{n-1}` of a `ReflectionSystem (Fin n) K` over a field `K` of
characteristic different from `2`:

* `U * w = -Uᵀ`,
* `w = -U⁻¹ * Uᵀ`,
* `det (x • 1 - w) = (det U)⁻¹ * det (x • U + Uᵀ)`,

where `U = howlettU S.B` is the upper-triangular matrix satisfying `U + Uᵀ = S.B`, with entries
`U i j = B i j` for `i < j`, `B i i / 2` for `i = j`, and `0` for `i > j`.

## Main definitions
* `ReflectionSystem.howlettU`: Upper-triangular matrix `U` with `U + Uᵀ = B`.
* `ReflectionSystem.prefixProd`: Partial product `s_0 * s_1 * ... * s_{k-1}`.
* `ReflectionSystem.principalElement`: The standard principal element `s_0 * s_1 * ... * s_{n-1}`.

## Main results
* `ReflectionSystem.howlettU_add_transpose`: `howlettU S.B + (howlettU S.B)ᵀ = S.B`.
* `ReflectionSystem.howlett_U_mul_principalElement`:
  `howlettU S.B * principalElement S = -(howlettU S.B)ᵀ`.
* `ReflectionSystem.howlettU_det`: `(howlettU B).det = ∏ i, B i i / 2`.
* `ReflectionSystem.howlettU_det_ne_zero`: `(howlettU S.B).det ≠ 0`.
* `ReflectionSystem.howlett_principalElement_eq_neg_inv_mul_transpose`:
  `principalElement S = -(howlettU S.B)⁻¹ * (howlettU S.B)ᵀ`.
* `ReflectionSystem.principal_charpoly_eq`:
  `(x • 1 - w).det = (det U)⁻¹ * (x • U + Uᵀ).det`.
-/

open Matrix

@[expose] public section

namespace ReflectionSystem

variable {n : ℕ} {K : Type*} [Field K]

/-- The upper-triangular matrix `U` associated to `B : Matrix (Fin n) (Fin n) K`, with
`U i j = B i j` for `i < j`, `B i i / 2` for `i = j`, and `0` for `i > j`. -/
def howlettU (B : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  of fun i j =>
    if i < j then B i j
    else if i = j then B i i / 2
    else 0

@[simp]
lemma howlettU_apply (B : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    howlettU B i j = if i < j then B i j else if i = j then B i i / 2 else 0 := rfl

/-- The upper-triangular matrix `U` decomposes the symmetric bilinear form as `U + Uᵀ = B`. -/
theorem howlettU_add_transpose [NeZero (2 : K)] (S : ReflectionSystem (Fin n) K) :
    howlettU S.B + (howlettU S.B)ᵀ = S.B := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne 2
  ext i j
  simp only [Matrix.add_apply, transpose_apply, howlettU_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hij, not_lt_of_gt hij, ne_of_gt hij]
  · simp only [lt_self_iff_false, ite_false, ite_true]
    field_simp
    ring
  · simp [hij, not_lt_of_gt hij, ne_of_gt hij, S.B_symm.apply i j]

/-- Prefix product `s_0 * s_1 * ... * s_{k-1}` of the generating reflections for `k ≤ n`. -/
def prefixProd (B : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0 => 1
  | k + 1 =>
    if hk : k < n then
      prefixProd B k * reflectionMatrix B ⟨k, hk⟩
    else
      prefixProd B k

/-- The standard principal (Coxeter) element `s_0 * s_1 * ... * s_{n-1}` of a reflection system
indexed by `Fin n`. -/
def principalElement (S : ReflectionSystem (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  prefixProd S.B n

lemma prefixProd_mem_group (S : ReflectionSystem (Fin n) K) (k : ℕ) :
    prefixProd S.B k ∈ S.group := by
  induction k with
  | zero => exact S.group.one_mem
  | succ k ih =>
    simp only [prefixProd]
    split_ifs with hk
    · exact S.group.mul_mem ih (Submonoid.subset_closure ⟨⟨k, hk⟩, rfl⟩)
    · exact ih

/-- The principal element belongs to the reflection group `S.group`. -/
theorem principalElement_mem_group (S : ReflectionSystem (Fin n) K) :
    principalElement S ∈ S.group :=
  prefixProd_mem_group S n

/-- Block-diagonal intermediate matrix `M_k` in the inductive proof of Howlett's formula:
top-left `k × k` block is `-(howlettU B)ᵀ`, bottom-right `(n - k) × (n - k)` block is
`howlettU B`. -/
private def howlettBlock (B : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    Matrix (Fin n) (Fin n) K :=
  of fun r c =>
    if (r : ℕ) < k ∧ (c : ℕ) < k then -(howlettU B)ᵀ r c
    else if k ≤ (r : ℕ) ∧ k ≤ (c : ℕ) then howlettU B r c
    else 0

private lemma howlettBlock_zero (B : Matrix (Fin n) (Fin n) K) :
    howlettBlock B 0 = howlettU B := by
  ext r c
  simp [howlettBlock]

private lemma howlettBlock_n (B : Matrix (Fin n) (Fin n) K) :
    howlettBlock B n = -(howlettU B)ᵀ := by
  ext r c
  simp [howlettBlock]

private lemma howlettBlock_step [NeZero (2 : K)] (S : ReflectionSystem (Fin n) K)
    (k : ℕ) (hk : k < n) :
    howlettBlock S.B k * reflectionMatrix S.B ⟨k, hk⟩ = howlettBlock S.B (k + 1) := by
  let idx : Fin n := ⟨k, hk⟩
  have h2 : (2 : K) ≠ 0 := NeZero.ne 2
  have hB : S.B idx idx ≠ 0 := S.B_diag_ne_zero idx
  have hsymm : ∀ a b, S.B a b = S.B b a := fun a b => S.B_symm.apply b a
  ext r c
  simp only [Matrix.mul_apply, reflectionMatrix_apply]
  have hexpand : ∀ m : Fin n,
      howlettBlock S.B k r m *
        ((if m = c then (1 : K) else 0) -
          (if m = idx then 2 * S.B idx c / S.B idx idx else 0)) =
      (if m = c then howlettBlock S.B k r m else 0) -
        (if m = idx then howlettBlock S.B k r m * (2 * S.B idx c / S.B idx idx) else 0) := by
    intro m
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun m _ => hexpand m), Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [howlettBlock, of_apply, transpose_apply, howlettU_apply]
  have hidx_val : (idx : ℕ) = k := rfl
  rcases lt_trichotomy (r : ℕ) k with hr_lt | hr_eq | hr_gt
  · have h1 : ¬ (k ≤ (r : ℕ)) := not_le_of_gt hr_lt
    have h2' : ¬ ((idx : ℕ) < k) := by omega
    have hr_lt1 : (r : ℕ) < k + 1 := by omega
    have h3 : ¬ (k + 1 ≤ (r : ℕ)) := by omega
    simp only [h1, false_and, ite_false, h2', and_false, hr_lt1, true_and, h3]
    by_cases hc_lt : (c : ℕ) < k
    · have hc_lt1 : (c : ℕ) < k + 1 := by omega
      simp [hr_lt, hc_lt, hc_lt1]
    · by_cases hc_eq : (c : ℕ) = k
      · have hc_lt1 : (c : ℕ) < k + 1 := by omega
        have hcr_not_lt : ¬ (c < r) := by
          intro h
          have h' : (c : ℕ) < (r : ℕ) := h
          omega
        have hcr_ne : c ≠ r := by omega
        simp [hr_lt, hc_lt, hc_lt1, hcr_not_lt, hcr_ne]
      · have hc_not_lt1 : ¬ ((c : ℕ) < k + 1) := by omega
        simp [hr_lt, hc_lt, hc_not_lt1]
  · have hr_idx : r = idx := Fin.ext hr_eq
    subst hr_idx
    have hnot_lt : ¬ ((idx : ℕ) < k) := by omega
    have hle : k ≤ (idx : ℕ) := by omega
    have hlt1 : (idx : ℕ) < k + 1 := by omega
    have hnot_le1 : ¬ (k + 1 ≤ (idx : ℕ)) := by omega
    simp only [hnot_lt, false_and, ite_false, hle, true_and, lt_self_iff_false, hlt1, hnot_le1,
      ite_true]
    have hhalf : S.B idx idx / 2 * (2 * S.B idx c / S.B idx idx) = S.B idx c := by
      field_simp
    rw [hhalf]
    rcases lt_trichotomy (c : ℕ) k with hc_lt | hc_eq | hc_gt
    · have hc_not_le : ¬ (k ≤ (c : ℕ)) := by omega
      have hc_lt1 : (c : ℕ) < k + 1 := by omega
      have hci : c < idx := hc_lt
      simp [hc_not_le, hc_lt1, hci, hsymm c idx]
    · have hc_idx : c = idx := Fin.ext hc_eq
      subst hc_idx
      simp only [hle, hlt1, ite_true, lt_self_iff_false, ite_false]
      field_simp
      ring
    · have hc_le : k ≤ (c : ℕ) := by omega
      have hc_not_lt1 : ¬ ((c : ℕ) < k + 1) := by omega
      have hic : idx < c := hc_gt
      simp [hc_le, hc_not_lt1, hic]
  · have hr_not_lt : ¬ ((r : ℕ) < k) := by omega
    have hr_le : k ≤ (r : ℕ) := by omega
    have hr_not_lt1 : ¬ ((r : ℕ) < k + 1) := by omega
    have hr_le1 : k + 1 ≤ (r : ℕ) := by omega
    have hidx_not_lt : ¬ (r < idx) := by
      intro h
      exact absurd h (not_lt_of_gt hr_gt)
    have hr_ne_idx : r ≠ idx := by
      intro h
      rw [h] at hr_gt
      exact absurd hr_gt (lt_irrefl _)
    simp only [hr_not_lt, false_and, ite_false, hr_le, true_and, hidx_not_lt, hr_ne_idx,
      hr_not_lt1, hr_le1]
    rcases lt_trichotomy (c : ℕ) k with hc_lt | hc_eq | hc_gt
    · have hc_not_le : ¬ (k ≤ (c : ℕ)) := by omega
      have hc_not_le1 : ¬ (k + 1 ≤ (c : ℕ)) := by omega
      simp [hc_not_le, hc_not_le1]
    · have hc_not_le1 : ¬ (k + 1 ≤ (c : ℕ)) := by omega
      have hc_idx : c = idx := Fin.ext hc_eq
      subst hc_idx
      simp [hidx_not_lt, hr_ne_idx, hc_not_le1]
    · have hc_le : k ≤ (c : ℕ) := by omega
      have hc_le1 : k + 1 ≤ (c : ℕ) := by omega
      simp [hc_le, hc_le1]

private lemma howlett_prefix_invariant [NeZero (2 : K)] (S : ReflectionSystem (Fin n) K) :
    ∀ k : ℕ, k ≤ n → howlettU S.B * prefixProd S.B k = howlettBlock S.B k
  | 0, _ => by
    simp [prefixProd, howlettBlock_zero]
  | k + 1, hk => by
    have hk_lt : k < n := hk
    have ih := howlett_prefix_invariant S k (le_of_lt hk_lt)
    simp only [prefixProd, hk_lt, dite_true]
    rw [← Matrix.mul_assoc, ih, howlettBlock_step S k hk_lt]

/-- **Howlett's Formula**: for any reflection system `S` over a field of characteristic `≠ 2`,
`howlettU S.B * principalElement S = -(howlettU S.B)ᵀ`. -/
theorem howlett_U_mul_principalElement [NeZero (2 : K)] (S : ReflectionSystem (Fin n) K) :
    howlettU S.B * principalElement S = -(howlettU S.B)ᵀ := by
  unfold principalElement
  rw [howlett_prefix_invariant S n (le_refl n), howlettBlock_n]

/-- `howlettU B` is upper triangular, so its determinant is the product of its diagonal entries
`∏ i, B i i / 2`. -/
theorem howlettU_det (B : Matrix (Fin n) (Fin n) K) :
    (howlettU B).det = ∏ i : Fin n, B i i / 2 := by
  have htri : (howlettU B).IsUpperTriangular := by
    intro i j hij
    have h1 : ¬ (i < j) := not_lt_of_gt hij
    have h2 : i ≠ j := ne_of_gt hij
    simp [howlettU_apply, h1, h2]
  rw [Matrix.det_of_isUpperTriangular htri]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [howlettU_apply]

/-- The determinant of `howlettU S.B` is nonzero when `2 ≠ 0` in `K`. -/
theorem howlettU_det_ne_zero [NeZero (2 : K)] (S : ReflectionSystem (Fin n) K) :
    (howlettU S.B).det ≠ 0 := by
  rw [howlettU_det]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  exact div_ne_zero (S.B_diag_ne_zero i) (NeZero.ne 2)

/-- **Howlett's Formula (inverse form)**: since `howlettU S.B` is invertible,
`principalElement S = -(howlettU S.B)⁻¹ * (howlettU S.B)ᵀ`. -/
theorem howlett_principalElement_eq_neg_inv_mul_transpose [NeZero (2 : K)]
    (S : ReflectionSystem (Fin n) K) :
    principalElement S = -(howlettU S.B)⁻¹ * (howlettU S.B)ᵀ := by
  have hU : IsUnit (howlettU S.B).det := (howlettU_det_ne_zero S).isUnit
  have hinv : (howlettU S.B)⁻¹ * howlettU S.B = 1 := Matrix.nonsing_inv_mul _ hU
  calc
    principalElement S = 1 * principalElement S := (Matrix.one_mul _).symm
    _ = ((howlettU S.B)⁻¹ * howlettU S.B) * principalElement S := by rw [hinv]
    _ = (howlettU S.B)⁻¹ * (howlettU S.B * principalElement S) := Matrix.mul_assoc _ _ _
    _ = (howlettU S.B)⁻¹ * (-(howlettU S.B)ᵀ) := by rw [howlett_U_mul_principalElement]
    _ = -(howlettU S.B)⁻¹ * (howlettU S.B)ᵀ := by rw [Matrix.mul_neg, Matrix.neg_mul]

/-- Up to the nonzero scalar `(det U)⁻¹`, the characteristic polynomial `det (x • 1 - w)` of the
principal element equals `det (x • U + Uᵀ)`. -/
theorem principal_charpoly_eq [NeZero (2 : K)] (S : ReflectionSystem (Fin n) K) (x : K) :
    (x • (1 : Matrix (Fin n) (Fin n) K) - principalElement S).det =
      (howlettU S.B).det⁻¹ * (x • howlettU S.B + (howlettU S.B)ᵀ).det := by
  have hmul : howlettU S.B * (x • (1 : Matrix (Fin n) (Fin n) K) - principalElement S) =
      x • howlettU S.B + (howlettU S.B)ᵀ := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, howlett_U_mul_principalElement]
    abel
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul] at hdet
  have hU := howlettU_det_ne_zero S
  calc
    (x • (1 : Matrix (Fin n) (Fin n) K) - principalElement S).det
        = (howlettU S.B).det⁻¹ * ((howlettU S.B).det *
            (x • (1 : Matrix (Fin n) (Fin n) K) - principalElement S).det) := by
          rw [inv_mul_cancel_left₀ hU]
    _ = (howlettU S.B).det⁻¹ * (x • howlettU S.B + (howlettU S.B)ᵀ).det := by
          rw [hdet]

end ReflectionSystem
