/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Int.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Absolute values and matrices

This file proves some bounds on matrices involving absolute values.

## Main results

* `Matrix.det_le`: if the entries of an `n × n` matrix are bounded by `x`,
  then the determinant is bounded by `n! x^n`
* `Matrix.det_sum_le`: if we have `s` `n × n` matrices and the entries of each
  matrix are bounded by `x`, then the determinant of their sum is bounded by `n! (s * x)^n`
* `Matrix.det_sum_smul_le`: if we have `s` `n × n` matrices each multiplied by
  a constant bounded by `y`, and the entries of each matrix are bounded by `x`,
  then the determinant of the linear combination is bounded by `n! (s * y * x)^n`
-/


open Matrix
open scoped Nat

namespace Matrix

open Equiv Finset

variable {R S : Type*} [CommRing R] [Nontrivial R]
  [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_le {A : Matrix n n R} {abv : AbsoluteValue R S} {x : S} (hx : ∀ i j, abv (A i j) ≤ x) :
    abv A.det ≤ (Fintype.card n)! • x ^ Fintype.card n :=
  calc
    abv A.det = abv (∑ σ : Perm n, Perm.sign σ • ∏ i, A (σ i) i) := congr_arg abv (det_apply _)
    _ ≤ ∑ σ : Perm n, abv (Perm.sign σ • ∏ i, A (σ i) i) := abv.sum_le _ _
    _ = ∑ σ : Perm n, ∏ i, abv (A (σ i) i) :=
      sum_congr rfl fun σ _ => by rw [abv.map_units_int_smul, abv.map_prod]
    _ ≤ ∑ _σ : Perm n, ∏ _i : n, x := by gcongr; simp [hx]
    _ = (Fintype.card n)! • x ^ Fintype.card n := by simp [Fintype.card_perm]

theorem det_sum_le {ι : Type*} (s : Finset ι) {A : ι → Matrix n n R} {abv : AbsoluteValue R S}
    {x : S} (hx : ∀ k i j, abv (A k i j) ≤ x) :
    abv (det (∑ k ∈ s, A k)) ≤ (Fintype.card n)! • (#s • x) ^ Fintype.card n :=
  det_le fun i j =>
    calc
      abv ((∑ k ∈ s, A k) i j) = abv (∑ k ∈ s, A k i j) := by simp only [sum_apply]
      _ ≤ ∑ k ∈ s, abv (A k i j) := abv.sum_le _ _
      _ ≤ ∑ _k ∈ s, x := by gcongr; apply hx
      _ = #s • x := sum_const _

theorem det_sum_smul_le {ι : Type*} (s : Finset ι) {c : ι → R} {A : ι → Matrix n n R}
    {abv : AbsoluteValue R S} {x : S} (hx : ∀ k i j, abv (A k i j) ≤ x) {y : S}
    (hy : ∀ k, abv (c k) ≤ y) :
    abv (det (∑ k ∈ s, c k • A k)) ≤
      Nat.factorial (Fintype.card n) • (#s • y * x) ^ Fintype.card n := by
  simpa only [smul_mul_assoc] using
    det_sum_le s fun k i j =>
      calc
        abv (c k * A k i j) = abv (c k) * abv (A k i j) := abv.map_mul _ _
        _ ≤ y * x := mul_le_mul (hy k) (hx k i j) (abv.nonneg _) ((abv.nonneg _).trans (hy k))

end Matrix
