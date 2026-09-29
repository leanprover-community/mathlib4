/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Evaluation of polynomials over an ordered field

We prove that an odd-degree polynomial over an ordered field changes sign.

-/

@[expose] public section

open Polynomial Finset

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {f : F[X]}

theorem pow_natDegree_sub_one_mul_le_eval (hdeg : f.natDegree ≠ 0) {x : F} (hx : 1 ≤ x) :
    x ^ (f.natDegree - 1) * (f.leadingCoeff * x -
      f.natDegree * (image (|f.coeff ·|) (range f.natDegree)).max'
        (by simpa using hdeg)) ≤ f.eval x := by
  generalize_proofs ne
  set M := (image (|f.coeff ·|) (range f.natDegree)).max' ne
  rw [Polynomial.eval_eq_sum_range, sum_range_succ, ← leadingCoeff]
  calc
    _ = #(range f.natDegree) • (- M * x ^ (f.natDegree - 1)) +
      f.leadingCoeff * x ^ f.natDegree := by grind [pow_succ' x (f.natDegree - 1)]
    _ ≤ _ := by
      gcongr
      refine card_nsmul_le_sum _ _ _ fun i hi ↦ ?_
      have : |f.coeff i| ≤ M := by grind [le_max']
      calc
        - M * x ^ (f.natDegree - 1) ≤ - M * x ^ i :=
          mul_le_mul_of_nonpos_left (by gcongr; grind) (by grind)
        _ ≤ f.coeff i * x ^ i := by gcongr; grind

theorem eval_le_pow_natDegree_sub_one_mul (hdeg : Odd f.natDegree) {x : F} (hx : x ≤ -1) :
    f.eval x ≤ x ^ (f.natDegree - 1) * (f.leadingCoeff * x +
      f.natDegree * (image (|f.coeff ·|) (range f.natDegree)).max'
        (by simpa using hdeg.pos.ne_zero)) := by
  generalize_proofs ne
  set M := (image (|f.coeff ·|) (range f.natDegree)).max' ne
  rw [Polynomial.eval_eq_sum_range, sum_range_succ, ← leadingCoeff]
  calc
    _ = #(range f.natDegree) • (M * x ^ (f.natDegree - 1)) +
      f.leadingCoeff * x ^ f.natDegree := by grind [pow_succ' x (f.natDegree - 1)]
    _ ≥ _ := by
      gcongr
      refine sum_le_card_nsmul _ _ _ fun i hi ↦ ?_
      have : |f.coeff i| ≤ M := by grind [le_max']
      calc
        f.coeff i * x ^ i ≤ |f.coeff i| * |x| ^ i := by
          simpa only [← abs_pow, ← abs_mul] using le_abs_self _
        _ ≤ M * |x| ^ (f.natDegree - 1) := by gcongr <;> grind
        _ = M * x ^ (f.natDegree - 1) := by grind [Even.pow_abs]

theorem exists_ge_imp_eval_pos (hdeg : f.natDegree ≠ 0) (hf : 0 < f.leadingCoeff) :
    ∃ y : F, ∀ x, y < x → 0 < f.eval x := by
  set z := (Finset.image (|f.coeff ·|) (Finset.range f.natDegree)).max' (by simpa using hdeg)
  use max 1 (f.natDegree * z / f.leadingCoeff)
  intro x _
  have : 1 < x := by grind
  calc
    f.eval x ≥ x ^ (f.natDegree - 1) * (f.leadingCoeff * x - f.natDegree * z) :=
      pow_natDegree_sub_one_mul_le_eval hdeg (by grind)
    _ > x ^ (f.natDegree - 1) * (f.leadingCoeff * (max 1 (f.natDegree * z / f.leadingCoeff)) -
        f.natDegree * z) := by gcongr
    _ ≥ x ^ (f.natDegree - 1) * (f.leadingCoeff * (f.natDegree * z / f.leadingCoeff) -
        f.natDegree * z) := by gcongr; grind
    _ ≥ 0 := by field_simp; ring_nf; rfl

theorem exists_le_imp_eval_neg (hdeg : Odd f.natDegree) (hf : 0 < f.leadingCoeff) :
    ∃ y : F, ∀ x, x < y → f.eval x < 0 := by
  set z := (Finset.image (|f.coeff ·|) (Finset.range f.natDegree)).max'
    (by grind [Finset.image_nonempty, Finset.nonempty_range_iff])
  use min (- 1) (- f.natDegree * z / f.leadingCoeff)
  intro x _
  have : 0 < x ^ (f.natDegree - 1) := by
    rw [← Even.pow_abs (by grind)]
    grind [pow_pos]
  calc
    f.eval x ≤ x ^ (f.natDegree - 1) * (f.leadingCoeff * x + f.natDegree * z) :=
      eval_le_pow_natDegree_sub_one_mul hdeg (by grind)
    _ < x ^ (f.natDegree - 1) * (f.leadingCoeff * (min (- 1) (- f.natDegree * z / f.leadingCoeff)) +
        f.natDegree * z) := by gcongr
    _ ≤ x ^ (f.natDegree - 1) * (f.leadingCoeff * (- f.natDegree * z / f.leadingCoeff) +
        f.natDegree * z) := by gcongr; grind
    _ ≤ 0 := by field_simp; ring_nf; rfl

/--
An odd-degree polynomial over an ordered field attains both positive and negative values.
-/
theorem exists_eval_neg_eval_pos (hdeg : Odd f.natDegree) : ∃ x y, f.eval x < 0 ∧ 0 < f.eval y := by
  wlog hf : 0 < f.leadingCoeff generalizing f with res
  · rcases res (f := - f) (by grind [natDegree_neg])
      (by grind [leadingCoeff_eq_zero, leadingCoeff_neg]) with ⟨x, y, hx, hy⟩
    exact ⟨y, x, by grind [eval_neg]⟩
  · rcases exists_ge_imp_eval_pos hdeg.pos.ne_zero hf with ⟨x, hx⟩
    rcases exists_le_imp_eval_neg hdeg hf with ⟨y, hy⟩
    exact ⟨y - 1, x + 1, hy _ (by grind), hx _ (by grind)⟩
