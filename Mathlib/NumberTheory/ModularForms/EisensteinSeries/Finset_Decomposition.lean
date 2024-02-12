/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Data.Complex.Abs
import Mathlib.Data.IsROrC.Basic

/-! # Decomposing `ℤ × ℤ` into squares

We partition `ℤ × ℤ` into squares of the form `Icc (-n) n × Icc (-n) n` for `n : ℕ`. This is useful
for bounding Eisenstein series.
-/

open Complex

open scoped BigOperators NNReal Classical Filter Matrix

noncomputable section

namespace EisensteinSeries

open Finset

/-- For  `m : ℤ` this is the finset of `ℤ × ℤ` of elements such that the maximum of the
absolute values of the pair is `m` -/
def square (m : ℤ) : Finset (ℤ × ℤ) :=
  ((Icc (-m) (m)) ×ˢ (Icc (-m) (m))).filter fun x => max x.1.natAbs x.2.natAbs = m

-- a re-definition in simp-normal form
lemma square_eq (m : ℤ) :
    square m = ((Icc (-m) m) ×ˢ (Icc (-m) m)).filter fun x => max |x.1| |x.2| = m := by
  simp [square]

lemma mem_square_aux {m : ℤ} {i} : i ∈ Icc (-m) m ×ˢ Icc (-m) m ↔ max |i.1| |i.2| ≤ m := by
  simp [abs_le]

lemma square_disj {n : ℤ} : Disjoint (square (n+1)) (Icc (-n) n ×ˢ Icc (-n) n) := by
  rw [square_eq]
  simp only [Finset.disjoint_left, mem_filter, mem_square_aux]
  rintro x ⟨-, hx⟩
  simp [hx]

lemma square_union {n : ℤ} :
    square (n+1) ∪ Icc (-n) n ×ˢ Icc (-n) n = Icc (-(n+1)) (n+1) ×ˢ Icc (-(n+1)) (n+1) := by
  ext x
  rw [mem_union, square_eq, mem_filter, mem_square_aux, mem_square_aux,
    and_iff_right_of_imp le_of_eq, Int.le_add_one_iff, or_comm]

lemma square_disjunion (n : ℤ) :
    (square (n+1)).disjUnion (Icc (-n) n ×ˢ Icc (-n) n) square_disj =
    Icc (-(n+1)) (n+1) ×ˢ Icc (-(n+1)) (n+1) := by rw [disjUnion_eq_union, square_union]

theorem square_size (n : ℕ) : Finset.card (square (n + 1)) = 8 * (n + 1) := by
  have : (((square (n+1)).disjUnion (Icc (-n : ℤ) n ×ˢ Icc (-n : ℤ) n) square_disj).card : ℤ) =
    (Icc (-(n+1 : ℤ)) (n+1) ×ˢ Icc (-(n+1 : ℤ)) (n+1)).card
  · rw [square_disjunion]
  rw [card_disjUnion, card_product, Nat.cast_add, Nat.cast_mul, card_product, Nat.cast_mul,
    Int.card_Icc, Int.card_Icc, Int.toNat_sub_of_le, Int.toNat_sub_of_le,
    ← eq_sub_iff_add_eq] at this
  · rw [← Nat.cast_inj (R := ℤ), this, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add_one]
    ring_nf
  · linarith
  · linarith

theorem natAbs_le_iff_mem_Icc (a : ℤ) (n : ℕ) :
    Int.natAbs a ≤ n ↔ a ∈ Finset.Icc (-(n : ℤ)) n := by
  rw [mem_Icc, ← abs_le, Int.abs_eq_natAbs, Int.ofNat_le]

@[simp]
theorem square_mem (n : ℕ) (x : ℤ × ℤ) : x ∈ square n ↔ max x.1.natAbs x.2.natAbs = n := by
  simp_rw [square, Finset.mem_filter, Nat.cast_inj, mem_product, and_iff_right_iff_imp,
    ← natAbs_le_iff_mem_Icc]
  rintro rfl
  simp only [le_max_iff, le_refl, true_or, or_true, and_self]

theorem square_size' {n : ℕ} (h : n ≠ 0) : Finset.card (square n) = 8 * n := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero h
  exact mod_cast square_size n

theorem squares_cover_all (y : ℤ × ℤ) : ∃! i : ℕ, y ∈ square i := by
  use max y.1.natAbs y.2.natAbs
  simp only [square_mem, and_self_iff, forall_eq']

@[simp]
lemma square_zero : square 0 = {(0, 0)} := rfl

theorem square_zero_card : Finset.card (square 0) = 1 := by
  rw [square_zero, card_singleton]

lemma fun_ne_zero_cases (x : Fin 2 → ℤ) : x ≠ 0 ↔ x 0 ≠ 0 ∨ x 1 ≠ 0 := by
  rw [Function.ne_iff]
  exact Fin.exists_fin_two

lemma square_mem_ne_zero_iff_ne_zero (n : ℕ) (x : Fin 2 → ℤ) (hx : ⟨x 0, x 1⟩ ∈ square n) :
    x ≠ 0 ↔ n ≠ 0 := by
  constructor
  intro h h0
  simp only [h0, Nat.cast_zero, square_zero, mem_singleton, Prod.mk.injEq] at hx
  rw [fun_ne_zero_cases, hx.1, hx.2] at h
  simp only [ne_eq, not_true_eq_false, or_self] at *
  intro hn h
  have hxx : x 0 = 0 ∧ x 1 = 0 := by
    simp only [h, Pi.zero_apply, and_self]
  rw [hxx.1, hxx.2] at hx
  simp only [square_mem, Int.natAbs_zero, max_self] at hx
  exact hn (id hx.symm)
