/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Order.EuclideanAbsoluteValue
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

#align_import data.polynomial.degree.card_pow_degree from "leanprover-community/mathlib"@"85d9f2189d9489f9983c0d01536575b0233bd305"

/-!
# Absolute value on polynomials over a finite field.

Let `𝔽_q` be a finite field of cardinality `q`, then the map sending a polynomial `p`
to `q ^ degree p` (where `q ^ degree 0 = 0`) is an absolute value.

## Main definitions

 * `Polynomial.cardPowDegree` is an absolute value on `𝔽_q[t]`, the ring of
   polynomials over a finite field of cardinality `q`, mapping a polynomial `p`
   to `q ^ degree p` (where `q ^ degree 0 = 0`)

## Main results
 * `Polynomial.cardPowDegree_isEuclidean`: `cardPowDegree` respects the
   Euclidean domain structure on the ring of polynomials

-/


namespace Polynomial

variable {Fq : Type*} [Field Fq] [Fintype Fq]

open AbsoluteValue

open Polynomial

/-- `cardPowDegree` is the absolute value on `𝔽_q[t]` sending `f` to `q ^ degree f`.

`cardPowDegree 0` is defined to be `0`. -/
noncomputable def cardPowDegree : AbsoluteValue Fq[X] ℤ :=
  have card_pos : 0 < Fintype.card Fq := Fintype.card_pos_iff.mpr inferInstance
  have pow_pos : ∀ n, 0 < (Fintype.card Fq : ℤ) ^ n := fun n =>
    pow_pos (Int.natCast_pos.mpr card_pos) n
  letI := Classical.decEq Fq;
  { toFun := fun p => if p = 0 then 0 else (Fintype.card Fq : ℤ) ^ p.natDegree
    nonneg' := fun p => by
      dsimp
      split_ifs
      · rfl
      exact pow_nonneg (Int.ofNat_zero_le _) _
    eq_zero' := fun p =>
      ite_eq_left_iff.trans <|
        ⟨fun h => by
          contrapose! h
          exact ⟨h, (pow_pos _).ne'⟩, absurd⟩
    add_le' := fun p q => by
      by_cases hp : p = 0; · simp [hp]
      by_cases hq : q = 0; · simp [hq]
      by_cases hpq : p + q = 0
      · simp only [hpq, hp, hq, eq_self_iff_true, if_true, if_false]
        exact add_nonneg (pow_pos _).le (pow_pos _).le
      simp only [hpq, hp, hq, if_false]
      refine le_trans (pow_le_pow_right (by omega) (Polynomial.natDegree_add_le _ _)) ?_
      refine
        le_trans (le_max_iff.mpr ?_)
          (max_le_add_of_nonneg (pow_nonneg (by omega) _) (pow_nonneg (by omega) _))
      exact (max_choice p.natDegree q.natDegree).imp (fun h => by rw [h]) fun h => by rw [h]
    map_mul' := fun p q => by
      by_cases hp : p = 0; · simp [hp]
      by_cases hq : q = 0; · simp [hq]
      have hpq : p * q ≠ 0 := mul_ne_zero hp hq
      simp only [hpq, hp, hq, eq_self_iff_true, if_true, if_false, Polynomial.natDegree_mul hp hq,
        pow_add] }
#align polynomial.card_pow_degree Polynomial.cardPowDegree

theorem cardPowDegree_apply [DecidableEq Fq] (p : Fq[X]) :
    cardPowDegree p = if p = 0 then 0 else (Fintype.card Fq : ℤ) ^ natDegree p := by
  rw [cardPowDegree]
  dsimp
  convert rfl
#align polynomial.card_pow_degree_apply Polynomial.cardPowDegree_apply

@[simp]
theorem cardPowDegree_zero : cardPowDegree (0 : Fq[X]) = 0 := rfl
#align polynomial.card_pow_degree_zero Polynomial.cardPowDegree_zero

@[simp]
theorem cardPowDegree_nonzero (p : Fq[X]) (hp : p ≠ 0) :
    cardPowDegree p = (Fintype.card Fq : ℤ) ^ p.natDegree :=
  if_neg hp
#align polynomial.card_pow_degree_nonzero Polynomial.cardPowDegree_nonzero

theorem cardPowDegree_isEuclidean : IsEuclidean (cardPowDegree : AbsoluteValue Fq[X] ℤ) :=
  have card_pos : 0 < Fintype.card Fq := Fintype.card_pos_iff.mpr inferInstance
  have pow_pos : ∀ n, 0 < (Fintype.card Fq : ℤ) ^ n := fun n =>
    pow_pos (Int.natCast_pos.mpr card_pos) n
  { map_lt_map_iff' := fun {p q} => by
      classical
      show cardPowDegree p < cardPowDegree q ↔ degree p < degree q
      simp only [cardPowDegree_apply]
      split_ifs with hp hq hq
      · simp only [hp, hq, lt_self_iff_false]
      · simp only [hp, hq, degree_zero, Ne, bot_lt_iff_ne_bot, degree_eq_bot, pow_pos,
          not_false_iff]
      · simp only [hp, hq, degree_zero, not_lt_bot, (pow_pos _).not_lt]
      · rw [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt, pow_lt_pow_iff_right]
        exact mod_cast @Fintype.one_lt_card Fq _ _ }
#align polynomial.card_pow_degree_is_euclidean Polynomial.cardPowDegree_isEuclidean

end Polynomial
