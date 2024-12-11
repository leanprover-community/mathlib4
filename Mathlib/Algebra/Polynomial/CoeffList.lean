/-
Copyright (c) 2023 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Data.List.Range
import Mathlib.Data.List.GetD

/-!
# A list of coefficients of a polynomial

## Definition

* `coeffList f`: a `List` of the coefficients, from leading term down to constant term.
* `coeffList 0` is defined to be `[]`.

This is useful for talking about polynomials in terms of list operations, and applying list theorems
to them, instead of working with `Finsupp` structures.

The most significant theorem here is `coeffList_eraseLead`, which says that `coeffList P` can be
written as `(leadingCoeff P) :: (List.replicate k 0) ++ (coeffList P.eraseLead)`. That is, the list
of coefficients starts with the leading coefficient, followed by some number of zeros, and then the
coefficients of `P.eraseLead`.
-/
open Polynomial

namespace Polynomial

variable {α : Type*} [Semiring α] {P : α[X]}

/-- A list of coefficients starting from the leading term down to the constant term. -/
noncomputable def coeffList (P : α[X]) : List α :=
  if P.support = ∅ then [] else (List.range (P.natDegree+1)).reverse.map P.coeff

--the above definition is chosen so that we don't need [DecidableEq α]; otherwise we could
--write `if P = 0 then ... `. The below two definitions make this a bit easier to work with.

theorem coeffList_of_zero (h : P = 0) : coeffList P = [] := by
  simp [h, coeffList]

theorem coeffList_nz (h : P ≠ 0) :
    coeffList P = (List.range (P.natDegree+1)).reverse.map P.coeff := by
  rw [coeffList, if_neg (mt support_eq_empty.mp h)]

/-- coeffList 0 = [] -/
@[simp]
theorem coeffList_zero (α : Type*) [Semiring α] : coeffList (0:α[X]) = [] := by
  simp [coeffList]

/-- only the zero polynomial gives nil list -/
theorem coeffList_nil (h : coeffList P = []) : P = 0 := by
  by_cases P = 0 <;> simp_all [coeffList]

/-- coeffList (C x) = [x] -/
@[simp]
theorem coeffList_C {η : α} (h : η ≠ 0): coeffList (C η) = [η] := by
  simpa [coeffList, if_neg h, List.range_succ]

/-- coeffList always starts with leadingCoeff -/
theorem coeffList_eq_cons_leadingCoeff (h : P ≠ 0) :
    ∃(ls : List α), coeffList P = P.leadingCoeff::ls := by
  by_cases P = 0 <;> simp_all [coeffList, List.range_succ]

/-- The length of the coefficient list is the degree. -/
@[simp]
theorem length_coeffList (P : α[X]) :
    (coeffList P).length = if P.support = ∅ then 0 else P.natDegree + 1 := by
  by_cases P = 0 <;> simp_all [coeffList]

/-- If the `P.nextCoeff ≠ 0`, then the tail of `P.coeffList` is `coeffList P.eraseLead`.-/
theorem coeffList_eraseLead_nz (h : P.nextCoeff ≠ 0) :
    coeffList P = P.leadingCoeff::P.eraseLead.coeffList := by
  have hd : P.natDegree = P.eraseLead.natDegree + 1 := eraseLead_natDegree_of_nextCoeff h
  simp only [coeffList, hd, ne_zero_eraseLead_of_nz_nextCoeff h,
    ne_zero_of_natDegree_gt (natDegree_pos_of_nextCoeff_ne_zero h),
    support_eq_empty, ↓reduceIte, List.range_succ, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.map_cons, List.map_reverse,
    List.cons.injEq, List.reverse_inj, List.map_inj_left, List.mem_range]
  constructor
  · exact hd ▸ coeff_natDegree
  · constructor <;> {
      intros
      symm
      apply Polynomial.eraseLead_coeff_of_ne
      linarith
    }

/- Coefficients of P are always the leading coefficient, some number of zeros, and then
  `coeffList P.eraseLead`. -/
theorem coeffList_eraseLead (h : P≠0) : ∃(n:ℕ), coeffList P =
    P.leadingCoeff::((List.replicate n 0)++P.eraseLead.coeffList) := by
  by_cases hdp : P.natDegree = 0
  · use 0
    rw [eq_C_of_natDegree_eq_zero hdp] at h ⊢
    simp [coeffList_C (C_ne_zero.mp h)]
  have hd : P.natDegree ≥ P.eraseLead.natDegree + 1 := by
    linarith [eraseLead_natDegree_le P, Nat.sub_add_cancel (Nat.ne_zero_iff_zero_lt.mp hdp)]
  replace ⟨dd, hd⟩ := exists_add_of_le hd
  use if P.eraseLead.support = ∅ then P.natDegree else dd
  --need α to be Inhabited to use get!, 0 is an accessible default
  inhabit α
  apply List.ext_get! --two subgoals: l=l₂ if (1) the lengths are equal and (2) l.get!=l₂.get!
    <;> by_cases hep : P.eraseLead.support = ∅ --four subgoals: is P.eraseLead zero or not
  case pos => --lengths are equal, P.eraseLead = 0
    rw [coeffList_nz h, coeffList]
    simp [if_pos hep]
  case neg => --lengths are equal, P.eraseLead ≠ 0
    simp only [length_coeffList, if_neg (mt support_eq_empty.mp h), if_neg hep, List.length_cons,
      List.length_append, List.length_replicate, Nat.succ.injEq]
    exact Nat.add_comm dd _ ▸ hd
  case pos => --contents are equal, P.eraseLead = 0
    simp only [if_pos hep, nonpos_iff_eq_zero, tsub_zero, List.get!_eq_getD]
    rintro (_|n1)
    · --0th element is the same
      rcases coeffList_eq_cons_leadingCoeff h
      simp_all
    · --1st element is the same
      simp_rw [coeffList_nz h, coeffList, if_pos hep]
      simp_all only [natDegree_zero, Fin.cast_mk, List.getElem_map,
        List.append_nil, List.length_cons, Nat.sub_zero, List.map_reverse]
      by_cases hnp : n1 + 1 < P.natDegree + 1
      case pos =>
        rw [List.getD_reverse _ (by simpa [hd] using hnp ), List.getD_cons_succ,
          List.getD_eq_getElem?_getD, List.length_map, List.length_range, List.getElem?_map,
          List.getElem?_range (by omega), Option.map_some', Option.getD_some, add_tsub_cancel_right,
          List.getD_replicate  _ (by omega)]
        obtain ⟨np, hnp⟩ := exists_add_of_le (Nat.le_of_lt_succ hnp)
        have h2 : np = P.natDegree - (n1 + 1) := by omega
        rw [← hd, ← h2, ← eraseLead_coeff_of_ne np (by omega), support_eq_empty.mp hep, coeff_zero]
      case neg =>
        replace hnp := Nat.ge_of_not_lt hnp
        rw [List.getD_cons_succ, List.getD_eq_default, List.getD_eq_default]
        · simp_all
        · simp_all only [List.length_reverse, List.length_map, List.length_range]
  case neg => --contents are equal, P.eraseLead ≠ 0
    simp only [List.get!_eq_getElem!, List.getElem!_eq_getElem?_getD, support_eq_empty, if_neg hep]
    rintro (_|n)
    · cases coeffList_eq_cons_leadingCoeff h
      simp_all
    · simp_rw [coeffList_nz h, coeffList, if_neg hep, List.map_reverse]
      by_cases hnp : n + 1 < P.natDegree + 1
      case pos =>
        obtain ⟨dp, _⟩ := exists_add_of_le (Nat.le_of_lt_succ hnp)
        rw [List.getElem?_reverse (by simpa using hnp), List.getElem?_cons_succ, List.length_map,
          List.length_range, List.getElem?_map, List.getElem?_range (by omega), Option.map_some',
          Option.getD_some]
        conv_lhs => equals P.eraseLead.coeff dp =>
          rw [eraseLead_coeff_of_ne (f := P) dp (by omega)]
          congr
          omega
        by_cases hnp2 : n < dd
        case pos => --goes into the 0's chunk
          simpa [List.getElem?_append, hnp2] using coeff_eq_zero_of_natDegree_lt (by linarith)
        case neg => --goes into the coeffList eraseLead chunk
          obtain ⟨_, hd3⟩ := exists_add_of_le (Nat.ge_of_not_lt hnp2)
          rw [List.getElem?_append_right (List.length_replicate _ _ ▸ Nat.le_of_not_gt hnp2),
            List.length_replicate, List.getElem?_reverse, List.getElem?_map]
          · rw [List.length_map, List.length_range, List.getElem?_range (by omega), hd3,
              Option.map_some', Option.getD_some, add_tsub_cancel_right]
            congr 1
            omega
          · rw [List.length_map, List.length_range, hd3]
            omega
      case neg =>
        rw [List.getElem?_cons_succ, ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD,
          List.getD_eq_default, List.getD_eq_default]
        · simpa using by omega
        · simpa using hnp

variable {α : Type*} [Ring α] (P : Polynomial α)

/-- The coefficient list is negated if the polynomial is negated. --/
theorem coeffList_neg : (-P).coeffList = P.coeffList.map (-·) := by
  by_cases hp : P = 0
  · rw [coeffList_of_zero hp, coeffList_of_zero (neg_eq_zero.mpr hp), List.map_nil]
  · rw [coeffList_nz hp, coeffList_nz (mt neg_eq_zero.mp hp : ¬(-P = 0)),
      natDegree_neg, List.map_map]
    simp

variable {α : Type*} [DivisionSemiring α] (P : Polynomial α)

/-- Over a division semiring, multiplying a polynomial by a nonzero constant multiplies
  the coefficient list. -/
theorem coeffList_mul_C {η : α} (hη : η ≠ 0) :
    coeffList (C η * P) = P.coeffList.map (η * ·) := by
  by_cases hp : P = 0
  · simp only [hp, mul_zero, coeffList_zero, List.map_nil]
  · have hcη : C η * P ≠ 0 := mul_ne_zero (mt (map_eq_zero _).mp hη) hp
    rw [coeffList_nz hcη, coeffList_nz hp, natDegree_mul_of_nonzero hη, List.map_map]
    simp

end Polynomial
