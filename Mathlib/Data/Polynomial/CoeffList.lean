/-
Copyright (c) 2023 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Data.Polynomial.EraseLead
import Mathlib.Data.List.Range

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
  have hpz : P ≠ 0 := ne_zero_of_nz_nextCoeff h
  simp [coeffList, hd, hpz, ne_zero_eraseLead_of_nz_nextCoeff h, List.range_succ]
  constructor
  { rw [← hd]; exact coeff_natDegree }
  constructor
  { rw [leadingCoeff]
    apply Eq.symm
    apply Polynomial.eraseLead_coeff_of_ne
    linarith }
  rw [List.map_reverse, List.map_reverse];
  congr 1
  rw [List.map_eq_map_iff]
  intro n hn
  rw [List.mem_range] at hn
  apply Eq.symm
  apply Polynomial.eraseLead_coeff_of_ne
  linarith

/- Coefficients of P are always the leading coefficient, some number of zeros, and then
  `coeffList P.eraseLead`. -/
theorem coeffList_eraseLead (h : P≠0) : ∃(n:ℕ), coeffList P =
    P.leadingCoeff::((List.replicate n 0)++P.eraseLead.coeffList) := by
  by_cases hdp : P.natDegree = 0
  case pos =>
    use 0
    rw [eq_C_of_natDegree_eq_zero hdp] at h ⊢
    have hcnz := coeffList_C (C_ne_zero.mp h)
    rw [hcnz]
    simp
  replace hdp := Nat.ne_zero_iff_zero_lt.mp hdp
  have hd : P.natDegree ≥ P.eraseLead.natDegree + 1 := by
    have := eraseLead_natDegree_le P
    have : P.eraseLead.natDegree + 1 ≤ (P.natDegree - 1) + 1 := (add_le_add_iff_right 1).mpr this
    rwa [Nat.sub_add_cancel hdp] at this
  obtain ⟨dd, hd⟩ := exists_add_of_le hd
  rw [Nat.add_comm] at hd
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
    intro n
    cases n
    case zero => --0th element is the same
      obtain ⟨ls, hls⟩ := coeffList_eq_cons_leadingCoeff h
      simp_all
    case succ n1 => --1st element on is the same
      simp_rw [coeffList_nz h, coeffList, if_pos hep]
      simp_all only [natDegree_zero, Fin.cast_mk, List.get_map,
        List.append_nil, List.length_cons, Nat.sub_zero]
      rw [List.map_reverse]
      by_cases hnp : n1 + 1 < P.natDegree + 1
      case pos =>
        rw [List.getD_reverse]; swap
        · rw [List.length_map, List.length_range]
          exact hd ▸ hnp
        rw [List.getD_cons_succ, List.getD, List.length_map, List.length_range, List.get?_map,
            List.get?_range, Option.map_some', Option.getD_some, add_tsub_cancel_right,
            List.getD_replicate_elem_eq]; swap
        · exact (add_lt_add_iff_right 1).mp (hd ▸ hnp)
        · obtain ⟨np, hnp⟩ := exists_add_of_le (Nat.le_of_lt_succ hnp)
          have hnp2 : np = P.natDegree - (n1 + 1) :=
            (Nat.sub_eq_of_eq_add (Nat.add_comm _ np ▸ hnp)).symm
          have : coeff P.eraseLead np = coeff P np := by
            apply eraseLead_coeff_of_ne np
            linarith
          rw [← hd, ← hnp2, ← this, support_eq_empty.mp hep, coeff_zero]
        · rw [support_eq_empty.mp hep]
          calc dd + 1 - (n1 + 1)
            _ ≤ dd + 1 := Nat.sub_le (dd + 1) (n1 + 1)
            _ < dd + 2 := (add_lt_add_iff_left dd).2 Nat.one_lt_two
      case neg =>
        replace hnp := Nat.ge_of_not_lt hnp
        rw [List.getD_cons_succ, List.getD_eq_default, List.getD_eq_default]
        · simp_all
        · simp_all only [List.length_reverse, List.length_map, List.length_range]
  case neg => --contents are equal, P.eraseLead ≠ 0
    simp [if_neg hep]
    intro n
    cases n
    case zero => --0th element is the same
      obtain ⟨ls, hls⟩ := coeffList_eq_cons_leadingCoeff h
      simp_all [List.get]
    case succ n1 => --1st element on is the same
      simp_rw [coeffList_nz h, coeffList, if_neg hep, List.map_reverse]
      by_cases hnp : n1 + 1 < P.natDegree + 1
      case pos =>
        obtain ⟨dp, hdp⟩ := exists_add_of_le (Nat.le_of_lt_succ hnp)
        rw [List.getD_reverse, List.getD_cons_succ, List.getD, List.length_map,
            List.length_range, List.get?_map, List.get?_range,  Option.map_some', Option.getD_some,
            add_tsub_cancel_right]
        case h => simpa
        have : coeff P.eraseLead dp = coeff P dp := by
          apply eraseLead_coeff_of_ne dp
          linarith
        rw [hdp, add_tsub_cancel_left, ← this]
        by_cases hnp2 : n1 < dd
        case pos => --goes into the 0's chunk
          rw [List.getD_append]
          case h =>
            rw [List.length_replicate]
            exact hnp2
          rw [List.getD_replicate_elem_eq]
          case h => exact hnp2
          apply coeff_eq_zero_of_natDegree_lt
          linarith
        case neg => --goes into the coeffList eraseLead chunk
          obtain ⟨d3, hd3⟩ := exists_add_of_le (Nat.ge_of_not_lt hnp2)
          rw [List.getD_append_right]
          case h =>
            rw [List.length_replicate]
            exact Nat.le_of_not_gt hnp2
          rw [List.length_replicate, List.getD_reverse, List.getD, List.get?_map]
          case h =>
            rw [List.length_map, List.length_range, hd3, add_tsub_cancel_left]
            linarith
          rw [List.length_map, List.length_range]
          rw [List.get?_range, Option.map_some', Option.getD_some, add_tsub_cancel_right]
          congr 1
          rw [hd3, add_tsub_cancel_left]
          rw [hd3] at hdp
          rw [hdp] at hd
          rw [← Nat.add_assoc, Nat.add_assoc, Nat.add_comm 1 _, ← Nat.add_assoc] at hd
          replace hd := Nat.add_right_cancel hd
          rw [Nat.add_assoc, Nat.add_comm d3 _] at hd
          replace hd := Nat.add_left_cancel hd
          exact (Nat.sub_eq_of_eq_add hd.symm).symm
          rw [Nat.sub_sub]
          apply Nat.sub_lt <;> simp
        rw [add_tsub_cancel_right]
        calc
          P.natDegree - Nat.succ n1 ≤ P.natDegree := Nat.sub_le _ _
          P.natDegree < P.natDegree + 1 := Nat.lt_succ_self _
      case neg =>
        replace hnp := Nat.ge_of_not_lt hnp
        simp only [List.getD_cons_succ]
        rw [List.getD_eq_default, List.getD_eq_default]
        simp_all
        simp_all only [List.length_reverse, List.length_map, List.length_range]

variable {α : Type*} [Ring α] (P : Polynomial α)

/-- The coefficient list is negated if the polynomial is negated. --/
theorem coeffList_neg : (-P).coeffList = P.coeffList.map (λx↦-x) := by
  by_cases hp : P = 0
  · rw [coeffList_of_zero hp, coeffList_of_zero (neg_eq_zero.mpr hp), List.map_nil]
  · rw [coeffList_nz hp, coeffList_nz (mt neg_eq_zero.mp hp : ¬(-P = 0)),
      natDegree_neg, List.map_map]
    congr; funext; simp

variable {α : Type*} [DivisionSemiring α] (P : Polynomial α)

/-- Over a division semiring, multiplying a polynomial by a nonzero constant multiplies
  the coefficient list. -/
theorem coeffList_mul_C {η : α} (hη : η ≠ 0) :
    coeffList (C η * P) = P.coeffList.map (λx↦η*x) := by
  by_cases hp : P = 0
  case pos => simp only [hp, mul_zero, coeffList_zero, List.map_nil]
  have hcη : C η * P ≠ 0 := mul_ne_zero (mt (map_eq_zero _).mp hη) hp
  rw [coeffList_nz hcη, coeffList_nz hp]
  rw [natDegree_mul_of_nonzero, List.map_map]
  congr
  funext n
  simp
  exact hη

end Polynomial
