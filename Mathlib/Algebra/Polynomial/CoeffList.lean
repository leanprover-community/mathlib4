/-
Copyright (c) 2023 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.EraseLead
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

variable {α : Type*}

section Semiring

variable [Semiring α]

/-- A list of coefficients starting from the leading term down to the constant term. Defining
this with P.support keeps it computable, even if the base ring doesn't have DecidableEq.
-/
def coeffList (P : α[X]) : List α :=
  if P.support = ∅ then [] else (List.range (P.natDegree+1)).reverse.map P.coeff

variable {P : α[X]}

theorem coeffList_of_ne_zero (h : P ≠ 0) :
    P.coeffList = (List.range (P.natDegree+1)).reverse.map P.coeff := by
  rw [coeffList, if_neg (mt support_eq_empty.mp h)]

variable (α) in
/-- coeffList 0 = [] -/
@[simp]
theorem coeffList_zero : (0 : α[X]).coeffList = [] := by
  simp [coeffList]

/-- only the zero polynomial gives nil list -/
theorem coeffList_nil (h : P.coeffList = []) : P = 0 := by
  simp_all [coeffList]

@[simp]
theorem coeffList_zero_iff (P : α[X]) : P.coeffList = [] ↔ P = 0 :=
  ⟨coeffList_nil, (· ▸ coeffList_zero α)⟩

/-- coeffList (C x) = [x] -/
@[simp]
theorem coeffList_C {x : α} (h : x ≠ 0) : (C x).coeffList = [x] := by
  simpa [coeffList, if_neg h, List.range_succ]

/-- coeffList always starts with leadingCoeff -/
theorem coeffList_eq_cons_leadingCoeff (h : P ≠ 0) :
    ∃ ls, P.coeffList = P.leadingCoeff :: ls := by
  simp [coeffList, List.range_succ, h]

/-- `List.head?` of coeffList is leadingCoeff -/
theorem head?_coeffList_eq_leadingCoeff (h : P ≠ 0) :
    P.coeffList.head? = P.leadingCoeff :=
  (coeffList_eq_cons_leadingCoeff h).casesOn fun _ ↦ (Eq.symm · ▸ rfl)

/-- `List.head` of coeffList is leadingCoeff -/
theorem head_coeffList_eq_leadingCoeff (h : P ≠ 0) :
    P.coeffList.head (mt coeffList_nil h) = P.leadingCoeff :=
  (coeffList_eq_cons_leadingCoeff h).casesOn fun _ _ ↦
    Option.some.injEq _ _ ▸ List.head?_eq_head _ ▸ head?_coeffList_eq_leadingCoeff h

/-- The length of the coefficient list is the degree plus one, or zero if P has empty support. -/
theorem length_coeffList_support (P : α[X]) :
    P.coeffList.length = if P.support = ∅ then 0 else P.natDegree + 1 := by
  by_cases h : P = 0 <;> simp [h, coeffList]

/-- The length of the coefficient list is the degree plus one, or zero if P is zero. -/
@[simp]
theorem length_coeffList [DecidableEq α] (P : α[X]) :
    P.coeffList.length = if P = 0 then 0 else P.natDegree + 1 := by
  simp [length_coeffList_support]

/-- If the `P.nextCoeff ≠ 0`, then the tail of `P.coeffList` is `coeffList P.eraseLead`.-/
theorem coeffList_of_nextCoeff_ne_zero (h : P.nextCoeff ≠ 0) :
    P.coeffList = P.leadingCoeff::P.eraseLead.coeffList := by
  simp only [coeffList, natDegree_eraseLead_add_one h, mt nextCoeff_eq_zero_of_eraseLead_eq_zero h,
    ne_zero_of_natDegree_gt (natDegree_pos_of_nextCoeff_ne_zero h), true_and,
    support_eq_empty, ↓reduceIte, List.range_succ, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.map_cons, List.map_reverse,
    List.cons.injEq, List.reverse_inj, List.map_inj_left, List.mem_range, coeff_natDegree]
  intros
  exact (Polynomial.eraseLead_coeff_of_ne _ (by linarith)).symm

/- Coefficients of P are always the leading coefficient, some number of zeros, and then
  `coeffList P.eraseLead`. -/
theorem coeffList_eraseLead (h : P ≠ 0) : ∃ n, P.coeffList =
    P.leadingCoeff :: ((List.replicate n 0) ++ P.eraseLead.coeffList) := by
  by_cases hdp : P.natDegree = 0
  · use 0
    rw [eq_C_of_natDegree_eq_zero hdp] at h ⊢
    simp [coeffList_C (C_ne_zero.mp h)]
  obtain ⟨n, hn⟩ : ∃ d, P.natDegree = P.eraseLead.natDegree + 1 + d :=
    exists_add_of_le (have := eraseLead_natDegree_le P; by omega)
  use if P.eraseLead.support = ∅ then P.natDegree else n
  apply List.ext_getElem?
  rintro (_|k)
  · cases coeffList_eq_cons_leadingCoeff h
    simp_all
  by_cases hep : P.eraseLead.support = ∅
  all_goals (
    simp_rw [coeffList_of_ne_zero h, coeffList, hep, List.map_reverse, reduceIte]
    by_cases hkd : k + 1 < P.natDegree + 1
    case neg =>
      rw [List.getElem?_eq_none] <;> simpa using by omega
    obtain ⟨dk, hdk⟩ := exists_add_of_le (Nat.le_of_lt_succ hkd)
    rw [List.getElem?_reverse (by simpa using hkd), List.getElem?_cons_succ, List.length_map,
      List.length_range, List.getElem?_map, List.getElem?_range (by omega), Option.map_some']
  )
  · rw [add_tsub_cancel_right, List.append_nil, ← Nat.eq_sub_of_add_eq' hdk.symm,
      List.getElem?_replicate_of_lt (by omega), ← eraseLead_coeff_of_ne dk (by omega),
      support_eq_empty.mp hep, coeff_zero]
  · conv_lhs => arg 1; equals P.eraseLead.coeff dk =>
      rw [eraseLead_coeff_of_ne (f := P) dk (by omega)]
      congr
      omega
    by_cases hkn : k < n
    case pos => --k points into the 0's chunk
      simpa [List.getElem?_append, hkn] using coeff_eq_zero_of_natDegree_lt (by omega)
    case neg => --k points into the coeffList eraseLead chunk
      rw [List.getElem?_append_right (List.length_replicate _ _ ▸ Nat.le_of_not_gt hkn),
        List.length_replicate, List.getElem?_reverse, List.getElem?_map]
      · rw [List.length_map, List.length_range, List.getElem?_range (by omega), Option.map_some']
        congr 2
        omega
      · simpa using by omega

end Semiring
section Ring
variable [Ring α] (P : α[X])

/-- The coefficient list is negated if the polynomial is negated. --/
theorem coeffList_neg : (-P).coeffList = P.coeffList.map (-·) := by
  by_cases hp : P = 0
  · rw [hp, coeffList_zero, neg_zero, coeffList_zero, List.map_nil]
  · simp [coeffList_of_ne_zero hp, coeffList_of_ne_zero (neg_ne_zero.mpr hp)]

end Ring
section DivisionSemiring

variable [DivisionSemiring α] (P : α[X])

/-- Over a division semiring, multiplying a polynomial by a nonzero constant multiplies
  the coefficient list. -/
theorem coeffList_mul_C {x : α} (hη : x ≠ 0) : (C x * P).coeffList = P.coeffList.map (x * ·) := by
  by_cases hp : P = 0
  · simp only [hp, mul_zero, coeffList_zero, List.map_nil]
  · have hcη := mul_ne_zero (mt (map_eq_zero C).mp hη) hp
    simp [coeffList_of_ne_zero hcη, coeffList_of_ne_zero hp, natDegree_mul_of_nonzero hη]

end DivisionSemiring
end Polynomial
