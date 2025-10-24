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

This is useful for talking about polynomials in terms of list operations. It is "redundant" data in
the sense that `Polynomial` is already a `Finsupp` (of its coefficients), and `Polynomial.coeff`
turns this into a function, and these have exactly the same data as `coeffList`. The difference is
that `coeffList` is intended for working together with list operations: getting `List.head`,
comparing adjacent coefficients with each other, or anything that involves induction on Polynomials
by dropping the leading term (which is `Polynomial.eraseLead`).

Note that `coeffList` _starts_ with the highest-degree terms and _ends_ with the constant term. This
might seem backwards in the sense that `Polynomial.coeff` and `List.get!` are reversed to one
another, but it means that induction on `List`s is the same as induction on
`Polynomial.leadingCoeff`.

The most significant theorem here is `coeffList_eraseLead`, which says that `coeffList P` can be
written as `leadingCoeff P :: List.replicate k 0 ++ coeffList P.eraseLead`. That is, the list
of coefficients starts with the leading coefficient, followed by some number of zeros, and then the
coefficients of `P.eraseLead`.
-/

namespace Polynomial

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- The list of coefficients starting from the leading term down to the constant term. -/
def coeffList (P : R[X]) : List R :=
  (List.range P.degree.succ).reverse.map P.coeff

variable {P : R[X]}

variable (R) in
@[simp]
theorem coeffList_zero : (0 : R[X]).coeffList = [] := by
  simp [coeffList]

/-- Only the zero polynomial has no coefficients. -/
@[simp]
theorem coeffList_eq_nil {P : R[X]} : P.coeffList = [] ↔ P = 0 := by
  simp [coeffList]

@[simp]
theorem coeffList_C {x : R} (h : x ≠ 0) : (C x).coeffList = [x] := by
  simp [coeffList, List.range_succ, degree_eq_natDegree (C_ne_zero.mpr h)]

theorem coeffList_eq_cons_leadingCoeff (h : P ≠ 0) :
    ∃ ls, P.coeffList = P.leadingCoeff :: ls := by
  simp [coeffList, List.range_succ, withBotSucc_degree_eq_natDegree_add_one h]

@[simp]
theorem head?_coeffList (h : P ≠ 0) :
    P.coeffList.head? = P.leadingCoeff :=
  (coeffList_eq_cons_leadingCoeff h).casesOn fun _ ↦ (Eq.symm · ▸ rfl)

@[simp] theorem head_coeffList (P : R[X]) (hP) :
    P.coeffList.head hP = P.leadingCoeff :=
  let h := coeffList_eq_nil.not.mp hP
  (coeffList_eq_cons_leadingCoeff h).casesOn fun _ _ ↦
    Option.some.injEq _ _ ▸ List.head?_eq_head _ ▸ head?_coeffList h

theorem length_coeffList_eq_withBotSucc_degree (P : R[X]) : P.coeffList.length = P.degree.succ := by
  simp [coeffList]

@[simp]
theorem length_coeffList_eq_ite [DecidableEq R] (P : R[X]) :
    P.coeffList.length = if P = 0 then 0 else P.natDegree + 1 := by
  by_cases h : P = 0 <;> simp [h, coeffList, withBotSucc_degree_eq_natDegree_add_one]

theorem leadingCoeff_cons_eraseLead (h : P.nextCoeff ≠ 0) :
    P.leadingCoeff :: P.eraseLead.coeffList = P.coeffList := by
  have h₂ := ne_zero_of_natDegree_gt (natDegree_pos_of_nextCoeff_ne_zero h)
  have h₃ := mt nextCoeff_eq_zero_of_eraseLead_eq_zero h
  simpa [natDegree_eraseLead_add_one h, coeffList, withBotSucc_degree_eq_natDegree_add_one h₂,
    withBotSucc_degree_eq_natDegree_add_one h₃, List.range_succ] using
    (Polynomial.eraseLead_coeff_of_ne · ·.ne)

@[simp]
theorem coeffList_monomial {x : R} (hx : x ≠ 0) (n : ℕ) :
    (monomial n x).coeffList = x :: List.replicate n 0 := by
  have h := mt (Polynomial.monomial_eq_zero_iff x n).mp hx
  apply List.ext_get (by classical simp [hx])
  rintro (_ | k) _ h₁
  · exact (coeffList_eq_cons_leadingCoeff h).rec (by simp_all)
  · rw [List.length_cons, List.length_replicate] at h₁
    have : ((monomial n) x).natDegree.succ = n + 1 := by
      simp [Polynomial.natDegree_monomial_eq n hx]
    simpa [coeffList, withBotSucc_degree_eq_natDegree_add_one h]
      using Polynomial.coeff_monomial_of_ne _ (by cutsat)

/- Coefficients of a polynomial `P` are always the leading coefficient, some number of zeros, and
then `coeffList P.eraseLead`. -/
theorem coeffList_eraseLead (h : P ≠ 0) :
    P.coeffList =
      P.leadingCoeff :: (.replicate (P.natDegree - P.eraseLead.degree.succ) 0
        ++ P.eraseLead.coeffList) := by
  by_cases hdp : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdp] at h ⊢
    simp [coeffList_C (C_ne_zero.mp h)]
  by_cases hep : P.eraseLead = 0
  · have h₂ : .monomial P.natDegree P.leadingCoeff = P := by
      simpa [hep] using P.eraseLead_add_monomial_natDegree_leadingCoeff
    nth_rewrite 1 [← h₂]
    simp [coeffList_monomial (Polynomial.leadingCoeff_ne_zero.mpr h), hep]
  have h₁ := withBotSucc_degree_eq_natDegree_add_one h
  have h₂ := withBotSucc_degree_eq_natDegree_add_one hep
  obtain ⟨n, hn, hn2⟩ : ∃ d, P.natDegree = P.eraseLead.natDegree + 1 + d ∧
      d = P.natDegree - P.eraseLead.degree.succ := by
    use P.natDegree - P.eraseLead.natDegree -  1
    have := eraseLead_natDegree_le P
    cutsat
  rw [← hn2]; clear hn2
  apply List.ext_getElem?
  rintro (_ | k)
  · obtain ⟨w,h⟩ := (coeffList_eq_cons_leadingCoeff h)
    simp_all
  simp only [coeffList, List.map_reverse]
  by_cases hkd : P.natDegree + 1 ≤ k + 1
  · rw [List.getElem?_eq_none]
      <;> simpa [hep, h] using by cutsat
  obtain ⟨dk, hdk⟩ := exists_add_of_le (Nat.le_of_lt_succ (Nat.lt_of_not_ge hkd))
  rw [List.getElem?_reverse (by simpa [withBotSucc_degree_eq_natDegree_add_one h] using hkd),
    List.getElem?_cons_succ, List.length_map, List.length_range, List.getElem?_map,
    List.getElem?_range (by cutsat), Option.map_some]
  conv_lhs => arg 1; equals P.eraseLead.coeff dk =>
    rw [eraseLead_coeff_of_ne (f := P) dk (by cutsat)]
    congr
    cutsat
  by_cases hkn : k < n
  · simpa [List.getElem?_append, hkn] using coeff_eq_zero_of_natDegree_lt (by cutsat)
  · rw [List.getElem?_append_right (List.length_replicate ▸ Nat.le_of_not_gt hkn),
      List.length_replicate, List.getElem?_reverse, List.getElem?_map]
    · rw [List.length_map, List.length_range,
        List.getElem?_range (by cutsat), Option.map_some]
      congr 2
      cutsat
    · simpa using by cutsat

end Semiring

section Ring

variable [Ring R] (P : R[X])

@[simp]
theorem coeffList_neg : (-P).coeffList = P.coeffList.map (-·) := by
  by_cases hp : P = 0
  · rw [hp, coeffList_zero, neg_zero, coeffList_zero, List.map_nil]
  · simp [coeffList]

end Ring

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] (P : R[X])

theorem coeffList_C_mul {x : R} (hx : x ≠ 0) : (C x * P).coeffList = P.coeffList.map (x * ·) := by
  by_cases hp : P = 0
  · simp [hp]
  · simp [coeffList, Polynomial.degree_C hx]

end NoZeroDivisors
end Polynomial
