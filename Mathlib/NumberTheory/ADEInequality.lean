/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.PNat.Basic
import Mathlib.Data.PNat.Interval
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
# The inequality `p⁻¹ + q⁻¹ + r⁻¹ > 1`

In this file we classify solutions to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`, for positive natural numbers `p`, `q`, and `r`.

The solutions are exactly of the form.
* `A' q r := {1,q,r}`
* `D' r := {2,2,r}`
* `E6 := {2,3,3}`, or `E7 := {2,3,4}`, or `E8 := {2,3,5}`

This inequality shows up in Lie theory,
in the classification of Dynkin diagrams, root systems, and semisimple Lie algebras.

## Main declarations

* `pqr.A' q r`, the multiset `{1,q,r}`
* `pqr.D' r`, the multiset `{2,2,r}`
* `pqr.E6`, the multiset `{2,3,3}`
* `pqr.E7`, the multiset `{2,3,4}`
* `pqr.E8`, the multiset `{2,3,5}`
* `pqr.classification`, the classification of solutions to `p⁻¹ + q⁻¹ + r⁻¹ > 1`

-/


namespace ADEInequality

open Multiset


/-- `A' q r := {1,q,r}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`. -/
def A' (q r : ℕ+) : Multiset ℕ+ :=
  {1, q, r}

/-- `A r := {1,1,r}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $A_r$. -/
def A (r : ℕ+) : Multiset ℕ+ :=
  A' 1 r

/-- `D' r := {2,2,r}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $D_{r+2}$. -/
def D' (r : ℕ+) : Multiset ℕ+ :=
  {2, 2, r}

/-- `E' r := {2,3,r}` is a `Multiset ℕ+`.
For `r ∈ {3,4,5}` is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $E_{r+3}$. -/
def E' (r : ℕ+) : Multiset ℕ+ :=
  {2, 3, r}

/-- `E6 := {2,3,3}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_6$. -/
def E6 : Multiset ℕ+ :=
  E' 3

/-- `E7 := {2,3,4}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_7$. -/
def E7 : Multiset ℕ+ :=
  E' 4

/-- `E8 := {2,3,5}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_8$. -/
def E8 : Multiset ℕ+ :=
  E' 5

/-- `sum_inv pqr` for a `pqr : Multiset ℕ+` is the sum of the inverses
of the elements of `pqr`, as rational number.

The intended argument is a multiset `{p,q,r}` of cardinality `3`. -/
def sumInv (pqr : Multiset ℕ+) : ℚ :=
  Multiset.sum (pqr.map fun (x : ℕ+) => x⁻¹)

theorem sumInv_pqr (p q r : ℕ+) : sumInv {p, q, r} = (p : ℚ)⁻¹ + (q : ℚ)⁻¹ + (r : ℚ)⁻¹ := by
  simp only [sumInv, add_zero, insert_eq_cons, add_assoc, map_cons, sum_cons,
    map_singleton, sum_singleton]

/-- A multiset `pqr` of positive natural numbers is `admissible`
if it is equal to `A' q r`, or `D' r`, or one of `E6`, `E7`, or `E8`. -/
def Admissible (pqr : Multiset ℕ+) : Prop :=
  (∃ q r, A' q r = pqr) ∨ (∃ r, D' r = pqr) ∨ E' 3 = pqr ∨ E' 4 = pqr ∨ E' 5 = pqr

theorem admissible_A' (q r : ℕ+) : Admissible (A' q r) :=
  Or.inl ⟨q, r, rfl⟩

theorem admissible_D' (n : ℕ+) : Admissible (D' n) :=
  Or.inr <| Or.inl ⟨n, rfl⟩

theorem admissible_E'3 : Admissible (E' 3) :=
  Or.inr <| Or.inr <| Or.inl rfl

theorem admissible_E'4 : Admissible (E' 4) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem admissible_E'5 : Admissible (E' 5) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr rfl

theorem admissible_E6 : Admissible E6 :=
  admissible_E'3

theorem admissible_E7 : Admissible E7 :=
  admissible_E'4

theorem admissible_E8 : Admissible E8 :=
  admissible_E'5

theorem Admissible.one_lt_sumInv {pqr : Multiset ℕ+} : Admissible pqr → 1 < sumInv pqr := by
  rw [Admissible]
  rintro (⟨p', q', H⟩ | ⟨n, H⟩ | H | H | H)
  · rw [← H, A', sumInv_pqr, add_assoc]
    simp only [lt_add_iff_pos_right, PNat.one_coe, inv_one, Nat.cast_one]
    apply add_pos <;> simp only [PNat.pos, Nat.cast_pos, inv_pos]
  · rw [← H, D', sumInv_pqr]
    norm_num
  all_goals
    rw [← H, E', sumInv_pqr]
    norm_num

theorem lt_three {p q r : ℕ+} (hpq : p ≤ q) (hqr : q ≤ r) (H : 1 < sumInv {p, q, r}) : p < 3 := by
  have h3 : (0 : ℚ) < 3 := by norm_num
  contrapose! H
  rw [sumInv_pqr]
  have h3q := H.trans hpq
  have h3r := h3q.trans hqr
  have hp : (p : ℚ)⁻¹ ≤ 3⁻¹ := by
    rw [inv_le_inv₀ _ h3]
    · assumption_mod_cast
    · norm_num
  have hq : (q : ℚ)⁻¹ ≤ 3⁻¹ := by
    rw [inv_le_inv₀ _ h3]
    · assumption_mod_cast
    · norm_num
  have hr : (r : ℚ)⁻¹ ≤ 3⁻¹ := by
    rw [inv_le_inv₀ _ h3]
    · assumption_mod_cast
    · norm_num
  calc
    (p : ℚ)⁻¹ + (q : ℚ)⁻¹ + (r : ℚ)⁻¹ ≤ 3⁻¹ + 3⁻¹ + 3⁻¹ := add_le_add (add_le_add hp hq) hr
    _ = 1 := by norm_num

theorem lt_four {q r : ℕ+} (hqr : q ≤ r) (H : 1 < sumInv {2, q, r}) : q < 4 := by
  have h4 : (0 : ℚ) < 4 := by norm_num
  contrapose! H
  rw [sumInv_pqr]
  have h4r := H.trans hqr
  have hq : (q : ℚ)⁻¹ ≤ 4⁻¹ := by
    rw [inv_le_inv₀ _ h4]
    · assumption_mod_cast
    · norm_num
  have hr : (r : ℚ)⁻¹ ≤ 4⁻¹ := by
    rw [inv_le_inv₀ _ h4]
    · assumption_mod_cast
    · norm_num
  calc
    (2⁻¹ + (q : ℚ)⁻¹ + (r : ℚ)⁻¹) ≤ 2⁻¹ + 4⁻¹ + 4⁻¹ := add_le_add (add_le_add le_rfl hq) hr
    _ = 1 := by norm_num

theorem lt_six {r : ℕ+} (H : 1 < sumInv {2, 3, r}) : r < 6 := by
  have h6 : (0 : ℚ) < 6 := by norm_num
  contrapose! H
  rw [sumInv_pqr]
  have hr : (r : ℚ)⁻¹ ≤ 6⁻¹ := by
    rw [inv_le_inv₀ _ h6]
    · assumption_mod_cast
    · norm_num
  calc
    (2⁻¹ + 3⁻¹ + (r : ℚ)⁻¹ : ℚ) ≤ 2⁻¹ + 3⁻¹ + 6⁻¹ := add_le_add (add_le_add le_rfl le_rfl) hr
    _ = 1 := by norm_num

theorem admissible_of_one_lt_sumInv_aux' {p q r : ℕ+} (hpq : p ≤ q) (hqr : q ≤ r)
    (H : 1 < sumInv {p, q, r}) : Admissible {p, q, r} := by
  have hp3 : p < 3 := lt_three hpq hqr H
  -- Porting note: `interval_cases` doesn't support `ℕ+` yet.
  replace hp3 := Finset.mem_Iio.mpr hp3
  conv at hp3 => change p ∈ ({1, 2} : Multiset ℕ+)
  fin_cases hp3
  · exact admissible_A' q r
  have hq4 : q < 4 := lt_four hqr H
  replace hq4 := Finset.mem_Ico.mpr ⟨hpq, hq4⟩; clear hpq
  conv at hq4 => change q ∈ ({2, 3} : Multiset ℕ+)
  fin_cases hq4
  · exact admissible_D' r
  have hr6 : r < 6 := lt_six H
  replace hr6 := Finset.mem_Ico.mpr ⟨hqr, hr6⟩; clear hqr
  conv at hr6 => change r ∈ ({3, 4, 5} : Multiset ℕ+)
  fin_cases hr6
  · exact admissible_E6
  · exact admissible_E7
  · exact admissible_E8

theorem admissible_of_one_lt_sumInv_aux :
    ∀ {pqr : List ℕ+} (_ : pqr.Sorted (· ≤ ·)) (_ : pqr.length = 3) (_ : 1 < sumInv pqr),
      Admissible pqr
  | [p, q, r], hs, _, H => by
    obtain ⟨⟨hpq, -⟩, hqr⟩ : (p ≤ q ∧ p ≤ r) ∧ q ≤ r := by simpa using hs
    exact admissible_of_one_lt_sumInv_aux' hpq hqr H

theorem admissible_of_one_lt_sumInv {p q r : ℕ+} (H : 1 < sumInv {p, q, r}) :
    Admissible {p, q, r} := by
  simp only [Admissible]
  let S := sort ((· ≤ ·) : ℕ+ → ℕ+ → Prop) {p, q, r}
  have hS : S.Sorted (· ≤ ·) := sort_sorted _ _
  have hpqr : ({p, q, r} : Multiset ℕ+) = S := (sort_eq LE.le {p, q, r}).symm
  rw [hpqr]
  rw [hpqr] at H
  apply admissible_of_one_lt_sumInv_aux hS _ H
  simp only [S, insert_eq_cons, length_sort, card_cons, card_singleton]

/-- A multiset `{p,q,r}` of positive natural numbers
is a solution to `(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1` if and only if
it is `admissible` which means it is one of:

* `A' q r := {1,q,r}`
* `D' r := {2,2,r}`
* `E6 := {2,3,3}`, or `E7 := {2,3,4}`, or `E8 := {2,3,5}`
-/
theorem classification (p q r : ℕ+) : 1 < sumInv {p, q, r} ↔ Admissible {p, q, r} :=
  ⟨admissible_of_one_lt_sumInv, Admissible.one_lt_sumInv⟩

end ADEInequality
