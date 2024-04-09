/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.ComputeDegree

#align_import data.polynomial.cancel_leads from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Cancel the leading terms of two polynomials

## Definition

* `cancelLeads p q`: the polynomial formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting.

## Main Results
The degree of `cancelLeads` is less than that of the larger of the two polynomials being cancelled.
Thus it is useful for induction or minimal-degree arguments.
-/


namespace Polynomial

noncomputable section

open Polynomial

variable {R : Type*}

section Ring

variable [Ring R] (p q : R[X])

/-- `cancelLeads p q` is formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting. -/
def cancelLeads : R[X] :=
  C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) * q -
    C q.leadingCoeff * X ^ (q.natDegree - p.natDegree) * p
#align polynomial.cancel_leads Polynomial.cancelLeads

variable {p q}

@[simp]
theorem neg_cancelLeads : -p.cancelLeads q = q.cancelLeads p :=
  neg_sub _ _
#align polynomial.neg_cancel_leads Polynomial.neg_cancelLeads

theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm
    (comm : p.leadingCoeff * q.leadingCoeff = q.leadingCoeff * p.leadingCoeff)
    (h : p.natDegree ≤ q.natDegree) (hq : 0 < q.natDegree) :
    (p.cancelLeads q).natDegree < q.natDegree := by
  by_cases hp : p = 0
  · convert hq
    simp [hp, cancelLeads]
  rw [cancelLeads, sub_eq_add_neg, tsub_eq_zero_iff_le.mpr h, pow_zero, mul_one]
  by_cases h0 :
    C p.leadingCoeff * q + -(C q.leadingCoeff * X ^ (q.natDegree - p.natDegree) * p) = 0
  · exact (le_of_eq (by simp only [h0, natDegree_zero])).trans_lt hq
  apply lt_of_le_of_ne
  · compute_degree!
    rwa [Nat.sub_add_cancel]
  · contrapose! h0
    rw [← leadingCoeff_eq_zero, leadingCoeff, h0, mul_assoc, X_pow_mul, ← tsub_add_cancel_of_le h,
      add_comm _ p.natDegree]
    simp only [coeff_mul_X_pow, coeff_neg, coeff_C_mul, add_tsub_cancel_left, coeff_add]
    rw [add_comm p.natDegree, tsub_add_cancel_of_le h, ← leadingCoeff, ← leadingCoeff, comm,
      add_right_neg]
#align polynomial.nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree_of_comm Polynomial.natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm

end Ring

section CommRing

variable [CommRing R] {p q : R[X]}

theorem dvd_cancelLeads_of_dvd_of_dvd {r : R[X]} (pq : p ∣ q) (pr : p ∣ r) : p ∣ q.cancelLeads r :=
  dvd_sub (pr.trans (Dvd.intro_left _ rfl)) (pq.trans (Dvd.intro_left _ rfl))
#align polynomial.dvd_cancel_leads_of_dvd_of_dvd Polynomial.dvd_cancelLeads_of_dvd_of_dvd

theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree (h : p.natDegree ≤ q.natDegree)
    (hq : 0 < q.natDegree) : (p.cancelLeads q).natDegree < q.natDegree :=
  natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm (mul_comm _ _) h hq
#align polynomial.nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree Polynomial.natDegree_cancelLeads_lt_of_natDegree_le_natDegree

end CommRing

end
