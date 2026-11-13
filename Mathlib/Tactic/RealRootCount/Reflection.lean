/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Polynomial.CoeffList

import Mathlib.Algebra.Polynomial.Sturm.Sequence
import Mathlib.Basic.Real.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.RealRootCount.SturmCertificate

/-!
# A checked `SturmCertificate` defines a Sturm sequence

This file proves that the entries of a `SturmCertificate` that passes `checkSturm` are the Sturm
sequence of its polynomial and its derivative, up to positive constant factors.
-/

open Polynomial SignType

namespace Mathlib.Tactic.RealRootCount

section ofCoeffList

variable {R : Type*} [Semiring R] {l : List R}

theorem coeff_ofCoeffList_length_sub_one (l : List R) :
    (ofCoeffList l).coeff (l.length - 1) = l.getLastD 0 := by
  simp only [coeff_ofCoeffList, List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem ofCoeffList_ne_zero (h : l.getLastD 0 ≠ 0) : ofCoeffList l ≠ 0 := by
  intro h1
  rw [← coeff_ofCoeffList_length_sub_one, h1] at h
  contradiction

theorem natDegree_ofCoeffList (h : l.getLastD 0 ≠ 0) :
    (ofCoeffList l).natDegree = l.length - 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · refine natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    rw [coeff_ofCoeffList, List.getD_eq_default _ _ (by lia)]
  · rwa [coeff_ofCoeffList_length_sub_one]

theorem ofCoeffList_coeffDerivative (p : List R) :
    ofCoeffList (coeffDerivative p) = derivative (ofCoeffList p) := by
  ext n
  rw [coeff_derivative, coeff_ofCoeffList, coeff_ofCoeffList, coeffDerivative]
  cases p with
  | nil => simp
  | cons c p =>
    rw [List.tail_cons, List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_zipIdx, List.getD_eq_getElem?_getD]
    cases p[n]? with
    | none => simp
    | some a => simp [Nat.cast_comm, add_comm]

theorem ofCoeffList_coeffAddSmul {R : Type*} [CommSemiring R] (c : R) (p q : List R) :
    ofCoeffList (coeffAddSmul c p q) = C c * ofCoeffList p + ofCoeffList q := by
  induction p generalizing q with
  | nil => rw [coeffAddSmul, ofCoeffList_nil, mul_zero, zero_add]
  | cons x p ih =>
    cases q with
    | nil =>
      rw [coeffAddSmul, ofCoeffList_cons, ih, ofCoeffList_cons, ofCoeffList_nil, C_mul]
      ring
    | cons y q =>
      rw [coeffAddSmul, ofCoeffList_cons, ih, ofCoeffList_cons, ofCoeffList_cons, C_add, C_mul]
      ring

theorem ofCoeffList_coeffMul {R : Type*} [CommSemiring R] (p q : List R) :
    ofCoeffList (coeffMul p q) = ofCoeffList p * ofCoeffList q := by
  induction p with
  | nil => rw [coeffMul, List.foldr_nil, ofCoeffList_nil, zero_mul]
  | cons c p ih =>
    calc ofCoeffList (coeffMul (c :: p) q)
      _ = ofCoeffList (coeffAddSmul c q (0 :: coeffMul p q)) := rfl
      _ = C c * ofCoeffList q + X * (ofCoeffList p * ofCoeffList q) := by
        rw [ofCoeffList_coeffAddSmul, ofCoeffList_zero_cons, ih]
      _ = ofCoeffList (c :: p) * ofCoeffList q := by rw [ofCoeffList_cons, add_mul, mul_assoc]

theorem ofCoeffList_eq_zero (h : ∀ x ∈ l, x = 0) : ofCoeffList l = 0 := by
  induction l with
  | nil => rw [ofCoeffList_nil]
  | cons c l ih =>
    rw [List.forall_mem_cons] at h
    rw [ofCoeffList_cons, h.1, ih h.2, map_zero, mul_zero, add_zero]

public theorem map_ofCoeffList_nil {R : Type*} [Ring R] :
    (ofCoeffList ([] : List ℤ)).map (Int.castRingHom R) = 0 := by
  simp

public theorem map_ofCoeffList_cons {R : Type*} [Ring R] (c : ℤ) (p : List ℤ) :
    (ofCoeffList (c :: p)).map (Int.castRingHom R) =
      (c : R[X]) + X * (ofCoeffList p).map (Int.castRingHom R) := by
  simp [ofCoeffList_cons]

end ofCoeffList

variable {p q : List ℤ} {st : SturmStep} {steps : List SturmStep}

/-- The real polynomial that `p` represents. -/
noncomputable def toReal (p : List ℤ) : ℝ[X] := (ofCoeffList p).map (Int.castRingHom ℝ)

theorem toReal_ne_zero (h : coeffLead p ≠ 0) : toReal p ≠ 0 := by
  simp only [toReal, Polynomial.map_ne_zero_iff, RingHom.injective_int]
  exact ofCoeffList_ne_zero h

theorem natDegree_toReal (h : coeffLead p ≠ 0) : (toReal p).natDegree = p.length - 1 := by
  simp only [toReal, natDegree_map_eq_of_injective, RingHom.injective_int, natDegree_ofCoeffList h]

theorem degree_toReal_lt_degree (hlen : p.length < q.length) (h : coeffLead q ≠ 0) :
    (toReal p).degree < (toReal q).degree := by
  rw [degree_eq_natDegree (toReal_ne_zero h), natDegree_toReal h, degree_lt_iff_coeff_zero]
  intro k hk
  rw [toReal, coeff_map, coeff_ofCoeffList, List.getD_eq_default _ _ (by lia), map_zero]

theorem toReal_coeffDerivative (p : List ℤ) :
    toReal (coeffDerivative p) = derivative (toReal p) := by
  simp only [toReal, derivative_map, ofCoeffList_coeffDerivative]

theorem toReal_coeffAddSmul (c : ℤ) (p q : List ℤ) :
    toReal (coeffAddSmul c p q) = C (c : ℝ) * toReal p + toReal q := by
  simp [toReal, ofCoeffList_coeffAddSmul]

theorem toReal_coeffMul (p q : List ℤ) : toReal (coeffMul p q) = toReal p * toReal q := by
  simp [toReal, ofCoeffList_coeffMul]

theorem SturmStep.check_iff :
    st.check p q = true ↔ 0 < st.a ∧ 0 < st.c ∧ coeffLead q ≠ 0 ∧ st.r.length < q.length ∧
      ∀ x ∈ coeffAddSmul st.c st.r (coeffAddSmul st.a p (coeffMul st.b q)), x = 0 := by
  simp [SturmStep.check, and_assoc]

theorem SturmStep.eq_zero_of_check (h : st.check p q = true) :
    C (st.a : ℝ) * toReal p + toReal st.b * toReal q + C (st.c : ℝ) * toReal st.r = 0 := by
  obtain ⟨_, _, _, _, hz⟩ := SturmStep.check_iff.mp h
  calc C (st.a : ℝ) * toReal p + toReal st.b * toReal q + C (st.c : ℝ) * toReal st.r
    _ = toReal (coeffAddSmul st.c st.r (coeffAddSmul st.a p (coeffMul st.b q))) := by
      rw [toReal_coeffAddSmul, toReal_coeffAddSmul, toReal_coeffMul, add_comm]
    _ = 0 := by rw [toReal, ofCoeffList_eq_zero hz, Polynomial.map_zero]

theorem checkSteps_nil : checkSteps p q [] = true ↔ q = [] := by
  cases q <;> simp [checkSteps]

theorem checkSteps_cons :
    checkSteps p q (st :: steps) = true ↔
      st.check p q = true ∧ checkSteps q st.r steps = true := by
  rw [checkSteps, Bool.and_eq_true]

end Mathlib.Tactic.RealRootCount
