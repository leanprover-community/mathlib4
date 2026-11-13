/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.Sturm.SturmTarski
public import Mathlib.Tactic.RealRootCount.SturmCertificate

import Mathlib.Data.List.GetD
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# `realRootCount?` computes the number of real roots of a polynomial

This file proves that when `realRootCount?` on `Mathlib.Tactic.RealRootCount.SturmCertificate`
computes a number, it is equal to the number of distinct real roots of the input polynomial.

## Main results

- `card_rootSet_of_realRootCount?`: If `realRootCount? d = some n` and `d` is a `SturmCertificate`
  of a polynomial `f` then `f` has `n` distinct roots.
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

variable {p q : List ℤ} {st : SturmStep} {steps : List SturmStep} {L : List (List ℤ)}

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

theorem sturmEntries?_nil : sturmEntries? p q [] = some L ↔ q = [] ∧ [p] = L := by
  cases q <;> simp [sturmEntries?]

theorem sturmEntries?_cons :
    sturmEntries? p q (st :: steps) = some L ↔
      st.check p q = true ∧ ∃ L', sturmEntries? q st.r steps = some L' ∧ p :: L' = L := by
  simp [sturmEntries?]

theorem exists_pos_eq_C_mul_neg_mod {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a c x y : K} {b u v r : K[X]} (ha : 0 < a) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y)
    (h : C a * (C x * u) + b * (C y * v) + C c * r = 0) (hdeg : r.degree < (C y * v).degree) :
    ∃ z > 0, r = C z * (-u % v) := by
  rw [degree_C_mul hy.ne', ← degree_C_mul hc.ne'] at hdeg
  have key : C c * r = C (a * x) * (-u % v) :=
    calc C c * r
      _ = (b * C y * v + C c * r) % v := (mul_add_mod_of_degree_lt hdeg).symm
      _ = (C (a * x) * -u) % v := by
        congrm ?_ % v
        rw [C_mul]
        linear_combination h
      _ = C (a * x) * (-u % v) := C_mul_mod ..
  refine ⟨c⁻¹ * (a * x), by positivity, mul_left_cancel₀ (C_ne_zero.mpr hc.ne') ?_⟩
  rw [key, ← mul_assoc, ← C_mul, mul_inv_cancel_left₀ hc.ne']

/-- `L` is the Sturm sequence of `u` and `v` up to positive constant factors. -/
def IsScaledSturmSeq (u v : ℝ[X]) (L : List ℝ[X]) : Prop :=
  List.Forall₂ (fun s t => ∃ c > 0, t = C c * s) (sturmSeq u v) L

theorem isScaledSturmSeq_of_sturmEntries? {u v : ℝ[X]} {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hp : toReal p = C x * u) (hq : toReal q = C y * v) (hu : u ≠ 0)
    (h : sturmEntries? p q steps = some L) :
    IsScaledSturmSeq u v (L.map toReal) := by
  unfold IsScaledSturmSeq
  induction steps generalizing p q u v x y L with
  | nil =>
    obtain ⟨rfl, rfl⟩ := sturmEntries?_nil.mp h
    obtain rfl : v = 0 := by simpa [toReal, hy.ne'] using hq.symm
    rw [sturmSeq_cons hu, sturmSeq_zero_left]
    exact .cons ⟨x, hx, hp⟩ .nil
  | cons st steps ih =>
    obtain ⟨hstep, L, hsteps, rfl⟩ := sturmEntries?_cons.mp h
    obtain ⟨ha, hc, hlead, hlen, _⟩ := SturmStep.check_iff.mp hstep
    obtain ⟨z, hz, hr⟩ : ∃ z > 0, toReal st.r = C z * (-u % v) := by
      apply exists_pos_eq_C_mul_neg_mod (Int.cast_pos.mpr ha) (Int.cast_pos.mpr hc) hx hy
      · simpa only [hp, hq] using SturmStep.eq_zero_of_check hstep
      · simpa only [hq] using degree_toReal_lt_degree hlen hlead
    rw [List.map_cons, sturmSeq_cons hu]
    have hv := toReal_ne_zero hlead
    rw [hq] at hv
    exact .cons ⟨x, hx, hp⟩ (ih hy hz hq hr (right_ne_zero_of_mul hv) hsteps)

theorem SturmCertificate.entries?_eq_some_iff {d : SturmCertificate} :
    d.entries? = some L ↔
      coeffLead d.s ≠ 0 ∧ sturmEntries? d.s (coeffDerivative d.s) d.steps = some L := by
  simp [SturmCertificate.entries?]

theorem isScaledSturmSeq_of_entries? {d : SturmCertificate} (h : d.entries? = some L) :
    IsScaledSturmSeq (toReal d.s) (derivative (toReal d.s)) (L.map toReal) := by
  obtain ⟨hlead, hsteps⟩ := SturmCertificate.entries?_eq_some_iff.mp h
  refine isScaledSturmSeq_of_sturmEntries? one_pos one_pos ?_ ?_ (toReal_ne_zero hlead) hsteps
  · simp
  · simp [toReal_coeffDerivative]

public theorem card_rootSet_of_realRootCount? {R : Type*} [CommRing R] [Algebra R ℝ] {f : R[X]}
    {d : SturmCertificate} {k n : ℕ} [Fintype (f.rootSet ℝ)]
    (hf : (k : R[X]) * f = (ofCoeffList d.s).map (Int.castRingHom R))
    (h : realRootCount? d = some n) :
    Fintype.card (f.rootSet ℝ) = n := by
  sorry

theorem eval_toReal_cons (c : ℤ) (p : List ℤ) (x : ℝ) :
    (toReal (c :: p)).eval x = c + x * (toReal p).eval x := by
  simp [toReal, map_ofCoeffList_cons]

theorem cast_evalScaled (n : ℤ) (d : ℕ) (p : List ℤ) {x : ℝ} (hx : d * x = n) :
    (d : ℝ) * evalScaled n d p = d ^ p.length * (toReal p).eval x := by
  induction p with
  | nil => simp [evalScaled, toReal]
  | cons c p ih =>
    rw [evalScaled, eval_toReal_cons, List.length_cons]
    push_cast
    calc (d : ℝ) * (c * d ^ p.length + n * evalScaled n d p)
      _ = c * d ^ (p.length + 1) + n * (d * evalScaled n d p) := by ring
      _ = c * d ^ (p.length + 1) + d * x * (d ^ p.length * (toReal p).eval x) := by rw [ih, hx]
      _ = d ^ (p.length + 1) * (c + x * (toReal p).eval x) := by ring

theorem sign_evalScaled (n : ℤ) {d : ℕ} (hd : 0 < d) (p : List ℤ) :
    sign (evalScaled n d p) = sign ((toReal p).eval ((n : ℝ) / d)) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  calc sign (evalScaled n d p)
    _ = sign ((d : ℝ) * evalScaled n d p) := by simp [sign_mul, sign_pos hd']
    _ = sign ((d : ℝ) ^ p.length * (toReal p).eval ((n : ℝ) / d)) := by
      rw [cast_evalScaled n d p (mul_div_cancel₀ _ hd'.ne')]
    _ = sign ((toReal p).eval ((n : ℝ) / d)) := by simp [sign_mul, sign_pow, sign_pos hd']

theorem signVariations_map_evalScaled (n : ℤ) {d : ℕ} (hd : 0 < d) (L : List (List ℤ)) :
    (L.map (evalScaled n d)).signVariations =
      ((L.map toReal).map (sign ∘ eval ((n : ℝ) / d))).signVariations := by
  rw [← List.signVariations_map_sign, List.map_map, List.map_map]
  congrm List.signVariations ?_
  exact List.map_congr_left fun e _ => sign_evalScaled n hd e

end Mathlib.Tactic.RealRootCount
