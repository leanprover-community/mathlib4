/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Algebra.Polynomial.Hex.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
Euclidean-algorithm correspondence for `HexPolyMathlib`.

This module transfers the executable `Hex.DensePoly` gcd and extended-gcd
surface across the `HexPolyMathlib.equiv` ring equivalence to Mathlib's
`Polynomial` Euclidean-domain API.
-/

public section

namespace HexPolyMathlib

universe u

variable {R : Type u}

noncomputable section

/-! # Lawfulness of executable division over a field -/

private theorem field_div_cancel [Field R] (a b : R) (hb : b ≠ 0) :
    a - (a / b) * b = 0 := by
  rw [div_mul_cancel₀ a hb, sub_self]

private theorem field_divMod_spec [Field R] [DecidableEq R]
    (p q : Hex.DensePoly R) :
    let qr := Hex.DensePoly.divMod p q
    qr.1 * q + qr.2 = p := by
  by_cases hq : q.size = 0
  · have hrem := Hex.DensePoly.divMod_remainder_eq_self_of_size_zero p q hq
    have hqzero : q = 0 := by
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_zero]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le q (by omega)
    change (Hex.DensePoly.divMod p q).1 * q +
      (Hex.DensePoly.divMod p q).2 = p
    rw [hrem, hqzero, Hex.DensePoly.mul_comm_poly,
      Hex.DensePoly.zero_mul, Hex.DensePoly.zero_add]
  · exact Hex.DensePoly.divMod_reconstruction p q fun a =>
      field_div_cancel a q.leadingCoeff
        (Hex.DensePoly.leadingCoeff_ne_zero_of_pos_size q
          (Nat.pos_of_ne_zero hq))

private theorem field_divMod_remainder_degree_lt [Field R] [DecidableEq R]
    (p q : Hex.DensePoly R) (hdegree : 0 < q.degree?.getD 0) :
    (Hex.DensePoly.divMod p q).2.degree?.getD 0 < q.degree?.getD 0 := by
  apply Hex.DensePoly.divMod_remainder_degree_lt_of_pos_degree_of_cancel p q hdegree
  intro a
  apply field_div_cancel
  apply Hex.DensePoly.leadingCoeff_ne_zero_of_pos_size
  by_cases hq : q.size = 0
  · simp [Hex.DensePoly.degree?, hq] at hdegree
  · exact Nat.pos_of_ne_zero hq

private theorem field_divMod_remainder_eq_zero_of_not_pos_degree
    [Field R] [DecidableEq R] (p q : Hex.DensePoly R)
    (hqfalse : q.isZero = false) (hdegree : ¬ 0 < q.degree?.getD 0) :
    (Hex.DensePoly.divMod p q).2 = 0 := by
  have hqsize_ne : q.size ≠ 0 := by
    intro hsize
    have hzero : q.isZero = true := by
      simpa [Hex.DensePoly.isZero, Hex.DensePoly.size,
        Array.isEmpty_iff_size_eq_zero] using hsize
    rw [hzero] at hqfalse
    contradiction
  have hqsize : q.size = 1 := by
    have hdeg : q.degree?.getD 0 = q.size - 1 := by
      simp [Hex.DensePoly.degree?, hqsize_ne]
    rw [hdeg] at hdegree
    omega
  exact Hex.DensePoly.divMod_remainder_eq_zero_of_degree_zero_of_cancel p q hqsize
    (fun a => field_div_cancel a q.leadingCoeff
      (Hex.DensePoly.leadingCoeff_ne_zero_of_pos_size q (by omega)))

private theorem degree_toPolynomial_remainder_lt [Field R] [DecidableEq R]
    (p q : Hex.DensePoly R) (hq : q ≠ 0) :
    (toPolynomial (Hex.DensePoly.divMod p q).2).degree <
      (toPolynomial q).degree := by
  let r := (Hex.DensePoly.divMod p q).2
  have hqpoly : toPolynomial q ≠ 0 := by
    intro h
    apply hq
    exact (equiv (R := R)).injective (by simpa using h)
  by_cases hpos : 0 < q.degree?.getD 0
  · have hnat : r.degree?.getD 0 < q.degree?.getD 0 := by
      simpa [r] using field_divMod_remainder_degree_lt p q hpos
    change (toPolynomial r).degree < (toPolynomial q).degree
    by_cases hr : r = 0
    · rw [hr, toPolynomial_zero, Polynomial.degree_zero,
        bot_lt_iff_ne_bot, Polynomial.degree_ne_bot]
      exact hqpoly
    · apply Polynomial.degree_lt_degree
      simpa only [natDegree_toPolynomial] using hnat
  · have hqfalse : q.isZero = false := by
      rw [Hex.DensePoly.isZero_eq_false_iff]
      by_contra hsize
      have hsize' : q.size = 0 := by omega
      apply hq
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_zero]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le q (by omega)
    have hr : r = 0 := by
      simpa [r] using
        field_divMod_remainder_eq_zero_of_not_pos_degree p q hqfalse hpos
    change (toPolynomial r).degree < (toPolynomial q).degree
    rw [hr, toPolynomial_zero, Polynomial.degree_zero,
      bot_lt_iff_ne_bot, Polynomial.degree_ne_bot]
    exact hqpoly

/-- Executable dense-polynomial remainder agrees with Mathlib polynomial
remainder over every field. -/
theorem toPolynomial_mod [Field R] [DecidableEq R]
    (p q : Hex.DensePoly R) :
    toPolynomial (p % q) = toPolynomial p % toPolynomial q := by
  by_cases hq : q = 0
  · subst q
    rw [toPolynomial_zero, EuclideanDomain.mod_zero]
    change toPolynomial (Hex.DensePoly.divMod p 0).2 = toPolynomial p
    rw [Hex.DensePoly.divMod_remainder_eq_self_of_size_zero]
    rfl
  · let qr := Hex.DensePoly.divMod p q
    let qp := toPolynomial q
    let lc := qp.leadingCoeff
    let monicQ := qp * Polynomial.C lc⁻¹
    have hqp : qp ≠ 0 := by
      intro h
      apply hq
      exact (equiv (R := R)).injective (by simpa [qp] using h)
    have hlc : lc ≠ 0 := by
      simpa [lc] using Polynomial.leadingCoeff_ne_zero.mpr hqp
    have hmonic : monicQ.Monic := by
      simpa [monicQ, lc] using Polynomial.monic_mul_leadingCoeff_inv hqp
    have hreconstruct :
        toPolynomial qr.2 + monicQ *
            (Polynomial.C lc * toPolynomial qr.1) = toPolynomial p := by
      have hraw := congrArg toPolynomial (field_divMod_spec p q)
      simp only [toPolynomial_add, toPolynomial_mul] at hraw
      dsimp [qr] at hraw ⊢
      calc
        toPolynomial (Hex.DensePoly.divMod p q).2 +
            monicQ * (Polynomial.C lc *
              toPolynomial (Hex.DensePoly.divMod p q).1) =
            toPolynomial (Hex.DensePoly.divMod p q).2 +
              toPolynomial q *
                toPolynomial (Hex.DensePoly.divMod p q).1 := by
                  dsimp [monicQ, qp, lc]
                  have hc :
                      Polynomial.C (toPolynomial q).leadingCoeff⁻¹ *
                          Polynomial.C (toPolynomial q).leadingCoeff = 1 := by
                    rw [← Polynomial.C_mul, inv_mul_cancel₀ hlc,
                      Polynomial.C_1]
                  rw [mul_assoc, ← mul_assoc
                    (Polynomial.C (toPolynomial q).leadingCoeff⁻¹), hc,
                    one_mul]
        _ = toPolynomial p := by rw [add_comm, mul_comm]; exact hraw
    have hdegree : (toPolynomial qr.2).degree < monicQ.degree := by
      rw [show monicQ.degree = qp.degree by
        exact Polynomial.degree_mul_leadingCoeff_inv qp hqp]
      simpa [qp, qr] using degree_toPolynomial_remainder_lt p q hq
    have hunique := Polynomial.div_modByMonic_unique
      (Polynomial.C lc * toPolynomial qr.1) (toPolynomial qr.2)
      hmonic ⟨hreconstruct, hdegree⟩
    change toPolynomial qr.2 = toPolynomial p % qp
    rw [Polynomial.mod_def]
    simpa [monicQ] using hunique.2.symm

private theorem polynomial_mod_mod [Field R] (p q : Polynomial R) :
    (p % q) % q = p % q := by
  by_cases hq : q = 0
  · simp [hq]
  · apply (Polynomial.mod_eq_self_iff hq).2
    exact Polynomial.degree_mod_lt p hq

/-- The executable long-division laws are valid over every Mathlib field. The
low priority lets coefficient libraries retain specialized proof packages
without creating an instance-selection preference cycle. -/
instance (priority := 50) instDivModLawsField [Field R] [DecidableEq R] :
    Hex.DensePoly.DivModLaws R where
  divMod_spec := field_divMod_spec
  divMod_remainder_degree_lt_of_pos_degree := field_divMod_remainder_degree_lt
  divModMonic_eq_divMod_of_monic := by
    intro p q hmonic
    by_cases hlt : p.degree?.getD 0 < q.degree?.getD 0
    · rw [Hex.DensePoly.divMod_eq_zero_self_of_degree_lt p q hlt]
      unfold Hex.DensePoly.divModMonic
      exact Hex.DensePoly.divModArray_eq_zero_self_of_degree_lt p q id hlt
    · apply Hex.DensePoly.divModMonic_eq_divMod_of_monic_of_scale p q hmonic hlt
      intro a
      rw [hmonic]
      simp
  mod_self_eq_zero := by
    intro p
    apply (equiv (R := R)).injective
    change toPolynomial (p % p) = toPolynomial 0
    rw [toPolynomial_zero, toPolynomial_mod]
    exact EuclideanDomain.mod_self (toPolynomial p)
  mod_eq_zero_of_dvd := by
    intro p q hdiv
    apply (equiv (R := R)).injective
    change toPolynomial (p % q) = toPolynomial 0
    rw [toPolynomial_zero, toPolynomial_mod]
    exact EuclideanDomain.mod_eq_zero.mpr (toPolynomial_dvd hdiv)
  mod_mod_of_not_pos_degree := by
    intro p q _
    apply (equiv (R := R)).injective
    change toPolynomial ((p % q) % q) = toPolynomial (p % q)
    simpa only [toPolynomial_mod] using
      polynomial_mod_mod (toPolynomial p) (toPolynomial q)
  mod_eq_mod_of_congr := by
    intro p q m hcongr
    apply (equiv (R := R)).injective
    change toPolynomial (p % m) = toPolynomial (q % m)
    rw [toPolynomial_mod, toPolynomial_mod]
    have hdiv : toPolynomial m ∣ toPolynomial p - toPolynomial q := by
      simpa using toPolynomial_dvd hcongr
    have hzero :
        (toPolynomial p - toPolynomial q) % toPolynomial m = 0 :=
      EuclideanDomain.mod_eq_zero.mpr hdiv
    rw [Polynomial.sub_mod] at hzero
    exact sub_eq_zero.mp hzero
  mod_add_mod := by
    intro p q m
    apply (equiv (R := R)).injective
    change toPolynomial ((p + q) % m) =
      toPolynomial (((p % m) + (q % m)) % m)
    simp only [toPolynomial_mod, toPolynomial_add]
    simpa only [Polynomial.add_mod] using
      (polynomial_mod_mod
        (toPolynomial p + toPolynomial q) (toPolynomial m)).symm
  mod_mul_mod := by
    intro p q m
    apply (equiv (R := R)).injective
    change toPolynomial ((p * q) % m) =
      toPolynomial (((p % m) * (q % m)) % m)
    simp only [toPolynomial_mod, toPolynomial_mul]
    exact Polynomial.mul_mod (toPolynomial p) (toPolynomial q) (toPolynomial m)

/-- Executable dense-polynomial gcd and xgcd laws over every Mathlib field. -/
instance (priority := 50) instGcdLawsField [Field R] [DecidableEq R] :
    Hex.DensePoly.GcdLaws R where
  gcd_dvd_left := by
    intro p q
    exact Hex.DensePoly.gcd_dvd_left_of_divModLaws
      field_divMod_remainder_eq_zero_of_not_pos_degree p q
  gcd_dvd_right := by
    intro p q
    exact Hex.DensePoly.gcd_dvd_right_of_divModLaws
      field_divMod_remainder_eq_zero_of_not_pos_degree p q
  dvd_gcd := Hex.DensePoly.dvd_gcd_of_divModLaws
  xgcd_bezout := Hex.DensePoly.xgcd_bezout_of_divModLaws

private theorem toPolynomial_dvd_of_dense_dvd [CommSemiring R] [DecidableEq R]
    {p q : Hex.DensePoly R} :
    p ∣ q → toPolynomial p ∣ toPolynomial q := by
  intro hpq
  rcases hpq with ⟨r, rfl⟩
  exact ⟨toPolynomial r, by simp⟩

private theorem dense_dvd_of_toPolynomial_dvd [CommRing R] [DecidableEq R]
    {p : Hex.DensePoly R} {q : Polynomial R} :
    q ∣ toPolynomial p → ofPolynomial q ∣ p := by
  intro hqp
  rcases hqp with ⟨r, hr⟩
  refine ⟨ofPolynomial r, ?_⟩
  calc
    p = ofPolynomial (toPolynomial p) := (ofPolynomial_toPolynomial p).symm
    _ = ofPolynomial (q * r) := by rw [hr]
    _ = ofPolynomial q * ofPolynomial r := by simp

private theorem toPolynomial_dvd_of_dense_ofPolynomial_dvd [CommRing R] [DecidableEq R]
    {p : Hex.DensePoly R} {q : Polynomial R} :
    ofPolynomial q ∣ p → q ∣ toPolynomial p := by
  intro hqp
  rcases hqp with ⟨r, hr⟩
  refine ⟨toPolynomial r, ?_⟩
  calc
    toPolynomial p = toPolynomial (ofPolynomial q * r) := by rw [hr]
    _ = q * toPolynomial r := by simp

/--
The raw executable dense-polynomial gcd is associated to Mathlib's normalized
polynomial gcd under `toPolynomial`. It is not generally equal before normalization:
`Hex.DensePoly.gcd` returns the last Euclidean remainder, while
`EuclideanDomain.gcd` for polynomials over a field is normalized.
-/
theorem toPolynomial_gcd_associated [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    Associated (toPolynomial (Hex.DensePoly.gcd p q))
      (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) := by
  apply associated_of_dvd_dvd
  · apply EuclideanDomain.dvd_gcd
    · exact toPolynomial_dvd_of_dense_dvd (Hex.DensePoly.gcd_dvd_left p q)
    · exact toPolynomial_dvd_of_dense_dvd (Hex.DensePoly.gcd_dvd_right p q)
  · apply toPolynomial_dvd_of_dense_ofPolynomial_dvd
    apply Hex.DensePoly.dvd_gcd
    · exact dense_dvd_of_toPolynomial_dvd
        (EuclideanDomain.gcd_dvd_left (toPolynomial p) (toPolynomial q))
    · exact dense_dvd_of_toPolynomial_dvd
        (EuclideanDomain.gcd_dvd_right (toPolynomial p) (toPolynomial q))

/--
The raw gcd component of `Hex.DensePoly.xgcd` is associated to Mathlib's
normalized polynomial gcd. This is the xgcd-facing form of
`toPolynomial_gcd_associated`, not a literal equality of raw outputs.
-/
theorem toPolynomial_xgcd_gcd_associated [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    Associated (toPolynomial (Hex.DensePoly.xgcd p q).gcd)
      (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) := by
  simpa [Hex.DensePoly.xgcd_gcd_eq_gcd] using toPolynomial_gcd_associated (R := R) p q

/--
The executable Bezout identity transports across `toPolynomial`.
The right hand side is the executable raw gcd component, not Mathlib's
normalized polynomial gcd. The `@[simp]` direction collapses the transported
Bezout combination to the named raw gcd; the matching pattern only fires when
the goal mentions `Hex.DensePoly.xgcd p q` literally with both coefficient
projections, so the rule is narrow.
-/
@[simp, grind =]
theorem toPolynomial_xgcd_bezout_raw [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    toPolynomial (Hex.DensePoly.xgcd p q).left * toPolynomial p +
      toPolynomial (Hex.DensePoly.xgcd p q).right * toPolynomial q =
        toPolynomial (Hex.DensePoly.xgcd p q).gcd := by
  let r := Hex.DensePoly.xgcd p q
  have h : r.left * p + r.right * q = r.gcd := by
    simpa [r] using Hex.DensePoly.xgcd_bezout p q
  have ht := congrArg (fun x => toPolynomial x) h
  simpa [r] using ht

/--
The transported executable Bezout combination is associated to Mathlib's
normalized polynomial gcd. This is the normalization-aware xgcd correspondence
surface: executable coefficients certify the raw gcd, whose transport is
associated to Mathlib's canonical gcd.
-/
theorem toPolynomial_xgcd_bezout_associated [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    Associated
      (toPolynomial (Hex.DensePoly.xgcd p q).left * toPolynomial p +
        toPolynomial (Hex.DensePoly.xgcd p q).right * toPolynomial q)
      (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) := by
  rw [toPolynomial_xgcd_bezout_raw (R := R) p q]
  exact toPolynomial_xgcd_gcd_associated (R := R) p q

/--
The ring equivalence sends the executable raw gcd to a polynomial associated to
Mathlib's normalized gcd. Use this theorem when the caller only needs the
gcd universal property; do not assume raw executable gcd outputs are normalized.
-/
theorem equiv_gcd_associated [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    Associated (equiv (Hex.DensePoly.gcd p q)) (EuclideanDomain.gcd (equiv p) (equiv q)) := by
  simpa using toPolynomial_gcd_associated (R := R) p q

/-- The ring equivalence transports the executable raw Bezout identity. -/
theorem equiv_xgcd_bezout_raw [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    equiv (Hex.DensePoly.xgcd p q).left * equiv p +
      equiv (Hex.DensePoly.xgcd p q).right * equiv q =
        equiv (Hex.DensePoly.xgcd p q).gcd := by
  simp

/--
The ring-equivalence form of the normalization-aware xgcd correspondence:
the executable Bezout combination is associated to Mathlib's normalized gcd.
-/
theorem equiv_xgcd_bezout_associated [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    Associated
      (equiv (Hex.DensePoly.xgcd p q).left * equiv p +
        equiv (Hex.DensePoly.xgcd p q).right * equiv q)
      (EuclideanDomain.gcd (equiv p) (equiv q)) := by
  simpa using toPolynomial_xgcd_bezout_associated (R := R) p q

end

end HexPolyMathlib
