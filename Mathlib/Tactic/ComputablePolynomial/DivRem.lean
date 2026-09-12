/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.Content

/-!
# `SparsePoly`: division with remainder and the equivalence with `Polynomial`

`divRem` (long division by leading-term cancellation, with the degree-decrease lemma
`degree_sub_leading_term_lt` justifying termination), its specification `divRem_spec`
(`a = b * q + r`), and finally `toPolyEquiv : SparsePoly R ≃ₐ[R] Polynomial R`, packaging the
semantics map as an `R`-algebra equivalence.
-/

@[expose] public section

namespace SparsePoly

open Polynomial

variable {R : Type} [CommRing R] [DecidableEq R]

lemma degree_sub_leading_term_lt [Div R]
    (P Q : SparsePoly R) {i j : ℕ} {x y : R} {as bs : List (ℕ × R)}
    (ha : P.coeffs = (i, x) :: as)
    (hb : Q.coeffs = (j, y) :: bs)
    (h_deg : j ≤ i) (h_div : y * (x / y) = x) (h_pos : 0 < i) :
    degree (P - ((x / y) • X^(i - j)) * Q) < i := by
  by_cases h_empty : (P - ((x / y) • X^(i - j)) * Q).coeffs = []
  · unfold degree
    rw [h_empty]
    grind
  rw [degree_eq_poly_degree _ h_empty]
  by_contra h_ge
  push Not at h_ge
  have h_coeff_zero : ∀ k ≥ i, (toPoly (P - ((x / y) • X^(i - j)) * Q)).coeff k = 0 := by
    intro k hk
    rw [sub_eq_add_neg, toPoly_add, toPoly_neg, toPoly_mul, toPoly_smul_X_pow]
    simp only [Polynomial.coeff_add, Polynomial.coeff_neg]
    have hP_deg : P.degree = i := by simp [degree, ha]
    have hQ_deg : Q.degree = j := by simp [degree, hb]
    have hP_nz : P.coeffs ≠ [] := by rw [ha]; grind
    have hQ_nz : Q.coeffs ≠ [] := by rw [hb]; grind
    rcases eq_or_lt_of_le hk with rfl | h_gt
    · have hP_lead : (toPoly P).coeff i = x := by
        simp only [toPoly, ha]
        unfold toPolyCore
        have h_tail_zero : (toPolyCore as).coeff i = 0 :=
          coeff_toPolyCore_eq_zero_of_forall_lt _ _ fun p hp => by
            have hs := P.sorted; rw [ha] at hs; exact List.rel_of_pairwise_cons hs hp
        simp [h_tail_zero]
      have hQ_lead : (Polynomial.C (x / y) * Polynomial.X ^ (i - j) * toPoly Q).coeff i = x := by
        rw [show Polynomial.C (x / y) * Polynomial.X ^ (i - j) * toPoly Q =
              (Polynomial.C (x / y) * toPoly Q) * Polynomial.X ^ (i - j) by ring]
        have h_coeff_mul_X_pow :
            (Polynomial.C (x / y) * toPoly Q * Polynomial.X ^ (i - j)).coeff i =
              (Polynomial.C (x / y) * toPoly Q).coeff j := by
          calc (Polynomial.C (x / y) * toPoly Q * Polynomial.X ^ (i - j)).coeff i
              = (Polynomial.C (x / y) * toPoly Q * Polynomial.X ^ (i - j)).coeff (j + (i - j)) := by
                simp [(by omega : j + (i - j) = i)]
            _ = (Polynomial.C (x / y) * toPoly Q).coeff j := by simp
        rw [h_coeff_mul_X_pow]
        have hQ_j : (toPoly Q).coeff j = y := by
          simp only [toPoly, hb]
          unfold toPolyCore
          have h_tail_zero : (toPolyCore bs).coeff j = 0 :=
            coeff_toPolyCore_eq_zero_of_forall_lt _ _ fun p hp => by
              have hs := Q.sorted; rw [hb] at hs; exact List.rel_of_pairwise_cons hs hp
          simp [h_tail_zero]
        grind
      grind
    · have hP_zero : (toPoly P).coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (by rw [← degree_eq_poly_degree P hP_nz, hP_deg]; exact h_gt)
      have hQ_zero : (Polynomial.C (x / y) * Polynomial.X ^ (i - j) * toPoly Q).coeff k = 0 := by
        rw [show Polynomial.C (x / y) * Polynomial.X ^ (i - j) * toPoly Q =
              (Polynomial.C (x / y) * toPoly Q) * Polynomial.X ^ (i - j) by ring,
          ← (by omega : (k - (i - j)) + (i - j) = k),
          Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul]
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (by rw [← degree_eq_poly_degree Q hQ_nz, hQ_deg]; omega), mul_zero]
      rw [hP_zero, hQ_zero, neg_zero, add_zero]
  have h_poly_zero : toPoly (P - ((x / y) • X^(i - j)) * Q) = 0 :=
    Polynomial.leadingCoeff_eq_zero.mp (h_coeff_zero _ h_ge)
  rw [show (toPoly (P - ((x / y) • X^(i - j)) * Q)).natDegree = 0 by
    rw [h_poly_zero, Polynomial.natDegree_zero]] at h_ge
  exact (not_lt_of_ge h_ge h_pos).elim

/-- Polynomial division with remainder: returns a quotient/remainder pair `(q, r)` with
`b * q + r = a`, using `IsExactDiv`-style division of leading coefficients (bailing out with
quotient `0` when the leading coefficient does not divide exactly). -/
def divRem [Div R] (a b : SparsePoly R) : SparsePoly R × SparsePoly R :=
  match _ha : a.coeffs, _hb : b.coeffs with
  | (i, x) :: _as, (j, y) :: _bs =>
    if _h_lt : i < j then
      (0, a)
    else
      if h_pos : i = 0 then
        let c := (x / y) • X^0
        if y * (x / y) = x then
          (c, a - c * b)
        else
          (0, a)
      else
        let c := (x / y) • X^(i - j)
        if _h_div : y * (x / y) = x then
          let (q', r') := divRem (a - ((x / y) • X^(i - j)) * b) b
          (q' + c, r')
        else
          (0, a)
  | _, _ => (0, a)
termination_by if a.coeffs = [] then 0 else a.degree + 1
decreasing_by
  simp_wf
  have hj_le_i : j ≤ i := by omega
  have h_pos_i : 0 < i := by omega
  have ha_not_empty : a.coeffs ≠ [] := by rw [_ha]; simp
  have h_deg : a.degree = i := by unfold degree; rw [_ha]; rfl
  rw [if_neg ha_not_empty, h_deg]
  by_cases h_empty : (a - ((x / y) • X^(i - j)) * b).coeffs = []
  · aesop
  · have h_lt_i := degree_sub_leading_term_lt a b _ha _hb hj_le_i _h_div h_pos_i
    aesop

instance [Div R] : Div (SparsePoly R) where
  div a b := (divRem a b).1

/-- Unfolding lemma to safely evaluate divRem without projection motive errors -/
lemma divRem_eq [Div R] (a b : SparsePoly R) :
    divRem a b =
      match _ha : a.coeffs, _hb : b.coeffs with
      | (i, x) :: _as, (j, y) :: _bs =>
        if _h_lt : i < j then
          (0, a)
        else
          if _h_pos : i = 0 then
            let c := (x / y) • X^0
            if y * (x / y) = x then
              (c, a - c * b)
            else
              (0, a)
          else
            let c := (x / y) • X^(i - j)
            if _h_div : y * (x / y) = x then
              let (q', r') := divRem (a - ((x / y) • X^(i - j)) * b) b
              (q' + c, r')
            else
              (0, a)
      | _, _ => (0, a) := by
  rw [divRem]

lemma divRem_spec [Div R] (a b : SparsePoly R) :
    b * (divRem a b).1 + (divRem a b).2 = a := by
  induction a using divRem.induct
  case b => exact b
  case case1 a i x as j y bs ha hb h_lt =>
    rw [divRem_eq, ha, hb]
    simp [h_lt]
  case case2 a i x as j y bs ha hb h_nlt h_pos h_div =>
    rw [divRem_eq, hb]
    simp
    aesop
  case case3 a i x as j y bs ha hb h_nlt h_pos h_ndiv =>
    rw [divRem_eq, hb]
    simp
    grind
  case case4 a i x as j y bs ha hb h_nlt h_npos h_div q' r' heq ih =>
    rw [divRem_eq, ha, hb]
    simp only [h_nlt, ↓reduceDIte, h_npos, h_div, Algebra.smul_mul_assoc]
    rw [show ∀ (q r c : SparsePoly R),
      b * (q + c) + r = (b * q + r) + b * c from fun _ _ _ => by grind]
    simp_all only [not_lt, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    grind
  case case5 a i x as j y bs ha hb h_nlt h_npos h_ndiv =>
    rw [divRem_eq, ha, hb]
    simp [h_nlt, h_npos, h_ndiv]
  case case6 =>
    rw [divRem_eq]
    split <;> grind

/-- Degree of multiplication. Requires `[IsDomain R]` so zero-divisors don't wipe out the leading
term. -/
lemma degree_mul [IsDomain R] (a b : SparsePoly R)
    (ha : a.coeffs ≠ []) (hb : b.coeffs ≠ []) : (a * b).degree = a.degree + b.degree := by
  rw [degree_eq_natDegree_toPoly (a * b), degree_eq_natDegree_toPoly a,
    degree_eq_natDegree_toPoly b, toPoly_mul]
  have h_ne : ∀ {c : SparsePoly R}, c.coeffs ≠ [] → toPoly c ≠ 0 := fun {c} hc h =>
    hc (by rw [toPoly_injective (h.trans toPoly_zero.symm)]; rfl)
  exact Polynomial.natDegree_mul (h_ne ha) (h_ne hb)

instance : DecidableEq (SparsePoly R) := fun a b =>
  decidable_of_iff' (a.coeffs = b.coeffs) (SparsePoly.ext_iff ..)

/-- Bridge: powers of `X` translate correctly. -/
theorem toPoly_pow (n : ℕ) : toPoly ((X : SparsePoly R)^n) = Polynomial.X^n := by
  induction n with
  | zero => simp [toPoly_one]
  | succ n ih => simp [pow_succ, toPoly_mul, toPoly_X, ih]

lemma toPoly_ofPoly (p : Polynomial R) :
    toPoly (p.eval₂ (algebraMap R (SparsePoly R)) X) = p := by
  induction p using Polynomial.induction_on with
  | C r =>
    simp only [eval₂_C]
    exact toPoly_C (R := R) r
  | add =>
    simp only [eval₂_add, toPoly_add]
    grind
  | monomial n r ih =>
    simp only [eval₂_mul, eval₂_C, eval₂_X_pow, toPoly_mul, toPoly_pow]
    rw [← toPoly_C]
    rfl

/-- The `R`-algebra isomorphism between the computable `SparsePoly R` and Mathlib's
`Polynomial R`, given by `toPoly` with inverse `eval₂ (algebraMap R _) X`. -/
noncomputable def toPolyEquiv : SparsePoly R ≃ₐ[R] Polynomial R where
  toFun := toPoly
  invFun p := p.eval₂ (algebraMap R (SparsePoly R)) X
  right_inv p := toPoly_ofPoly p
  left_inv p := by
    apply toPoly_injective
    rw [toPoly_ofPoly]
  map_add' := toPoly_add
  map_mul' := toPoly_mul
  commutes' r := toPoly_C r

@[simp]
theorem ofPoly_X : toPolyEquiv.symm Polynomial.X = (X : SparsePoly R) := by
  simp [toPolyEquiv]

end SparsePoly
