/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.Degree
public import Mathlib.Algebra.GCDMonoid.Basic

/-!
# `SparsePoly`: gcd, content and primitive part

A subresultant-style division-free `gcdPrim`, the `content` (gcd of the coefficients over a
`GCDMonoid`), the `primitivePart`, and the resulting `gcd`. Also the `coeff` function and its
agreement with `Polynomial.coeff` under `toPoly`, and scalar-multiplication lemmas.
-/

@[expose] public section

namespace SparsePoly

open Polynomial

variable {R : Type} [CommRing R] [DecidableEq R]

/-- A subresultant-style GCD of two polynomials that avoids division: it repeatedly cancels leading
terms via cross-multiplication (`y • a - x • X^(i-j) * b`), producing a GCD up to a scalar/content
factor. -/
def gcdPrim (a b : SparsePoly R) : SparsePoly R :=
  match _ha : a.coeffs with
  | [] => b
  | (i, x) :: _as =>
    match hb : b.coeffs with
    | [] => a
    | (j, y) :: bs =>
      if h_const : i = 0 ∧ j = 0 then
        a
      else if h_gt : i > j then
        gcdPrim (y • a - x • X^(i-j) * b) b
      else
        gcdPrim a (x • b - y • X^(j-i) * a)
termination_by a.degree + b.degree
decreasing_by
  · simp_wf
    have h_drop := deg_pseudo_rem_a a b i j x y _as bs _ha hb h_gt
    aesop
  · simp_wf
    have hj_pos : 0 < j := by omega
    have h_drop := deg_pseudo_rem_b a b i j x y _as bs _ha hb h_gt hj_pos
    aesop

omit [DecidableEq R] in
lemma foldl_gcd_dvd_acc [GCDMonoid R] (l : List (ℕ × R)) (acc : R) :
    l.foldl (fun a x => gcd a x.2) acc ∣ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact (ih (gcd acc hd.2)).trans (gcd_dvd_left _ _)

omit [DecidableEq R] in
lemma foldl_gcd_dvd_mem [GCDMonoid R] {l : List (ℕ × R)} {i : ℕ} {c : R}
    (h : (i, c) ∈ l) (acc : R) : l.foldl (fun a x => gcd a x.2) acc ∣ c := by
  induction l generalizing acc with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons] at h ⊢
    rcases h with rfl | h_mem
    · exact (foldl_gcd_dvd_acc tl (gcd acc c)).trans (gcd_dvd_right _ _)
    · exact ih h_mem (gcd acc hd.2)

omit [DecidableEq R] in
lemma content_dvd_coeff_final [GCDMonoid R] {l : List (ℕ × R)} {i : ℕ} {c : R}
    (h : (i, c) ∈ l) : l.foldl (init := 0) (fun acc x => gcd acc x.2) ∣ c :=
  foldl_gcd_dvd_mem h 0

/-- The content of a polynomial: the `gcd` of all its coefficients. -/
def content [GCDMonoid R] (a : SparsePoly R) : R :=
  a.coeffs.foldl (init := 0) (gcd · ·.2)

/-- The primitive part of a polynomial: the result of dividing every coefficient by the content,
yielding a polynomial whose coefficients have `gcd` a unit. -/
def primitivePart [GCDMonoid R]
    [Div R] [IsExactDiv R] (a : SparsePoly R) : SparsePoly R where
  coeffs :=
    let b := a.content
    a.coeffs.map fun (i, a) => (i, a / b)
  sorted := by
    have h_sorted := a.sorted
    grind
  nonzero := by
    intro x hx
    simp only [List.mem_map, Prod.exists] at hx
    rcases hx with ⟨i, c, h_mem, rfl⟩
    have hc_nz := a.nonzero (i, c) h_mem
    let b := a.content
    intro h_div_zero
    have h_mul := congr_arg (fun (z : R) => b * z) h_div_zero
    simp only [mul_zero] at h_mul
    have h_dvd : b ∣ c := content_dvd_coeff_final h_mem
    rw [IsExactDiv.mul_div_cancel h_dvd] at h_mul
    exact hc_nz h_mul

/-- The GCD of two polynomials: the GCD of their contents times the primitive part of the
division-free `gcdPrim`. -/
nonrec def gcd [GCDMonoid R]
    [Div R] [IsExactDiv R] (a b : SparsePoly R) : SparsePoly R :=
  gcd a.content b.content • (gcdPrim a b).primitivePart

instance : IsExactDiv ℤ where
  mul_div_cancel := Int.mul_ediv_cancel'

instance {R} [CommGroupWithZero R] : IsExactDiv R where
  mul_div_cancel h := by
    apply mul_div_cancel_of_imp'; rintro rfl
    simpa only [zero_dvd_iff] using h


omit [DecidableEq R] in
/-- Helper: If all elements in the list have exponents strictly
  less than k, the coefficient at k is 0. -/
lemma coeff_toPolyCore_eq_zero_of_forall_lt (l : List (ℕ × R)) (k : ℕ)
    (h : ∀ p ∈ l, p.1 < k) : (toPolyCore l).coeff k = 0 := by
  induction l with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    rcases hd with ⟨j, y⟩
    have h_k_ne_j : k ≠ j := (by aesop : j < k).ne'
    have h_tail_zero : (toPolyCore tl).coeff k = 0 := by
      apply ih
      intro p hp
      exact h _ (by simp [hp])
    unfold toPolyCore
    simp [h_k_ne_j, h_tail_zero]

omit [DecidableEq R] in
lemma degree_eq_poly_degree (a : SparsePoly R) (h : a.coeffs ≠ []) :
    a.degree = (toPoly a).natDegree := by
  rcases h_coeffs : a.coeffs with _ | ⟨⟨i, x⟩, as⟩
  · contradiction
  have h_deg : a.degree = i := by simp [degree, h_coeffs]
  rw [h_deg]
  have h_as_lt : ∀ p ∈ as, p.1 < i := by
    intro p hp
    have h_sorted := a.sorted
    rw [h_coeffs] at h_sorted
    exact List.rel_of_pairwise_cons h_sorted hp
  have h_coeff_i : (toPoly a).coeff i = x := by
    simp only [toPoly, h_coeffs]
    unfold toPolyCore
    have h_tail_zero : (toPolyCore as).coeff i = 0 :=
      coeff_toPolyCore_eq_zero_of_forall_lt _ _ h_as_lt
    simp [h_tail_zero]
  have h_nz : (toPoly a).coeff i ≠ 0 := by
    rw [h_coeff_i]
    exact a.nonzero (i, x) (by rw [h_coeffs]; simp)
  have h_zero : ∀ k > i, (toPoly a).coeff k = 0 := by
    intro k hk
    simp only [toPoly, h_coeffs]
    unfold toPolyCore
    have h_tail_zero : (toPolyCore as).coeff k = 0 :=
      coeff_toPolyCore_eq_zero_of_forall_lt _ _ fun p hp => (h_as_lt p hp).trans hk
    simp [hk.ne', h_tail_zero]
  symm
  apply le_antisymm
  · by_contra h_gt
    push Not at h_gt
    rw [Polynomial.leadingCoeff_eq_zero.mp (h_zero _ h_gt)] at h_nz
    simp at h_nz
  · by_contra h_lt
    push Not at h_lt
    exact h_nz (Polynomial.coeff_eq_zero_of_natDegree_lt h_lt)

omit [DecidableEq R] in
/-- Core Helper: Pushing scalar multiplication through the list translation -/
lemma toPolyCore_map_smul (c : R) (l : List (ℕ × R)) :
    toPolyCore (l.map fun p => (p.1, c * p.2)) = Polynomial.C c * toPolyCore l := by
  induction l with
  | nil => unfold toPolyCore; simp
  | cons hd tl ih =>
    rcases hd with ⟨i, x⟩
    simp only [List.map_cons]
    unfold toPolyCore
    rw [ih, mul_add, map_mul]
    ring

/-- The coefficient of `X ^ n` read off a raw `(exponent, coefficient)` list (`0` if absent). -/
def coeffCore : List (ℕ × R) → ℕ → R
  | [], _ => 0
  | (i, a) :: tl, n => if n = i then a else coeffCore tl n

/-- The coefficient of `X^n` in a `SparsePoly R`, found by searching its coefficient list. -/
def coeff (P : SparsePoly R) (n : ℕ) : R :=
  coeffCore P.coeffs n

omit [DecidableEq R] in
/-- Core List Helper: Custom list search matches Mathlib Polynomial evaluation -/
lemma coeffCore_eq_toPolyCore_coeff (l : List (ℕ × R)) (n : ℕ)
    (hsorted : l.Pairwise (·.1 > ·.1)) :
    coeffCore l n = (toPolyCore l).coeff n := by
  induction l generalizing n with
  | nil => unfold coeffCore toPolyCore; simp
  | cons hd tl ih =>
    rcases hd with ⟨i, x⟩
    have hhead : ∀ p ∈ tl, i > p.1 := (List.pairwise_cons.1 hsorted).1
    have htail : tl.Pairwise (·.1 > ·.1) := (List.pairwise_cons.1 hsorted).2
    unfold coeffCore toPolyCore
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
    by_cases h_eq : n = i
    · have h_tail_zero : (toPolyCore tl).coeff n = 0 :=
        coeff_toPolyCore_of_degLt tl fun p hp => by grind
      simp [h_eq]
      grind
    · simp [h_eq, ih n htail]

omit [DecidableEq R] in
/-- The Main Bridge Lemma -/
lemma coeff_toPoly (P : SparsePoly R) (n : ℕ) :
    P.coeff n = (toPoly P).coeff n :=
  coeffCore_eq_toPolyCore_coeff P.coeffs n P.sorted

lemma toPoly_smul (c : R) (P : SparsePoly R) :
    toPoly (c • P) = Polynomial.C c * toPoly P := by
  change toPoly (C c * P) = Polynomial.C c * toPoly P
  rw [toPoly_mul, toPoly_C]

/-- How scalar multiplication affects the translated polynomial's coefficients -/
lemma coeff_smul (c : R) (P : SparsePoly R) (n : ℕ) :
    (toPoly (c • P)).coeff n = c * (toPoly P).coeff n := by
  change (toPoly (C c * P)).coeff n = c * (toPoly P).coeff n
  rw [toPoly_mul, toPoly_C, Polynomial.coeff_C_mul]

lemma toPoly_smul_X_pow_mul (c : R) (n : ℕ) (Q : SparsePoly R) :
    toPoly ((c • X^n) * Q) = Polynomial.C c * Polynomial.X^n * toPoly Q := by
  rw [toPoly_mul, toPoly_smul]
  have hX : toPoly (X : SparsePoly R) = Polynomial.X := by
    by_cases h1 : (1 : R) = 0 <;>
      · unfold X toPoly ofSortedList; simp [toPolyCore, Polynomial.X, h1]
  have hpow : toPoly ((X : SparsePoly R)^n) = Polynomial.X^n := by
    induction n with
    | zero => simp [pow_zero, toPoly_one]
    | succ n ih =>
      simpa [pow_succ, ih, hX] using toPoly_mul ((X : SparsePoly R)^n) (X : SparsePoly R)
  rw [hpow]

/-- Bridge: Translates a SparsePoly monomial into a Mathlib Polynomial -/
lemma toPoly_smul_X_pow (c : R) (n : ℕ) :
    toPoly (c • X^n) = Polynomial.C c * Polynomial.X^n := by
  calc
    toPoly (c • X^n) = toPoly ((c • X^n) * (1 : SparsePoly R)) := by simp
    _ = Polynomial.C c * Polynomial.X^n * toPoly (1 : SparsePoly R) :=
      toPoly_smul_X_pow_mul (R := R) c n (1 : SparsePoly R)
    _ = Polynomial.C c * Polynomial.X^n := by simp [toPoly_one]

end SparsePoly
