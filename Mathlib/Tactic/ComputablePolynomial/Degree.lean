/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.Ring

/-!
# `SparsePoly`: degree and pseudo-division bounds

The degree of a `SparsePoly` (the head exponent), its agreement with `Polynomial.natDegree`
under `toPoly`, and the degree bounds for the cross-multiplication pseudo-remainder steps used
by the division-free `gcdPrim`. Also defines the `IsExactDiv` typeclass (division is exact on
divisibility), used by the exact division and gcd files.
-/

@[expose] public section

namespace SparsePoly

open Polynomial

variable {R : Type} [CommRing R] [DecidableEq R]

/-- A typeclass asserting that division `/` is exact on divisibility: whenever `b ∣ a`, one has
`b * (a / b) = a`. This holds for `ℤ` (Euclidean division) and for fields. -/
class IsExactDiv (R : Type*) [Monoid R] [Div R] : Prop where
  mul_div_cancel {a b : R} : b ∣ a → b * (a / b) = a

/-- The degree of a `SparsePoly R`, i.e. the exponent of its leading (head) term, or `0` for the
zero polynomial. -/
def degree (a : SparsePoly R) : ℕ := (a.coeffs.headD (0, 0)).1

omit [DecidableEq R] in
lemma degree_eq_head (p : SparsePoly R) (i : ℕ) (x : R) (tail : List (ℕ × R))
    (h : p.coeffs = (i, x) :: tail) : p.degree = i := by
  rw [degree, h]
  simp

omit [DecidableEq R] in
lemma natDegree_toPolyCore_lt (i : ℕ) (x : R) (tail : List (ℕ × R))
    (h_sorted : ((i, x) :: tail).Pairwise (·.1 > ·.1)) :
    (toPolyCore tail).natDegree < i ∨ toPolyCore tail = 0 := by
  by_cases h0 : toPolyCore tail = 0
  · exact Or.inr h0
  · refine Or.inl (lt_of_not_ge fun hge => h0 ?_)
    have h_degLt_nd : degLt (toPolyCore tail).natDegree tail :=
      fun p hp => lt_of_lt_of_le ((List.pairwise_cons.1 h_sorted).1 p hp) hge
    exact Polynomial.leadingCoeff_eq_zero.1 (coeff_toPolyCore_of_degLt tail h_degLt_nd)

omit [DecidableEq R] in
lemma degree_eq_natDegree_toPoly (p : SparsePoly R) :
    p.degree = (toPoly p).natDegree := by
  by_cases hnil : p.coeffs = []
  · simp [degree, toPoly, toPolyCore, hnil]
  · rcases List.exists_cons_of_ne_nil hnil with ⟨hd, tl, hcoeffs⟩
    rcases hd with ⟨i, x⟩
    have hs : ((i, x) :: tl).Pairwise (·.1 > ·.1) := by simpa [hcoeffs] using p.sorted
    have hdegTl : degLt i tl := degLt_of_sorted_cons hs
    have hx0 : x ≠ 0 := by
     have := p.nonzero (i, x) (by simp [hcoeffs])
     simpa using this
    have hcoeff_i : (toPoly p).coeff i = x := by
     rw [toPoly, hcoeffs]
     simpa using coeff_toPolyCore_head (i := i) (a := x) tl hdegTl
    have hcoeff_i_ne : (toPoly p).coeff i ≠ 0 := by simpa [hcoeff_i] using hx0
    have hupper : ∀ k > i, (toPoly p).coeff k = 0 := by
     intro k hk
     have hdegTl' : degLt k tl := fun e he => lt_trans (hdegTl e he) hk
     rw [toPoly, hcoeffs, toPolyCore, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
     have hik : i ≠ k := by grind
     simp [coeff_toPolyCore_of_degLt tl hdegTl']
     grind
    have hle : i ≤ (toPoly p).natDegree := Polynomial.le_natDegree_of_ne_zero hcoeff_i_ne
    have hge : (toPoly p).natDegree ≤ i := by
     by_contra hgt
     have hi_lt : i < (toPoly p).natDegree := lt_of_not_ge hgt
     have hz : (toPoly p).coeff (toPoly p).natDegree = 0 := by grind
     specialize hupper (toPoly p).natDegree hi_lt
     aesop
    rw [show p.degree = i by simp [degree, hcoeffs], le_antisymm hge hle]

/-- The pseudo-division of `a` annihilates the leading `x*y*X^i` term (when `i > j`). -/
lemma toPoly_pseudo_rem_a (a b : SparsePoly R) (i j : ℕ) (x y : R) (as bs : List (ℕ × R))
    (ha : a.coeffs = (i, x) :: as) (hb : b.coeffs = (j, y) :: bs) (hij : i > j) :
    (y • a - x • X^(i-j) * b).degree =
      (Polynomial.C y * toPolyCore as -
        Polynomial.C x * Polynomial.X^(i-j) * toPolyCore bs).natDegree := by
  have hX : toPoly (X : SparsePoly R) = Polynomial.X := by
    by_cases h1 : (1 : R) = 0 <;>
      · unfold X toPoly ofSortedList; simp [toPolyCore, h1, Polynomial.X]
  have hpow : ∀ n : ℕ, toPoly ((X : SparsePoly R)^n) = Polynomial.X^n := by
    intro n
    induction n with
    | zero => simp [toPoly_one]
    | succ n ih =>
      simpa [pow_succ, ih, hX] using toPoly_mul ((X : SparsePoly R)^n) (X : SparsePoly R)
  have hsmul_a : toPoly (y • a) = Polynomial.C y * toPoly a := by
    change toPoly (C y * a) = _; rw [toPoly_mul, toPoly_C]
  have hsmul_X : toPoly (x • (X : SparsePoly R)^(i - j)) =
      Polynomial.C x * Polynomial.X^(i - j) := by
    change toPoly (C x * (X : SparsePoly R)^(i - j)) = _; rw [toPoly_mul, toPoly_C, hpow]
  have htoa : toPoly a = Polynomial.C x * Polynomial.X^i + toPolyCore as := by
    simp [toPoly, toPolyCore, ha]
  have htob : toPoly b = Polynomial.C y * Polynomial.X^j + toPolyCore bs := by
    simp [toPoly, toPolyCore, hb]
  have hcross :
      (Polynomial.C x * Polynomial.X^(i - j)) * (Polynomial.C y * Polynomial.X^j)
        = Polynomial.C y * (Polynomial.C x * Polynomial.X^i) := by
    have hpowX : (Polynomial.X : Polynomial R)^(i - j) * Polynomial.X^j = Polynomial.X^i := by
      rw [← pow_add, Nat.sub_add_cancel hij.le]
    rw [← hpowX]; ring
  have hpoly :
      toPoly (y • a - x • X^(i-j) * b) =
        Polynomial.C y * toPolyCore as - Polynomial.C x * Polynomial.X^(i-j) * toPolyCore bs := by
    rw [sub_eq_add_neg, toPoly_add, toPoly_neg, toPoly_mul, hsmul_a, hsmul_X, htoa, htob,
      mul_add, mul_add, hcross]
    ring
  rw [degree_eq_natDegree_toPoly _, hpoly]

/-- The pseudo-division of `b` annihilates the leading `x*y*X^j` term (when `¬ i > j`). -/
lemma toPoly_pseudo_rem_b (a b : SparsePoly R) (i j : ℕ) (x y : R) (as bs : List (ℕ × R))
    (ha : a.coeffs = (i, x) :: as) (hb : b.coeffs = (j, y) :: bs) (hji : ¬ (i > j)) :
    (x • b - y • X^(j-i) * a).degree =
      (Polynomial.C x * toPolyCore bs -
        Polynomial.C y * Polynomial.X^(j-i) * toPolyCore as).natDegree := by
  have hX : toPoly (X : SparsePoly R) = Polynomial.X := by
    by_cases h1 : (1 : R) = 0 <;>
      · unfold X toPoly ofSortedList; simp [toPolyCore, h1, Polynomial.X]
  have hpow : ∀ n : ℕ, toPoly ((X : SparsePoly R)^n) = Polynomial.X^n := by
    intro n
    induction n with
    | zero => simp [toPoly_one]
    | succ n ih =>
      simpa [pow_succ, ih, hX] using toPoly_mul ((X : SparsePoly R)^n) (X : SparsePoly R)
  have hsmul_b : toPoly (x • b) = Polynomial.C x * toPoly b := by
    change toPoly (C x * b) = _; rw [toPoly_mul, toPoly_C]
  have hsmul_X : toPoly (y • (X : SparsePoly R)^(j - i)) =
      Polynomial.C y * Polynomial.X^(j - i) := by
    change toPoly (C y * (X : SparsePoly R)^(j - i)) = _; rw [toPoly_mul, toPoly_C, hpow]
  have htoa : toPoly a = Polynomial.C x * Polynomial.X^i + toPolyCore as := by
    simp [toPoly, toPolyCore, ha]
  have htob : toPoly b = Polynomial.C y * Polynomial.X^j + toPolyCore bs := by
    simp [toPoly, toPolyCore, hb]
  have hcross :
      (Polynomial.C y * Polynomial.X^(j - i)) * (Polynomial.C x * Polynomial.X^i)
        = Polynomial.C x * (Polynomial.C y * Polynomial.X^j) := by
    have hpowX : (Polynomial.X : Polynomial R)^(j - i) * Polynomial.X^i = Polynomial.X^j := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [← hpowX]; ring
  have hpoly :
      toPoly (x • b - y • X^(j-i) * a) =
        Polynomial.C x * toPolyCore bs - Polynomial.C y * Polynomial.X^(j-i) * toPolyCore as := by
    rw [sub_eq_add_neg, toPoly_add, toPoly_neg, toPoly_mul, hsmul_b, hsmul_X, htob, htoa,
      mul_add, mul_add, hcross]
    ring
  rw [degree_eq_natDegree_toPoly _, hpoly]

lemma deg_pseudo_rem_a (a b : SparsePoly R) (i j : ℕ) (x y : R) (as bs : List (ℕ × R))
    (ha : a.coeffs = (i, x) :: as) (hb : b.coeffs = (j, y) :: bs) (hij : i > j) :
    (y • a - x • X^(i-j) * b).degree < a.degree := by
  rw [degree_eq_head a i x as ha, toPoly_pseudo_rem_a a b i j x y as bs ha hb hij]
  have h_coeff : ∀ k ≥ i, (Polynomial.C y * toPolyCore as -
      Polynomial.C x * Polynomial.X ^ (i - j) * toPolyCore bs).coeff k = 0 := by
    intro k hk
    have h_as_sorted : ((i, x) :: as).Pairwise (·.1 > ·.1) := by simpa [ha] using a.sorted
    have h_bs_sorted : ((j, y) :: bs).Pairwise (·.1 > ·.1) := by simpa [hb] using b.sorted
    have h_as_deg := natDegree_toPolyCore_lt i x as h_as_sorted
    have h_bs_deg := natDegree_toPolyCore_lt j y bs h_bs_sorted
    have h_as_coeff : (toPolyCore as).coeff k = 0 := by
      rcases h_as_deg with hlt | h0
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [h0]; simp
    have h_bs_coeff : (toPolyCore bs).coeff (k - (i - j)) = 0 := by
      rcases h_bs_deg with hlt | h0
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [h0]; simp
    have h_term1 : (Polynomial.C y * toPolyCore as).coeff k = 0 := by
      rw [Polynomial.coeff_C_mul, h_as_coeff, mul_zero]
    have h_term2 : (Polynomial.C x * Polynomial.X ^ (i - j) * toPolyCore bs).coeff k = 0 := by
      rw [show Polynomial.C x * Polynomial.X ^ (i - j) * toPolyCore bs
            = (Polynomial.C x * toPolyCore bs) * Polynomial.X ^ (i - j) by ring,
        ← (by omega : (k - (i - j)) + (i - j) = k),
        Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul, h_bs_coeff, mul_zero]
    rw [Polynomial.coeff_sub, h_term1, h_term2, sub_zero]
  by_cases h_zero : (Polynomial.C y * toPolyCore as -
      Polynomial.C x * Polynomial.X ^ (i - j) * toPolyCore bs) = 0
  · rw [h_zero, Polynomial.natDegree_zero]; omega
  · exact lt_of_not_ge fun h_ge => h_zero (Polynomial.leadingCoeff_eq_zero.mp (h_coeff _ h_ge))

lemma deg_pseudo_rem_b (a b : SparsePoly R) (i j : ℕ) (x y : R) (as bs : List (ℕ × R))
    (ha : a.coeffs = (i, x) :: as) (hb : b.coeffs = (j, y) :: bs) (hji : ¬(i > j))
    (hj_pos : 0 < j) :
    (x • b - y • X^(j-i) * a).degree < b.degree := by
  rw [degree_eq_head b j y bs hb, toPoly_pseudo_rem_b a b i j x y as bs ha hb hji]
  have h_coeff : ∀ k ≥ j, (Polynomial.C x * toPolyCore bs -
      Polynomial.C y * Polynomial.X ^ (j - i) * toPolyCore as).coeff k = 0 := by
    intro k hk
    have h_as_sorted : ((i, x) :: as).Pairwise (·.1 > ·.1) := by simpa [ha] using a.sorted
    have h_bs_sorted : ((j, y) :: bs).Pairwise (·.1 > ·.1) := by simpa [hb] using b.sorted
    have h_as_deg := natDegree_toPolyCore_lt i x as h_as_sorted
    have h_bs_deg := natDegree_toPolyCore_lt j y bs h_bs_sorted
    have h_bs_coeff : (toPolyCore bs).coeff k = 0 := by
      rcases h_bs_deg with hlt | h0
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [h0]; simp
    have h_as_coeff : (toPolyCore as).coeff (k - (j - i)) = 0 := by
      rcases h_as_deg with hlt | h0
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [h0]; simp
    have h_term1 : (Polynomial.C x * toPolyCore bs).coeff k = 0 := by
      rw [Polynomial.coeff_C_mul, h_bs_coeff, mul_zero]
    have h_term2 : (Polynomial.C y * Polynomial.X ^ (j - i) * toPolyCore as).coeff k = 0 := by
      rw [show Polynomial.C y * Polynomial.X ^ (j - i) * toPolyCore as
            = (Polynomial.C y * toPolyCore as) * Polynomial.X ^ (j - i) by ring,
        ← (by omega : (k - (j - i)) + (j - i) = k),
        Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul, h_as_coeff, mul_zero]
    rw [Polynomial.coeff_sub, h_term1, h_term2, sub_zero]
  by_cases h_zero : (Polynomial.C x * toPolyCore bs -
      Polynomial.C y * Polynomial.X ^ (j - i) * toPolyCore as) = 0
  · rw [h_zero, Polynomial.natDegree_zero]; exact hj_pos
  · exact lt_of_not_ge fun h_ge => h_zero (Polynomial.leadingCoeff_eq_zero.mp (h_coeff _ h_ge))

end SparsePoly
