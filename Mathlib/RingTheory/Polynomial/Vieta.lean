/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.MvPolynomial.Symmetric

#align_import ring_theory.polynomial.vieta from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Vieta's Formula

The main result is `Multiset.prod_X_add_C_eq_sum_esymm`, which shows that the product of
linear terms `X + λ` with `λ` in a `Multiset s` is equal to a linear combination of the
symmetric functions `esymm s`.

From this, we deduce `MvPolynomial.prod_X_add_C_eq_sum_esymm` which is the equivalent formula
for the product of linear terms `X + X i` with `i` in a `Fintype σ` as a linear combination
of the symmetric polynomials `esymm σ R j`.

For `R` be an integral domain (so that `p.roots` is defined for any `p : R[X]` as a multiset),
we derive `Polynomial.coeff_eq_esymm_roots_of_card`, the relationship between the coefficients and
the roots of `p` for a polynomial `p` that splits (i.e. having as many roots as its degree).
-/


open Polynomial

namespace Multiset

open Polynomial

section Semiring

variable {R : Type*} [CommSemiring R]

/-- A sum version of **Vieta's formula** for `Multiset`: the product of the linear terms `X + λ`
where `λ` runs through a multiset `s` is equal to a linear combination of the symmetric functions
`esymm s` of the `λ`'s . -/
theorem prod_X_add_C_eq_sum_esymm (s : Multiset R) :
    (s.map fun r => X + C r).prod =
      ∑ j ∈ Finset.range (Multiset.card s + 1), (C (s.esymm j) * X ^ (Multiset.card s - j)) := by
  classical
    rw [prod_map_add, antidiagonal_eq_map_powerset, map_map, ← bind_powerset_len,
      map_bind, sum_bind, Finset.sum_eq_multiset_sum, Finset.range_val, map_congr (Eq.refl _)]
    intro _ _
    rw [esymm, ← sum_hom', ← sum_map_mul_right, map_congr (Eq.refl _)]
    intro s ht
    rw [mem_powersetCard] at ht
    dsimp
    rw [prod_hom' s (Polynomial.C : R →+* R[X])]
    simp [ht, map_const, prod_replicate, prod_hom', map_id', card_sub]
set_option linter.uppercaseLean3 false in
#align multiset.prod_X_add_C_eq_sum_esymm Multiset.prod_X_add_C_eq_sum_esymm

/-- Vieta's formula for the coefficients of the product of linear terms `X + λ` where `λ` runs
through a multiset `s` : the `k`th coefficient is the symmetric function `esymm (card s - k) s`. -/
theorem prod_X_add_C_coeff (s : Multiset R) {k : ℕ} (h : k ≤ Multiset.card s) :
    (s.map fun r => X + C r).prod.coeff k = s.esymm (Multiset.card s - k) := by
  convert Polynomial.ext_iff.mp (prod_X_add_C_eq_sum_esymm s) k using 1
  simp_rw [finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single_of_mem (Multiset.card s - k) _]
  · rw [if_pos (Nat.sub_sub_self h).symm]
  · intro j hj1 hj2
    suffices k ≠ card s - j by rw [if_neg this]
    intro hn
    rw [hn, Nat.sub_sub_self (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj1))] at hj2
    exact Ne.irrefl hj2
  · rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.sub_le (Multiset.card s) k)
set_option linter.uppercaseLean3 false in
#align multiset.prod_X_add_C_coeff Multiset.prod_X_add_C_coeff

theorem prod_X_add_C_coeff' {σ} (s : Multiset σ) (r : σ → R) {k : ℕ} (h : k ≤ Multiset.card s) :
    (s.map fun i => X + C (r i)).prod.coeff k = (s.map r).esymm (Multiset.card s - k) := by
  erw [← map_map (fun r => X + C r) r, prod_X_add_C_coeff] <;> rw [s.card_map r]; assumption
set_option linter.uppercaseLean3 false in
#align multiset.prod_X_add_C_coeff' Multiset.prod_X_add_C_coeff'

theorem _root_.Finset.prod_X_add_C_coeff {σ} (s : Finset σ) (r : σ → R) {k : ℕ} (h : k ≤ s.card) :
    (∏ i ∈ s, (X + C (r i))).coeff k = ∑ t ∈ s.powersetCard (s.card - k), ∏ i ∈ t, r i := by
  rw [Finset.prod, prod_X_add_C_coeff' _ r h, Finset.esymm_map_val]
  rfl
set_option linter.uppercaseLean3 false in
#align finset.prod_X_add_C_coeff Finset.prod_X_add_C_coeff

end Semiring

section Ring

variable {R : Type*} [CommRing R]

theorem esymm_neg (s : Multiset R) (k : ℕ) : (map Neg.neg s).esymm k = (-1) ^ k * esymm s k := by
  rw [esymm, esymm, ← Multiset.sum_map_mul_left, Multiset.powersetCard_map, Multiset.map_map,
    map_congr rfl]
  intro x hx
  rw [(mem_powersetCard.mp hx).right.symm, ← prod_replicate, ← Multiset.map_const]
  nth_rw 3 [← map_id' x]
  rw [← prod_map_mul, map_congr rfl, Function.comp_apply]
  exact fun z _ => neg_one_mul z
#align multiset.esymm_neg Multiset.esymm_neg

theorem prod_X_sub_X_eq_sum_esymm (s : Multiset R) :
    (s.map fun t => X - C t).prod =
      ∑ j ∈ Finset.range (Multiset.card s + 1),
        (-1) ^ j * (C (s.esymm j) * X ^ (Multiset.card s - j)) := by
  conv_lhs =>
    congr
    congr
    ext x
    rw [sub_eq_add_neg]
    rw [← map_neg C x]
  convert prod_X_add_C_eq_sum_esymm (map (fun t => -t) s) using 1
  · rw [map_map]; rfl
  · simp only [esymm_neg, card_map, mul_assoc, map_mul, map_pow, map_neg, map_one]
set_option linter.uppercaseLean3 false in
#align multiset.prod_X_sub_C_eq_sum_esymm Multiset.prod_X_sub_X_eq_sum_esymm

theorem prod_X_sub_C_coeff (s : Multiset R) {k : ℕ} (h : k ≤ Multiset.card s) :
    (s.map fun t => X - C t).prod.coeff k =
    (-1) ^ (Multiset.card s - k) * s.esymm (Multiset.card s - k) := by
  conv_lhs =>
    congr
    congr
    congr
    ext x
    rw [sub_eq_add_neg]
    rw [← map_neg C x]
  convert prod_X_add_C_coeff (map (fun t => -t) s) _ using 1
  · rw [map_map]; rfl
  · rw [esymm_neg, card_map]
  · rwa [card_map]
set_option linter.uppercaseLean3 false in
#align multiset.prod_X_sub_C_coeff Multiset.prod_X_sub_C_coeff

/-- Vieta's formula for the coefficients and the roots of a polynomial over an integral domain
  with as many roots as its degree. -/
theorem _root_.Polynomial.coeff_eq_esymm_roots_of_card [IsDomain R] {p : R[X]}
    (hroots : Multiset.card p.roots = p.natDegree) {k : ℕ} (h : k ≤ p.natDegree) :
    p.coeff k = p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hroots]
  rw [coeff_C_mul, mul_assoc]; congr
  have : k ≤ card (roots p) := by rw [hroots]; exact h
  convert p.roots.prod_X_sub_C_coeff this using 3 <;> rw [hroots]
#align polynomial.coeff_eq_esymm_roots_of_card Polynomial.coeff_eq_esymm_roots_of_card

/-- Vieta's formula for split polynomials over a field. -/
theorem _root_.Polynomial.coeff_eq_esymm_roots_of_splits {F} [Field F] {p : F[X]}
    (hsplit : p.Splits (RingHom.id F)) {k : ℕ} (h : k ≤ p.natDegree) :
    p.coeff k = p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) :=
  Polynomial.coeff_eq_esymm_roots_of_card (splits_iff_card_roots.1 hsplit) h
#align polynomial.coeff_eq_esymm_roots_of_splits Polynomial.coeff_eq_esymm_roots_of_splits

end Ring

end Multiset

section MvPolynomial

open Finset Polynomial Fintype

variable (R σ : Type*) [CommSemiring R] [Fintype σ]

/-- A sum version of Vieta's formula for `MvPolynomial`: viewing `X i` as variables,
the product of linear terms `λ + X i` is equal to a linear combination of
the symmetric polynomials `esymm σ R j`. -/
theorem MvPolynomial.prod_C_add_X_eq_sum_esymm :
    (∏ i : σ, (Polynomial.X + Polynomial.C (MvPolynomial.X i))) =
      ∑ j ∈ range (card σ + 1), Polynomial.C
        (MvPolynomial.esymm σ R j) * Polynomial.X ^ (card σ - j) := by
  let s := Finset.univ.val.map fun i : σ => (MvPolynomial.X i : MvPolynomial σ R)
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map, ← Finset.card_univ, Finset.card_def]
  simp_rw [this, MvPolynomial.esymm_eq_multiset_esymm σ R, Finset.prod_eq_multiset_prod]
  convert Multiset.prod_X_add_C_eq_sum_esymm s
  simp_rw [s, Multiset.map_map, Function.comp_apply]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.prod_C_add_X_eq_sum_esymm MvPolynomial.prod_C_add_X_eq_sum_esymm

theorem MvPolynomial.prod_X_add_C_coeff (k : ℕ) (h : k ≤ card σ) :
    (∏ i : σ, (Polynomial.X + Polynomial.C (MvPolynomial.X i)) : Polynomial _).coeff k =
    MvPolynomial.esymm σ R (card σ - k) := by
  let s := Finset.univ.val.map fun i => (MvPolynomial.X i : MvPolynomial σ R)
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map, ← Finset.card_univ, Finset.card_def]
  rw [this] at h ⊢
  rw [MvPolynomial.esymm_eq_multiset_esymm σ R, Finset.prod_eq_multiset_prod]
  convert Multiset.prod_X_add_C_coeff s h
  dsimp
  simp_rw [s, Multiset.map_map, Function.comp_apply]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.prod_X_add_C_coeff MvPolynomial.prod_X_add_C_coeff

end MvPolynomial
