/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import Mathlib.Data.Polynomial.Splits
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


open BigOperators Polynomial

namespace Multiset

open Polynomial

section Semiring

variable {R : Type*} [CommSemiring R]

/-- A sum version of Vieta's formula for `Multiset`: the product of the linear terms `X + λ` where
`λ` runs through a multiset `s` is equal to a linear combination of the symmetric functions
`esymm s` of the `λ`'s .-/
theorem prod_X_add_C_eq_sum_esymm (s : Multiset R) :
    (s.map fun r => X + C r).prod =
      ∑ j in Finset.range (Multiset.card s + 1), (C (s.esymm j) * X ^ (Multiset.card s - j)) := by
  classical
    rw [prod_map_add, antidiagonal_eq_map_powerset, map_map, ← bind_powerset_len,
      map_bind, sum_bind, Finset.sum_eq_multiset_sum, Finset.range_val, map_congr (Eq.refl _)]
    intro _ _
    rw [esymm, ← sum_hom', ← sum_map_mul_right, map_congr (Eq.refl _)]
    intro s ht
    rw [mem_powersetLen] at ht
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
  -- ⊢ esymm s (↑card s - k) = coeff (∑ j in Finset.range (↑card s + 1), ↑C (esymm  …
  simp_rw [finset_sum_coeff, coeff_C_mul_X_pow]
  -- ⊢ esymm s (↑card s - k) = ∑ x in Finset.range (↑card s + 1), if k = ↑card s -  …
  rw [Finset.sum_eq_single_of_mem (Multiset.card s - k) _]
  · rw [if_pos (Nat.sub_sub_self h).symm]
    -- 🎉 no goals
  · intro j hj1 hj2
    -- ⊢ (if k = ↑card s - j then esymm s j else 0) = 0
    suffices k ≠ card s - j by rw [if_neg this]
    -- ⊢ k ≠ ↑card s - j
    · intro hn
      -- ⊢ False
      rw [hn, Nat.sub_sub_self (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj1))] at hj2
      -- ⊢ False
      exact Ne.irrefl hj2
      -- 🎉 no goals
  · rw [Finset.mem_range]
    -- ⊢ ↑card s - k < ↑card s + 1
    exact Nat.sub_lt_succ (Multiset.card s) k
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align multiset.prod_X_add_C_coeff Multiset.prod_X_add_C_coeff

theorem prod_X_add_C_coeff' {σ} (s : Multiset σ) (r : σ → R) {k : ℕ} (h : k ≤ Multiset.card s) :
    (s.map fun i => X + C (r i)).prod.coeff k = (s.map r).esymm (Multiset.card s - k) := by
  erw [← map_map (fun r => X + C r) r, prod_X_add_C_coeff] <;> rw [s.card_map r]; assumption
  -- ⊢ esymm (map r s) (↑card (map r s) - k) = esymm (map r s) (↑card s - k)
                                                               -- 🎉 no goals
                                                               -- ⊢ k ≤ ↑card s
                                                                                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align multiset.prod_X_add_C_coeff' Multiset.prod_X_add_C_coeff'

theorem _root_.Finset.prod_X_add_C_coeff {σ} (s : Finset σ) (r : σ → R) {k : ℕ} (h : k ≤ s.card) :
    (∏ i in s, (X + C (r i))).coeff k = ∑ t in s.powersetLen (s.card - k), ∏ i in t, r i := by
  rw [Finset.prod, prod_X_add_C_coeff' _ r h, Finset.esymm_map_val]
  -- ⊢ ∑ t in Finset.powersetLen (↑card s.val - k) s, Finset.prod t r = ∑ t in Fins …
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align finset.prod_X_add_C_coeff Finset.prod_X_add_C_coeff

end Semiring

section Ring

variable {R : Type*} [CommRing R]

theorem esymm_neg (s : Multiset R) (k : ℕ) : (map Neg.neg s).esymm k = (-1) ^ k * esymm s k := by
  rw [esymm, esymm, ← Multiset.sum_map_mul_left, Multiset.powersetLen_map, Multiset.map_map,
    map_congr (Eq.refl _)]
  intro x hx
  -- ⊢ (prod ∘ map Neg.neg) x = (-1) ^ k * prod x
  rw [(mem_powersetLen.mp hx).right.symm, ← prod_replicate, ← Multiset.map_const]
  -- ⊢ (prod ∘ map Neg.neg) x = prod (map (Function.const R (-1)) x) * prod x
  nth_rw 3 [← map_id' x]
  -- ⊢ (prod ∘ map Neg.neg) x = prod (map (Function.const R (-1)) x) * prod (map (f …
  rw [← prod_map_mul, map_congr (Eq.refl _)];rfl
                                             -- ⊢ ∀ (x_1 : R), x_1 ∈ x → Function.const R (-1) x_1 * x_1 = -x_1
  exact fun z _ => neg_one_mul z
  -- 🎉 no goals
#align multiset.esymm_neg Multiset.esymm_neg

theorem prod_X_sub_X_eq_sum_esymm (s : Multiset R) :
    (s.map fun t => X - C t).prod =
      ∑ j in Finset.range (Multiset.card s + 1),
        (-1) ^ j * (C (s.esymm j) * X ^ (Multiset.card s - j)) := by
  conv_lhs =>
    congr
    congr
    ext x
    rw [sub_eq_add_neg]
    rw [← map_neg C x]
  convert prod_X_add_C_eq_sum_esymm (map (fun t => -t) s) using 1
  -- ⊢ prod (map (fun x => X + ↑C (-x)) s) = prod (map (fun r => X + ↑C r) (map (fu …
  · rw [map_map]; rfl
    -- ⊢ prod (map (fun x => X + ↑C (-x)) s) = prod (map ((fun r => X + ↑C r) ∘ fun t …
                  -- 🎉 no goals
  · simp only [esymm_neg, card_map, mul_assoc, map_mul, map_pow, map_neg, map_one]
    -- 🎉 no goals
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
    -- ⊢ coeff (prod (map (fun x => X + ↑C (-x)) s)) k = coeff (prod (map ((fun r =>  …
                  -- 🎉 no goals
  · rw [esymm_neg, card_map]
    -- 🎉 no goals
  · rwa [card_map]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align multiset.prod_X_sub_C_coeff Multiset.prod_X_sub_C_coeff

/-- Vieta's formula for the coefficients and the roots of a polynomial over an integral domain
  with as many roots as its degree. -/
theorem _root_.Polynomial.coeff_eq_esymm_roots_of_card [IsDomain R] {p : R[X]}
    (hroots : Multiset.card p.roots = p.natDegree) {k : ℕ} (h : k ≤ p.natDegree) :
    p.coeff k = p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hroots]
  -- ⊢ coeff (↑C (leadingCoeff p) * prod (map (fun a => X - ↑C a) (roots p))) k = l …
  rw [coeff_C_mul, mul_assoc]; congr
  -- ⊢ leadingCoeff p * coeff (prod (map (fun a => X - ↑C a) (roots p))) k = leadin …
                               -- ⊢ coeff (prod (map (fun a => X - ↑C a) (roots p))) k = (-1) ^ (natDegree p - k …
  have : k ≤ card (roots p) := by rw [hroots]; exact h
  -- ⊢ coeff (prod (map (fun a => X - ↑C a) (roots p))) k = (-1) ^ (natDegree p - k …
  convert p.roots.prod_X_sub_C_coeff this using 3 <;> rw [hroots]
  -- ⊢ natDegree p - k = ↑card (roots p) - k
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
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
      ∑ j in range (card σ + 1), Polynomial.C
        (MvPolynomial.esymm σ R j) * Polynomial.X ^ (card σ - j) := by
  let s := Finset.univ.val.map fun i : σ => (MvPolynomial.X i : MvPolynomial σ R)
  -- ⊢ ∏ i : σ, (Polynomial.X + ↑Polynomial.C (X i)) = ∑ j in range (Fintype.card σ …
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map, ←Finset.card_univ, Finset.card_def]
  simp_rw [this, MvPolynomial.esymm_eq_multiset_esymm σ R, Finset.prod_eq_multiset_prod]
  -- ⊢ Multiset.prod (Multiset.map (fun x => Polynomial.X + ↑Polynomial.C (X x)) un …
  convert Multiset.prod_X_add_C_eq_sum_esymm s
  -- ⊢ Multiset.map (fun x => Polynomial.X + ↑Polynomial.C (X x)) univ.val = Multis …
  simp_rw [Multiset.map_map, Function.comp_apply]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.prod_C_add_X_eq_sum_esymm MvPolynomial.prod_C_add_X_eq_sum_esymm

theorem MvPolynomial.prod_X_add_C_coeff (k : ℕ) (h : k ≤ card σ) :
    (∏ i : σ, (Polynomial.X + Polynomial.C (MvPolynomial.X i)) : Polynomial _).coeff k =
    MvPolynomial.esymm σ R (card σ - k) := by
  let s := Finset.univ.val.map fun i => (MvPolynomial.X i : MvPolynomial σ R)
  -- ⊢ Polynomial.coeff (∏ i : σ, (Polynomial.X + ↑Polynomial.C (X i))) k = esymm σ …
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map, ←Finset.card_univ, Finset.card_def]
  rw [this] at h ⊢
  -- ⊢ Polynomial.coeff (∏ i : σ, (Polynomial.X + ↑Polynomial.C (X i))) k = esymm σ …
  rw [MvPolynomial.esymm_eq_multiset_esymm σ R, Finset.prod_eq_multiset_prod]
  -- ⊢ Polynomial.coeff (Multiset.prod (Multiset.map (fun i => Polynomial.X + ↑Poly …
  convert Multiset.prod_X_add_C_coeff s h
  -- ⊢ Multiset.map (fun i => Polynomial.X + ↑Polynomial.C (X i)) univ.val = Multis …
  dsimp
  -- ⊢ Multiset.map (fun i => Polynomial.X + ↑Polynomial.C (X i)) univ.val = Multis …
  simp_rw [Multiset.map_map, Function.comp_apply]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.prod_X_add_C_coeff MvPolynomial.prod_X_add_C_coeff

end MvPolynomial
