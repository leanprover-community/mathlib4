/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark

! This file was ported from Lean 3 source module algebra.polynomial.big_operators
! leanprover-community/mathlib commit 47adfab39a11a072db552f47594bf8ed2cf8a722
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.WithZero
import Mathbin.Data.Polynomial.Monic

/-!
# Lemmas for the interaction between polynomials and `∑` and `∏`.

Recall that `∑` and `∏` are notation for `finset.sum` and `finset.prod` respectively.

## Main results

- `polynomial.nat_degree_prod_of_monic` : the degree of a product of monic polynomials is the
  product of degrees. We prove this only for `[comm_semiring R]`,
  but it ought to be true for `[semiring R]` and `list.prod`.
- `polynomial.nat_degree_prod` : for polynomials over an integral domain,
  the degree of the product is the sum of degrees.
- `polynomial.leading_coeff_prod` : for polynomials over an integral domain,
  the leading coefficient is the product of leading coefficients.
- `polynomial.prod_X_sub_C_coeff_card_pred` carries most of the content for computing
  the second coefficient of the characteristic polynomial.
-/


open Finset

open Multiset

open BigOperators Polynomial

universe u w

variable {R : Type u} {ι : Type w}

namespace Polynomial

variable (s : Finset ι)

section Semiring

variable {S : Type _} [Semiring S]

theorem natDegree_list_sum_le (l : List S[X]) : natDegree l.Sum ≤ (l.map natDegree).foldr max 0 :=
  List.sum_le_foldr_max natDegree (by simp) natDegree_add_le _
#align polynomial.nat_degree_list_sum_le Polynomial.natDegree_list_sum_le

theorem natDegree_multiset_sum_le (l : Multiset S[X]) :
    natDegree l.Sum ≤ (l.map natDegree).foldr max max_left_comm 0 :=
  Quotient.inductionOn l (by simpa using nat_degree_list_sum_le)
#align polynomial.nat_degree_multiset_sum_le Polynomial.natDegree_multiset_sum_le

theorem natDegree_sum_le (f : ι → S[X]) :
    natDegree (∑ i in s, f i) ≤ s.fold max 0 (natDegree ∘ f) := by
  simpa using nat_degree_multiset_sum_le (s.val.map f)
#align polynomial.nat_degree_sum_le Polynomial.natDegree_sum_le

theorem degree_list_sum_le (l : List S[X]) : degree l.Sum ≤ (l.map natDegree).maximum :=
  by
  by_cases h : l.sum = 0
  · simp [h]
  · rw [degree_eq_nat_degree h]
    suffices (l.map nat_degree).maximum = ((l.map nat_degree).foldr max 0 : ℕ)
      by
      rw [this]
      simpa [this] using nat_degree_list_sum_le l
    rw [← List.foldr_max_of_ne_nil]
    · congr
    contrapose! h
    rw [List.map_eq_nil] at h
    simp [h]
#align polynomial.degree_list_sum_le Polynomial.degree_list_sum_le

theorem natDegree_list_prod_le (l : List S[X]) : natDegree l.Prod ≤ (l.map natDegree).Sum :=
  by
  induction' l with hd tl IH
  · simp
  · simpa using nat_degree_mul_le.trans (add_le_add_left IH _)
#align polynomial.nat_degree_list_prod_le Polynomial.natDegree_list_prod_le

theorem degree_list_prod_le (l : List S[X]) : degree l.Prod ≤ (l.map degree).Sum :=
  by
  induction' l with hd tl IH
  · simp
  · simpa using (degree_mul_le _ _).trans (add_le_add_left IH _)
#align polynomial.degree_list_prod_le Polynomial.degree_list_prod_le

theorem coeff_list_prod_of_natDegree_le (l : List S[X]) (n : ℕ) (hl : ∀ p ∈ l, natDegree p ≤ n) :
    coeff (List.prod l) (l.length * n) = (l.map fun p => coeff p n).Prod :=
  by
  induction' l with hd tl IH
  · simp
  · have hl' : ∀ p ∈ tl, nat_degree p ≤ n := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    simp only [List.prod_cons, List.map, List.length]
    rw [add_mul, one_mul, add_comm, ← IH hl', mul_comm tl.length]
    have h : nat_degree tl.prod ≤ n * tl.length :=
      by
      refine' (nat_degree_list_prod_le _).trans _
      rw [← tl.length_map nat_degree, mul_comm]
      refine' List.sum_le_card_nsmul _ _ _
      simpa using hl'
    have hdn : nat_degree hd ≤ n := hl _ (List.mem_cons_self _ _)
    rcases hdn.eq_or_lt with (rfl | hdn')
    · cases' h.eq_or_lt with h' h'
      · rw [← h', coeff_mul_degree_add_degree, leading_coeff, leading_coeff]
      · rw [coeff_eq_zero_of_nat_degree_lt, coeff_eq_zero_of_nat_degree_lt h', mul_zero]
        exact nat_degree_mul_le.trans_lt (add_lt_add_left h' _)
    · rw [coeff_eq_zero_of_nat_degree_lt hdn', coeff_eq_zero_of_nat_degree_lt, zero_mul]
      exact nat_degree_mul_le.trans_lt (add_lt_add_of_lt_of_le hdn' h)
#align polynomial.coeff_list_prod_of_nat_degree_le Polynomial.coeff_list_prod_of_natDegree_le

end Semiring

section CommSemiring

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

theorem natDegree_multiset_prod_le : t.Prod.natDegree ≤ (t.map natDegree).Sum :=
  Quotient.inductionOn t (by simpa using nat_degree_list_prod_le)
#align polynomial.nat_degree_multiset_prod_le Polynomial.natDegree_multiset_prod_le

theorem natDegree_prod_le : (∏ i in s, f i).natDegree ≤ ∑ i in s, (f i).natDegree := by
  simpa using nat_degree_multiset_prod_le (s.1.map f)
#align polynomial.nat_degree_prod_le Polynomial.natDegree_prod_le

/-- The degree of a product of polynomials is at most the sum of the degrees,
where the degree of the zero polynomial is ⊥.
-/
theorem degree_multiset_prod_le : t.Prod.degree ≤ (t.map Polynomial.degree).Sum :=
  Quotient.inductionOn t (by simpa using degree_list_prod_le)
#align polynomial.degree_multiset_prod_le Polynomial.degree_multiset_prod_le

theorem degree_prod_le : (∏ i in s, f i).degree ≤ ∑ i in s, (f i).degree := by
  simpa only [Multiset.map_map] using degree_multiset_prod_le (s.1.map f)
#align polynomial.degree_prod_le Polynomial.degree_prod_le

/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `polynomial.leading_coeff_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem leadingCoeff_multiset_prod' (h : (t.map leadingCoeff).Prod ≠ 0) :
    t.Prod.leadingCoeff = (t.map leadingCoeff).Prod :=
  by
  induction' t using Multiset.induction_on with a t ih; · simp
  simp only [Multiset.map_cons, Multiset.prod_cons] at h⊢
  rw [Polynomial.leadingCoeff_mul'] <;>
    · rwa [ih]
      apply right_ne_zero_of_mul h
#align polynomial.leading_coeff_multiset_prod' Polynomial.leadingCoeff_multiset_prod'

/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `polynomial.leading_coeff_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem leadingCoeff_prod' (h : (∏ i in s, (f i).leadingCoeff) ≠ 0) :
    (∏ i in s, f i).leadingCoeff = ∏ i in s, (f i).leadingCoeff := by
  simpa using leading_coeff_multiset_prod' (s.1.map f) (by simpa using h)
#align polynomial.leading_coeff_prod' Polynomial.leadingCoeff_prod'

/-- The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is nonzero.

See `polynomial.nat_degree_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem natDegree_multiset_prod' (h : (t.map fun f => leadingCoeff f).Prod ≠ 0) :
    t.Prod.natDegree = (t.map fun f => natDegree f).Sum :=
  by
  revert h
  refine' Multiset.induction_on t _ fun a t ih ht => _; · simp
  rw [Multiset.map_cons, Multiset.prod_cons] at ht⊢
  rw [Multiset.sum_cons, Polynomial.natDegree_mul', ih]
  · apply right_ne_zero_of_mul ht
  · rwa [Polynomial.leadingCoeff_multiset_prod']
    apply right_ne_zero_of_mul ht
#align polynomial.nat_degree_multiset_prod' Polynomial.natDegree_multiset_prod'

/-- The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is nonzero.

See `polynomial.nat_degree_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem natDegree_prod' (h : (∏ i in s, (f i).leadingCoeff) ≠ 0) :
    (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree := by
  simpa using nat_degree_multiset_prod' (s.1.map f) (by simpa using h)
#align polynomial.nat_degree_prod' Polynomial.natDegree_prod'

theorem natDegree_multiset_prod_of_monic (h : ∀ f ∈ t, Monic f) :
    t.Prod.natDegree = (t.map natDegree).Sum :=
  by
  nontriviality R
  apply nat_degree_multiset_prod'
  suffices (t.map fun f => leading_coeff f).Prod = 1
    by
    rw [this]
    simp
  convert prod_replicate t.card (1 : R)
  · simp only [eq_replicate, Multiset.card_map, eq_self_iff_true, true_and_iff]
    rintro i hi
    obtain ⟨i, hi, rfl⟩ := multiset.mem_map.mp hi
    apply h
    assumption
  · simp
#align polynomial.nat_degree_multiset_prod_of_monic Polynomial.natDegree_multiset_prod_of_monic

theorem natDegree_prod_of_monic (h : ∀ i ∈ s, (f i).Monic) :
    (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree := by
  simpa using nat_degree_multiset_prod_of_monic (s.1.map f) (by simpa using h)
#align polynomial.nat_degree_prod_of_monic Polynomial.natDegree_prod_of_monic

theorem coeff_multiset_prod_of_natDegree_le (n : ℕ) (hl : ∀ p ∈ t, natDegree p ≤ n) :
    coeff t.Prod (t.card * n) = (t.map fun p => coeff p n).Prod :=
  by
  induction t using Quotient.inductionOn
  simpa using coeff_list_prod_of_nat_degree_le _ _ hl
#align polynomial.coeff_multiset_prod_of_nat_degree_le Polynomial.coeff_multiset_prod_of_natDegree_le

theorem coeff_prod_of_natDegree_le (f : ι → R[X]) (n : ℕ) (h : ∀ p ∈ s, natDegree (f p) ≤ n) :
    coeff (∏ i in s, f i) (s.card * n) = ∏ i in s, coeff (f i) n :=
  by
  cases' s with l hl
  convert coeff_multiset_prod_of_nat_degree_le (l.map f) _ _
  · simp
  · simp
  · simpa using h
#align polynomial.coeff_prod_of_nat_degree_le Polynomial.coeff_prod_of_natDegree_le

theorem coeff_zero_multiset_prod : t.Prod.coeff 0 = (t.map fun f => coeff f 0).Prod :=
  by
  refine' Multiset.induction_on t _ fun a t ht => _; · simp
  rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, Polynomial.mul_coeff_zero, ht]
#align polynomial.coeff_zero_multiset_prod Polynomial.coeff_zero_multiset_prod

theorem coeff_zero_prod : (∏ i in s, f i).coeff 0 = ∏ i in s, (f i).coeff 0 := by
  simpa using coeff_zero_multiset_prod (s.1.map f)
#align polynomial.coeff_zero_prod Polynomial.coeff_zero_prod

end CommSemiring

section CommRing

variable [CommRing R]

open Monic

-- Eventually this can be generalized with Vieta's formulas
-- plus the connection between roots and factorization.
theorem multiset_prod_x_sub_c_nextCoeff (t : Multiset R) :
    nextCoeff (t.map fun x => X - C x).Prod = -t.Sum :=
  by
  rw [next_coeff_multiset_prod]
  · simp only [next_coeff_X_sub_C]
    exact t.sum_hom (-AddMonoidHom.id R)
  · intros
    apply monic_X_sub_C
#align polynomial.multiset_prod_X_sub_C_next_coeff Polynomial.multiset_prod_x_sub_c_nextCoeff

theorem prod_x_sub_c_nextCoeff {s : Finset ι} (f : ι → R) :
    nextCoeff (∏ i in s, X - C (f i)) = -∑ i in s, f i := by
  simpa using multiset_prod_X_sub_C_next_coeff (s.1.map f)
#align polynomial.prod_X_sub_C_next_coeff Polynomial.prod_x_sub_c_nextCoeff

theorem multiset_prod_x_sub_c_coeff_card_pred (t : Multiset R) (ht : 0 < t.card) :
    (t.map fun x => X - C x).Prod.coeff (t.card - 1) = -t.Sum :=
  by
  nontriviality R
  convert multiset_prod_X_sub_C_next_coeff (by assumption)
  rw [next_coeff]; split_ifs
  · rw [nat_degree_multiset_prod_of_monic] at h <;> simp only [Multiset.mem_map] at *
    swap
    · rintro _ ⟨_, _, rfl⟩
      apply monic_X_sub_C
    simp_rw [Multiset.sum_eq_zero_iff, Multiset.mem_map] at h
    contrapose! h
    obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp ht
    exact ⟨_, ⟨_, ⟨x, hx, rfl⟩, nat_degree_X_sub_C _⟩, one_ne_zero⟩
  congr ; rw [nat_degree_multiset_prod_of_monic] <;> · simp [nat_degree_X_sub_C, monic_X_sub_C]
#align polynomial.multiset_prod_X_sub_C_coeff_card_pred Polynomial.multiset_prod_x_sub_c_coeff_card_pred

theorem prod_x_sub_c_coeff_card_pred (s : Finset ι) (f : ι → R) (hs : 0 < s.card) :
    (∏ i in s, X - C (f i)).coeff (s.card - 1) = -∑ i in s, f i := by
  simpa using multiset_prod_X_sub_C_coeff_card_pred (s.1.map f) (by simpa using hs)
#align polynomial.prod_X_sub_C_coeff_card_pred Polynomial.prod_x_sub_c_coeff_card_pred

end CommRing

section NoZeroDivisors

section Semiring

variable [Semiring R] [NoZeroDivisors R]

/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
`[nontrivial R]` is needed, otherwise for `l = []` we have `⊥` in the LHS and `0` in the RHS.
-/
theorem degree_list_prod [Nontrivial R] (l : List R[X]) : l.Prod.degree = (l.map degree).Sum :=
  map_list_prod (@degreeMonoidHom R _ _ _) l
#align polynomial.degree_list_prod Polynomial.degree_list_prod

end Semiring

section CommSemiring

variable [CommSemiring R] [NoZeroDivisors R] (f : ι → R[X]) (t : Multiset R[X])

/-- The degree of a product of polynomials is equal to
the sum of the degrees.

See `polynomial.nat_degree_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem natDegree_prod (h : ∀ i ∈ s, f i ≠ 0) :
    (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree :=
  by
  nontriviality R
  apply nat_degree_prod'
  rw [prod_ne_zero_iff]
  intro x hx; simp [h x hx]
#align polynomial.nat_degree_prod Polynomial.natDegree_prod

theorem natDegree_multiset_prod (h : (0 : R[X]) ∉ t) : natDegree t.Prod = (t.map natDegree).Sum :=
  by
  nontriviality R
  rw [nat_degree_multiset_prod']
  simp_rw [Ne.def, Multiset.prod_eq_zero_iff, Multiset.mem_map, leading_coeff_eq_zero]
  rintro ⟨_, h, rfl⟩
  contradiction
#align polynomial.nat_degree_multiset_prod Polynomial.natDegree_multiset_prod

/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
theorem degree_multiset_prod [Nontrivial R] : t.Prod.degree = (t.map fun f => degree f).Sum :=
  map_multiset_prod (@degreeMonoidHom R _ _ _) _
#align polynomial.degree_multiset_prod Polynomial.degree_multiset_prod

/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
theorem degree_prod [Nontrivial R] : (∏ i in s, f i).degree = ∑ i in s, (f i).degree :=
  map_prod (@degreeMonoidHom R _ _ _) _ _
#align polynomial.degree_prod Polynomial.degree_prod

/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `polynomial.leading_coeff_multiset_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem leadingCoeff_multiset_prod : t.Prod.leadingCoeff = (t.map fun f => leadingCoeff f).Prod :=
  by
  rw [← leading_coeff_hom_apply, MonoidHom.map_multiset_prod]
  rfl
#align polynomial.leading_coeff_multiset_prod Polynomial.leadingCoeff_multiset_prod

/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `polynomial.leading_coeff_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem leadingCoeff_prod : (∏ i in s, f i).leadingCoeff = ∏ i in s, (f i).leadingCoeff := by
  simpa using leading_coeff_multiset_prod (s.1.map f)
#align polynomial.leading_coeff_prod Polynomial.leadingCoeff_prod

end CommSemiring

end NoZeroDivisors

end Polynomial

