/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
import Mathlib.Algebra.Order.WithZero
import Mathlib.Data.Polynomial.Monic

#align_import algebra.polynomial.big_operators from "leanprover-community/mathlib"@"47adfab39a11a072db552f47594bf8ed2cf8a722"

/-!
# Lemmas for the interaction between polynomials and `∑` and `∏`.

Recall that `∑` and `∏` are notation for `Finset.sum` and `Finset.prod` respectively.

## Main results

- `Polynomial.natDegree_prod_of_monic` : the degree of a product of monic polynomials is the
  product of degrees. We prove this only for `[CommSemiring R]`,
  but it ought to be true for `[Semiring R]` and `List.prod`.
- `Polynomial.natDegree_prod` : for polynomials over an integral domain,
  the degree of the product is the sum of degrees.
- `Polynomial.leadingCoeff_prod` : for polynomials over an integral domain,
  the leading coefficient is the product of leading coefficients.
- `Polynomial.prod_X_sub_C_coeff_card_pred` carries most of the content for computing
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

variable {S : Type*} [Semiring S]

theorem natDegree_list_sum_le (l : List S[X]) : natDegree l.sum ≤ (l.map natDegree).foldr max 0 :=
  List.sum_le_foldr_max natDegree (by simp) natDegree_add_le _
                                      -- 🎉 no goals
#align polynomial.nat_degree_list_sum_le Polynomial.natDegree_list_sum_le

theorem natDegree_multiset_sum_le (l : Multiset S[X]) :
    natDegree l.sum ≤ (l.map natDegree).foldr max max_left_comm 0 :=
  Quotient.inductionOn l (by simpa using natDegree_list_sum_le)
                             -- 🎉 no goals
#align polynomial.nat_degree_multiset_sum_le Polynomial.natDegree_multiset_sum_le

theorem natDegree_sum_le (f : ι → S[X]) :
    natDegree (∑ i in s, f i) ≤ s.fold max 0 (natDegree ∘ f) := by
  simpa using natDegree_multiset_sum_le (s.val.map f)
  -- 🎉 no goals
#align polynomial.nat_degree_sum_le Polynomial.natDegree_sum_le

theorem degree_list_sum_le (l : List S[X]) : degree l.sum ≤ (l.map natDegree).maximum := by
  by_cases h : l.sum = 0
  -- ⊢ degree (List.sum l) ≤ List.maximum (List.map natDegree l)
  · simp [h]
    -- 🎉 no goals
  · rw [degree_eq_natDegree h]
    -- ⊢ ↑(natDegree (List.sum l)) ≤ List.maximum (List.map natDegree l)
    suffices (l.map natDegree).maximum = ((l.map natDegree).foldr max 0 : ℕ) by
      rw [this]
      simpa [this, Nat.cast_withBot] using natDegree_list_sum_le l
    rw [← List.foldr_max_of_ne_nil]
    -- ⊢ ↑(List.foldr max ⊥ (List.map natDegree l)) = ↑(List.foldr max 0 (List.map na …
    · congr
      -- 🎉 no goals
    contrapose! h
    -- ⊢ List.sum l = 0
    rw [List.map_eq_nil] at h
    -- ⊢ List.sum l = 0
    simp [h]
    -- 🎉 no goals
#align polynomial.degree_list_sum_le Polynomial.degree_list_sum_le

theorem natDegree_list_prod_le (l : List S[X]) : natDegree l.prod ≤ (l.map natDegree).sum := by
  induction' l with hd tl IH
  -- ⊢ natDegree (List.prod []) ≤ List.sum (List.map natDegree [])
  · simp
    -- 🎉 no goals
  · simpa using natDegree_mul_le.trans (add_le_add_left IH _)
    -- 🎉 no goals
#align polynomial.nat_degree_list_prod_le Polynomial.natDegree_list_prod_le

theorem degree_list_prod_le (l : List S[X]) : degree l.prod ≤ (l.map degree).sum := by
  induction' l with hd tl IH
  -- ⊢ degree (List.prod []) ≤ List.sum (List.map degree [])
  · simp
    -- 🎉 no goals
  · simpa using (degree_mul_le _ _).trans (add_le_add_left IH _)
    -- 🎉 no goals
#align polynomial.degree_list_prod_le Polynomial.degree_list_prod_le

theorem coeff_list_prod_of_natDegree_le (l : List S[X]) (n : ℕ) (hl : ∀ p ∈ l, natDegree p ≤ n) :
    coeff (List.prod l) (l.length * n) = (l.map fun p => coeff p n).prod := by
  induction' l with hd tl IH
  -- ⊢ coeff (List.prod []) (List.length [] * n) = List.prod (List.map (fun p => co …
  · simp
    -- 🎉 no goals
  · have hl' : ∀ p ∈ tl, natDegree p ≤ n := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    -- ⊢ coeff (List.prod (hd :: tl)) (List.length (hd :: tl) * n) = List.prod (List. …
    simp only [List.prod_cons, List.map, List.length]
    -- ⊢ coeff (hd * List.prod tl) ((List.length tl + 1) * n) = coeff hd n * List.pro …
    rw [add_mul, one_mul, add_comm, ← IH hl', mul_comm tl.length]
    -- ⊢ coeff (hd * List.prod tl) (n + n * List.length tl) = coeff hd n * coeff (Lis …
    have h : natDegree tl.prod ≤ n * tl.length := by
      refine' (natDegree_list_prod_le _).trans _
      rw [← tl.length_map natDegree, mul_comm]
      refine' List.sum_le_card_nsmul _ _ _
      simpa using hl'
    have hdn : natDegree hd ≤ n := hl _ (List.mem_cons_self _ _)
    -- ⊢ coeff (hd * List.prod tl) (n + n * List.length tl) = coeff hd n * coeff (Lis …
    rcases hdn.eq_or_lt with (rfl | hdn')
    -- ⊢ coeff (hd * List.prod tl) (natDegree hd + natDegree hd * List.length tl) = c …
    · cases' h.eq_or_lt with h' h'
      -- ⊢ coeff (hd * List.prod tl) (natDegree hd + natDegree hd * List.length tl) = c …
      · rw [← h', coeff_mul_degree_add_degree, leadingCoeff, leadingCoeff]
        -- 🎉 no goals
      · rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt h', mul_zero]
        -- ⊢ natDegree (hd * List.prod tl) < natDegree hd + natDegree hd * List.length tl
        exact natDegree_mul_le.trans_lt (add_lt_add_left h' _)
        -- 🎉 no goals
    · rw [coeff_eq_zero_of_natDegree_lt hdn', coeff_eq_zero_of_natDegree_lt, zero_mul]
      -- ⊢ natDegree (hd * List.prod tl) < n + n * List.length tl
      exact natDegree_mul_le.trans_lt (add_lt_add_of_lt_of_le hdn' h)
      -- 🎉 no goals
#align polynomial.coeff_list_prod_of_nat_degree_le Polynomial.coeff_list_prod_of_natDegree_le

end Semiring

section CommSemiring

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

theorem natDegree_multiset_prod_le : t.prod.natDegree ≤ (t.map natDegree).sum :=
  Quotient.inductionOn t (by simpa using natDegree_list_prod_le)
                             -- 🎉 no goals
#align polynomial.nat_degree_multiset_prod_le Polynomial.natDegree_multiset_prod_le

theorem natDegree_prod_le : (∏ i in s, f i).natDegree ≤ ∑ i in s, (f i).natDegree := by
  simpa using natDegree_multiset_prod_le (s.1.map f)
  -- 🎉 no goals
#align polynomial.nat_degree_prod_le Polynomial.natDegree_prod_le

/-- The degree of a product of polynomials is at most the sum of the degrees,
where the degree of the zero polynomial is ⊥.
-/
theorem degree_multiset_prod_le : t.prod.degree ≤ (t.map Polynomial.degree).sum :=
  Quotient.inductionOn t (by simpa using degree_list_prod_le)
                             -- 🎉 no goals
#align polynomial.degree_multiset_prod_le Polynomial.degree_multiset_prod_le

theorem degree_prod_le : (∏ i in s, f i).degree ≤ ∑ i in s, (f i).degree := by
  simpa only [Multiset.map_map] using degree_multiset_prod_le (s.1.map f)
  -- 🎉 no goals
#align polynomial.degree_prod_le Polynomial.degree_prod_le

/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `Polynomial.leadingCoeff_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem leadingCoeff_multiset_prod' (h : (t.map leadingCoeff).prod ≠ 0) :
    t.prod.leadingCoeff = (t.map leadingCoeff).prod := by
  induction' t using Multiset.induction_on with a t ih; · simp
  -- ⊢ leadingCoeff (prod 0) = prod (Multiset.map leadingCoeff 0)
                                                          -- 🎉 no goals
  simp only [Multiset.map_cons, Multiset.prod_cons] at h ⊢
  -- ⊢ leadingCoeff (a * prod t) = leadingCoeff a * prod (Multiset.map leadingCoeff …
  rw [Polynomial.leadingCoeff_mul'] <;>
  -- ⊢ leadingCoeff a * leadingCoeff (prod t) = leadingCoeff a * prod (Multiset.map …
    · rw [ih]
      -- ⊢ prod (Multiset.map leadingCoeff t) ≠ 0
      -- ⊢ leadingCoeff a * prod (Multiset.map leadingCoeff t) ≠ 0
      -- ⊢ ¬prod (Multiset.map leadingCoeff t) = 0
      simp [*]
      -- 🎉 no goals
      -- ⊢ prod (Multiset.map leadingCoeff t) ≠ 0
      apply right_ne_zero_of_mul h
      -- 🎉 no goals
#align polynomial.leading_coeff_multiset_prod' Polynomial.leadingCoeff_multiset_prod'

/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `Polynomial.leadingCoeff_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem leadingCoeff_prod' (h : (∏ i in s, (f i).leadingCoeff) ≠ 0) :
    (∏ i in s, f i).leadingCoeff = ∏ i in s, (f i).leadingCoeff := by
  simpa using leadingCoeff_multiset_prod' (s.1.map f) (by simpa using h)
  -- 🎉 no goals
#align polynomial.leading_coeff_prod' Polynomial.leadingCoeff_prod'

/-- The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is nonzero.

See `Polynomial.natDegree_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem natDegree_multiset_prod' (h : (t.map fun f => leadingCoeff f).prod ≠ 0) :
    t.prod.natDegree = (t.map fun f => natDegree f).sum := by
  revert h
  -- ⊢ prod (Multiset.map (fun f => leadingCoeff f) t) ≠ 0 → natDegree (prod t) = M …
  refine' Multiset.induction_on t _ fun a t ih ht => _; · simp
  -- ⊢ prod (Multiset.map (fun f => leadingCoeff f) 0) ≠ 0 → natDegree (prod 0) = M …
                                                          -- 🎉 no goals
  rw [Multiset.map_cons, Multiset.prod_cons] at ht ⊢
  -- ⊢ natDegree (a * prod t) = Multiset.sum (natDegree a ::ₘ Multiset.map (fun f = …
  rw [Multiset.sum_cons, Polynomial.natDegree_mul', ih]
  -- ⊢ prod (Multiset.map (fun f => leadingCoeff f) t) ≠ 0
  · apply right_ne_zero_of_mul ht
    -- 🎉 no goals
  · rwa [Polynomial.leadingCoeff_multiset_prod']
    -- ⊢ prod (Multiset.map leadingCoeff t) ≠ 0
    apply right_ne_zero_of_mul ht
    -- 🎉 no goals
#align polynomial.nat_degree_multiset_prod' Polynomial.natDegree_multiset_prod'

/-- The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is nonzero.

See `Polynomial.natDegree_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem natDegree_prod' (h : (∏ i in s, (f i).leadingCoeff) ≠ 0) :
    (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree := by
  simpa using natDegree_multiset_prod' (s.1.map f) (by simpa using h)
  -- 🎉 no goals
#align polynomial.nat_degree_prod' Polynomial.natDegree_prod'

theorem natDegree_multiset_prod_of_monic (h : ∀ f ∈ t, Monic f) :
    t.prod.natDegree = (t.map natDegree).sum := by
  nontriviality R
  -- ⊢ natDegree (prod t) = Multiset.sum (Multiset.map natDegree t)
  apply natDegree_multiset_prod'
  -- ⊢ prod (Multiset.map (fun f => leadingCoeff f) t) ≠ 0
  suffices (t.map fun f => leadingCoeff f).prod = 1 by
    rw [this]
    simp
  convert prod_replicate (Multiset.card t) (1 : R)
  -- ⊢ Multiset.map (fun f => leadingCoeff f) t = replicate (↑Multiset.card t) 1
  · simp only [eq_replicate, Multiset.card_map, eq_self_iff_true, true_and_iff]
    -- ⊢ ∀ (b : R), b ∈ Multiset.map (fun f => leadingCoeff f) t → b = 1
    rintro i hi
    -- ⊢ i = 1
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hi
    -- ⊢ leadingCoeff i = 1
    apply h
    -- ⊢ i ∈ t
    assumption
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align polynomial.nat_degree_multiset_prod_of_monic Polynomial.natDegree_multiset_prod_of_monic

theorem natDegree_prod_of_monic (h : ∀ i ∈ s, (f i).Monic) :
    (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree := by
  simpa using natDegree_multiset_prod_of_monic (s.1.map f) (by simpa using h)
  -- 🎉 no goals
#align polynomial.nat_degree_prod_of_monic Polynomial.natDegree_prod_of_monic

theorem coeff_multiset_prod_of_natDegree_le (n : ℕ) (hl : ∀ p ∈ t, natDegree p ≤ n) :
    coeff t.prod ((Multiset.card t) * n) = (t.map fun p => coeff p n).prod := by
  induction t using Quotient.inductionOn
  -- ⊢ coeff (prod (Quotient.mk (List.isSetoid R[X]) a✝)) (↑Multiset.card (Quotient …
  simpa using coeff_list_prod_of_natDegree_le _ _ hl
  -- 🎉 no goals
#align polynomial.coeff_multiset_prod_of_nat_degree_le Polynomial.coeff_multiset_prod_of_natDegree_le

theorem coeff_prod_of_natDegree_le (f : ι → R[X]) (n : ℕ) (h : ∀ p ∈ s, natDegree (f p) ≤ n) :
    coeff (∏ i in s, f i) (s.card * n) = ∏ i in s, coeff (f i) n := by
  cases' s with l hl
  -- ⊢ coeff (∏ i in { val := l, nodup := hl }, f i) (Finset.card { val := l, nodup …
  convert coeff_multiset_prod_of_natDegree_le (l.map f) n ?_
  · simp
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
  · simpa using h
    -- 🎉 no goals
#align polynomial.coeff_prod_of_nat_degree_le Polynomial.coeff_prod_of_natDegree_le

theorem coeff_zero_multiset_prod : t.prod.coeff 0 = (t.map fun f => coeff f 0).prod := by
  refine' Multiset.induction_on t _ fun a t ht => _; · simp
  -- ⊢ coeff (prod 0) 0 = prod (Multiset.map (fun f => coeff f 0) 0)
                                                       -- 🎉 no goals
  rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, Polynomial.mul_coeff_zero, ht]
  -- 🎉 no goals
#align polynomial.coeff_zero_multiset_prod Polynomial.coeff_zero_multiset_prod

theorem coeff_zero_prod : (∏ i in s, f i).coeff 0 = ∏ i in s, (f i).coeff 0 := by
  simpa using coeff_zero_multiset_prod (s.1.map f)
  -- 🎉 no goals
#align polynomial.coeff_zero_prod Polynomial.coeff_zero_prod

end CommSemiring

section CommRing

variable [CommRing R]

open Monic

-- Eventually this can be generalized with Vieta's formulas
-- plus the connection between roots and factorization.
theorem multiset_prod_X_sub_C_nextCoeff (t : Multiset R) :
    nextCoeff (t.map fun x => X - C x).prod = -t.sum := by
  rw [nextCoeff_multiset_prod]
  -- ⊢ Multiset.sum (Multiset.map (fun i => nextCoeff (X - ↑C i)) t) = -Multiset.su …
  · simp only [nextCoeff_X_sub_C]
    -- ⊢ Multiset.sum (Multiset.map (fun x => -x) t) = -Multiset.sum t
    exact t.sum_hom (-AddMonoidHom.id R)
    -- 🎉 no goals
  · intros
    -- ⊢ Monic (X - ↑C i✝)
    apply monic_X_sub_C
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.multiset_prod_X_sub_C_next_coeff Polynomial.multiset_prod_X_sub_C_nextCoeff

theorem prod_X_sub_C_nextCoeff {s : Finset ι} (f : ι → R) :
    nextCoeff (∏ i in s, (X - C (f i))) = -∑ i in s, f i := by
  simpa using multiset_prod_X_sub_C_nextCoeff (s.1.map f)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.prod_X_sub_C_next_coeff Polynomial.prod_X_sub_C_nextCoeff

theorem multiset_prod_X_sub_C_coeff_card_pred (t : Multiset R) (ht : 0 < Multiset.card t) :
    (t.map fun x => X - C x).prod.coeff ((Multiset.card t) - 1) = -t.sum := by
  nontriviality R
  -- ⊢ coeff (prod (Multiset.map (fun x => X - ↑C x) t)) (↑Multiset.card t - 1) = - …
  convert multiset_prod_X_sub_C_nextCoeff (by assumption)
  -- ⊢ coeff (prod (Multiset.map (fun x => X - ↑C x) t)) (↑Multiset.card t - 1) = n …
  rw [nextCoeff]; split_ifs with h
  -- ⊢ coeff (prod (Multiset.map (fun x => X - ↑C x) t)) (↑Multiset.card t - 1) = i …
                  -- ⊢ coeff (prod (Multiset.map (fun x => X - ↑C x) t)) (↑Multiset.card t - 1) = 0
  · rw [natDegree_multiset_prod_of_monic] at h <;> simp only [Multiset.mem_map] at *
    -- ⊢ coeff (prod (Multiset.map (fun x => X - ↑C x) t)) (↑Multiset.card t - 1) = 0
                                                   -- ⊢ coeff (prod (Multiset.map (fun x => X - ↑C x) t)) (↑Multiset.card t - 1) = 0
                                                   -- ⊢ ∀ (f : R[X]), (∃ a, a ∈ t ∧ X - ↑C a = f) → Monic f
    swap
    -- ⊢ ∀ (f : R[X]), (∃ a, a ∈ t ∧ X - ↑C a = f) → Monic f
    · rintro _ ⟨_, _, rfl⟩
      -- ⊢ Monic (X - ↑C w✝)
      apply monic_X_sub_C
      -- 🎉 no goals
    simp_rw [Multiset.sum_eq_zero_iff, Multiset.mem_map] at h
    -- ⊢ coeff (prod (Multiset.map (fun x => X - ↑C x) t)) (↑Multiset.card t - 1) = 0
    contrapose! h
    -- ⊢ ∃ x, (∃ a, (∃ a_1, a_1 ∈ t ∧ X - ↑C a_1 = a) ∧ natDegree a = x) ∧ x ≠ 0
    obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp ht
    -- ⊢ ∃ x, (∃ a, (∃ a_1, a_1 ∈ t ∧ X - ↑C a_1 = a) ∧ natDegree a = x) ∧ x ≠ 0
    exact ⟨_, ⟨_, ⟨x, hx, rfl⟩, natDegree_X_sub_C _⟩, one_ne_zero⟩
    -- 🎉 no goals
  congr; rw [natDegree_multiset_prod_of_monic] <;> · simp [natDegree_X_sub_C, monic_X_sub_C]
  -- ⊢ ↑Multiset.card t = natDegree (prod (Multiset.map (fun x => X - ↑C x) t))
         -- ⊢ ↑Multiset.card t = Multiset.sum (Multiset.map natDegree (Multiset.map (fun x …
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.multiset_prod_X_sub_C_coeff_card_pred Polynomial.multiset_prod_X_sub_C_coeff_card_pred

theorem prod_X_sub_C_coeff_card_pred (s : Finset ι) (f : ι → R) (hs : 0 < s.card) :
    (∏ i in s, (X - C (f i))).coeff (s.card - 1) = -∑ i in s, f i := by
  simpa using multiset_prod_X_sub_C_coeff_card_pred (s.1.map f) (by simpa using hs)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.prod_X_sub_C_coeff_card_pred Polynomial.prod_X_sub_C_coeff_card_pred

end CommRing

section NoZeroDivisors

section Semiring

variable [Semiring R] [NoZeroDivisors R]

/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
`[Nontrivial R]` is needed, otherwise for `l = []` we have `⊥` in the LHS and `0` in the RHS.
-/
theorem degree_list_prod [Nontrivial R] (l : List R[X]) : l.prod.degree = (l.map degree).sum :=
  map_list_prod (@degreeMonoidHom R _ _ _) l
#align polynomial.degree_list_prod Polynomial.degree_list_prod

end Semiring

section CommSemiring

variable [CommSemiring R] [NoZeroDivisors R] (f : ι → R[X]) (t : Multiset R[X])

/-- The degree of a product of polynomials is equal to
the sum of the degrees.

See `Polynomial.natDegree_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem natDegree_prod (h : ∀ i ∈ s, f i ≠ 0) :
    (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree := by
  nontriviality R
  -- ⊢ natDegree (∏ i in s, f i) = ∑ i in s, natDegree (f i)
  apply natDegree_prod'
  -- ⊢ ∏ i in s, leadingCoeff (f i) ≠ 0
  rw [prod_ne_zero_iff]
  -- ⊢ ∀ (a : ι), a ∈ s → leadingCoeff (f a) ≠ 0
  intro x hx; simp [h x hx]
  -- ⊢ leadingCoeff (f x) ≠ 0
              -- 🎉 no goals
#align polynomial.nat_degree_prod Polynomial.natDegree_prod

theorem natDegree_multiset_prod (h : (0 : R[X]) ∉ t) :
    natDegree t.prod = (t.map natDegree).sum := by
  nontriviality R
  -- ⊢ natDegree (prod t) = Multiset.sum (Multiset.map natDegree t)
  rw [natDegree_multiset_prod']
  -- ⊢ prod (Multiset.map (fun f => leadingCoeff f) t) ≠ 0
  simp_rw [Ne.def, Multiset.prod_eq_zero_iff, Multiset.mem_map, leadingCoeff_eq_zero]
  -- ⊢ ¬∃ a, a ∈ t ∧ a = 0
  rintro ⟨_, h, rfl⟩
  -- ⊢ False
  contradiction
  -- 🎉 no goals
#align polynomial.nat_degree_multiset_prod Polynomial.natDegree_multiset_prod

/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
theorem degree_multiset_prod [Nontrivial R] : t.prod.degree = (t.map fun f => degree f).sum :=
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

See `Polynomial.leadingCoeff_multiset_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem leadingCoeff_multiset_prod :
    t.prod.leadingCoeff = (t.map fun f => leadingCoeff f).prod := by
  rw [← leadingCoeffHom_apply, MonoidHom.map_multiset_prod]
  -- ⊢ prod (Multiset.map (↑leadingCoeffHom) t) = prod (Multiset.map (fun f => lead …
  rfl
  -- 🎉 no goals
#align polynomial.leading_coeff_multiset_prod Polynomial.leadingCoeff_multiset_prod

/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `Polynomial.leadingCoeff_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem leadingCoeff_prod : (∏ i in s, f i).leadingCoeff = ∏ i in s, (f i).leadingCoeff := by
  simpa using leadingCoeff_multiset_prod (s.1.map f)
  -- 🎉 no goals
#align polynomial.leading_coeff_prod Polynomial.leadingCoeff_prod

end CommSemiring

end NoZeroDivisors

end Polynomial
