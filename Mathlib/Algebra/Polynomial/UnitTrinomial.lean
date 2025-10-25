/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Polynomial.Mirror
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Int.Order.Units
import Mathlib.RingTheory.Coprime.Basic

/-!
# Unit Trinomials

This file defines irreducible trinomials and proves an irreducibility criterion.

## Main definitions

- `Polynomial.IsUnitTrinomial`

## Main results

- `Polynomial.IsUnitTrinomial.irreducible_of_coprime`: An irreducibility criterion for unit
  trinomials.

-/

assert_not_exists TopologicalSpace

namespace Polynomial

open scoped Polynomial

open Finset

section Semiring

variable {R : Type*} [Semiring R] (k m n : ℕ) (u v w : R)

/-- Shorthand for a trinomial -/
noncomputable def trinomial :=
  C u * X ^ k + C v * X ^ m + C w * X ^ n

theorem trinomial_def : trinomial k m n u v w = C u * X ^ k + C v * X ^ m + C w * X ^ n :=
  rfl

variable {k m n u v w}

theorem trinomial_leading_coeff' (hkm : k < m) (hmn : m < n) :
    (trinomial k m n u v w).coeff n = w := by
  rw [trinomial_def, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    if_neg (hkm.trans hmn).ne', if_neg hmn.ne', if_pos rfl, zero_add, zero_add]

theorem trinomial_middle_coeff (hkm : k < m) (hmn : m < n) :
    (trinomial k m n u v w).coeff m = v := by
  rw [trinomial_def, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    if_neg hkm.ne', if_pos rfl, if_neg hmn.ne, zero_add, add_zero]

theorem trinomial_trailing_coeff' (hkm : k < m) (hmn : m < n) :
    (trinomial k m n u v w).coeff k = u := by
  rw [trinomial_def, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    if_pos rfl, if_neg hkm.ne, if_neg (hkm.trans hmn).ne, add_zero, add_zero]

theorem trinomial_natDegree (hkm : k < m) (hmn : m < n) (hw : w ≠ 0) :
    (trinomial k m n u v w).natDegree = n := by
  refine
    natDegree_eq_of_degree_eq_some
      ((Finset.sup_le fun i h => ?_).antisymm <|
        le_degree_of_ne_zero <| by rwa [trinomial_leading_coeff' hkm hmn])
  replace h := support_trinomial' k m n u v w h
  rw [mem_insert, mem_insert, mem_singleton] at h
  rcases h with (rfl | rfl | rfl)
  · exact WithBot.coe_le_coe.mpr (hkm.trans hmn).le
  · exact WithBot.coe_le_coe.mpr hmn.le
  · exact le_rfl

theorem trinomial_natTrailingDegree (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) :
    (trinomial k m n u v w).natTrailingDegree = k := by
  refine
    natTrailingDegree_eq_of_trailingDegree_eq_some
      ((Finset.le_inf fun i h => ?_).antisymm <|
          trailingDegree_le_of_ne_zero <| by rwa [trinomial_trailing_coeff' hkm hmn]).symm
  replace h := support_trinomial' k m n u v w h
  rw [mem_insert, mem_insert, mem_singleton] at h
  rcases h with (rfl | rfl | rfl)
  · exact le_rfl
  · exact WithTop.coe_le_coe.mpr hkm.le
  · exact WithTop.coe_le_coe.mpr (hkm.trans hmn).le

theorem trinomial_leadingCoeff (hkm : k < m) (hmn : m < n) (hw : w ≠ 0) :
    (trinomial k m n u v w).leadingCoeff = w := by
  rw [leadingCoeff, trinomial_natDegree hkm hmn hw, trinomial_leading_coeff' hkm hmn]

theorem trinomial_trailingCoeff (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) :
    (trinomial k m n u v w).trailingCoeff = u := by
  rw [trailingCoeff, trinomial_natTrailingDegree hkm hmn hu, trinomial_trailing_coeff' hkm hmn]

theorem trinomial_monic (hkm : k < m) (hmn : m < n) : (trinomial k m n u v 1).Monic := by
  nontriviality R
  exact trinomial_leadingCoeff hkm hmn one_ne_zero

theorem trinomial_mirror (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) (hw : w ≠ 0) :
    (trinomial k m n u v w).mirror = trinomial k (n - m + k) n w v u := by
  rw [mirror, trinomial_natTrailingDegree hkm hmn hu, reverse, trinomial_natDegree hkm hmn hw,
    trinomial_def, reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
    reflect_C_mul_X_pow, revAt_le (hkm.trans hmn).le, revAt_le hmn.le, revAt_le le_rfl, add_mul,
    add_mul, mul_assoc, mul_assoc, mul_assoc, ← pow_add, ← pow_add, ← pow_add,
    Nat.sub_add_cancel (hkm.trans hmn).le, Nat.sub_self, zero_add, add_comm, add_comm (C u * X ^ n),
    ← add_assoc, ← trinomial_def]

theorem trinomial_support (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    (trinomial k m n u v w).support = {k, m, n} :=
  support_trinomial hkm hmn hu hv hw

end Semiring

variable (p q : ℤ[X])

/-- A unit trinomial is a trinomial with unit coefficients. -/
def IsUnitTrinomial :=
  ∃ (k m n : ℕ) (_ : k < m) (_ : m < n) (u v w : Units ℤ), p = trinomial k m n (u : ℤ) v w

variable {p q}

namespace IsUnitTrinomial

theorem not_isUnit (hp : p.IsUnitTrinomial) : ¬IsUnit p := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  exact fun h =>
    ne_zero_of_lt hmn
      ((trinomial_natDegree hkm hmn w.ne_zero).symm.trans
        (natDegree_eq_of_degree_eq_some (degree_eq_zero_of_isUnit h)))

theorem card_support_eq_three (hp : p.IsUnitTrinomial) : #p.support = 3 := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  exact card_support_trinomial hkm hmn u.ne_zero v.ne_zero w.ne_zero

theorem ne_zero (hp : p.IsUnitTrinomial) : p ≠ 0 := by
  rintro rfl
  simpa using hp.card_support_eq_three

theorem coeff_isUnit (hp : p.IsUnitTrinomial) {k : ℕ} (hk : k ∈ p.support) :
    IsUnit (p.coeff k) := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  have := support_trinomial' k m n (u : ℤ) v w hk
  rw [mem_insert, mem_insert, mem_singleton] at this
  rcases this with (rfl | rfl | rfl)
  · refine ⟨u, by rw [trinomial_trailing_coeff' hkm hmn]⟩
  · refine ⟨v, by rw [trinomial_middle_coeff hkm hmn]⟩
  · refine ⟨w, by rw [trinomial_leading_coeff' hkm hmn]⟩

theorem leadingCoeff_isUnit (hp : p.IsUnitTrinomial) : IsUnit p.leadingCoeff :=
  hp.coeff_isUnit (natDegree_mem_support_of_nonzero hp.ne_zero)

theorem trailingCoeff_isUnit (hp : p.IsUnitTrinomial) : IsUnit p.trailingCoeff :=
  hp.coeff_isUnit (natTrailingDegree_mem_support_of_nonzero hp.ne_zero)

end IsUnitTrinomial

theorem isUnitTrinomial_iff :
    p.IsUnitTrinomial ↔ #p.support = 3 ∧ ∀ k ∈ p.support, IsUnit (p.coeff k) := by
  refine ⟨fun hp => ⟨hp.card_support_eq_three, fun k => hp.coeff_isUnit⟩, fun hp => ?_⟩
  obtain ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩ := card_support_eq_three.mp hp.1
  rw [support_trinomial hkm hmn hx hy hz] at hp
  replace hx := hp.2 k (mem_insert_self k {m, n})
  replace hy := hp.2 m (mem_insert_of_mem (mem_insert_self m {n}))
  replace hz := hp.2 n (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n)))
  simp_rw [coeff_add, coeff_C_mul, coeff_X_pow_self, mul_one, coeff_X_pow] at hx hy hz
  rw [if_neg hkm.ne, if_neg (hkm.trans hmn).ne] at hx
  rw [if_neg hkm.ne', if_neg hmn.ne] at hy
  rw [if_neg (hkm.trans hmn).ne', if_neg hmn.ne'] at hz
  simp_rw [mul_zero, zero_add, add_zero] at hx hy hz
  exact ⟨k, m, n, hkm, hmn, hx.unit, hy.unit, hz.unit, rfl⟩

theorem isUnitTrinomial_iff' :
    p.IsUnitTrinomial ↔
      (p * p.mirror).coeff (((p * p.mirror).natDegree + (p * p.mirror).natTrailingDegree) / 2) =
        3 := by
  rw [natDegree_mul_mirror, natTrailingDegree_mul_mirror, ← mul_add,
    Nat.mul_div_right _ zero_lt_two, coeff_mul_mirror]
  refine ⟨?_, fun hp => ?_⟩
  · rintro ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩
    rw [sum_def, trinomial_support hkm hmn u.ne_zero v.ne_zero w.ne_zero,
      sum_insert (mt mem_insert.mp (not_or_intro hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne))),
      sum_insert (mt mem_singleton.mp hmn.ne), sum_singleton, trinomial_leading_coeff' hkm hmn,
      trinomial_middle_coeff hkm hmn, trinomial_trailing_coeff' hkm hmn]
    simp_rw [← Units.val_pow_eq_pow_val, Int.units_sq, Units.val_one]
    decide
  · have key : ∀ k ∈ p.support, p.coeff k ^ 2 = 1 := fun k hk =>
      Int.sq_eq_one_of_sq_le_three
        ((single_le_sum (fun k _ => sq_nonneg (p.coeff k)) hk).trans hp.le) (mem_support_iff.mp hk)
    refine isUnitTrinomial_iff.mpr ⟨?_, fun k hk => .of_pow_eq_one (key k hk) two_ne_zero⟩
    rw [sum_def, sum_congr rfl key, sum_const, Nat.smul_one_eq_cast] at hp
    exact Nat.cast_injective hp

theorem isUnitTrinomial_iff'' (h : p * p.mirror = q * q.mirror) :
    p.IsUnitTrinomial ↔ q.IsUnitTrinomial := by
  rw [isUnitTrinomial_iff', isUnitTrinomial_iff', h]

namespace IsUnitTrinomial

theorem irreducible_aux1 {k m n : ℕ} (hkm : k < m) (hmn : m < n) (u v w : Units ℤ)
    (hp : p = trinomial k m n (u : ℤ) v w) :
    C (v : ℤ) * (C (u : ℤ) * X ^ (m + n) + C (w : ℤ) * X ^ (n - m + k + n)) =
      ⟨Finsupp.filter (· ∈ Set.Ioo (k + n) (n + n)) (p * p.mirror).toFinsupp⟩ := by
  have key : n - m + k < n := by rwa [← lt_tsub_iff_right, tsub_lt_tsub_iff_left_of_le hmn.le]
  rw [hp, trinomial_mirror hkm hmn u.ne_zero w.ne_zero]
  simp_rw [trinomial_def, C_mul_X_pow_eq_monomial, add_mul, mul_add, monomial_mul_monomial,
    toFinsupp_add, toFinsupp_monomial, AddMonoidAlgebra, Finsupp.filter_add]
  rw [Finsupp.filter_single_of_neg, Finsupp.filter_single_of_neg, Finsupp.filter_single_of_neg,
    Finsupp.filter_single_of_neg, Finsupp.filter_single_of_neg, Finsupp.filter_single_of_pos,
    Finsupp.filter_single_of_neg, Finsupp.filter_single_of_pos, Finsupp.filter_single_of_neg]
  · simp only [add_zero, zero_add]
    -- Porting note: the next `rw` is needed to see through the defeq `Finsupp = AddMonoidAlgebra`
    rw [ofFinsupp_add]
    simp only [ofFinsupp_single]
    rw [C_mul_monomial, C_mul_monomial, mul_comm (v : ℤ) w, add_comm (n - m + k) n]
  · exact fun h => h.2.ne rfl
  · refine ⟨?_, by gcongr⟩
    rwa [add_comm, add_lt_add_iff_left, lt_add_iff_pos_left, tsub_pos_iff_lt]
  · exact fun h => h.1.ne (add_comm k n)
  · constructor <;> gcongr
  · rw [← add_assoc, add_tsub_cancel_of_le hmn.le, add_comm]
    exact fun h => h.1.ne rfl
  · grind
  · exact fun h => h.1.ne rfl
  · exact fun h => asymm ((add_lt_add_iff_left k).mp h.1) key
  · exact fun h => asymm ((add_lt_add_iff_left k).mp h.1) (hkm.trans hmn)

theorem irreducible_aux2 {k m m' n : ℕ} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
    (u v w : Units ℤ) (hp : p = trinomial k m n (u : ℤ) v w) (hq : q = trinomial k m' n (u : ℤ) v w)
    (h : p * p.mirror = q * q.mirror) : q = p ∨ q = p.mirror := by
  let f : ℤ[X] → ℤ[X] := fun p => ⟨Finsupp.filter (· ∈ Set.Ioo (k + n) (n + n)) p.toFinsupp⟩
  replace h := congr_arg f h
  replace h := (irreducible_aux1 hkm hmn u v w hp).trans h
  replace h := h.trans (irreducible_aux1 hkm' hmn' u v w hq).symm
  rw [(isUnit_C.mpr v.isUnit).mul_right_inj] at h
  rw [binomial_eq_binomial u.ne_zero w.ne_zero] at h
  simp only [add_left_inj, Units.val_inj] at h
  rcases h with (⟨rfl, -⟩ | ⟨rfl, rfl, h⟩ | ⟨-, hm, hm'⟩)
  · exact Or.inl (hq.trans hp.symm)
  · refine Or.inr ?_
    rw [← trinomial_mirror hkm' hmn' u.ne_zero u.ne_zero, eq_comm, mirror_eq_iff] at hp
    exact hq.trans hp
  · grind

theorem irreducible_aux3 {k m m' n : ℕ} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
    (u v w x z : Units ℤ) (hp : p = trinomial k m n (u : ℤ) v w)
    (hq : q = trinomial k m' n (x : ℤ) v z) (h : p * p.mirror = q * q.mirror) :
    q = p ∨ q = p.mirror := by
  have hmul := congr_arg leadingCoeff h
  rw [leadingCoeff_mul, leadingCoeff_mul, mirror_leadingCoeff, mirror_leadingCoeff, hp, hq,
    trinomial_leadingCoeff hkm hmn w.ne_zero, trinomial_leadingCoeff hkm' hmn' z.ne_zero,
    trinomial_trailingCoeff hkm hmn u.ne_zero, trinomial_trailingCoeff hkm' hmn' x.ne_zero]
    at hmul
  have hadd := congr_arg (eval 1) h
  rw [eval_mul, eval_mul, mirror_eval_one, mirror_eval_one, ← sq, ← sq, hp, hq] at hadd
  simp only [eval_add, eval_C_mul, eval_X_pow, one_pow, mul_one, trinomial_def] at hadd
  rw [add_assoc, add_assoc, add_comm (u : ℤ), add_comm (x : ℤ), add_assoc, add_assoc] at hadd
  simp only [add_sq', add_assoc, add_right_inj, ← Units.val_pow_eq_pow_val, Int.units_sq] at hadd
  rw [mul_assoc, hmul, ← mul_assoc, add_right_inj,
    mul_right_inj' (show 2 * (v : ℤ) ≠ 0 from mul_ne_zero two_ne_zero v.ne_zero)] at hadd
  replace hadd :=
    (Int.isUnit_add_isUnit_eq_isUnit_add_isUnit w.isUnit u.isUnit z.isUnit x.isUnit).mp hadd
  simp only [Units.val_inj] at hadd
  rcases hadd with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact irreducible_aux2 hkm hmn hkm' hmn' u v w hp hq h
  · rw [← mirror_inj, trinomial_mirror hkm' hmn' w.ne_zero u.ne_zero] at hq
    rw [mul_comm q, ← q.mirror_mirror, q.mirror.mirror_mirror] at h
    rw [← mirror_inj, or_comm, ← mirror_eq_iff]
    exact
      irreducible_aux2 hkm hmn (lt_add_of_pos_left k (tsub_pos_of_lt hmn'))
        (lt_tsub_iff_right.mp ((tsub_lt_tsub_iff_left_of_le hmn'.le).mpr hkm')) u v w hp hq h

theorem irreducible_of_coprime (hp : p.IsUnitTrinomial)
    (h : IsRelPrime p p.mirror) : Irreducible p := by
  refine irreducible_of_mirror hp.not_isUnit (fun q hpq => ?_) h
  have hq : IsUnitTrinomial q := (isUnitTrinomial_iff'' hpq).mp hp
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hp⟩ := hp
  obtain ⟨k', m', n', hkm', hmn', x, y, z, hq⟩ := hq
  have hk : k = k' := by
    rw [← mul_right_inj' (show 2 ≠ 0 from two_ne_zero), ←
      trinomial_natTrailingDegree hkm hmn u.ne_zero, ← hp, ← natTrailingDegree_mul_mirror, hpq,
      natTrailingDegree_mul_mirror, hq, trinomial_natTrailingDegree hkm' hmn' x.ne_zero]
  have hn : n = n' := by
    rw [← mul_right_inj' (show 2 ≠ 0 from two_ne_zero), ← trinomial_natDegree hkm hmn w.ne_zero, ←
      hp, ← natDegree_mul_mirror, hpq, natDegree_mul_mirror, hq,
      trinomial_natDegree hkm' hmn' z.ne_zero]
  subst hk
  subst hn
  rcases eq_or_eq_neg_of_sq_eq_sq (y : ℤ) (v : ℤ)
      ((Int.isUnit_sq y.isUnit).trans (Int.isUnit_sq v.isUnit).symm) with
    (h1 | h1)
  · rw [h1] at hq
    rcases irreducible_aux3 hkm hmn hkm' hmn' u v w x z hp hq hpq with (h2 | h2)
    · exact Or.inl h2
    · exact Or.inr (Or.inr (Or.inl h2))
  · rw [h1] at hq
    rw [trinomial_def] at hp
    rw [← neg_inj, neg_add, neg_add, ← neg_mul, ← neg_mul, ← neg_mul, ← C_neg, ← C_neg, ← C_neg]
      at hp
    rw [← neg_mul_neg, ← mirror_neg] at hpq
    rcases irreducible_aux3 hkm hmn hkm' hmn' (-u) (-v) (-w) x z hp hq hpq with (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr p.mirror_neg))

/-- A unit trinomial is irreducible if it is coprime with its mirror -/
theorem irreducible_of_isCoprime (hp : p.IsUnitTrinomial) (h : IsCoprime p p.mirror) :
    Irreducible p :=
  irreducible_of_coprime hp fun _ => h.isUnit_of_dvd'

end IsUnitTrinomial

end Polynomial
