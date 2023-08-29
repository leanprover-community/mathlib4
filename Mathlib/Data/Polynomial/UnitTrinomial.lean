/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.Polynomial.Mirror

#align_import data.polynomial.unit_trinomial from "leanprover-community/mathlib"@"302eab4f46abb63de520828de78c04cb0f9b5836"

/-!
# Unit Trinomials

This file defines irreducible trinomials and proves an irreducibility criterion.

## Main definitions

- `Polynomial.IsUnitTrinomial`

## Main results

- `Polynomial.IsUnitTrinomial.irreducible_of_coprime`: An irreducibility criterion for unit
  trinomials.

-/


namespace Polynomial

open scoped Polynomial

open Finset

section Semiring

variable {R : Type*} [Semiring R] (k m n : ℕ) (u v w : R)

/-- Shorthand for a trinomial -/
noncomputable def trinomial :=
  C u * X ^ k + C v * X ^ m + C w * X ^ n
#align polynomial.trinomial Polynomial.trinomial

theorem trinomial_def : trinomial k m n u v w = C u * X ^ k + C v * X ^ m + C w * X ^ n :=
  rfl
#align polynomial.trinomial_def Polynomial.trinomial_def

variable {k m n u v w}

theorem trinomial_leading_coeff' (hkm : k < m) (hmn : m < n) :
    (trinomial k m n u v w).coeff n = w := by
  rw [trinomial_def, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    if_neg (hkm.trans hmn).ne', if_neg hmn.ne', if_pos rfl, zero_add, zero_add]
#align polynomial.trinomial_leading_coeff' Polynomial.trinomial_leading_coeff'

theorem trinomial_middle_coeff (hkm : k < m) (hmn : m < n) :
    (trinomial k m n u v w).coeff m = v := by
  rw [trinomial_def, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    if_neg hkm.ne', if_pos rfl, if_neg hmn.ne, zero_add, add_zero]
#align polynomial.trinomial_middle_coeff Polynomial.trinomial_middle_coeff

theorem trinomial_trailing_coeff' (hkm : k < m) (hmn : m < n) :
    (trinomial k m n u v w).coeff k = u := by
  rw [trinomial_def, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    if_pos rfl, if_neg hkm.ne, if_neg (hkm.trans hmn).ne, add_zero, add_zero]
#align polynomial.trinomial_trailing_coeff' Polynomial.trinomial_trailing_coeff'

theorem trinomial_natDegree (hkm : k < m) (hmn : m < n) (hw : w ≠ 0) :
    (trinomial k m n u v w).natDegree = n := by
  refine'
    natDegree_eq_of_degree_eq_some
      ((Finset.sup_le fun i h => _).antisymm <|
        le_degree_of_ne_zero <| by rwa [trinomial_leading_coeff' hkm hmn])
  replace h := support_trinomial' k m n u v w h
  -- ⊢ ↑i ≤ ↑n
  rw [mem_insert, mem_insert, mem_singleton] at h
  -- ⊢ ↑i ≤ ↑n
  rcases h with (rfl | rfl | rfl)
  · exact WithBot.coe_le_coe.mpr (hkm.trans hmn).le
    -- 🎉 no goals
  · exact WithBot.coe_le_coe.mpr hmn.le
    -- 🎉 no goals
  · exact le_rfl
    -- 🎉 no goals
#align polynomial.trinomial_nat_degree Polynomial.trinomial_natDegree

theorem trinomial_natTrailingDegree (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) :
    (trinomial k m n u v w).natTrailingDegree = k := by
  refine'
    natTrailingDegree_eq_of_trailingDegree_eq_some
      ((Finset.le_inf fun i h => _).antisymm <|
          le_trailingDegree_of_ne_zero <| by rwa [trinomial_trailing_coeff' hkm hmn]).symm
  replace h := support_trinomial' k m n u v w h
  -- ⊢ ↑k ≤ ↑i
  rw [mem_insert, mem_insert, mem_singleton] at h
  -- ⊢ ↑k ≤ ↑i
  rcases h with (rfl | rfl | rfl)
  · exact le_rfl
    -- 🎉 no goals
  · exact WithTop.coe_le_coe.mpr hkm.le
    -- 🎉 no goals
  · exact WithTop.coe_le_coe.mpr (hkm.trans hmn).le
    -- 🎉 no goals
#align polynomial.trinomial_nat_trailing_degree Polynomial.trinomial_natTrailingDegree

theorem trinomial_leadingCoeff (hkm : k < m) (hmn : m < n) (hw : w ≠ 0) :
    (trinomial k m n u v w).leadingCoeff = w := by
  rw [leadingCoeff, trinomial_natDegree hkm hmn hw, trinomial_leading_coeff' hkm hmn]
  -- 🎉 no goals
#align polynomial.trinomial_leading_coeff Polynomial.trinomial_leadingCoeff

theorem trinomial_trailingCoeff (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) :
    (trinomial k m n u v w).trailingCoeff = u := by
  rw [trailingCoeff, trinomial_natTrailingDegree hkm hmn hu, trinomial_trailing_coeff' hkm hmn]
  -- 🎉 no goals
#align polynomial.trinomial_trailing_coeff Polynomial.trinomial_trailingCoeff

theorem trinomial_monic (hkm : k < m) (hmn : m < n) : (trinomial k m n u v 1).Monic := by
  nontriviality R
  -- ⊢ Monic (trinomial k m n u v 1)
  exact trinomial_leadingCoeff hkm hmn one_ne_zero
  -- 🎉 no goals
#align polynomial.trinomial_monic Polynomial.trinomial_monic

theorem trinomial_mirror (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) (hw : w ≠ 0) :
    (trinomial k m n u v w).mirror = trinomial k (n - m + k) n w v u := by
  rw [mirror, trinomial_natTrailingDegree hkm hmn hu, reverse, trinomial_natDegree hkm hmn hw,
    trinomial_def, reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
    reflect_C_mul_X_pow, revAt_le (hkm.trans hmn).le, revAt_le hmn.le, revAt_le le_rfl, add_mul,
    add_mul, mul_assoc, mul_assoc, mul_assoc, ← pow_add, ← pow_add, ← pow_add,
    Nat.sub_add_cancel (hkm.trans hmn).le, Nat.sub_self, zero_add, add_comm, add_comm (C u * X ^ n),
    ← add_assoc, ← trinomial_def]
#align polynomial.trinomial_mirror Polynomial.trinomial_mirror

theorem trinomial_support (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    (trinomial k m n u v w).support = {k, m, n} :=
  support_trinomial hkm hmn hu hv hw
#align polynomial.trinomial_support Polynomial.trinomial_support

end Semiring

variable (p q : ℤ[X])

/-- A unit trinomial is a trinomial with unit coefficients. -/
def IsUnitTrinomial :=
  ∃ (k m n : ℕ) (_ : k < m) (_ : m < n) (u v w : Units ℤ), p = trinomial k m n (u : ℤ) v w
#align polynomial.is_unit_trinomial Polynomial.IsUnitTrinomial

variable {p q}

namespace IsUnitTrinomial

theorem not_isUnit (hp : p.IsUnitTrinomial) : ¬IsUnit p := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  -- ⊢ ¬IsUnit (trinomial k m n ↑u ↑v ↑w)
  exact fun h =>
    ne_zero_of_lt hmn
      ((trinomial_natDegree hkm hmn w.ne_zero).symm.trans
        (natDegree_eq_of_degree_eq_some (degree_eq_zero_of_isUnit h)))
#align polynomial.is_unit_trinomial.not_is_unit Polynomial.IsUnitTrinomial.not_isUnit

theorem card_support_eq_three (hp : p.IsUnitTrinomial) : p.support.card = 3 := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  -- ⊢ card (support (trinomial k m n ↑u ↑v ↑w)) = 3
  exact card_support_trinomial hkm hmn u.ne_zero v.ne_zero w.ne_zero
  -- 🎉 no goals
#align polynomial.is_unit_trinomial.card_support_eq_three Polynomial.IsUnitTrinomial.card_support_eq_three

theorem ne_zero (hp : p.IsUnitTrinomial) : p ≠ 0 := by
  rintro rfl
  -- ⊢ False
  exact Nat.zero_ne_bit1 1 hp.card_support_eq_three
  -- 🎉 no goals
#align polynomial.is_unit_trinomial.ne_zero Polynomial.IsUnitTrinomial.ne_zero

theorem coeff_isUnit (hp : p.IsUnitTrinomial) {k : ℕ} (hk : k ∈ p.support) :
    IsUnit (p.coeff k) := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  -- ⊢ IsUnit (coeff (trinomial k m n ↑u ↑v ↑w) k✝)
  have := support_trinomial' k m n (u : ℤ) v w hk
  -- ⊢ IsUnit (coeff (trinomial k m n ↑u ↑v ↑w) k✝)
  rw [mem_insert, mem_insert, mem_singleton] at this
  -- ⊢ IsUnit (coeff (trinomial k m n ↑u ↑v ↑w) k✝)
  rcases this with (rfl | rfl | rfl)
  · refine' ⟨u, by rw [trinomial_trailing_coeff' hkm hmn]⟩
    -- 🎉 no goals
  · refine' ⟨v, by rw [trinomial_middle_coeff hkm hmn]⟩
    -- 🎉 no goals
  · refine' ⟨w, by rw [trinomial_leading_coeff' hkm hmn]⟩
    -- 🎉 no goals
#align polynomial.is_unit_trinomial.coeff_is_unit Polynomial.IsUnitTrinomial.coeff_isUnit

theorem leadingCoeff_isUnit (hp : p.IsUnitTrinomial) : IsUnit p.leadingCoeff :=
  hp.coeff_isUnit (natDegree_mem_support_of_nonzero hp.ne_zero)
#align polynomial.is_unit_trinomial.leading_coeff_is_unit Polynomial.IsUnitTrinomial.leadingCoeff_isUnit

theorem trailingCoeff_isUnit (hp : p.IsUnitTrinomial) : IsUnit p.trailingCoeff :=
  hp.coeff_isUnit (natTrailingDegree_mem_support_of_nonzero hp.ne_zero)
#align polynomial.is_unit_trinomial.trailing_coeff_is_unit Polynomial.IsUnitTrinomial.trailingCoeff_isUnit

end IsUnitTrinomial

theorem isUnitTrinomial_iff :
    p.IsUnitTrinomial ↔ p.support.card = 3 ∧ ∀ k ∈ p.support, IsUnit (p.coeff k) := by
  refine' ⟨fun hp => ⟨hp.card_support_eq_three, fun k => hp.coeff_isUnit⟩, fun hp => _⟩
  -- ⊢ IsUnitTrinomial p
  obtain ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩ := card_support_eq_three.mp hp.1
  -- ⊢ IsUnitTrinomial (↑C x * X ^ k + ↑C y * X ^ m + ↑C z * X ^ n)
  rw [support_trinomial hkm hmn hx hy hz] at hp
  -- ⊢ IsUnitTrinomial (↑C x * X ^ k + ↑C y * X ^ m + ↑C z * X ^ n)
  replace hx := hp.2 k (mem_insert_self k {m, n})
  -- ⊢ IsUnitTrinomial (↑C x * X ^ k + ↑C y * X ^ m + ↑C z * X ^ n)
  replace hy := hp.2 m (mem_insert_of_mem (mem_insert_self m {n}))
  -- ⊢ IsUnitTrinomial (↑C x * X ^ k + ↑C y * X ^ m + ↑C z * X ^ n)
  replace hz := hp.2 n (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n)))
  -- ⊢ IsUnitTrinomial (↑C x * X ^ k + ↑C y * X ^ m + ↑C z * X ^ n)
  simp_rw [coeff_add, coeff_C_mul, coeff_X_pow_self, mul_one, coeff_X_pow] at hx hy hz
  -- ⊢ IsUnitTrinomial (↑C x * X ^ k + ↑C y * X ^ m + ↑C z * X ^ n)
  rw [if_neg hkm.ne, if_neg (hkm.trans hmn).ne] at hx
  -- ⊢ IsUnitTrinomial (↑C x * X ^ k + ↑C y * X ^ m + ↑C z * X ^ n)
  rw [if_neg hkm.ne', if_neg hmn.ne] at hy
  -- ⊢ IsUnitTrinomial (↑C x * X ^ k + ↑C y * X ^ m + ↑C z * X ^ n)
  rw [if_neg (hkm.trans hmn).ne', if_neg hmn.ne'] at hz
  -- ⊢ IsUnitTrinomial (↑C x * X ^ k + ↑C y * X ^ m + ↑C z * X ^ n)
  simp_rw [mul_zero, zero_add, add_zero] at hx hy hz
  -- ⊢ IsUnitTrinomial (↑C x * X ^ k + ↑C y * X ^ m + ↑C z * X ^ n)
  exact ⟨k, m, n, hkm, hmn, hx.unit, hy.unit, hz.unit, rfl⟩
  -- 🎉 no goals
#align polynomial.is_unit_trinomial_iff Polynomial.isUnitTrinomial_iff

theorem isUnitTrinomial_iff' :
    p.IsUnitTrinomial ↔
      (p * p.mirror).coeff (((p * p.mirror).natDegree + (p * p.mirror).natTrailingDegree) / 2) =
        3 := by
  rw [natDegree_mul_mirror, natTrailingDegree_mul_mirror, ← mul_add,
    Nat.mul_div_right _ zero_lt_two, coeff_mul_mirror]
  refine' ⟨_, fun hp => _⟩
  -- ⊢ IsUnitTrinomial p → (sum p fun n x => x ^ 2) = 3
  · rintro ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩
    -- ⊢ (sum (trinomial k m n ↑u ↑v ↑w) fun n x => x ^ 2) = 3
    rw [sum_def, trinomial_support hkm hmn u.ne_zero v.ne_zero w.ne_zero,
      sum_insert (mt mem_insert.mp (not_or_of_not hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne))),
      sum_insert (mt mem_singleton.mp hmn.ne), sum_singleton, trinomial_leading_coeff' hkm hmn,
      trinomial_middle_coeff hkm hmn, trinomial_trailing_coeff' hkm hmn]
    simp_rw [← Units.val_pow_eq_pow_val, Int.units_sq]
    -- 🎉 no goals
  · have key : ∀ k ∈ p.support, p.coeff k ^ 2 = 1 := fun k hk =>
      Int.sq_eq_one_of_sq_le_three
        ((single_le_sum (fun k _ => sq_nonneg (p.coeff k)) hk).trans hp.le) (mem_support_iff.mp hk)
    refine' isUnitTrinomial_iff.mpr ⟨_, fun k hk => isUnit_ofPowEqOne (key k hk) two_ne_zero⟩
    -- ⊢ card (support p) = 3
    rw [sum_def, sum_congr rfl key, sum_const, Nat.smul_one_eq_coe] at hp
    -- ⊢ card (support p) = 3
    exact Nat.cast_injective hp
    -- 🎉 no goals
#align polynomial.is_unit_trinomial_iff' Polynomial.isUnitTrinomial_iff'

theorem isUnitTrinomial_iff'' (h : p * p.mirror = q * q.mirror) :
    p.IsUnitTrinomial ↔ q.IsUnitTrinomial := by
  rw [isUnitTrinomial_iff', isUnitTrinomial_iff', h]
  -- 🎉 no goals
#align polynomial.is_unit_trinomial_iff'' Polynomial.isUnitTrinomial_iff''

namespace IsUnitTrinomial

theorem irreducible_aux1 {k m n : ℕ} (hkm : k < m) (hmn : m < n) (u v w : Units ℤ)
    (hp : p = trinomial k m n (u : ℤ) v w) :
    C (v : ℤ) * (C (u : ℤ) * X ^ (m + n) + C (w : ℤ) * X ^ (n - m + k + n)) =
      ⟨Finsupp.filter (Set.Ioo (k + n) (n + n)) (p * p.mirror).toFinsupp⟩ := by
  have key : n - m + k < n := by rwa [← lt_tsub_iff_right, tsub_lt_tsub_iff_left_of_le hmn.le]
  -- ⊢ ↑C ↑v * (↑C ↑u * X ^ (m + n) + ↑C ↑w * X ^ (n - m + k + n)) = { toFinsupp := …
  rw [hp, trinomial_mirror hkm hmn u.ne_zero w.ne_zero]
  -- ⊢ ↑C ↑v * (↑C ↑u * X ^ (m + n) + ↑C ↑w * X ^ (n - m + k + n)) = { toFinsupp := …
  simp_rw [trinomial_def, C_mul_X_pow_eq_monomial, add_mul, mul_add, monomial_mul_monomial,
    toFinsupp_add, toFinsupp_monomial]
  -- Porting note: added next line (less powerful `simp`).
  rw [Finsupp.filter_add, Finsupp.filter_add, Finsupp.filter_add, Finsupp.filter_add,
    Finsupp.filter_add, Finsupp.filter_add, Finsupp.filter_add, Finsupp.filter_add]
  rw [Finsupp.filter_single_of_neg, Finsupp.filter_single_of_neg, Finsupp.filter_single_of_neg,
    Finsupp.filter_single_of_neg, Finsupp.filter_single_of_neg, Finsupp.filter_single_of_pos,
    Finsupp.filter_single_of_neg, Finsupp.filter_single_of_pos, Finsupp.filter_single_of_neg]
  · simp only [add_zero, zero_add, ofFinsupp_add, ofFinsupp_single]
    -- ⊢ ↑C ↑v * ↑(monomial (m + n)) ↑u + ↑C ↑v * ↑(monomial (n - m + k + n)) ↑w = {  …
    -- Porting note: added next two lines (less powerful `simp`).
    rw [ofFinsupp_add]
    -- ⊢ ↑C ↑v * ↑(monomial (m + n)) ↑u + ↑C ↑v * ↑(monomial (n - m + k + n)) ↑w = {  …
    simp only [ofFinsupp_single]
    -- ⊢ ↑C ↑v * ↑(monomial (m + n)) ↑u + ↑C ↑v * ↑(monomial (n - m + k + n)) ↑w = ↑( …
    rw [C_mul_monomial, C_mul_monomial, mul_comm (v : ℤ) w, add_comm (n - m + k) n]
    -- 🎉 no goals
  · exact fun h => h.2.ne rfl
    -- 🎉 no goals
  · refine' ⟨_, add_lt_add_left key n⟩
    -- ⊢ k + n < n + (n - m + k)
    rwa [add_comm, add_lt_add_iff_left, lt_add_iff_pos_left, tsub_pos_iff_lt]
    -- 🎉 no goals
  · exact fun h => h.1.ne (add_comm k n)
    -- 🎉 no goals
  · exact ⟨add_lt_add_right hkm n, add_lt_add_right hmn n⟩
    -- 🎉 no goals
  · rw [← add_assoc, add_tsub_cancel_of_le hmn.le, add_comm]
    -- ⊢ ¬Set.Ioo (n + k) (n + n) (n + k)
    exact fun h => h.1.ne rfl
    -- 🎉 no goals
  · intro h
    -- ⊢ False
    have := h.1
    -- ⊢ False
    rw [add_comm, add_lt_add_iff_right] at this
    -- ⊢ False
    exact asymm this hmn
    -- 🎉 no goals
  · exact fun h => h.1.ne rfl
    -- 🎉 no goals
  · exact fun h => asymm ((add_lt_add_iff_left k).mp h.1) key
    -- 🎉 no goals
  · exact fun h => asymm ((add_lt_add_iff_left k).mp h.1) (hkm.trans hmn)
    -- 🎉 no goals
#align polynomial.is_unit_trinomial.irreducible_aux1 Polynomial.IsUnitTrinomial.irreducible_aux1

theorem irreducible_aux2 {k m m' n : ℕ} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
    (u v w : Units ℤ) (hp : p = trinomial k m n (u : ℤ) v w) (hq : q = trinomial k m' n (u : ℤ) v w)
    (h : p * p.mirror = q * q.mirror) : q = p ∨ q = p.mirror := by
  let f : ℤ[X] → ℤ[X] := fun p => ⟨Finsupp.filter (Set.Ioo (k + n) (n + n)) p.toFinsupp⟩
  -- ⊢ q = p ∨ q = mirror p
  replace h := congr_arg f h
  -- ⊢ q = p ∨ q = mirror p
  replace h := (irreducible_aux1 hkm hmn u v w hp).trans h
  -- ⊢ q = p ∨ q = mirror p
  replace h := h.trans (irreducible_aux1 hkm' hmn' u v w hq).symm
  -- ⊢ q = p ∨ q = mirror p
  rw [(isUnit_C.mpr v.isUnit).mul_right_inj] at h
  -- ⊢ q = p ∨ q = mirror p
  rw [binomial_eq_binomial u.ne_zero w.ne_zero] at h
  -- ⊢ q = p ∨ q = mirror p
  simp only [add_left_inj, Units.eq_iff] at h
  -- ⊢ q = p ∨ q = mirror p
  rcases h with (⟨rfl, -⟩ | ⟨rfl, rfl, h⟩ | ⟨-, hm, hm'⟩)
  · exact Or.inl (hq.trans hp.symm)
    -- 🎉 no goals
  · refine' Or.inr _
    -- ⊢ q = mirror p
    rw [← trinomial_mirror hkm' hmn' u.ne_zero u.ne_zero, eq_comm, mirror_eq_iff] at hp
    -- ⊢ q = mirror p
    exact hq.trans hp
    -- 🎉 no goals
  · suffices m = m' by
      rw [this] at hp
      exact Or.inl (hq.trans hp.symm)
    rw [tsub_add_eq_add_tsub hmn.le, eq_tsub_iff_add_eq_of_le, ← two_mul] at hm
    -- ⊢ m = m'
    rw [tsub_add_eq_add_tsub hmn'.le, eq_tsub_iff_add_eq_of_le, ← two_mul] at hm'
    exact mul_left_cancel₀ two_ne_zero (hm.trans hm'.symm)
    -- ⊢ m' ≤ n + k
    exact hmn'.le.trans (Nat.le_add_right n k)
    -- ⊢ m ≤ n + k
    exact hmn.le.trans (Nat.le_add_right n k)
    -- 🎉 no goals
#align polynomial.is_unit_trinomial.irreducible_aux2 Polynomial.IsUnitTrinomial.irreducible_aux2

theorem irreducible_aux3 {k m m' n : ℕ} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
    (u v w x z : Units ℤ) (hp : p = trinomial k m n (u : ℤ) v w)
    (hq : q = trinomial k m' n (x : ℤ) v z) (h : p * p.mirror = q * q.mirror) :
    q = p ∨ q = p.mirror := by
  have hmul := congr_arg leadingCoeff h
  -- ⊢ q = p ∨ q = mirror p
  rw [leadingCoeff_mul, leadingCoeff_mul, mirror_leadingCoeff, mirror_leadingCoeff, hp, hq,
    trinomial_leadingCoeff hkm hmn w.ne_zero, trinomial_leadingCoeff hkm' hmn' z.ne_zero,
    trinomial_trailingCoeff hkm hmn u.ne_zero, trinomial_trailingCoeff hkm' hmn' x.ne_zero]
    at hmul
  have hadd := congr_arg (eval 1) h
  -- ⊢ q = p ∨ q = mirror p
  rw [eval_mul, eval_mul, mirror_eval_one, mirror_eval_one, ← sq, ← sq, hp, hq] at hadd
  -- ⊢ q = p ∨ q = mirror p
  simp only [eval_add, eval_C_mul, eval_pow, eval_X, one_pow, mul_one, trinomial_def] at hadd
  -- ⊢ q = p ∨ q = mirror p
  rw [add_assoc, add_assoc, add_comm (u : ℤ), add_comm (x : ℤ), add_assoc, add_assoc] at hadd
  -- ⊢ q = p ∨ q = mirror p
  simp only [add_sq', add_assoc, add_right_inj, ← Units.val_pow_eq_pow_val, Int.units_sq] at hadd
  -- ⊢ q = p ∨ q = mirror p
  rw [mul_assoc, hmul, ← mul_assoc, add_right_inj,
    mul_right_inj' (show 2 * (v : ℤ) ≠ 0 from mul_ne_zero two_ne_zero v.ne_zero)] at hadd
  replace hadd :=
    (Int.isUnit_add_isUnit_eq_isUnit_add_isUnit w.isUnit u.isUnit z.isUnit x.isUnit).mp hadd
  simp only [Units.eq_iff] at hadd
  -- ⊢ q = p ∨ q = mirror p
  rcases hadd with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  -- ⊢ q = p ∨ q = mirror p
  · exact irreducible_aux2 hkm hmn hkm' hmn' u v w hp hq h
    -- 🎉 no goals
  · rw [← mirror_inj, trinomial_mirror hkm' hmn' w.ne_zero u.ne_zero] at hq
    -- ⊢ q = p ∨ q = mirror p
    rw [mul_comm q, ← q.mirror_mirror, q.mirror.mirror_mirror] at h
    -- ⊢ q = p ∨ q = mirror p
    rw [← mirror_inj, or_comm, ← mirror_eq_iff]
    -- ⊢ mirror q = p ∨ mirror q = mirror p
    exact
      irreducible_aux2 hkm hmn (lt_add_of_pos_left k (tsub_pos_of_lt hmn'))
        (lt_tsub_iff_right.mp ((tsub_lt_tsub_iff_left_of_le hmn'.le).mpr hkm')) u v w hp hq h
#align polynomial.is_unit_trinomial.irreducible_aux3 Polynomial.IsUnitTrinomial.irreducible_aux3

theorem irreducible_of_coprime (hp : p.IsUnitTrinomial)
    (h : ∀ q : ℤ[X], q ∣ p → q ∣ p.mirror → IsUnit q) : Irreducible p := by
  refine' irreducible_of_mirror hp.not_isUnit (fun q hpq => _) h
  -- ⊢ q = p ∨ q = -p ∨ q = mirror p ∨ q = -mirror p
  have hq : IsUnitTrinomial q := (isUnitTrinomial_iff'' hpq).mp hp
  -- ⊢ q = p ∨ q = -p ∨ q = mirror p ∨ q = -mirror p
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hp⟩ := hp
  -- ⊢ q = p ∨ q = -p ∨ q = mirror p ∨ q = -mirror p
  obtain ⟨k', m', n', hkm', hmn', x, y, z, hq⟩ := hq
  -- ⊢ q = p ∨ q = -p ∨ q = mirror p ∨ q = -mirror p
  have hk : k = k' := by
    rw [← mul_right_inj' (show 2 ≠ 0 from two_ne_zero), ←
      trinomial_natTrailingDegree hkm hmn u.ne_zero, ← hp, ← natTrailingDegree_mul_mirror, hpq,
      natTrailingDegree_mul_mirror, hq, trinomial_natTrailingDegree hkm' hmn' x.ne_zero]
  have hn : n = n' := by
    rw [← mul_right_inj' (show 2 ≠ 0 from two_ne_zero), ← trinomial_natDegree hkm hmn w.ne_zero, ←
      hp, ← natDegree_mul_mirror, hpq, natDegree_mul_mirror, hq,
      trinomial_natDegree hkm' hmn' z.ne_zero]
  subst hk
  -- ⊢ q = p ∨ q = -p ∨ q = mirror p ∨ q = -mirror p
  subst hn
  -- ⊢ q = p ∨ q = -p ∨ q = mirror p ∨ q = -mirror p
  rcases eq_or_eq_neg_of_sq_eq_sq (y : ℤ) (v : ℤ)
      ((Int.isUnit_sq y.isUnit).trans (Int.isUnit_sq v.isUnit).symm) with
    (h1 | h1)
  · -- Porting note: `rw [h1] at *` rewrites at `h1`
    rw [h1] at hq
    -- ⊢ q = p ∨ q = -p ∨ q = mirror p ∨ q = -mirror p
    rcases irreducible_aux3 hkm hmn hkm' hmn' u v w x z hp hq hpq with (h2 | h2)
    -- ⊢ q = p ∨ q = -p ∨ q = mirror p ∨ q = -mirror p
    · exact Or.inl h2
      -- 🎉 no goals
    · exact Or.inr (Or.inr (Or.inl h2))
      -- 🎉 no goals
  · -- Porting note: `rw [h1] at *` rewrites at `h1`
    rw [h1] at hq
    -- ⊢ q = p ∨ q = -p ∨ q = mirror p ∨ q = -mirror p
    rw [trinomial_def] at hp
    -- ⊢ q = p ∨ q = -p ∨ q = mirror p ∨ q = -mirror p
    rw [← neg_inj, neg_add, neg_add, ← neg_mul, ← neg_mul, ← neg_mul, ← C_neg, ← C_neg, ← C_neg]
      at hp
    rw [← neg_mul_neg, ← mirror_neg] at hpq
    -- ⊢ q = p ∨ q = -p ∨ q = mirror p ∨ q = -mirror p
    rcases irreducible_aux3 hkm hmn hkm' hmn' (-u) (-v) (-w) x z hp hq hpq with (rfl | rfl)
    -- ⊢ -p = p ∨ -p = -p ∨ -p = mirror p ∨ -p = -mirror p
    · exact Or.inr (Or.inl rfl)
      -- 🎉 no goals
    · exact Or.inr (Or.inr (Or.inr p.mirror_neg))
      -- 🎉 no goals
#align polynomial.is_unit_trinomial.irreducible_of_coprime Polynomial.IsUnitTrinomial.irreducible_of_coprime

/-- A unit trinomial is irreducible if it is coprime with its mirror -/
theorem irreducible_of_isCoprime (hp : p.IsUnitTrinomial) (h : IsCoprime p p.mirror) :
    Irreducible p :=
  irreducible_of_coprime hp fun _ => h.isUnit_of_dvd'
#align polynomial.is_unit_trinomial.irreducible_of_is_coprime Polynomial.IsUnitTrinomial.irreducible_of_isCoprime

/-- A unit trinomial is irreducible if it has no complex roots in common with its mirror -/
theorem irreducible_of_coprime' (hp : IsUnitTrinomial p)
    (h : ∀ z : ℂ, ¬(aeval z p = 0 ∧ aeval z (mirror p) = 0)) : Irreducible p := by
  refine' hp.irreducible_of_coprime fun q hq hq' => _
  -- ⊢ IsUnit q
  suffices ¬0 < q.natDegree by
    rcases hq with ⟨p, rfl⟩
    replace hp := hp.leadingCoeff_isUnit
    rw [leadingCoeff_mul] at hp
    replace hp := isUnit_of_mul_isUnit_left hp
    rw [not_lt, le_zero_iff] at this
    rwa [eq_C_of_natDegree_eq_zero this, isUnit_C, ← this]
  intro hq''
  -- ⊢ False
  rw [natDegree_pos_iff_degree_pos] at hq''
  -- ⊢ False
  rw [← degree_map_eq_of_injective (algebraMap ℤ ℂ).injective_int] at hq''
  -- ⊢ False
  cases' Complex.exists_root hq'' with z hz
  -- ⊢ False
  rw [IsRoot, eval_map, ← aeval_def] at hz
  -- ⊢ False
  refine' h z ⟨_, _⟩
  -- ⊢ ↑(aeval z) p = 0
  · cases' hq with g' hg'
    -- ⊢ ↑(aeval z) p = 0
    rw [hg', aeval_mul, hz, zero_mul]
    -- 🎉 no goals
  · cases' hq' with g' hg'
    -- ⊢ ↑(aeval z) (mirror p) = 0
    rw [hg', aeval_mul, hz, zero_mul]
    -- 🎉 no goals
#align polynomial.is_unit_trinomial.irreducible_of_coprime' Polynomial.IsUnitTrinomial.irreducible_of_coprime'

-- TODO: Develop more theory (e.g., it suffices to check that `aeval z p ≠ 0` for `z = 0`
-- and `z` a root of unity)
end IsUnitTrinomial

end Polynomial
