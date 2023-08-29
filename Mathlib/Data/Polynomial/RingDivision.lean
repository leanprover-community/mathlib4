/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker, Johan Commelin
-/
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Polynomial.Degree.Lemmas
import Mathlib.Data.Polynomial.Div
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.BigOperators

#align_import data.polynomial.ring_division from "leanprover-community/mathlib"@"8efcf8022aac8e01df8d302dcebdbc25d6a886c8"

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $ R[X] $

## Main definitions

* `Polynomial.roots p`: The multiset containing all the roots of `p`, including their
  multiplicities.
* `Polynomial.rootSet p E`: The set of distinct roots of `p` in an algebra `E`.

## Main statements

* `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C`: If a polynomial has as many roots as its
  degree, it can be written as the product of its leading coefficient with `∏ (X - a)` where `a`
  ranges through its roots.

-/

set_option autoImplicit true


noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R] {p q : R[X]}

section

variable [Semiring S]

theorem natDegree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p ≠ 0) {z : S}
    (hz : aeval z p = 0) (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.natDegree :=
  natDegree_pos_of_eval₂_root hp (algebraMap R S) hz inj
#align polynomial.nat_degree_pos_of_aeval_root Polynomial.natDegree_pos_of_aeval_root

theorem degree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p ≠ 0) {z : S} (hz : aeval z p = 0)
    (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.degree :=
  natDegree_pos_iff_degree_pos.mp (natDegree_pos_of_aeval_root hp hz inj)
#align polynomial.degree_pos_of_aeval_root Polynomial.degree_pos_of_aeval_root

theorem modByMonic_eq_of_dvd_sub (hq : q.Monic) {p₁ p₂ : R[X]} (h : q ∣ p₁ - p₂) :
    p₁ %ₘ q = p₂ %ₘ q := by
  nontriviality R
  -- ⊢ p₁ %ₘ q = p₂ %ₘ q
  obtain ⟨f, sub_eq⟩ := h
  -- ⊢ p₁ %ₘ q = p₂ %ₘ q
  refine' (div_modByMonic_unique (p₂ /ₘ q + f) _ hq ⟨_, degree_modByMonic_lt _ hq⟩).2
  -- ⊢ p₂ %ₘ q + q * (p₂ /ₘ q + f) = p₁
  rw [sub_eq_iff_eq_add.mp sub_eq, mul_add, ← add_assoc, modByMonic_add_div _ hq, add_comm]
  -- 🎉 no goals
#align polynomial.mod_by_monic_eq_of_dvd_sub Polynomial.modByMonic_eq_of_dvd_sub

theorem add_modByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q := by
  by_cases hq : q.Monic
  -- ⊢ (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q
  · cases' subsingleton_or_nontrivial R with hR hR
    -- ⊢ (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q
    · simp only [eq_iff_true_of_subsingleton]
      -- 🎉 no goals
    · exact
      (div_modByMonic_unique (p₁ /ₘ q + p₂ /ₘ q) _ hq
          ⟨by
            rw [mul_add, add_left_comm, add_assoc, modByMonic_add_div _ hq, ← add_assoc,
              add_comm (q * _), modByMonic_add_div _ hq],
            (degree_add_le _ _).trans_lt
              (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))⟩).2
  · simp_rw [modByMonic_eq_of_not_monic _ hq]
    -- 🎉 no goals
#align polynomial.add_mod_by_monic Polynomial.add_modByMonic

theorem smul_modByMonic (c : R) (p : R[X]) : c • p %ₘ q = c • (p %ₘ q) := by
  by_cases hq : q.Monic
  -- ⊢ c • p %ₘ q = c • (p %ₘ q)
  · cases' subsingleton_or_nontrivial R with hR hR
    -- ⊢ c • p %ₘ q = c • (p %ₘ q)
    · simp only [eq_iff_true_of_subsingleton]
      -- 🎉 no goals
    · exact
      (div_modByMonic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
          ⟨by rw [mul_smul_comm, ← smul_add, modByMonic_add_div p hq],
            (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)⟩).2
  · simp_rw [modByMonic_eq_of_not_monic _ hq]
    -- 🎉 no goals
#align polynomial.smul_mod_by_monic Polynomial.smul_modByMonic

/-- `_ %ₘ q` as an `R`-linear map. -/
@[simps]
def modByMonicHom (q : R[X]) : R[X] →ₗ[R] R[X] where
  toFun p := p %ₘ q
  map_add' := add_modByMonic
  map_smul' := smul_modByMonic
#align polynomial.mod_by_monic_hom Polynomial.modByMonicHom

end

section

variable [Ring S]

theorem aeval_modByMonic_eq_self_of_root [Algebra R S] {p q : R[X]} (hq : q.Monic) {x : S}
    (hx : aeval x q = 0) : aeval x (p %ₘ q) = aeval x p := by
    --`eval₂_modByMonic_eq_self_of_root` doesn't work here as it needs commutativity
  rw [modByMonic_eq_sub_mul_div p hq, _root_.map_sub, _root_.map_mul, hx, zero_mul,
    sub_zero]
#align polynomial.aeval_mod_by_monic_eq_self_of_root Polynomial.aeval_modByMonic_eq_self_of_root

end

end CommRing

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

instance : NoZeroDivisors R[X] where
  eq_zero_or_eq_zero_of_mul_eq_zero h := by
    rw [← leadingCoeff_eq_zero, ← leadingCoeff_eq_zero]
    -- ⊢ leadingCoeff a✝ = 0 ∨ leadingCoeff b✝ = 0
    refine' eq_zero_or_eq_zero_of_mul_eq_zero _
    -- ⊢ leadingCoeff a✝ * leadingCoeff b✝ = 0
    rw [← leadingCoeff_zero, ← leadingCoeff_mul, h]
    -- 🎉 no goals

theorem natDegree_mul (hp : p ≠ 0) (hq : q ≠ 0) : (p*q).natDegree = p.natDegree + q.natDegree := by
  rw [← WithBot.coe_eq_coe, ← Nat.cast_withBot, ←degree_eq_natDegree (mul_ne_zero hp hq),
    WithBot.coe_add, ← Nat.cast_withBot, ←degree_eq_natDegree hp, ← Nat.cast_withBot,
    ← degree_eq_natDegree hq, degree_mul]
#align polynomial.nat_degree_mul Polynomial.natDegree_mul

theorem trailingDegree_mul : (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  by_cases hp : p = 0
  -- ⊢ trailingDegree (p * q) = trailingDegree p + trailingDegree q
  · rw [hp, zero_mul, trailingDegree_zero, top_add]
    -- 🎉 no goals
  by_cases hq : q = 0
  -- ⊢ trailingDegree (p * q) = trailingDegree p + trailingDegree q
  · rw [hq, mul_zero, trailingDegree_zero, add_top]
    -- 🎉 no goals
  · rw [trailingDegree_eq_natTrailingDegree hp, trailingDegree_eq_natTrailingDegree hq,
    trailingDegree_eq_natTrailingDegree (mul_ne_zero hp hq), natTrailingDegree_mul hp hq]
    apply WithTop.coe_add
    -- 🎉 no goals
#align polynomial.trailing_degree_mul Polynomial.trailingDegree_mul

@[simp]
theorem natDegree_pow (p : R[X]) (n : ℕ) : natDegree (p ^ n) = n * natDegree p := by
  classical
  exact if hp0 : p = 0 then
    if hn0 : n = 0 then by simp [hp0, hn0]
    else by rw [hp0, zero_pow (Nat.pos_of_ne_zero hn0)]; simp
  else
    natDegree_pow'
      (by rw [← leadingCoeff_pow, Ne.def, leadingCoeff_eq_zero]; exact pow_ne_zero _ hp0)
#align polynomial.nat_degree_pow Polynomial.natDegree_pow

theorem degree_le_mul_left (p : R[X]) (hq : q ≠ 0) : degree p ≤ degree (p * q) := by
  classical
  exact if hp : p = 0 then by simp only [hp, zero_mul, le_refl]
  else by
    rw [degree_mul, degree_eq_natDegree hp, degree_eq_natDegree hq];
      exact WithBot.coe_le_coe.2 (Nat.le_add_right _ _)
#align polynomial.degree_le_mul_left Polynomial.degree_le_mul_left

theorem natDegree_le_of_dvd {p q : R[X]} (h1 : p ∣ q) (h2 : q ≠ 0) : p.natDegree ≤ q.natDegree := by
  rcases h1 with ⟨q, rfl⟩; rw [mul_ne_zero_iff] at h2
  -- ⊢ natDegree p ≤ natDegree (p * q)
                           -- ⊢ natDegree p ≤ natDegree (p * q)
  rw [natDegree_mul h2.1 h2.2]; exact Nat.le_add_right _ _
  -- ⊢ natDegree p ≤ natDegree p + natDegree q
                                -- 🎉 no goals
#align polynomial.nat_degree_le_of_dvd Polynomial.natDegree_le_of_dvd

theorem degree_le_of_dvd {p q : R[X]} (h1 : p ∣ q) (h2 : q ≠ 0) : degree p ≤ degree q := by
  rcases h1 with ⟨q, rfl⟩; rw [mul_ne_zero_iff] at h2
  -- ⊢ degree p ≤ degree (p * q)
                           -- ⊢ degree p ≤ degree (p * q)
  exact degree_le_mul_left p h2.2
  -- 🎉 no goals
#align polynomial.degree_le_of_dvd Polynomial.degree_le_of_dvd

theorem eq_zero_of_dvd_of_degree_lt {p q : R[X]} (h₁ : p ∣ q) (h₂ : degree q < degree p) :
    q = 0 := by
  by_contra hc
  -- ⊢ False
  exact (lt_iff_not_ge _ _).mp h₂ (degree_le_of_dvd h₁ hc)
  -- 🎉 no goals
#align polynomial.eq_zero_of_dvd_of_degree_lt Polynomial.eq_zero_of_dvd_of_degree_lt

theorem eq_zero_of_dvd_of_natDegree_lt {p q : R[X]} (h₁ : p ∣ q) (h₂ : natDegree q < natDegree p) :
    q = 0 := by
  by_contra hc
  -- ⊢ False
  exact (lt_iff_not_ge _ _).mp h₂ (natDegree_le_of_dvd h₁ hc)
  -- 🎉 no goals
#align polynomial.eq_zero_of_dvd_of_nat_degree_lt Polynomial.eq_zero_of_dvd_of_natDegree_lt

theorem not_dvd_of_degree_lt {p q : R[X]} (h0 : q ≠ 0) (hl : q.degree < p.degree) : ¬p ∣ q := by
  by_contra hcontra
  -- ⊢ False
  exact h0 (eq_zero_of_dvd_of_degree_lt hcontra hl)
  -- 🎉 no goals
#align polynomial.not_dvd_of_degree_lt Polynomial.not_dvd_of_degree_lt

theorem not_dvd_of_natDegree_lt {p q : R[X]} (h0 : q ≠ 0) (hl : q.natDegree < p.natDegree) :
    ¬p ∣ q := by
  by_contra hcontra
  -- ⊢ False
  exact h0 (eq_zero_of_dvd_of_natDegree_lt hcontra hl)
  -- 🎉 no goals
#align polynomial.not_dvd_of_nat_degree_lt Polynomial.not_dvd_of_natDegree_lt

/-- This lemma is useful for working with the `intDegree` of a rational function. -/
theorem natDegree_sub_eq_of_prod_eq {p₁ p₂ q₁ q₂ : R[X]} (hp₁ : p₁ ≠ 0) (hq₁ : q₁ ≠ 0)
    (hp₂ : p₂ ≠ 0) (hq₂ : q₂ ≠ 0) (h_eq : p₁ * q₂ = p₂ * q₁) :
    (p₁.natDegree : ℤ) - q₁.natDegree = (p₂.natDegree : ℤ) - q₂.natDegree := by
  rw [sub_eq_sub_iff_add_eq_add]
  -- ⊢ ↑(natDegree p₁) + ↑(natDegree q₂) = ↑(natDegree p₂) + ↑(natDegree q₁)
  norm_cast
  -- ⊢ natDegree p₁ + natDegree q₂ = natDegree p₂ + natDegree q₁
  rw [← natDegree_mul hp₁ hq₂, ← natDegree_mul hp₂ hq₁, h_eq]
  -- 🎉 no goals
#align polynomial.nat_degree_sub_eq_of_prod_eq Polynomial.natDegree_sub_eq_of_prod_eq

theorem natDegree_eq_zero_of_isUnit (h : IsUnit p) : natDegree p = 0 := by
  nontriviality R
  -- ⊢ natDegree p = 0
  obtain ⟨q, hq⟩ := h.exists_right_inv
  -- ⊢ natDegree p = 0
  have := natDegree_mul (left_ne_zero_of_mul_eq_one hq) (right_ne_zero_of_mul_eq_one hq)
  -- ⊢ natDegree p = 0
  rw [hq, natDegree_one, eq_comm, add_eq_zero_iff] at this
  -- ⊢ natDegree p = 0
  exact this.1
  -- 🎉 no goals
#align polynomial.nat_degree_eq_zero_of_is_unit Polynomial.natDegree_eq_zero_of_isUnit

theorem degree_eq_zero_of_isUnit [Nontrivial R] (h : IsUnit p) : degree p = 0 :=
  (natDegree_eq_zero_iff_degree_le_zero.mp <| natDegree_eq_zero_of_isUnit h).antisymm
    (zero_le_degree_iff.mpr h.ne_zero)
#align polynomial.degree_eq_zero_of_is_unit Polynomial.degree_eq_zero_of_isUnit

@[simp]
theorem degree_coe_units [Nontrivial R] (u : R[X]ˣ) : degree (u : R[X]) = 0 :=
  degree_eq_zero_of_isUnit ⟨u, rfl⟩
#align polynomial.degree_coe_units Polynomial.degree_coe_units

/-- Characterization of a unit of a polynomial ring over an integral domain `R`.
See `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent` when `R` is a commutative ring. -/
theorem isUnit_iff : IsUnit p ↔ ∃ r : R, IsUnit r ∧ C r = p :=
  ⟨fun hp =>
    ⟨p.coeff 0,
      let h := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hp)
      ⟨isUnit_C.1 (h ▸ hp), h.symm⟩⟩,
    fun ⟨_, hr, hrp⟩ => hrp ▸ isUnit_C.2 hr⟩
#align polynomial.is_unit_iff Polynomial.isUnit_iff

variable [CharZero R]

-- Porting note: bit0/bit1 are deprecated
-- @[simp, deprecated]
-- theorem degree_bit0_eq (p : R[X]) : degree (bit0 p) = degree p := by
--   rw [bit0_eq_two_mul, degree_mul, (by simp : (2 : R[X]) = C 2),
--     @Polynomial.degree_C R _ _ two_ne_zero, zero_add]
-- #align polynomial.degree_bit0_eq Polynomial.degree_bit0_eq
--
-- @[simp]
-- theorem natDegree_bit0_eq (p : R[X]) : natDegree (bit0 p) = natDegree p :=
--   natDegree_eq_of_degree_eq <| degree_bit0_eq p
-- #align polynomial.nat_degree_bit0_eq Polynomial.natDegree_bit0_eq
--
-- @[simp]
-- theorem natDegree_bit1_eq (p : R[X]) : natDegree (bit1 p) = natDegree p := by
--   rw [bit1]
--   apply le_antisymm
--   convert natDegree_add_le _ _
--   · simp
--   by_cases h : p.natDegree = 0
--   · simp [h]
--   apply le_natDegree_of_ne_zero
--   intro hh
--   apply h
--   simp_all [coeff_one, if_neg (Ne.symm h)]
-- #align polynomial.nat_degree_bit1_eq Polynomial.natDegree_bit1_eq
--
-- theorem degree_bit1_eq {p : R[X]} (hp : 0 < degree p) : degree (bit1 p) = degree p := by
--   rw [bit1, degree_add_eq_left_of_degree_lt, degree_bit0_eq]
--   rwa [degree_one, degree_bit0_eq]
-- #align polynomial.degree_bit1_eq Polynomial.degree_bit1_eq

end NoZeroDivisors

section NoZeroDivisors

variable [CommSemiring R] [NoZeroDivisors R] {p q : R[X]}

theorem irreducible_of_monic (hp : p.Monic) (hp1 : p ≠ 1) :
    Irreducible p ↔ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → f = 1 ∨ g = 1 := by
  refine'
    ⟨fun h f g hf hg hp => (h.2 f g hp.symm).imp hf.eq_one_of_isUnit hg.eq_one_of_isUnit, fun h =>
      ⟨hp1 ∘ hp.eq_one_of_isUnit, fun f g hfg =>
        (h (g * C f.leadingCoeff) (f * C g.leadingCoeff) _ _ _).symm.imp (isUnit_of_mul_eq_one f _)
          (isUnit_of_mul_eq_one g _)⟩⟩
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, mul_comm, ← hfg, ← Monic]
    -- 🎉 no goals
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, ← hfg, ← Monic]
    -- 🎉 no goals
  · rw [mul_mul_mul_comm, ← C_mul, ← leadingCoeff_mul, ← hfg, hp.leadingCoeff, C_1, mul_one,
      mul_comm, ← hfg]
#align polynomial.irreducible_of_monic Polynomial.irreducible_of_monic

theorem Monic.irreducible_iff_natDegree (hp : p.Monic) :
    Irreducible p ↔
      p ≠ 1 ∧ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → f.natDegree = 0 ∨ g.natDegree = 0 := by
  by_cases hp1 : p = 1; · simp [hp1]
  -- ⊢ Irreducible p ↔ p ≠ 1 ∧ ∀ (f g : R[X]), Monic f → Monic g → f * g = p → natD …
                          -- 🎉 no goals
  rw [irreducible_of_monic hp hp1, and_iff_right hp1]
  -- ⊢ (∀ (f g : R[X]), Monic f → Monic g → f * g = p → f = 1 ∨ g = 1) ↔ ∀ (f g : R …
  refine' forall₄_congr fun a b ha hb => _
  -- ⊢ a * b = p → a = 1 ∨ b = 1 ↔ a * b = p → natDegree a = 0 ∨ natDegree b = 0
  rw [ha.natDegree_eq_zero_iff_eq_one, hb.natDegree_eq_zero_iff_eq_one]
  -- 🎉 no goals
#align polynomial.monic.irreducible_iff_nat_degree Polynomial.Monic.irreducible_iff_natDegree

theorem Monic.irreducible_iff_natDegree' (hp : p.Monic) : Irreducible p ↔ p ≠ 1 ∧
    ∀ f g : R[X], f.Monic → g.Monic → f * g = p → g.natDegree ∉ Ioc 0 (p.natDegree / 2) := by
  simp_rw [hp.irreducible_iff_natDegree, mem_Ioc, Nat.le_div_iff_mul_le zero_lt_two, mul_two]
  -- ⊢ (p ≠ 1 ∧ ∀ (f g : R[X]), Monic f → Monic g → f * g = p → natDegree f = 0 ∨ n …
  apply and_congr_right'
  -- ⊢ (∀ (f g : R[X]), Monic f → Monic g → f * g = p → natDegree f = 0 ∨ natDegree …
  constructor <;> intro h f g hf hg he <;> subst he
  -- ⊢ (∀ (f g : R[X]), Monic f → Monic g → f * g = p → natDegree f = 0 ∨ natDegree …
                  -- ⊢ ¬(0 < natDegree g ∧ natDegree g + natDegree g ≤ natDegree p)
                  -- ⊢ natDegree f = 0 ∨ natDegree g = 0
                                           -- ⊢ ¬(0 < natDegree g ∧ natDegree g + natDegree g ≤ natDegree (f * g))
                                           -- ⊢ natDegree f = 0 ∨ natDegree g = 0
  · rw [hf.natDegree_mul hg, add_le_add_iff_right]
    -- ⊢ ¬(0 < natDegree g ∧ natDegree g ≤ natDegree f)
    exact fun ha => (h f g hf hg rfl).elim (ha.1.trans_le ha.2).ne' ha.1.ne'
    -- 🎉 no goals
  · simp_rw [hf.natDegree_mul hg, pos_iff_ne_zero] at h
    -- ⊢ natDegree f = 0 ∨ natDegree g = 0
    contrapose! h
    -- ⊢ ∃ f_1 g_1, Monic f_1 ∧ Monic g_1 ∧ f_1 * g_1 = f * g ∧ natDegree g_1 ≠ 0 ∧ n …
    obtain hl | hl := le_total f.natDegree g.natDegree
    -- ⊢ ∃ f_1 g_1, Monic f_1 ∧ Monic g_1 ∧ f_1 * g_1 = f * g ∧ natDegree g_1 ≠ 0 ∧ n …
    · exact ⟨g, f, hg, hf, mul_comm g f, h.1, add_le_add_left hl _⟩
      -- 🎉 no goals
    · exact ⟨f, g, hf, hg, rfl, h.2, add_le_add_right hl _⟩
      -- 🎉 no goals
#align polynomial.monic.irreducible_iff_nat_degree' Polynomial.Monic.irreducible_iff_natDegree'

theorem Monic.not_irreducible_iff_exists_add_mul_eq_coeff (hm : p.Monic) (hnd : p.natDegree = 2) :
    ¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂ := by
  cases subsingleton_or_nontrivial R
  -- ⊢ ¬Irreducible p ↔ ∃ c₁ c₂, coeff p 0 = c₁ * c₂ ∧ coeff p 1 = c₁ + c₂
  · simp [natDegree_of_subsingleton] at hnd
    -- 🎉 no goals
  rw [hm.irreducible_iff_natDegree', and_iff_right, hnd]
  -- ⊢ (¬∀ (f g : R[X]), Monic f → Monic g → f * g = p → ¬natDegree g ∈ Ioc 0 (2 /  …
  push_neg; constructor
  -- ⊢ (∃ f g, Monic f ∧ Monic g ∧ f * g = p ∧ natDegree g ∈ Ioc 0 (2 / 2)) ↔ ∃ c₁  …
  · rintro ⟨a, b, ha, hb, rfl, hdb⟩
    -- ⊢ ∃ c₁ c₂, coeff (a * b) 0 = c₁ * c₂ ∧ coeff (a * b) 1 = c₁ + c₂
    simp only [zero_lt_two, Nat.div_self, ge_iff_le,
      Nat.Ioc_succ_singleton, zero_add, mem_singleton] at hdb
    have hda := hnd
    -- ⊢ ∃ c₁ c₂, coeff (a * b) 0 = c₁ * c₂ ∧ coeff (a * b) 1 = c₁ + c₂
    rw [ha.natDegree_mul hb, hdb] at hda
    -- ⊢ ∃ c₁ c₂, coeff (a * b) 0 = c₁ * c₂ ∧ coeff (a * b) 1 = c₁ + c₂
    use a.coeff 0, b.coeff 0, mul_coeff_zero a b
    -- ⊢ coeff (a * b) 1 = coeff a 0 + coeff b 0
    simpa only [nextCoeff, hnd, add_right_cancel hda, hdb] using ha.nextCoeff_mul hb
    -- 🎉 no goals
  · rintro ⟨c₁, c₂, hmul, hadd⟩
    -- ⊢ ∃ f g, Monic f ∧ Monic g ∧ f * g = p ∧ natDegree g ∈ Ioc 0 (2 / 2)
    refine
      ⟨X + C c₁, X + C c₂, monic_X_add_C _, monic_X_add_C _, ?_, ?_ ⟩
    · rw [p.as_sum_range_C_mul_X_pow, hnd, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one, ← hnd, hm.coeff_natDegree, hnd, hmul, hadd, C_mul, C_add, C_1]
      ring
      -- 🎉 no goals
    · rw [mem_Ioc, natDegree_X_add_C _]
      -- ⊢ 0 < 1 ∧ 1 ≤ 2 / 2
      simp
      -- 🎉 no goals
  · rintro rfl
    -- ⊢ False
    simp [natDegree_one] at hnd
    -- 🎉 no goals
#align polynomial.monic.not_irreducible_iff_exists_add_mul_eq_coeff Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff

theorem root_mul : IsRoot (p * q) a ↔ IsRoot p a ∨ IsRoot q a := by
  simp_rw [IsRoot, eval_mul, mul_eq_zero]
  -- 🎉 no goals
#align polynomial.root_mul Polynomial.root_mul

theorem root_or_root_of_root_mul (h : IsRoot (p * q) a) : IsRoot p a ∨ IsRoot q a :=
  root_mul.1 h
#align polynomial.root_or_root_of_root_mul Polynomial.root_or_root_of_root_mul

end NoZeroDivisors

section Ring

variable [Ring R] [IsDomain R] {p q : R[X]}

instance : IsDomain R[X] :=
  NoZeroDivisors.to_isDomain _

end Ring

section CommRing

variable [CommRing R]

/- Porting note: the ML3 proof no longer worked because of a conflict in the
inferred type and synthesized type for `DecidableRel` when using `Nat.le_find_iff` from
`Mathlib.Data.Polynomial.Div` After some discussion on [Zulip]
(https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/decidability.20leakage)
introduced `Polynomial.rootMultiplicity_eq_nat_find_of_nonzero` to contain the issue
-/
/-- The multiplicity of `a` as root of a nonzero polynomial `p` is at least `n` iff
  `(X - a) ^ n` divides `p`. -/
theorem le_rootMultiplicity_iff {p : R[X]} (p0 : p ≠ 0) {a : R} {n : ℕ} :
    n ≤ rootMultiplicity a p ↔ (X - C a) ^ n ∣ p := by
  classical
  rw [rootMultiplicity_eq_nat_find_of_nonzero p0, Nat.le_find_iff]
  simp_rw [Classical.not_not]
  refine ⟨fun h => ?_, fun h m hm => (pow_dvd_pow _ hm).trans h⟩
  cases' n with n;
  · rw [pow_zero]
    apply one_dvd;
  · exact h n n.lt_succ_self
#align polynomial.le_root_multiplicity_iff Polynomial.le_rootMultiplicity_iff

theorem rootMultiplicity_le_iff {p : R[X]} (p0 : p ≠ 0) (a : R) (n : ℕ) :
    rootMultiplicity a p ≤ n ↔ ¬(X - C a) ^ (n + 1) ∣ p := by
  rw [← (le_rootMultiplicity_iff p0).not, not_le, Nat.lt_add_one_iff]
  -- 🎉 no goals
#align polynomial.root_multiplicity_le_iff Polynomial.rootMultiplicity_le_iff

theorem pow_rootMultiplicity_not_dvd {p : R[X]} (p0 : p ≠ 0) (a : R) :
    ¬(X - C a) ^ (rootMultiplicity a p + 1) ∣ p := by rw [← rootMultiplicity_le_iff p0]
                                                      -- 🎉 no goals
#align polynomial.pow_root_multiplicity_not_dvd Polynomial.pow_rootMultiplicity_not_dvd

/-- The multiplicity of `p + q` is at least the minimum of the multiplicities. -/
theorem rootMultiplicity_add {p q : R[X]} (a : R) (hzero : p + q ≠ 0) :
    min (rootMultiplicity a p) (rootMultiplicity a q) ≤ rootMultiplicity a (p + q) := by
  rw [le_rootMultiplicity_iff hzero]
  -- ⊢ (X - ↑C a) ^ min (rootMultiplicity a p) (rootMultiplicity a q) ∣ p + q
  have hdivp : (X - C a) ^ rootMultiplicity a p ∣ p := pow_rootMultiplicity_dvd p a
  -- ⊢ (X - ↑C a) ^ min (rootMultiplicity a p) (rootMultiplicity a q) ∣ p + q
  have hdivq : (X - C a) ^ rootMultiplicity a q ∣ q := pow_rootMultiplicity_dvd q a
  -- ⊢ (X - ↑C a) ^ min (rootMultiplicity a p) (rootMultiplicity a q) ∣ p + q
  exact min_pow_dvd_add hdivp hdivq
  -- 🎉 no goals
#align polynomial.root_multiplicity_add Polynomial.rootMultiplicity_add

variable [IsDomain R] {p q : R[X]}

section Roots

open Multiset

theorem prime_X_sub_C (r : R) : Prime (X - C r) :=
  ⟨X_sub_C_ne_zero r, not_isUnit_X_sub_C r, fun _ _ => by
    simp_rw [dvd_iff_isRoot, IsRoot.def, eval_mul, mul_eq_zero]
    -- ⊢ eval r x✝¹ = 0 ∨ eval r x✝ = 0 → eval r x✝¹ = 0 ∨ eval r x✝ = 0
    exact id⟩
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.prime_X_sub_C Polynomial.prime_X_sub_C

theorem prime_X : Prime (X : R[X]) := by
  convert prime_X_sub_C (0 : R)
  -- ⊢ X = X - ↑C 0
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.prime_X Polynomial.prime_X

theorem Monic.prime_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Prime p :=
  have : p = X - C (-p.coeff 0) := by simpa [hm.leadingCoeff] using eq_X_add_C_of_degree_eq_one hp1
                                      -- 🎉 no goals
  this.symm ▸ prime_X_sub_C _
#align polynomial.monic.prime_of_degree_eq_one Polynomial.Monic.prime_of_degree_eq_one

theorem irreducible_X_sub_C (r : R) : Irreducible (X - C r) :=
  (prime_X_sub_C r).irreducible
set_option linter.uppercaseLean3 false in
#align polynomial.irreducible_X_sub_C Polynomial.irreducible_X_sub_C

theorem irreducible_X : Irreducible (X : R[X]) :=
  Prime.irreducible prime_X
set_option linter.uppercaseLean3 false in
#align polynomial.irreducible_X Polynomial.irreducible_X

theorem Monic.irreducible_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Irreducible p :=
  (hm.prime_of_degree_eq_one hp1).irreducible
#align polynomial.monic.irreducible_of_degree_eq_one Polynomial.Monic.irreducible_of_degree_eq_one

theorem eq_of_monic_of_associated (hp : p.Monic) (hq : q.Monic) (hpq : Associated p q) : p = q := by
  obtain ⟨u, hu⟩ := hpq
  -- ⊢ p = q
  unfold Monic at hp hq
  -- ⊢ p = q
  rw [eq_C_of_degree_le_zero (degree_coe_units _).le] at hu
  -- ⊢ p = q
  rw [← hu, leadingCoeff_mul, hp, one_mul, leadingCoeff_C] at hq
  -- ⊢ p = q
  rwa [hq, C_1, mul_one] at hu
  -- 🎉 no goals
#align polynomial.eq_of_monic_of_associated Polynomial.eq_of_monic_of_associated

theorem rootMultiplicity_mul {p q : R[X]} {x : R} (hpq : p * q ≠ 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q := by
  classical
  have hp : p ≠ 0 := left_ne_zero_of_mul hpq
  have hq : q ≠ 0 := right_ne_zero_of_mul hpq
  rw [rootMultiplicity_eq_multiplicity (p * q), dif_neg hpq, rootMultiplicity_eq_multiplicity p,
    dif_neg hp, rootMultiplicity_eq_multiplicity q, dif_neg hq,
    multiplicity.mul' (prime_X_sub_C x)]
#align polynomial.root_multiplicity_mul Polynomial.rootMultiplicity_mul

theorem rootMultiplicity_X_sub_C_self {x : R} : rootMultiplicity x (X - C x) = 1 := by
  classical
  rw [rootMultiplicity_eq_multiplicity, dif_neg (X_sub_C_ne_zero x),
    multiplicity.get_multiplicity_self]
set_option linter.uppercaseLean3 false in
#align polynomial.root_multiplicity_X_sub_C_self Polynomial.rootMultiplicity_X_sub_C_self

-- porting note: swapped instance argument order
theorem rootMultiplicity_X_sub_C [DecidableEq R] {x y : R} :
    rootMultiplicity x (X - C y) = if x = y then 1 else 0 := by
  split_ifs with hxy
  -- ⊢ rootMultiplicity x (X - ↑C y) = 1
  · rw [hxy]
    -- ⊢ rootMultiplicity y (X - ↑C y) = 1
    exact rootMultiplicity_X_sub_C_self
    -- 🎉 no goals
  exact rootMultiplicity_eq_zero (mt root_X_sub_C.mp (Ne.symm hxy))
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.root_multiplicity_X_sub_C Polynomial.rootMultiplicity_X_sub_C

/-- The multiplicity of `a` as root of `(X - a) ^ n` is `n`. -/
theorem rootMultiplicity_X_sub_C_pow (a : R) (n : ℕ) : rootMultiplicity a ((X - C a) ^ n) = n := by
  induction' n with n hn
  -- ⊢ rootMultiplicity a ((X - ↑C a) ^ Nat.zero) = Nat.zero
  · refine' rootMultiplicity_eq_zero _
    -- ⊢ ¬IsRoot ((X - ↑C a) ^ Nat.zero) a
    simp only [eval_one, IsRoot.def, not_false_iff, one_ne_zero, pow_zero, Nat.zero_eq]
    -- 🎉 no goals
  have hzero := pow_ne_zero n.succ (X_sub_C_ne_zero a)
  -- ⊢ rootMultiplicity a ((X - ↑C a) ^ Nat.succ n) = Nat.succ n
  rw [pow_succ (X - C a) n] at hzero ⊢
  -- ⊢ rootMultiplicity a ((X - ↑C a) * (X - ↑C a) ^ n) = Nat.succ n
  simp only [rootMultiplicity_mul hzero, rootMultiplicity_X_sub_C_self, hn, Nat.one_add]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.root_multiplicity_X_sub_C_pow Polynomial.rootMultiplicity_X_sub_C_pow

theorem exists_multiset_roots [DecidableEq R] :
    ∀ {p : R[X]} (_ : p ≠ 0), ∃ s : Multiset R,
      (Multiset.card s : WithBot ℕ) ≤ degree p ∧ ∀ a, s.count a = rootMultiplicity a p
  | p, hp =>
    haveI := Classical.propDecidable (∃ x, IsRoot p x)
    if h : ∃ x, IsRoot p x then
      let ⟨x, hx⟩ := h
      have hpd : 0 < degree p := degree_pos_of_root hp hx
      have hd0 : p /ₘ (X - C x) ≠ 0 := fun h => by
        rw [← mul_divByMonic_eq_iff_isRoot.2 hx, h, mul_zero] at hp; exact hp rfl
        -- ⊢ False
                                                                     -- 🎉 no goals
      have wf : degree (p /ₘ (X - C x)) < degree p :=
        degree_divByMonic_lt _ (monic_X_sub_C x) hp ((degree_X_sub_C x).symm ▸ by decide)
                                                                                  -- 🎉 no goals
      let ⟨t, htd, htr⟩ := @exists_multiset_roots _ (p /ₘ (X - C x)) hd0
      have hdeg : degree (X - C x) ≤ degree p := by
        rw [degree_X_sub_C, degree_eq_natDegree hp]
        -- ⊢ 1 ≤ ↑(natDegree p)
        rw [degree_eq_natDegree hp] at hpd
        -- ⊢ 1 ≤ ↑(natDegree p)
        exact WithBot.coe_le_coe.2 (WithBot.coe_lt_coe.1 hpd)
        -- 🎉 no goals
      have hdiv0 : p /ₘ (X - C x) ≠ 0 :=
        mt (divByMonic_eq_zero_iff (monic_X_sub_C x)).1 <| not_lt.2 hdeg
      ⟨x ::ₘ t,
        calc
          (card (x ::ₘ t) : WithBot ℕ) = Multiset.card t + 1 := by
            congr
            -- ⊢ ↑Multiset.card (x ::ₘ t) = Add.add (↑(↑Multiset.card t)) 1
            exact_mod_cast Multiset.card_cons _ _
            -- 🎉 no goals
          _ ≤ degree p := by
            rw [← degree_add_divByMonic (monic_X_sub_C x) hdeg, degree_X_sub_C, add_comm];
            -- ⊢ 1 + ↑(↑Multiset.card t) ≤ 1 + degree (p /ₘ (X - ↑C x))
              exact add_le_add (le_refl (1 : WithBot ℕ)) htd,
              -- 🎉 no goals
        by
          change ∀ (a : R), count a (x ::ₘ t) = rootMultiplicity a p
          -- ⊢ ∀ (a : R), count a (x ::ₘ t) = rootMultiplicity a p
          intro a
          -- ⊢ count a (x ::ₘ t) = rootMultiplicity a p
          conv_rhs => rw [← mul_divByMonic_eq_iff_isRoot.mpr hx]
          -- ⊢ count a (x ::ₘ t) = rootMultiplicity a ((X - ↑C x) * (p /ₘ (X - ↑C x)))
          rw [rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero x) hdiv0),
            rootMultiplicity_X_sub_C, ← htr a]
          split_ifs with ha
          -- ⊢ count a (x ::ₘ t) = 1 + count a t
          · rw [ha, count_cons_self, add_comm]
            -- 🎉 no goals
          · rw [count_cons_of_ne ha, zero_add]⟩
            -- 🎉 no goals
    else
      ⟨0, (degree_eq_natDegree hp).symm ▸ WithBot.coe_le_coe.2 (Nat.zero_le _), by
        intro a
        -- ⊢ count a 0 = rootMultiplicity a p
        rw [count_zero, rootMultiplicity_eq_zero (not_exists.mp h a)]⟩
        -- 🎉 no goals
termination_by _ p _ => natDegree p
decreasing_by {
  simp_wf
  apply WithBot.coe_lt_coe.mp
  simp only [degree_eq_natDegree hp, degree_eq_natDegree hd0, ←Nat.cast_withBot] at wf;
  assumption}
#align polynomial.exists_multiset_roots Polynomial.exists_multiset_roots

/-- `roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities. -/
noncomputable def roots (p : R[X]) : Multiset R :=
  haveI := Classical.decEq R
  haveI := Classical.dec (p = 0)
  if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)
#align polynomial.roots Polynomial.roots

theorem roots_def [DecidableEq R] (p : R[X]) [Decidable (p = 0)] :
    p.roots = if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h) := by
  -- porting noteL `‹_›` doesn't work for instance arguments
  rename_i iR ip0
  -- ⊢ roots p = if h : p = 0 then ∅ else Classical.choose (_ : ∃ s, ↑(↑Multiset.ca …
  obtain rfl := Subsingleton.elim iR (Classical.decEq R)
  -- ⊢ roots p = if h : p = 0 then ∅ else Classical.choose (_ : ∃ s, ↑(↑Multiset.ca …
  obtain rfl := Subsingleton.elim ip0 (Classical.dec (p = 0))
  -- ⊢ roots p = if h : p = 0 then ∅ else Classical.choose (_ : ∃ s, ↑(↑Multiset.ca …
  rfl
  -- 🎉 no goals
#align polynomial.roots_def Polynomial.roots_def

@[simp]
theorem roots_zero : (0 : R[X]).roots = 0 :=
  dif_pos rfl
#align polynomial.roots_zero Polynomial.roots_zero

theorem card_roots (hp0 : p ≠ 0) : (Multiset.card (roots p) : WithBot ℕ) ≤ degree p := by
  classical
  unfold roots
  rw [dif_neg hp0]
  exact (Classical.choose_spec (exists_multiset_roots hp0)).1
#align polynomial.card_roots Polynomial.card_roots

theorem card_roots' (p : R[X]) : Multiset.card p.roots ≤ natDegree p := by
  by_cases hp0 : p = 0
  -- ⊢ ↑Multiset.card (roots p) ≤ natDegree p
  · simp [hp0]
    -- 🎉 no goals
  exact WithBot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq <| degree_eq_natDegree hp0))
  -- 🎉 no goals
#align polynomial.card_roots' Polynomial.card_roots'

theorem card_roots_sub_C {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    (Multiset.card (p - C a).roots : WithBot ℕ) ≤ degree p :=
  calc
    (Multiset.card (p - C a).roots : WithBot ℕ) ≤ degree (p - C a) :=
      card_roots <| mt sub_eq_zero.1 fun h => not_le_of_gt hp0 <| h.symm ▸ degree_C_le
    _ = degree p := by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0
                       -- ⊢ degree (p + ↑C (-a)) = degree p
                                                     -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.card_roots_sub_C Polynomial.card_roots_sub_C

theorem card_roots_sub_C' {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    Multiset.card (p - C a).roots ≤ natDegree p :=
  WithBot.coe_le_coe.1
    (le_trans (card_roots_sub_C hp0)
      (le_of_eq <| degree_eq_natDegree fun h => by simp_all [lt_irrefl]))
                                                   -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.card_roots_sub_C' Polynomial.card_roots_sub_C'

@[simp]
theorem count_roots [DecidableEq R] (p : R[X]) : p.roots.count a = rootMultiplicity a p := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  rw [roots_def, dif_neg hp]
  exact (Classical.choose_spec (exists_multiset_roots hp)).2 a
#align polynomial.count_roots Polynomial.count_roots

@[simp]
theorem mem_roots' : a ∈ p.roots ↔ p ≠ 0 ∧ IsRoot p a := by
  classical
  rw [← count_pos, count_roots p, rootMultiplicity_pos']
#align polynomial.mem_roots' Polynomial.mem_roots'

theorem mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ IsRoot p a :=
  mem_roots'.trans <| and_iff_right hp
#align polynomial.mem_roots Polynomial.mem_roots

theorem ne_zero_of_mem_roots (h : a ∈ p.roots) : p ≠ 0 :=
  (mem_roots'.1 h).1
#align polynomial.ne_zero_of_mem_roots Polynomial.ne_zero_of_mem_roots

theorem isRoot_of_mem_roots (h : a ∈ p.roots) : IsRoot p a :=
  (mem_roots'.1 h).2
#align polynomial.is_root_of_mem_roots Polynomial.isRoot_of_mem_roots

-- Porting note: added during port.
lemma mem_roots_iff_aeval_eq_zero (w : p ≠ 0) : x ∈ roots p ↔ aeval x p = 0 := by
  rw [mem_roots w, IsRoot.def, aeval_def, eval₂_eq_eval_map]
  -- ⊢ eval x p = 0 ↔ eval x (map (algebraMap R R) p) = 0
  simp
  -- 🎉 no goals

theorem card_le_degree_of_subset_roots {p : R[X]} {Z : Finset R} (h : Z.val ⊆ p.roots) :
    Z.card ≤ p.natDegree :=
  (Multiset.card_le_of_le (Finset.val_le_iff_val_subset.2 h)).trans (Polynomial.card_roots' p)
#align polynomial.card_le_degree_of_subset_roots Polynomial.card_le_degree_of_subset_roots

theorem finite_setOf_isRoot {p : R[X]} (hp : p ≠ 0) : Set.Finite { x | IsRoot p x } := by
  classical
  simpa only [← Finset.setOf_mem, Multiset.mem_toFinset, mem_roots hp]
    using p.roots.toFinset.finite_toSet
#align polynomial.finite_set_of_is_root Polynomial.finite_setOf_isRoot

theorem eq_zero_of_infinite_isRoot (p : R[X]) (h : Set.Infinite { x | IsRoot p x }) : p = 0 :=
  not_imp_comm.mp finite_setOf_isRoot h
#align polynomial.eq_zero_of_infinite_is_root Polynomial.eq_zero_of_infinite_isRoot

theorem exists_max_root [LinearOrder R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x ≤ x₀ :=
  Set.exists_upper_bound_image _ _ <| finite_setOf_isRoot hp
#align polynomial.exists_max_root Polynomial.exists_max_root

theorem exists_min_root [LinearOrder R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x₀ ≤ x :=
  Set.exists_lower_bound_image _ _ <| finite_setOf_isRoot hp
#align polynomial.exists_min_root Polynomial.exists_min_root

theorem eq_of_infinite_eval_eq (p q : R[X]) (h : Set.Infinite { x | eval x p = eval x q }) :
    p = q := by
  rw [← sub_eq_zero]
  -- ⊢ p - q = 0
  apply eq_zero_of_infinite_isRoot
  -- ⊢ Set.Infinite {x | IsRoot (p - q) x}
  simpa only [IsRoot, eval_sub, sub_eq_zero]
  -- 🎉 no goals
#align polynomial.eq_of_infinite_eval_eq Polynomial.eq_of_infinite_eval_eq

theorem roots_mul {p q : R[X]} (hpq : p * q ≠ 0) : (p * q).roots = p.roots + q.roots := by
  classical
  exact Multiset.ext.mpr fun r => by
    rw [count_add, count_roots, count_roots, count_roots, rootMultiplicity_mul hpq]
#align polynomial.roots_mul Polynomial.roots_mul

theorem roots.le_of_dvd (h : q ≠ 0) : p ∣ q → roots p ≤ roots q := by
  rintro ⟨k, rfl⟩
  -- ⊢ roots p ≤ roots (p * k)
  exact Multiset.le_iff_exists_add.mpr ⟨k.roots, roots_mul h⟩
  -- 🎉 no goals
#align polynomial.roots.le_of_dvd Polynomial.roots.le_of_dvd

theorem mem_roots_sub_C' {p : R[X]} {a x : R} : x ∈ (p - C a).roots ↔ p ≠ C a ∧ p.eval x = a := by
  rw [mem_roots', IsRoot.def, sub_ne_zero, eval_sub, sub_eq_zero, eval_C]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.mem_roots_sub_C' Polynomial.mem_roots_sub_C'

theorem mem_roots_sub_C {p : R[X]} {a x : R} (hp0 : 0 < degree p) :
    x ∈ (p - C a).roots ↔ p.eval x = a :=
  mem_roots_sub_C'.trans <| and_iff_right fun hp => hp0.not_le <| hp.symm ▸ degree_C_le
set_option linter.uppercaseLean3 false in
#align polynomial.mem_roots_sub_C Polynomial.mem_roots_sub_C

@[simp]
theorem roots_X_sub_C (r : R) : roots (X - C r) = {r} := by
  classical
  ext s
  rw [count_roots, rootMultiplicity_X_sub_C, count_singleton]
set_option linter.uppercaseLean3 false in
#align polynomial.roots_X_sub_C Polynomial.roots_X_sub_C

@[simp]
theorem roots_X : roots (X : R[X]) = {0} := by rw [← roots_X_sub_C, C_0, sub_zero]
                                               -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.roots_X Polynomial.roots_X

@[simp]
theorem roots_C (x : R) : (C x).roots = 0 := by
  classical exact
  if H : x = 0 then by rw [H, C_0, roots_zero]
  else
    Multiset.ext.mpr fun r => (by
      rw [count_roots, count_zero, rootMultiplicity_eq_zero (not_isRoot_C _ _ H)])
set_option linter.uppercaseLean3 false in
#align polynomial.roots_C Polynomial.roots_C

@[simp]
theorem roots_one : (1 : R[X]).roots = ∅ :=
  roots_C 1
#align polynomial.roots_one Polynomial.roots_one

@[simp]
theorem roots_C_mul (p : R[X]) (ha : a ≠ 0) : (C a * p).roots = p.roots := by
  by_cases hp : p = 0 <;>
  -- ⊢ roots (↑C a * p) = roots p
    simp only [roots_mul, *, Ne.def, mul_eq_zero, C_eq_zero, or_self_iff, not_false_iff, roots_C,
      zero_add, mul_zero]
set_option linter.uppercaseLean3 false in
#align polynomial.roots_C_mul Polynomial.roots_C_mul

@[simp]
theorem roots_smul_nonzero (p : R[X]) (ha : a ≠ 0) : (a • p).roots = p.roots := by
  rw [smul_eq_C_mul, roots_C_mul _ ha]
  -- 🎉 no goals
#align polynomial.roots_smul_nonzero Polynomial.roots_smul_nonzero

theorem roots_list_prod (L : List R[X]) :
    (0 : R[X]) ∉ L → L.prod.roots = (L : Multiset R[X]).bind roots :=
  List.recOn L (fun _ => roots_one) fun hd tl ih H => by
    rw [List.mem_cons, not_or] at H
    -- ⊢ roots (List.prod (hd :: tl)) = Multiset.bind (↑(hd :: tl)) roots
    rw [List.prod_cons, roots_mul (mul_ne_zero (Ne.symm H.1) <| List.prod_ne_zero H.2), ←
      Multiset.cons_coe, Multiset.cons_bind, ih H.2]
#align polynomial.roots_list_prod Polynomial.roots_list_prod

theorem roots_multiset_prod (m : Multiset R[X]) : (0 : R[X]) ∉ m → m.prod.roots = m.bind roots := by
  rcases m with ⟨L⟩
  -- ⊢ ¬0 ∈ Quot.mk Setoid.r L → roots (prod (Quot.mk Setoid.r L)) = Multiset.bind  …
  simpa only [Multiset.coe_prod, quot_mk_to_coe''] using roots_list_prod L
  -- 🎉 no goals
#align polynomial.roots_multiset_prod Polynomial.roots_multiset_prod

theorem roots_prod {ι : Type*} (f : ι → R[X]) (s : Finset ι) :
    s.prod f ≠ 0 → (s.prod f).roots = s.val.bind fun i => roots (f i) := by
  rcases s with ⟨m, hm⟩
  -- ⊢ Finset.prod { val := m, nodup := hm } f ≠ 0 → roots (Finset.prod { val := m, …
  simpa [Multiset.prod_eq_zero_iff, Multiset.bind_map] using roots_multiset_prod (m.map f)
  -- 🎉 no goals
#align polynomial.roots_prod Polynomial.roots_prod

@[simp]
theorem roots_pow (p : R[X]) (n : ℕ) : (p ^ n).roots = n • p.roots := by
  induction' n with n ihn
  -- ⊢ roots (p ^ Nat.zero) = Nat.zero • roots p
  · rw [pow_zero, roots_one, Nat.zero_eq, zero_smul, empty_eq_zero]
    -- 🎉 no goals
  · rcases eq_or_ne p 0 with (rfl | hp)
    -- ⊢ roots (0 ^ Nat.succ n) = Nat.succ n • roots 0
    · rw [zero_pow n.succ_pos, roots_zero, smul_zero]
      -- 🎉 no goals
    · rw [pow_succ', roots_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ihn, Nat.succ_eq_add_one,
        add_smul, one_smul]
#align polynomial.roots_pow Polynomial.roots_pow

theorem roots_X_pow (n : ℕ) : (X ^ n : R[X]).roots = n • ({0} : Multiset R) := by
  rw [roots_pow, roots_X]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.roots_X_pow Polynomial.roots_X_pow

theorem roots_C_mul_X_pow (ha : a ≠ 0) (n : ℕ) :
    Polynomial.roots (C a * X ^ n) = n • ({0} : Multiset R) := by
  rw [roots_C_mul _ ha, roots_X_pow]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.roots_C_mul_X_pow Polynomial.roots_C_mul_X_pow

@[simp]
theorem roots_monomial (ha : a ≠ 0) (n : ℕ) : (monomial n a).roots = n • ({0} : Multiset R) := by
  rw [← C_mul_X_pow_eq_monomial, roots_C_mul_X_pow ha]
  -- 🎉 no goals
#align polynomial.roots_monomial Polynomial.roots_monomial

theorem roots_prod_X_sub_C (s : Finset R) : (s.prod fun a => X - C a).roots = s.val := by
  apply (roots_prod (fun a => X - C a) s ?_).trans
  -- ⊢ (Multiset.bind s.val fun i => roots (X - ↑C i)) = s.val
  · simp_rw [roots_X_sub_C]
    -- ⊢ (Multiset.bind s.val fun i => {i}) = s.val
    rw [Multiset.bind_singleton, Multiset.map_id']
    -- 🎉 no goals
  · refine prod_ne_zero_iff.mpr (fun a _ => X_sub_C_ne_zero a)
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.roots_prod_X_sub_C Polynomial.roots_prod_X_sub_C

@[simp]
theorem roots_multiset_prod_X_sub_C (s : Multiset R) : (s.map fun a => X - C a).prod.roots = s := by
  rw [roots_multiset_prod, Multiset.bind_map]
  -- ⊢ (Multiset.bind s fun a => roots (X - ↑C a)) = s
  · simp_rw [roots_X_sub_C]
    -- ⊢ (Multiset.bind s fun a => {a}) = s
    rw [Multiset.bind_singleton, Multiset.map_id']
    -- 🎉 no goals
  · rw [Multiset.mem_map]
    -- ⊢ ¬∃ a, a ∈ s ∧ X - ↑C a = 0
    rintro ⟨a, -, h⟩
    -- ⊢ False
    exact X_sub_C_ne_zero a h
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.roots_multiset_prod_X_sub_C Polynomial.roots_multiset_prod_X_sub_C

@[simp]
theorem natDegree_multiset_prod_X_sub_C_eq_card (s : Multiset R) :
    (s.map fun a => X - C a).prod.natDegree = Multiset.card s := by
  rw [natDegree_multiset_prod_of_monic, Multiset.map_map]
  -- ⊢ Multiset.sum (Multiset.map (natDegree ∘ fun a => X - ↑C a) s) = ↑Multiset.ca …
  · simp only [(· ∘ ·), natDegree_X_sub_C, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
      mul_one]
  · exact Multiset.forall_mem_map_iff.2 fun a _ => monic_X_sub_C a
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_multiset_prod_X_sub_C_eq_card Polynomial.natDegree_multiset_prod_X_sub_C_eq_card

theorem card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
    Multiset.card (roots ((X : R[X]) ^ n - C a)) ≤ n :=
  WithBot.coe_le_coe.1 <|
    calc
      (Multiset.card (roots ((X : R[X]) ^ n - C a)) : WithBot ℕ) ≤ degree ((X : R[X]) ^ n - C a) :=
        card_roots (X_pow_sub_C_ne_zero hn a)
      _ = n := degree_X_pow_sub_C hn a
set_option linter.uppercaseLean3 false in
#align polynomial.card_roots_X_pow_sub_C Polynomial.card_roots_X_pow_sub_C

section NthRoots

/-- `nthRoots n a` noncomputably returns the solutions to `x ^ n = a`-/
def nthRoots (n : ℕ) (a : R) : Multiset R :=
  roots ((X : R[X]) ^ n - C a)
#align polynomial.nth_roots Polynomial.nthRoots

@[simp]
theorem mem_nthRoots {n : ℕ} (hn : 0 < n) {a x : R} : x ∈ nthRoots n a ↔ x ^ n = a := by
  rw [nthRoots, mem_roots (X_pow_sub_C_ne_zero hn a), IsRoot.def, eval_sub, eval_C, eval_pow,
    eval_X, sub_eq_zero]
#align polynomial.mem_nth_roots Polynomial.mem_nthRoots

@[simp]
theorem nthRoots_zero (r : R) : nthRoots 0 r = 0 := by
  simp only [empty_eq_zero, pow_zero, nthRoots, ← C_1, ← C_sub, roots_C]
  -- 🎉 no goals
#align polynomial.nth_roots_zero Polynomial.nthRoots_zero

theorem card_nthRoots (n : ℕ) (a : R) : Multiset.card (nthRoots n a) ≤ n := by
  classical exact
  (if hn : n = 0 then
    if h : (X : R[X]) ^ n - C a = 0 then by
      simp [Nat.zero_le, nthRoots, roots, h, dif_pos rfl, empty_eq_zero, Multiset.card_zero]
    else
      WithBot.coe_le_coe.1
        (le_trans (card_roots h)
          (by
            rw [hn, pow_zero, ← C_1, ← RingHom.map_sub]
            exact degree_C_le))
  else by
    rw [← WithBot.coe_le_coe]
    simp only [← Nat.cast_withBot]
    rw [← degree_X_pow_sub_C (Nat.pos_of_ne_zero hn) a]
    exact card_roots (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) a))
#align polynomial.card_nth_roots Polynomial.card_nthRoots

@[simp]
theorem nthRoots_two_eq_zero_iff {r : R} : nthRoots 2 r = 0 ↔ ¬IsSquare r := by
  simp_rw [isSquare_iff_exists_sq, eq_zero_iff_forall_not_mem, mem_nthRoots (by norm_num : 0 < 2),
    ← not_exists, eq_comm]
#align polynomial.nth_roots_two_eq_zero_iff Polynomial.nthRoots_two_eq_zero_iff

/-- The multiset `nthRoots ↑n (1 : R)` as a Finset. -/
def nthRootsFinset (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] : Finset R :=
  haveI := Classical.decEq R
  Multiset.toFinset (nthRoots n (1 : R))
#align polynomial.nth_roots_finset Polynomial.nthRootsFinset

-- porting note: new
lemma nthRootsFinset_def (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] [DecidableEq R] :
    nthRootsFinset n R = Multiset.toFinset (nthRoots n (1 : R)) := by
  unfold nthRootsFinset
  -- ⊢ toFinset (nthRoots n 1) = toFinset (nthRoots n 1)
  convert rfl
  -- 🎉 no goals

@[simp]
theorem mem_nthRootsFinset {n : ℕ} (h : 0 < n) {x : R} :
    x ∈ nthRootsFinset n R ↔ x ^ (n : ℕ) = 1 := by
  classical
  rw [nthRootsFinset_def, mem_toFinset, mem_nthRoots h]
#align polynomial.mem_nth_roots_finset Polynomial.mem_nthRootsFinset

@[simp]
theorem nthRootsFinset_zero : nthRootsFinset 0 R = ∅ := by classical simp [nthRootsFinset_def]
                                                           -- 🎉 no goals
#align polynomial.nth_roots_finset_zero Polynomial.nthRootsFinset_zero

end NthRoots

theorem Monic.comp (hp : p.Monic) (hq : q.Monic) (h : q.natDegree ≠ 0) : (p.comp q).Monic := by
  rw [Monic.def, leadingCoeff_comp h, Monic.def.1 hp, Monic.def.1 hq, one_pow, one_mul]
  -- 🎉 no goals
#align polynomial.monic.comp Polynomial.Monic.comp

theorem Monic.comp_X_add_C (hp : p.Monic) (r : R) : (p.comp (X + C r)).Monic := by
  refine' hp.comp (monic_X_add_C _) fun ha => _
  -- ⊢ False
  rw [natDegree_X_add_C] at ha
  -- ⊢ False
  exact one_ne_zero ha
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.monic.comp_X_add_C Polynomial.Monic.comp_X_add_C

theorem Monic.comp_X_sub_C (hp : p.Monic) (r : R) : (p.comp (X - C r)).Monic := by
  simpa using hp.comp_X_add_C (-r)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.monic.comp_X_sub_C Polynomial.Monic.comp_X_sub_C

theorem units_coeff_zero_smul (c : R[X]ˣ) (p : R[X]) : (c : R[X]).coeff 0 • p = c * p := by
  rw [← Polynomial.C_mul', ← Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]
  -- 🎉 no goals
#align polynomial.units_coeff_zero_smul Polynomial.units_coeff_zero_smul

@[simp]
theorem natDegree_coe_units (u : R[X]ˣ) : natDegree (u : R[X]) = 0 :=
  natDegree_eq_of_degree_eq_some (degree_coe_units u)
#align polynomial.nat_degree_coe_units Polynomial.natDegree_coe_units

theorem comp_eq_zero_iff : p.comp q = 0 ↔ p = 0 ∨ p.eval (q.coeff 0) = 0 ∧ q = C (q.coeff 0) := by
  constructor
  -- ⊢ comp p q = 0 → p = 0 ∨ eval (coeff q 0) p = 0 ∧ q = ↑C (coeff q 0)
  · intro h
    -- ⊢ p = 0 ∨ eval (coeff q 0) p = 0 ∧ q = ↑C (coeff q 0)
    have key : p.natDegree = 0 ∨ q.natDegree = 0 := by
      rw [← mul_eq_zero, ← natDegree_comp, h, natDegree_zero]
    replace key := Or.imp eq_C_of_natDegree_eq_zero eq_C_of_natDegree_eq_zero key
    -- ⊢ p = 0 ∨ eval (coeff q 0) p = 0 ∧ q = ↑C (coeff q 0)
    cases' key with key key
    -- ⊢ p = 0 ∨ eval (coeff q 0) p = 0 ∧ q = ↑C (coeff q 0)
    · rw [key, C_comp] at h
      -- ⊢ p = 0 ∨ eval (coeff q 0) p = 0 ∧ q = ↑C (coeff q 0)
      exact Or.inl (key.trans h)
      -- 🎉 no goals
    · rw [key, comp_C, C_eq_zero] at h
      -- ⊢ p = 0 ∨ eval (coeff q 0) p = 0 ∧ q = ↑C (coeff q 0)
      exact Or.inr ⟨h, key⟩
      -- 🎉 no goals
  · exact fun h =>
      Or.rec (fun h => by rw [h, zero_comp]) (fun h => by rw [h.2, comp_C, h.1, C_0]) h
#align polynomial.comp_eq_zero_iff Polynomial.comp_eq_zero_iff

theorem zero_of_eval_zero [Infinite R] (p : R[X]) (h : ∀ x, p.eval x = 0) : p = 0 := by
  classical
  by_contra hp
  refine @Fintype.false R _ ?_
  exact ⟨p.roots.toFinset, fun x => Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (h _))⟩
#align polynomial.zero_of_eval_zero Polynomial.zero_of_eval_zero

theorem funext [Infinite R] {p q : R[X]} (ext : ∀ r : R, p.eval r = q.eval r) : p = q := by
  rw [← sub_eq_zero]
  -- ⊢ p - q = 0
  apply zero_of_eval_zero
  -- ⊢ ∀ (x : R), eval x (p - q) = 0
  intro x
  -- ⊢ eval x (p - q) = 0
  rw [eval_sub, sub_eq_zero, ext]
  -- 🎉 no goals
#align polynomial.funext Polynomial.funext

variable [CommRing T]

/-- The set of distinct roots of `p` in `E`.

If you have a non-separable polynomial, use `Polynomial.roots` for the multiset
where multiple roots have the appropriate multiplicity. -/
def rootSet (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Set S :=
  haveI := Classical.decEq S
  (p.map (algebraMap T S)).roots.toFinset
#align polynomial.root_set Polynomial.rootSet

theorem rootSet_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] [DecidableEq S] :
    p.rootSet S = (p.map (algebraMap T S)).roots.toFinset := by
  rw [rootSet]
  -- ⊢ ↑(toFinset (roots (map (algebraMap T S) p))) = ↑(toFinset (roots (map (algeb …
  convert rfl
  -- 🎉 no goals
#align polynomial.root_set_def Polynomial.rootSet_def

@[simp]
theorem rootSet_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (C a).rootSet S = ∅ := by
  classical
  rw [rootSet_def, map_C, roots_C, Multiset.toFinset_zero, Finset.coe_empty]
set_option linter.uppercaseLean3 false in
#align polynomial.root_set_C Polynomial.rootSet_C

@[simp]
theorem rootSet_zero (S) [CommRing S] [IsDomain S] [Algebra T S] : (0 : T[X]).rootSet S = ∅ := by
  rw [← C_0, rootSet_C]
  -- 🎉 no goals
#align polynomial.root_set_zero Polynomial.rootSet_zero

instance rootSetFintype (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S] :
    Fintype (p.rootSet S) :=
  FinsetCoe.fintype _
#align polynomial.root_set_fintype Polynomial.rootSetFintype

theorem rootSet_finite (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S] :
    (p.rootSet S).Finite :=
  Set.toFinite _
#align polynomial.root_set_finite Polynomial.rootSet_finite

/-- The set of roots of all polynomials of bounded degree and having coefficients in a finite set
is finite. -/
theorem bUnion_roots_finite {R S : Type*} [Semiring R] [CommRing S] [IsDomain S] [DecidableEq S]
    (m : R →+* S) (d : ℕ) {U : Set R} (h : U.Finite) :
    (⋃ (f : R[X]) (_ : f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U),
        ((f.map m).roots.toFinset.toSet : Set S)).Finite :=
  Set.Finite.biUnion
    (by
      -- We prove that the set of polynomials under consideration is finite because its
      -- image by the injective map `π` is finite
      let π : R[X] → Fin (d + 1) → R := fun f i => f.coeff i
      -- ⊢ Set.Finite fun f => natDegree f ≤ d ∧ ∀ (i : ℕ), coeff f i ∈ U
      refine' ((Set.Finite.pi fun _ => h).subset <| _).of_finite_image (_ : Set.InjOn π _)
      -- ⊢ (π '' fun f => natDegree f ≤ d ∧ ∀ (i : ℕ), coeff f i ∈ U) ⊆ Set.pi Set.univ …
      · exact Set.image_subset_iff.2 fun f hf i _ => hf.2 i
        -- 🎉 no goals
      · refine' fun x hx y hy hxy => (ext_iff_natDegree_le hx.1 hy.1).2 fun i hi => _
        -- ⊢ coeff x i = coeff y i
        exact id congr_fun hxy ⟨i, Nat.lt_succ_of_le hi⟩)
        -- 🎉 no goals
    fun i _ => Finset.finite_toSet _
#align polynomial.bUnion_roots_finite Polynomial.bUnion_roots_finite

theorem mem_rootSet' {p : T[X]} {S : Type*} [CommRing S] [IsDomain S] [Algebra T S] {a : S} :
    a ∈ p.rootSet S ↔ p.map (algebraMap T S) ≠ 0 ∧ aeval a p = 0 := by
  classical
  rw [rootSet_def, Finset.mem_coe, mem_toFinset, mem_roots', IsRoot.def, ← eval₂_eq_eval_map,
    aeval_def]
#align polynomial.mem_root_set' Polynomial.mem_rootSet'

theorem mem_rootSet {p : T[X]} {S : Type*} [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {a : S} : a ∈ p.rootSet S ↔ p ≠ 0 ∧ aeval a p = 0 := by
  rw [mem_rootSet',
    (map_injective _ (NoZeroSMulDivisors.algebraMap_injective T S)).ne_iff' (Polynomial.map_zero _)]
#align polynomial.mem_root_set Polynomial.mem_rootSet

theorem mem_rootSet_of_ne {p : T[X]} {S : Type*} [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] (hp : p ≠ 0) {a : S} : a ∈ p.rootSet S ↔ aeval a p = 0 :=
  mem_rootSet.trans <| and_iff_right hp
#align polynomial.mem_root_set_of_ne Polynomial.mem_rootSet_of_ne

theorem rootSet_maps_to' {p : T[X]} {S S'} [CommRing S] [IsDomain S] [Algebra T S] [CommRing S']
    [IsDomain S'] [Algebra T S'] (hp : p.map (algebraMap T S') = 0 → p.map (algebraMap T S) = 0)
    (f : S →ₐ[T] S') : (p.rootSet S).MapsTo f (p.rootSet S') := fun x hx => by
  rw [mem_rootSet'] at hx ⊢
  -- ⊢ map (algebraMap T S') p ≠ 0 ∧ ↑(aeval (↑f x)) p = 0
  rw [aeval_algHom, AlgHom.comp_apply, hx.2, _root_.map_zero]
  -- ⊢ map (algebraMap T S') p ≠ 0 ∧ 0 = 0
  exact ⟨mt hp hx.1, rfl⟩
  -- 🎉 no goals
#align polynomial.root_set_maps_to' Polynomial.rootSet_maps_to'

theorem ne_zero_of_mem_rootSet {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    (h : a ∈ p.rootSet S) : p ≠ 0 := fun hf => by rwa [hf, rootSet_zero] at h
                                                  -- 🎉 no goals
#align polynomial.ne_zero_of_mem_root_set Polynomial.ne_zero_of_mem_rootSet

theorem aeval_eq_zero_of_mem_rootSet {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    (hx : a ∈ p.rootSet S) : aeval a p = 0 :=
  (mem_rootSet'.1 hx).2
#align polynomial.aeval_eq_zero_of_mem_root_set Polynomial.aeval_eq_zero_of_mem_rootSet

theorem rootSet_mapsTo {p : T[X]} {S S'} [CommRing S] [IsDomain S] [Algebra T S] [CommRing S']
    [IsDomain S'] [Algebra T S'] [NoZeroSMulDivisors T S'] (f : S →ₐ[T] S') :
    (p.rootSet S).MapsTo f (p.rootSet S') := by
  refine' rootSet_maps_to' (fun h₀ => _) f
  -- ⊢ map (algebraMap T S) p = 0
  obtain rfl : p = 0 :=
    map_injective _ (NoZeroSMulDivisors.algebraMap_injective T S') (by rwa [Polynomial.map_zero])
  exact Polynomial.map_zero _
  -- 🎉 no goals
#align polynomial.root_set_maps_to Polynomial.rootSet_mapsTo

end Roots

theorem coeff_coe_units_zero_ne_zero (u : R[X]ˣ) : coeff (u : R[X]) 0 ≠ 0 := by
  conv in 0 => rw [← natDegree_coe_units u]
  -- ⊢ coeff (↑u) (natDegree ↑u) ≠ 0
  rw [← leadingCoeff, Ne.def, leadingCoeff_eq_zero]
  -- ⊢ ¬↑u = 0
  exact Units.ne_zero _
  -- 🎉 no goals
#align polynomial.coeff_coe_units_zero_ne_zero Polynomial.coeff_coe_units_zero_ne_zero

theorem degree_eq_degree_of_associated (h : Associated p q) : degree p = degree q := by
  let ⟨u, hu⟩ := h
  -- ⊢ degree p = degree q
  simp [hu.symm]
  -- 🎉 no goals
#align polynomial.degree_eq_degree_of_associated Polynomial.degree_eq_degree_of_associated

theorem degree_eq_one_of_irreducible_of_root (hi : Irreducible p) {x : R} (hx : IsRoot p x) :
    degree p = 1 :=
  let ⟨g, hg⟩ := dvd_iff_isRoot.2 hx
  have : IsUnit (X - C x) ∨ IsUnit g := hi.isUnit_or_isUnit hg
  this.elim
    (fun h => by
      have h₁ : degree (X - C x) = 1 := degree_X_sub_C x
      -- ⊢ degree p = 1
      have h₂ : degree (X - C x) = 0 := degree_eq_zero_of_isUnit h
      -- ⊢ degree p = 1
      rw [h₁] at h₂; exact absurd h₂ (by decide))
      -- ⊢ degree p = 1
                     -- 🎉 no goals
    fun hgu => by rw [hg, degree_mul, degree_X_sub_C, degree_eq_zero_of_isUnit hgu, add_zero]
                  -- 🎉 no goals
#align polynomial.degree_eq_one_of_irreducible_of_root Polynomial.degree_eq_one_of_irreducible_of_root

/-- Division by a monic polynomial doesn't change the leading coefficient. -/
theorem leadingCoeff_divByMonic_of_monic {R : Type u} [CommRing R] {p q : R[X]} (hmonic : q.Monic)
    (hdegree : q.degree ≤ p.degree) : (p /ₘ q).leadingCoeff = p.leadingCoeff := by
  nontriviality
  -- ⊢ leadingCoeff (p /ₘ q) = leadingCoeff p
  have h : q.leadingCoeff * (p /ₘ q).leadingCoeff ≠ 0 := by
    simpa [divByMonic_eq_zero_iff hmonic, hmonic.leadingCoeff,
      Nat.WithBot.one_le_iff_zero_lt] using hdegree
  nth_rw 2 [← modByMonic_add_div p hmonic]
  -- ⊢ leadingCoeff (p /ₘ q) = leadingCoeff (p %ₘ q + q * (p /ₘ q))
  rw [leadingCoeff_add_of_degree_lt, leadingCoeff_monic_mul hmonic]
  -- ⊢ degree (p %ₘ q) < degree (q * (p /ₘ q))
  rw [degree_mul' h, degree_add_divByMonic hmonic hdegree]
  -- ⊢ degree (p %ₘ q) < degree p
  exact (degree_modByMonic_lt p hmonic).trans_le hdegree
  -- 🎉 no goals
#align polynomial.leading_coeff_div_by_monic_of_monic Polynomial.leadingCoeff_divByMonic_of_monic

theorem leadingCoeff_divByMonic_X_sub_C (p : R[X]) (hp : degree p ≠ 0) (a : R) :
    leadingCoeff (p /ₘ (X - C a)) = leadingCoeff p := by
  nontriviality
  -- ⊢ leadingCoeff (p /ₘ (X - ↑C a)) = leadingCoeff p
  cases' hp.lt_or_lt with hd hd
  -- ⊢ leadingCoeff (p /ₘ (X - ↑C a)) = leadingCoeff p
  · rw [degree_eq_bot.mp <| (Nat.WithBot.lt_zero_iff _).mp hd, zero_divByMonic]
    -- 🎉 no goals
  refine' leadingCoeff_divByMonic_of_monic (monic_X_sub_C a) _
  -- ⊢ degree (X - ↑C a) ≤ degree p
  rwa [degree_X_sub_C, Nat.WithBot.one_le_iff_zero_lt]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.leading_coeff_div_by_monic_X_sub_C Polynomial.leadingCoeff_divByMonic_X_sub_C

theorem eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le {R} [CommRing R] {p q : R[X]}
    (hp : p.Monic) (hdiv : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) :
    q = C q.leadingCoeff * p := by
  obtain ⟨r, hr⟩ := hdiv
  -- ⊢ q = ↑C (leadingCoeff q) * p
  obtain rfl | hq := eq_or_ne q 0; · simp
  -- ⊢ 0 = ↑C (leadingCoeff 0) * p
                                     -- 🎉 no goals
  have rzero : r ≠ 0 := fun h => by simp [h, hq] at hr
  -- ⊢ q = ↑C (leadingCoeff q) * p
  rw [hr, natDegree_mul'] at hdeg; swap
  -- ⊢ q = ↑C (leadingCoeff q) * p
                                   -- ⊢ leadingCoeff p * leadingCoeff r ≠ 0
  · rw [hp.leadingCoeff, one_mul, leadingCoeff_ne_zero]
    -- ⊢ r ≠ 0
    exact rzero
    -- 🎉 no goals
  rw [mul_comm, @eq_C_of_natDegree_eq_zero _ _ r] at hr
  -- ⊢ q = ↑C (leadingCoeff q) * p
  · convert hr
    -- ⊢ leadingCoeff q = coeff r 0
    convert leadingCoeff_C (coeff r 0) using 1
    -- ⊢ leadingCoeff q = leadingCoeff (↑C (coeff r 0))
    rw [hr, leadingCoeff_mul_monic hp]
    -- 🎉 no goals
  · exact (add_right_inj _).1 (le_antisymm hdeg <| Nat.le.intro rfl)
    -- 🎉 no goals
#align polynomial.eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le

theorem eq_of_monic_of_dvd_of_natDegree_le {R} [CommRing R] {p q : R[X]} (hp : p.Monic)
    (hq : q.Monic) (hdiv : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) : q = p := by
  convert eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hp hdiv hdeg
  -- ⊢ p = ↑C (leadingCoeff q) * p
  rw [hq.leadingCoeff, C_1, one_mul]
  -- 🎉 no goals
#align polynomial.eq_of_monic_of_dvd_of_nat_degree_le Polynomial.eq_of_monic_of_dvd_of_natDegree_le

theorem isCoprime_X_sub_C_of_isUnit_sub {R} [CommRing R] {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (X - C a) (X - C b) :=
  ⟨-C h.unit⁻¹.val, C h.unit⁻¹.val, by
    rw [neg_mul_comm, ← left_distrib, neg_add_eq_sub, sub_sub_sub_cancel_left, ← C_sub, ← C_mul]
    -- ⊢ ↑C (↑(IsUnit.unit h)⁻¹ * (a - b)) = 1
    rw [←C_1]
    -- ⊢ ↑C (↑(IsUnit.unit h)⁻¹ * (a - b)) = ↑C 1
    congr
    -- ⊢ ↑(IsUnit.unit h)⁻¹ * (a - b) = 1
    exact h.val_inv_mul⟩
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.is_coprime_X_sub_C_of_is_unit_sub Polynomial.isCoprime_X_sub_C_of_isUnit_sub

theorem pairwise_coprime_X_sub_C {K} [Field K] {I : Type v} {s : I → K} (H : Function.Injective s) :
    Pairwise (IsCoprime on fun i : I => X - C (s i)) := fun _ _ hij =>
  isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne <| H.ne hij).isUnit
set_option linter.uppercaseLean3 false in
#align polynomial.pairwise_coprime_X_sub_C Polynomial.pairwise_coprime_X_sub_C

theorem monic_prod_multiset_X_sub_C : Monic (p.roots.map fun a => X - C a).prod :=
  monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a
set_option linter.uppercaseLean3 false in
#align polynomial.monic_prod_multiset_X_sub_C Polynomial.monic_prod_multiset_X_sub_C

theorem prod_multiset_root_eq_finset_root [DecidableEq R] :
    (p.roots.map fun a => X - C a).prod =
      p.roots.toFinset.prod fun a => (X - C a) ^ rootMultiplicity a p :=
  by simp only [count_roots, Finset.prod_multiset_map_count]
     -- 🎉 no goals
#align polynomial.prod_multiset_root_eq_finset_root Polynomial.prod_multiset_root_eq_finset_root

/-- The product `∏ (X - a)` for `a` inside the multiset `p.roots` divides `p`. -/
theorem prod_multiset_X_sub_C_dvd (p : R[X]) : (p.roots.map fun a => X - C a).prod ∣ p := by
  classical
  rw [← map_dvd_map _ (IsFractionRing.injective R <| FractionRing R) monic_prod_multiset_X_sub_C]
  rw [prod_multiset_root_eq_finset_root, Polynomial.map_prod]
  refine' Finset.prod_dvd_of_coprime (fun a _ b _ h => _) fun a _ => _
  · simp_rw [Polynomial.map_pow, Polynomial.map_sub, map_C, map_X]
    exact (pairwise_coprime_X_sub_C (IsFractionRing.injective R <| FractionRing R) h).pow
  · exact Polynomial.map_dvd _ (pow_rootMultiplicity_dvd p a)
set_option linter.uppercaseLean3 false in
#align polynomial.prod_multiset_X_sub_C_dvd Polynomial.prod_multiset_X_sub_C_dvd

/-- A Galois connection. -/
theorem _root_.Multiset.prod_X_sub_C_dvd_iff_le_roots {p : R[X]} (hp : p ≠ 0) (s : Multiset R) :
    (s.map fun a => X - C a).prod ∣ p ↔ s ≤ p.roots := by
  classical exact
  ⟨fun h =>
    Multiset.le_iff_count.2 fun r => by
      rw [count_roots, le_rootMultiplicity_iff hp, ← Multiset.prod_replicate, ←
        Multiset.map_replicate fun a => X - C a, ← Multiset.filter_eq]
      exact (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| s.filter_le _).trans h,
    fun h =>
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map h).trans p.prod_multiset_X_sub_C_dvd⟩
set_option linter.uppercaseLean3 false in
#align multiset.prod_X_sub_C_dvd_iff_le_roots Multiset.prod_X_sub_C_dvd_iff_le_roots

theorem exists_prod_multiset_X_sub_C_mul (p : R[X]) :
    ∃ q,
      (p.roots.map fun a => X - C a).prod * q = p ∧
        Multiset.card p.roots + q.natDegree = p.natDegree ∧ q.roots = 0 := by
  obtain ⟨q, he⟩ := p.prod_multiset_X_sub_C_dvd
  -- ⊢ ∃ q, Multiset.prod (Multiset.map (fun a => X - ↑C a) (roots p)) * q = p ∧ ↑M …
  use q, he.symm
  -- ⊢ ↑Multiset.card (roots p) + natDegree q = natDegree p ∧ roots q = 0
  obtain rfl | hq := eq_or_ne q 0
  -- ⊢ ↑Multiset.card (roots p) + natDegree 0 = natDegree p ∧ roots 0 = 0
  · rw [mul_zero] at he
    -- ⊢ ↑Multiset.card (roots p) + natDegree 0 = natDegree p ∧ roots 0 = 0
    subst he
    -- ⊢ ↑Multiset.card (roots 0) + natDegree 0 = natDegree 0 ∧ roots 0 = 0
    simp
    -- 🎉 no goals
  constructor
  -- ⊢ ↑Multiset.card (roots p) + natDegree q = natDegree p
  · conv_rhs => rw [he]
    -- ⊢ ↑Multiset.card (roots p) + natDegree q = natDegree (Multiset.prod (Multiset. …
    rw [monic_prod_multiset_X_sub_C.natDegree_mul' hq, natDegree_multiset_prod_X_sub_C_eq_card]
    -- 🎉 no goals
  · replace he := congr_arg roots he.symm
    -- ⊢ roots q = 0
    rw [roots_mul, roots_multiset_prod_X_sub_C] at he
    -- ⊢ roots q = 0
    exacts [add_right_eq_self.1 he, mul_ne_zero monic_prod_multiset_X_sub_C.ne_zero hq]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.exists_prod_multiset_X_sub_C_mul Polynomial.exists_prod_multiset_X_sub_C_mul

/-- A polynomial `p` that has as many roots as its degree
can be written `p = p.leadingCoeff * ∏(X - a)`, for `a` in `p.roots`. -/
theorem C_leadingCoeff_mul_prod_multiset_X_sub_C (hroots : Multiset.card p.roots = p.natDegree) :
    C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p :=
  (eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le monic_prod_multiset_X_sub_C
      p.prod_multiset_X_sub_C_dvd
      ((natDegree_multiset_prod_X_sub_C_eq_card _).trans hroots).ge).symm
set_option linter.uppercaseLean3 false in
#align polynomial.C_leading_coeff_mul_prod_multiset_X_sub_C Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C

/-- A monic polynomial `p` that has as many roots as its degree
can be written `p = ∏(X - a)`, for `a` in `p.roots`. -/
theorem prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp : p.Monic)
    (hroots : Multiset.card p.roots = p.natDegree) : (p.roots.map fun a => X - C a).prod = p := by
  convert C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  -- ⊢ Multiset.prod (Multiset.map (fun a => X - ↑C a) (roots p)) = ↑C (leadingCoef …
  rw [hp.leadingCoeff, C_1, one_mul]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq

end CommRing

section

variable {A B : Type*} [CommRing A] [CommRing B]

theorem le_rootMultiplicity_map {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0) (a : A) :
    rootMultiplicity a p ≤ rootMultiplicity (f a) (p.map f) := by
  rw [le_rootMultiplicity_iff hmap]
  -- ⊢ (X - ↑C (↑f a)) ^ rootMultiplicity a p ∣ map f p
  refine' _root_.trans _ ((mapRingHom f).map_dvd (pow_rootMultiplicity_dvd p a))
  -- ⊢ (X - ↑C (↑f a)) ^ rootMultiplicity a p ∣ ↑(mapRingHom f) ((X - ↑C a) ^ rootM …
  rw [map_pow, map_sub, coe_mapRingHom, map_X, map_C]
  -- 🎉 no goals
#align polynomial.le_root_multiplicity_map Polynomial.le_rootMultiplicity_map

theorem eq_rootMultiplicity_map {p : A[X]} {f : A →+* B} (hf : Function.Injective f) (a : A) :
    rootMultiplicity a p = rootMultiplicity (f a) (p.map f) := by
  by_cases hp0 : p = 0; · simp only [hp0, rootMultiplicity_zero, Polynomial.map_zero]
  -- ⊢ rootMultiplicity a p = rootMultiplicity (↑f a) (map f p)
                          -- 🎉 no goals
  apply le_antisymm (le_rootMultiplicity_map ((Polynomial.map_ne_zero_iff hf).mpr hp0) a)
  -- ⊢ rootMultiplicity (↑f a) (map f p) ≤ rootMultiplicity a p
  rw [le_rootMultiplicity_iff hp0, ← map_dvd_map f hf ((monic_X_sub_C a).pow _),
    Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  apply pow_rootMultiplicity_dvd
  -- 🎉 no goals
#align polynomial.eq_root_multiplicity_map Polynomial.eq_rootMultiplicity_map

theorem count_map_roots [IsDomain A] [DecidableEq B] {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0)
    (b : B) :
    (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) := by
  rw [le_rootMultiplicity_iff hmap, ← Multiset.prod_replicate, ←
    Multiset.map_replicate fun a => X - C a]
  rw [← Multiset.filter_eq]
  -- ⊢ Multiset.prod (Multiset.map (fun a => X - ↑C a) (Multiset.filter (Eq b) (Mul …
  refine
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| Multiset.filter_le (Eq b) _).trans ?_
  convert Polynomial.map_dvd f p.prod_multiset_X_sub_C_dvd
  -- ⊢ Multiset.prod (Multiset.map (fun a => X - ↑C a) (Multiset.map (↑f) (roots p) …
  simp only [Polynomial.map_multiset_prod, Multiset.map_map]
  -- ⊢ Multiset.prod (Multiset.map ((fun x => X - ↑C x) ∘ fun x => ↑f x) (roots p)) …
  congr; ext1
  -- ⊢ ((fun x => X - ↑C x) ∘ fun x => ↑f x) = map f ∘ fun x => X - ↑C x
         -- ⊢ ((fun x => X - ↑C x) ∘ fun x => ↑f x) x✝ = (map f ∘ fun x => X - ↑C x) x✝
  simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
  -- 🎉 no goals
#align polynomial.count_map_roots Polynomial.count_map_roots

theorem count_map_roots_of_injective [IsDomain A] [DecidableEq B] (p : A[X]) {f : A →+* B}
    (hf : Function.Injective f) (b : B) :
    (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) := by
  by_cases hp0 : p = 0
  -- ⊢ Multiset.count b (Multiset.map (↑f) (roots p)) ≤ rootMultiplicity b (map f p)
  · simp only [hp0, roots_zero, Multiset.map_zero, Multiset.count_zero, Polynomial.map_zero,
      rootMultiplicity_zero]
  · exact count_map_roots ((Polynomial.map_ne_zero_iff hf).mpr hp0) b
    -- 🎉 no goals
#align polynomial.count_map_roots_of_injective Polynomial.count_map_roots_of_injective

theorem map_roots_le [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
    p.roots.map f ≤ (p.map f).roots := by
  classical
  exact Multiset.le_iff_count.2 fun b => by
    rw [count_roots]
    apply count_map_roots h
#align polynomial.map_roots_le Polynomial.map_roots_le

theorem map_roots_le_of_injective [IsDomain A] [IsDomain B] (p : A[X]) {f : A →+* B}
    (hf : Function.Injective f) : p.roots.map f ≤ (p.map f).roots := by
  by_cases hp0 : p = 0
  -- ⊢ Multiset.map (↑f) (roots p) ≤ roots (map f p)
  · simp only [hp0, roots_zero, Multiset.map_zero, Polynomial.map_zero]; rfl
    -- ⊢ 0 ≤ 0
                                                                         -- 🎉 no goals
  exact map_roots_le ((Polynomial.map_ne_zero_iff hf).mpr hp0)
  -- 🎉 no goals
#align polynomial.map_roots_le_of_injective Polynomial.map_roots_le_of_injective

theorem card_roots_le_map [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
    Multiset.card p.roots ≤ Multiset.card (p.map f).roots := by
  rw [← p.roots.card_map f]
  -- ⊢ ↑Multiset.card (Multiset.map (↑f) (roots p)) ≤ ↑Multiset.card (roots (map f  …
  exact Multiset.card_le_of_le (map_roots_le h)
  -- 🎉 no goals
#align polynomial.card_roots_le_map Polynomial.card_roots_le_map

theorem card_roots_le_map_of_injective [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B}
    (hf : Function.Injective f) : Multiset.card p.roots ≤ Multiset.card (p.map f).roots := by
  by_cases hp0 : p = 0
  -- ⊢ ↑Multiset.card (roots p) ≤ ↑Multiset.card (roots (map f p))
  · simp only [hp0, roots_zero, Polynomial.map_zero, Multiset.card_zero]; rfl
    -- ⊢ 0 ≤ 0
                                                                          -- 🎉 no goals
  exact card_roots_le_map ((Polynomial.map_ne_zero_iff hf).mpr hp0)
  -- 🎉 no goals
#align polynomial.card_roots_le_map_of_injective Polynomial.card_roots_le_map_of_injective

theorem roots_map_of_injective_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]}
    {f : A →+* B} (hf : Function.Injective f) (hroots : Multiset.card p.roots = p.natDegree) :
    p.roots.map f = (p.map f).roots := by
  apply Multiset.eq_of_le_of_card_le (map_roots_le_of_injective p hf)
  -- ⊢ ↑Multiset.card (roots (map f p)) ≤ ↑Multiset.card (Multiset.map (↑f) (roots  …
  simpa only [Multiset.card_map, hroots] using (card_roots' _).trans (natDegree_map_le f p)
  -- 🎉 no goals
#align polynomial.roots_map_of_injective_of_card_eq_nat_degree Polynomial.roots_map_of_injective_of_card_eq_natDegree

end

section

variable [Semiring R] [CommRing S] [IsDomain S] (φ : R →+* S)

theorem isUnit_of_isUnit_leadingCoeff_of_isUnit_map {f : R[X]} (hf : IsUnit f.leadingCoeff)
    (H : IsUnit (map φ f)) : IsUnit f := by
  have dz := degree_eq_zero_of_isUnit H
  -- ⊢ IsUnit f
  rw [degree_map_eq_of_leadingCoeff_ne_zero] at dz
  -- ⊢ IsUnit f
  · rw [eq_C_of_degree_eq_zero dz]
    -- ⊢ IsUnit (↑C (coeff f 0))
    refine' IsUnit.map C _
    -- ⊢ IsUnit (coeff f 0)
    convert hf
    -- ⊢ coeff f 0 = leadingCoeff f
    change coeff f 0 = coeff f (natDegree f)
    -- ⊢ coeff f 0 = coeff f (natDegree f)
    rw [(degree_eq_iff_natDegree_eq _).1 dz]
    -- ⊢ coeff f 0 = coeff f Zero.zero
    rfl
    -- ⊢ f ≠ 0
    rintro rfl
    -- ⊢ False
    simp at H
    -- 🎉 no goals
  · intro h
    -- ⊢ False
    have u : IsUnit (φ f.leadingCoeff) := IsUnit.map φ hf
    -- ⊢ False
    rw [h] at u
    -- ⊢ False
    simp at u
    -- 🎉 no goals
#align polynomial.is_unit_of_is_unit_leading_coeff_of_is_unit_map Polynomial.isUnit_of_isUnit_leadingCoeff_of_isUnit_map

end

section

variable [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (φ : R →+* S)

/-- A polynomial over an integral domain `R` is irreducible if it is monic and
  irreducible after mapping into an integral domain `S`.

A special case of this lemma is that a polynomial over `ℤ` is irreducible if
  it is monic and irreducible over `ℤ/pℤ` for some prime `p`.
-/
theorem Monic.irreducible_of_irreducible_map (f : R[X]) (h_mon : Monic f)
    (h_irr : Irreducible (Polynomial.map φ f)) : Irreducible f := by
  refine' ⟨h_irr.not_unit ∘ IsUnit.map (mapRingHom φ), fun a b h => _⟩
  -- ⊢ IsUnit a ∨ IsUnit b
  dsimp [Monic] at h_mon
  -- ⊢ IsUnit a ∨ IsUnit b
  have q := (leadingCoeff_mul a b).symm
  -- ⊢ IsUnit a ∨ IsUnit b
  rw [← h, h_mon] at q
  -- ⊢ IsUnit a ∨ IsUnit b
  refine' (h_irr.isUnit_or_isUnit <|
    (congr_arg (Polynomial.map φ) h).trans (Polynomial.map_mul φ)).imp _ _ <;>
      apply isUnit_of_isUnit_leadingCoeff_of_isUnit_map <;>
      -- ⊢ IsUnit (Polynomial.leadingCoeff a)
      -- ⊢ IsUnit (Polynomial.leadingCoeff b)
    apply isUnit_of_mul_eq_one
    -- ⊢ Polynomial.leadingCoeff a * ?refine'_1.hf.b = 1
    -- ⊢ Polynomial.leadingCoeff b * ?refine'_2.hf.b = 1
  · exact q;
    -- 🎉 no goals
  · rw [mul_comm]
    -- ⊢ ?refine'_2.hf.h.b * Polynomial.leadingCoeff b = 1
    exact q
    -- 🎉 no goals
#align polynomial.monic.irreducible_of_irreducible_map Polynomial.Monic.irreducible_of_irreducible_map

end

end Polynomial
