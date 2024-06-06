/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker, Johan Commelin
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Div

#align_import data.polynomial.ring_division from "leanprover-community/mathlib"@"8efcf8022aac8e01df8d302dcebdbc25d6a886c8"

/-!
# Theory of univariate polynomials

We prove basic results about univariate polynomials.

-/

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
  obtain ⟨f, sub_eq⟩ := h
  refine (div_modByMonic_unique (p₂ /ₘ q + f) _ hq ⟨?_, degree_modByMonic_lt _ hq⟩).2
  rw [sub_eq_iff_eq_add.mp sub_eq, mul_add, ← add_assoc, modByMonic_add_div _ hq, add_comm]
#align polynomial.mod_by_monic_eq_of_dvd_sub Polynomial.modByMonic_eq_of_dvd_sub

theorem add_modByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q := by
  by_cases hq : q.Monic
  · cases' subsingleton_or_nontrivial R with hR hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (div_modByMonic_unique (p₁ /ₘ q + p₂ /ₘ q) _ hq
          ⟨by
            rw [mul_add, add_left_comm, add_assoc, modByMonic_add_div _ hq, ← add_assoc,
              add_comm (q * _), modByMonic_add_div _ hq],
            (degree_add_le _ _).trans_lt
              (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))⟩).2
  · simp_rw [modByMonic_eq_of_not_monic _ hq]
#align polynomial.add_mod_by_monic Polynomial.add_modByMonic

theorem smul_modByMonic (c : R) (p : R[X]) : c • p %ₘ q = c • (p %ₘ q) := by
  by_cases hq : q.Monic
  · cases' subsingleton_or_nontrivial R with hR hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (div_modByMonic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
          ⟨by rw [mul_smul_comm, ← smul_add, modByMonic_add_div p hq],
            (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)⟩).2
  · simp_rw [modByMonic_eq_of_not_monic _ hq]
#align polynomial.smul_mod_by_monic Polynomial.smul_modByMonic

/-- `_ %ₘ q` as an `R`-linear map. -/
@[simps]
def modByMonicHom (q : R[X]) : R[X] →ₗ[R] R[X] where
  toFun p := p %ₘ q
  map_add' := add_modByMonic
  map_smul' := smul_modByMonic
#align polynomial.mod_by_monic_hom Polynomial.modByMonicHom

theorem neg_modByMonic (p mod : R[X]) : (-p) %ₘ mod = - (p %ₘ mod) :=
  (modByMonicHom mod).map_neg p

theorem sub_modByMonic (a b mod : R[X]) : (a - b) %ₘ mod = a %ₘ mod - b %ₘ mod :=
  (modByMonicHom mod).map_sub a b

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
    refine eq_zero_or_eq_zero_of_mul_eq_zero ?_
    rw [← leadingCoeff_zero, ← leadingCoeff_mul, h]

theorem natDegree_mul (hp : p ≠ 0) (hq : q ≠ 0) : (p*q).natDegree = p.natDegree + q.natDegree := by
  rw [← Nat.cast_inj (R := WithBot ℕ), ← degree_eq_natDegree (mul_ne_zero hp hq),
    Nat.cast_add, ← degree_eq_natDegree hp, ← degree_eq_natDegree hq, degree_mul]
#align polynomial.nat_degree_mul Polynomial.natDegree_mul

theorem trailingDegree_mul : (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, trailingDegree_zero, top_add]
  by_cases hq : q = 0
  · rw [hq, mul_zero, trailingDegree_zero, add_top]
  · rw [trailingDegree_eq_natTrailingDegree hp, trailingDegree_eq_natTrailingDegree hq,
    trailingDegree_eq_natTrailingDegree (mul_ne_zero hp hq), natTrailingDegree_mul hp hq]
    apply WithTop.coe_add
#align polynomial.trailing_degree_mul Polynomial.trailingDegree_mul

@[simp]
theorem natDegree_pow (p : R[X]) (n : ℕ) : natDegree (p ^ n) = n * natDegree p := by
  classical
  obtain rfl | hp := eq_or_ne p 0
  · obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
  exact natDegree_pow' $ by
    rw [← leadingCoeff_pow, Ne, leadingCoeff_eq_zero]; exact pow_ne_zero _ hp
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
  rw [natDegree_mul h2.1 h2.2]; exact Nat.le_add_right _ _
#align polynomial.nat_degree_le_of_dvd Polynomial.natDegree_le_of_dvd

theorem degree_le_of_dvd {p q : R[X]} (h1 : p ∣ q) (h2 : q ≠ 0) : degree p ≤ degree q := by
  rcases h1 with ⟨q, rfl⟩; rw [mul_ne_zero_iff] at h2
  exact degree_le_mul_left p h2.2
#align polynomial.degree_le_of_dvd Polynomial.degree_le_of_dvd

theorem eq_zero_of_dvd_of_degree_lt {p q : R[X]} (h₁ : p ∣ q) (h₂ : degree q < degree p) :
    q = 0 := by
  by_contra hc
  exact (lt_iff_not_ge _ _).mp h₂ (degree_le_of_dvd h₁ hc)
#align polynomial.eq_zero_of_dvd_of_degree_lt Polynomial.eq_zero_of_dvd_of_degree_lt

theorem eq_zero_of_dvd_of_natDegree_lt {p q : R[X]} (h₁ : p ∣ q) (h₂ : natDegree q < natDegree p) :
    q = 0 := by
  by_contra hc
  exact (lt_iff_not_ge _ _).mp h₂ (natDegree_le_of_dvd h₁ hc)
#align polynomial.eq_zero_of_dvd_of_nat_degree_lt Polynomial.eq_zero_of_dvd_of_natDegree_lt

theorem not_dvd_of_degree_lt {p q : R[X]} (h0 : q ≠ 0) (hl : q.degree < p.degree) : ¬p ∣ q := by
  by_contra hcontra
  exact h0 (eq_zero_of_dvd_of_degree_lt hcontra hl)
#align polynomial.not_dvd_of_degree_lt Polynomial.not_dvd_of_degree_lt

theorem not_dvd_of_natDegree_lt {p q : R[X]} (h0 : q ≠ 0) (hl : q.natDegree < p.natDegree) :
    ¬p ∣ q := by
  by_contra hcontra
  exact h0 (eq_zero_of_dvd_of_natDegree_lt hcontra hl)
#align polynomial.not_dvd_of_nat_degree_lt Polynomial.not_dvd_of_natDegree_lt

/-- This lemma is useful for working with the `intDegree` of a rational function. -/
theorem natDegree_sub_eq_of_prod_eq {p₁ p₂ q₁ q₂ : R[X]} (hp₁ : p₁ ≠ 0) (hq₁ : q₁ ≠ 0)
    (hp₂ : p₂ ≠ 0) (hq₂ : q₂ ≠ 0) (h_eq : p₁ * q₂ = p₂ * q₁) :
    (p₁.natDegree : ℤ) - q₁.natDegree = (p₂.natDegree : ℤ) - q₂.natDegree := by
  rw [sub_eq_sub_iff_add_eq_add]
  norm_cast
  rw [← natDegree_mul hp₁ hq₂, ← natDegree_mul hp₂ hq₁, h_eq]
#align polynomial.nat_degree_sub_eq_of_prod_eq Polynomial.natDegree_sub_eq_of_prod_eq

theorem natDegree_eq_zero_of_isUnit (h : IsUnit p) : natDegree p = 0 := by
  nontriviality R
  obtain ⟨q, hq⟩ := h.exists_right_inv
  have := natDegree_mul (left_ne_zero_of_mul_eq_one hq) (right_ne_zero_of_mul_eq_one hq)
  rw [hq, natDegree_one, eq_comm, add_eq_zero_iff] at this
  exact this.1
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

theorem not_isUnit_of_degree_pos (p : R[X])
    (hpl : 0 < p.degree) : ¬ IsUnit p := by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.elim p 0] at hpl
  intro h
  simp [degree_eq_zero_of_isUnit h] at hpl

theorem not_isUnit_of_natDegree_pos (p : R[X])
    (hpl : 0 < p.natDegree) : ¬ IsUnit p :=
  not_isUnit_of_degree_pos _ (natDegree_pos_iff_degree_pos.mp hpl)

variable [CharZero R]

end NoZeroDivisors

section NoZeroDivisors

variable [CommSemiring R] [NoZeroDivisors R] {p q : R[X]}

theorem irreducible_of_monic (hp : p.Monic) (hp1 : p ≠ 1) :
    Irreducible p ↔ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → f = 1 ∨ g = 1 := by
  refine
    ⟨fun h f g hf hg hp => (h.2 f g hp.symm).imp hf.eq_one_of_isUnit hg.eq_one_of_isUnit, fun h =>
      ⟨hp1 ∘ hp.eq_one_of_isUnit, fun f g hfg =>
        (h (g * C f.leadingCoeff) (f * C g.leadingCoeff) ?_ ?_ ?_).symm.imp
          (isUnit_of_mul_eq_one f _)
          (isUnit_of_mul_eq_one g _)⟩⟩
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, mul_comm, ← hfg, ← Monic]
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, ← hfg, ← Monic]
  · rw [mul_mul_mul_comm, ← C_mul, ← leadingCoeff_mul, ← hfg, hp.leadingCoeff, C_1, mul_one,
      mul_comm, ← hfg]
#align polynomial.irreducible_of_monic Polynomial.irreducible_of_monic

theorem Monic.irreducible_iff_natDegree (hp : p.Monic) :
    Irreducible p ↔
      p ≠ 1 ∧ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → f.natDegree = 0 ∨ g.natDegree = 0 := by
  by_cases hp1 : p = 1; · simp [hp1]
  rw [irreducible_of_monic hp hp1, and_iff_right hp1]
  refine forall₄_congr fun a b ha hb => ?_
  rw [ha.natDegree_eq_zero_iff_eq_one, hb.natDegree_eq_zero_iff_eq_one]
#align polynomial.monic.irreducible_iff_nat_degree Polynomial.Monic.irreducible_iff_natDegree

theorem Monic.irreducible_iff_natDegree' (hp : p.Monic) : Irreducible p ↔ p ≠ 1 ∧
    ∀ f g : R[X], f.Monic → g.Monic → f * g = p → g.natDegree ∉ Ioc 0 (p.natDegree / 2) := by
  simp_rw [hp.irreducible_iff_natDegree, mem_Ioc, Nat.le_div_iff_mul_le zero_lt_two, mul_two]
  apply and_congr_right'
  constructor <;> intro h f g hf hg he <;> subst he
  · rw [hf.natDegree_mul hg, add_le_add_iff_right]
    exact fun ha => (h f g hf hg rfl).elim (ha.1.trans_le ha.2).ne' ha.1.ne'
  · simp_rw [hf.natDegree_mul hg, pos_iff_ne_zero] at h
    contrapose! h
    obtain hl | hl := le_total f.natDegree g.natDegree
    · exact ⟨g, f, hg, hf, mul_comm g f, h.1, add_le_add_left hl _⟩
    · exact ⟨f, g, hf, hg, rfl, h.2, add_le_add_right hl _⟩
#align polynomial.monic.irreducible_iff_nat_degree' Polynomial.Monic.irreducible_iff_natDegree'

/-- Alternate phrasing of `Polynomial.Monic.irreducible_iff_natDegree'` where we only have to check
one divisor at a time. -/
theorem Monic.irreducible_iff_lt_natDegree_lt {p : R[X]} (hp : p.Monic) (hp1 : p ≠ 1) :
    Irreducible p ↔ ∀ q, Monic q → natDegree q ∈ Finset.Ioc 0 (natDegree p / 2) → ¬ q ∣ p := by
  rw [hp.irreducible_iff_natDegree', and_iff_right hp1]
  constructor
  · rintro h g hg hdg ⟨f, rfl⟩
    exact h f g (hg.of_mul_monic_left hp) hg (mul_comm f g) hdg
  · rintro h f g - hg rfl hdg
    exact h g hg hdg (dvd_mul_left g f)

theorem Monic.not_irreducible_iff_exists_add_mul_eq_coeff (hm : p.Monic) (hnd : p.natDegree = 2) :
    ¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂ := by
  cases subsingleton_or_nontrivial R
  · simp [natDegree_of_subsingleton] at hnd
  rw [hm.irreducible_iff_natDegree', and_iff_right, hnd]
  · push_neg
    constructor
    · rintro ⟨a, b, ha, hb, rfl, hdb⟩
      simp only [zero_lt_two, Nat.div_self, ge_iff_le,
        Nat.Ioc_succ_singleton, zero_add, mem_singleton] at hdb
      have hda := hnd
      rw [ha.natDegree_mul hb, hdb] at hda
      use a.coeff 0, b.coeff 0, mul_coeff_zero a b
      simpa only [nextCoeff, hnd, add_right_cancel hda, hdb] using ha.nextCoeff_mul hb
    · rintro ⟨c₁, c₂, hmul, hadd⟩
      refine
        ⟨X + C c₁, X + C c₂, monic_X_add_C _, monic_X_add_C _, ?_, ?_⟩
      · rw [p.as_sum_range_C_mul_X_pow, hnd, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_one, ← hnd, hm.coeff_natDegree, hnd, hmul, hadd, C_mul, C_add, C_1]
        ring
      · rw [mem_Ioc, natDegree_X_add_C _]
        simp
  · rintro rfl
    simp [natDegree_one] at hnd
#align polynomial.monic.not_irreducible_iff_exists_add_mul_eq_coeff Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff

theorem root_mul : IsRoot (p * q) a ↔ IsRoot p a ∨ IsRoot q a := by
  simp_rw [IsRoot, eval_mul, mul_eq_zero]
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

section CommSemiring

variable [CommSemiring R]

theorem Monic.C_dvd_iff_isUnit {p : R[X]} (hp : Monic p) {a : R} :
    C a ∣ p ↔ IsUnit a :=
  ⟨fun h => isUnit_iff_dvd_one.mpr <|
      hp.coeff_natDegree ▸ (C_dvd_iff_dvd_coeff _ _).mp h p.natDegree,
   fun ha => (ha.map C).dvd⟩

theorem degree_pos_of_not_isUnit_of_dvd_monic {a p : R[X]} (ha : ¬ IsUnit a)
    (hap : a ∣ p) (hp : Monic p) :
    0 < degree a :=
  lt_of_not_ge <| fun h => ha <| by
    rw [Polynomial.eq_C_of_degree_le_zero h] at hap ⊢
    simpa [hp.C_dvd_iff_isUnit, isUnit_C] using hap

theorem natDegree_pos_of_not_isUnit_of_dvd_monic {a p : R[X]} (ha : ¬ IsUnit a)
    (hap : a ∣ p) (hp : Monic p) :
    0 < natDegree a :=
  natDegree_pos_iff_degree_pos.mpr <| degree_pos_of_not_isUnit_of_dvd_monic ha hap hp

theorem degree_pos_of_monic_of_not_isUnit {a : R[X]} (hu : ¬ IsUnit a) (ha : Monic a) :
    0 < degree a :=
  degree_pos_of_not_isUnit_of_dvd_monic hu dvd_rfl ha

theorem natDegree_pos_of_monic_of_not_isUnit {a : R[X]} (hu : ¬ IsUnit a) (ha : Monic a) :
    0 < natDegree a :=
  natDegree_pos_iff_degree_pos.mpr <| degree_pos_of_monic_of_not_isUnit hu ha

theorem eq_zero_of_mul_eq_zero_of_smul (P : R[X]) (h : ∀ r : R, r • P = 0 → r = 0) :
    ∀ (Q : R[X]), P * Q = 0 → Q = 0 := by
  intro Q hQ
  suffices ∀ i, P.coeff i • Q = 0 by
    rw [← leadingCoeff_eq_zero]
    apply h
    simpa [ext_iff, mul_comm Q.leadingCoeff] using fun i ↦ congr_arg (·.coeff Q.natDegree) (this i)
  apply Nat.strong_decreasing_induction
  · use P.natDegree
    intro i hi
    rw [coeff_eq_zero_of_natDegree_lt hi, zero_smul]
  intro l IH
  obtain _|hl := (natDegree_smul_le (P.coeff l) Q).lt_or_eq
  · apply eq_zero_of_mul_eq_zero_of_smul _ h (P.coeff l • Q)
    rw [smul_eq_C_mul, mul_left_comm, hQ, mul_zero]
  suffices P.coeff l * Q.leadingCoeff = 0 by
    rwa [← leadingCoeff_eq_zero, ← coeff_natDegree, coeff_smul, hl, coeff_natDegree, smul_eq_mul]
  let m := Q.natDegree
  suffices (P * Q).coeff (l + m) = P.coeff l * Q.leadingCoeff by rw [← this, hQ, coeff_zero]
  rw [coeff_mul]
  apply Finset.sum_eq_single (l, m) _ (by simp)
  simp only [Finset.mem_antidiagonal, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
  intro i j hij H
  obtain hi|rfl|hi := lt_trichotomy i l
  · have hj : m < j := by omega
    rw [coeff_eq_zero_of_natDegree_lt hj, mul_zero]
  · omega
  · rw [← coeff_C_mul, ← smul_eq_C_mul, IH _ hi, coeff_zero]
termination_by Q => Q.natDegree

open nonZeroDivisors in
/-- *McCoy theorem*: a polynomial `P : R[X]` is a zerodivisor if and only if there is `a : R`
such that `a ≠ 0` and `a • P = 0`. -/
theorem nmem_nonZeroDivisors_iff {P : R[X]} : P ∉ R[X]⁰ ↔ ∃ a : R, a ≠ 0 ∧ a • P = 0 := by
  refine ⟨fun hP ↦ ?_, fun ⟨a, ha, h⟩ h1 ↦ ha <| C_eq_zero.1 <| (h1 _) <| smul_eq_C_mul a ▸ h⟩
  by_contra! h
  obtain ⟨Q, hQ⟩ := _root_.nmem_nonZeroDivisors_iff.1 hP
  refine hQ.2 (eq_zero_of_mul_eq_zero_of_smul P (fun a ha ↦ ?_) Q (mul_comm P _ ▸ hQ.1))
  contrapose! ha
  exact h a ha

open nonZeroDivisors in
protected lemma mem_nonZeroDivisors_iff {P : R[X]} : P ∈ R[X]⁰ ↔ ∀ a : R, a • P = 0 → a = 0 := by
  simpa [not_imp_not] using (nmem_nonZeroDivisors_iff (P := P)).not

end CommSemiring

section CommRing

variable [CommRing R]

/- Porting note: the ML3 proof no longer worked because of a conflict in the
inferred type and synthesized type for `DecidableRel` when using `Nat.le_find_iff` from
`Mathlib.Algebra.Polynomial.Div` After some discussion on [Zulip]
(https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/decidability.20leakage)
introduced `Polynomial.rootMultiplicity_eq_nat_find_of_nonzero` to contain the issue
-/
/-- The multiplicity of `a` as root of a nonzero polynomial `p` is at least `n` iff
  `(X - a) ^ n` divides `p`. -/
theorem le_rootMultiplicity_iff {p : R[X]} (p0 : p ≠ 0) {a : R} {n : ℕ} :
    n ≤ rootMultiplicity a p ↔ (X - C a) ^ n ∣ p := by
  classical
  rw [rootMultiplicity_eq_nat_find_of_nonzero p0, @Nat.le_find_iff _ (_)]
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
#align polynomial.root_multiplicity_le_iff Polynomial.rootMultiplicity_le_iff

theorem pow_rootMultiplicity_not_dvd {p : R[X]} (p0 : p ≠ 0) (a : R) :
    ¬(X - C a) ^ (rootMultiplicity a p + 1) ∣ p := by rw [← rootMultiplicity_le_iff p0]
#align polynomial.pow_root_multiplicity_not_dvd Polynomial.pow_rootMultiplicity_not_dvd

theorem X_sub_C_pow_dvd_iff {p : R[X]} {t : R} {n : ℕ} :
    (X - C t) ^ n ∣ p ↔ X ^ n ∣ p.comp (X + C t) := by
  convert (map_dvd_iff <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

theorem comp_X_add_C_eq_zero_iff {p : R[X]} (t : R) :
    p.comp (X + C t) = 0 ↔ p = 0 := AddEquivClass.map_eq_zero_iff (algEquivAevalXAddC t)

theorem comp_X_add_C_ne_zero_iff {p : R[X]} (t : R) :
    p.comp (X + C t) ≠ 0 ↔ p ≠ 0 := Iff.not <| comp_X_add_C_eq_zero_iff t

theorem rootMultiplicity_eq_rootMultiplicity {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (X + C t)).rootMultiplicity 0 := by
  classical
  simp_rw [rootMultiplicity_eq_multiplicity, comp_X_add_C_eq_zero_iff]
  congr; ext; congr 1
  rw [C_0, sub_zero]
  convert (multiplicity.multiplicity_map_eq <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

theorem rootMultiplicity_eq_natTrailingDegree' {p : R[X]} :
    p.rootMultiplicity 0 = p.natTrailingDegree := by
  by_cases h : p = 0
  · simp only [h, rootMultiplicity_zero, natTrailingDegree_zero]
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff h, map_zero, sub_zero, X_pow_dvd_iff, not_forall]
    exact ⟨p.natTrailingDegree,
      fun h' ↦ trailingCoeff_nonzero_iff_nonzero.2 h <| h' <| Nat.lt.base _⟩
  · rw [le_rootMultiplicity_iff h, map_zero, sub_zero, X_pow_dvd_iff]
    exact fun _ ↦ coeff_eq_zero_of_lt_natTrailingDegree

theorem rootMultiplicity_eq_natTrailingDegree {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (X + C t)).natTrailingDegree :=
  rootMultiplicity_eq_rootMultiplicity.trans rootMultiplicity_eq_natTrailingDegree'

theorem eval_divByMonic_eq_trailingCoeff_comp {p : R[X]} {t : R} :
    (p /ₘ (X - C t) ^ p.rootMultiplicity t).eval t = (p.comp (X + C t)).trailingCoeff := by
  obtain rfl | hp := eq_or_ne p 0
  · rw [zero_divByMonic, eval_zero, zero_comp, trailingCoeff_zero]
  have mul_eq := p.pow_mul_divByMonic_rootMultiplicity_eq t
  set m := p.rootMultiplicity t
  set g := p /ₘ (X - C t) ^ m
  have : (g.comp (X + C t)).coeff 0 = g.eval t := by
    rw [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add]
  rw [← congr_arg (comp · <| X + C t) mul_eq, mul_comp, pow_comp, sub_comp, X_comp, C_comp,
    add_sub_cancel_right, ← reverse_leadingCoeff, reverse_X_pow_mul, reverse_leadingCoeff,
    trailingCoeff, Nat.le_zero.1 (natTrailingDegree_le_of_ne_zero <|
      this ▸ eval_divByMonic_pow_rootMultiplicity_ne_zero t hp), this]

section nonZeroDivisors

open scoped nonZeroDivisors

theorem Monic.mem_nonZeroDivisors {p : R[X]} (h : p.Monic) : p ∈ R[X]⁰ :=
  mem_nonZeroDivisors_iff.2 fun _ hx ↦ (mul_left_eq_zero_iff h).1 hx

theorem mem_nonZeroDivisors_of_leadingCoeff {p : R[X]} (h : p.leadingCoeff ∈ R⁰) : p ∈ R[X]⁰ := by
  refine mem_nonZeroDivisors_iff.2 fun x hx ↦ leadingCoeff_eq_zero.1 ?_
  by_contra hx'
  rw [← mul_right_mem_nonZeroDivisors_eq_zero_iff h] at hx'
  simp only [← leadingCoeff_mul' hx', hx, leadingCoeff_zero, not_true] at hx'

end nonZeroDivisors

theorem rootMultiplicity_mul_X_sub_C_pow {p : R[X]} {a : R} {n : ℕ} (h : p ≠ 0) :
    (p * (X - C a) ^ n).rootMultiplicity a = p.rootMultiplicity a + n := by
  have h2 := monic_X_sub_C a |>.pow n |>.mul_left_ne_zero h
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff h2, add_assoc, add_comm n, ← add_assoc, pow_add,
      dvd_cancel_right_mem_nonZeroDivisors (monic_X_sub_C a |>.pow n |>.mem_nonZeroDivisors)]
    exact pow_rootMultiplicity_not_dvd h a
  · rw [le_rootMultiplicity_iff h2, pow_add]
    exact mul_dvd_mul_right (pow_rootMultiplicity_dvd p a) _

/-- The multiplicity of `a` as root of `(X - a) ^ n` is `n`. -/
theorem rootMultiplicity_X_sub_C_pow [Nontrivial R] (a : R) (n : ℕ) :
    rootMultiplicity a ((X - C a) ^ n) = n := by
  have := rootMultiplicity_mul_X_sub_C_pow (a := a) (n := n) C.map_one_ne_zero
  rwa [rootMultiplicity_C, map_one, one_mul, zero_add] at this
set_option linter.uppercaseLean3 false in
#align polynomial.root_multiplicity_X_sub_C_pow Polynomial.rootMultiplicity_X_sub_C_pow

theorem rootMultiplicity_X_sub_C_self [Nontrivial R] {x : R} :
    rootMultiplicity x (X - C x) = 1 :=
  pow_one (X - C x) ▸ rootMultiplicity_X_sub_C_pow x 1
set_option linter.uppercaseLean3 false in
#align polynomial.root_multiplicity_X_sub_C_self Polynomial.rootMultiplicity_X_sub_C_self

-- Porting note: swapped instance argument order
theorem rootMultiplicity_X_sub_C [Nontrivial R] [DecidableEq R] {x y : R} :
    rootMultiplicity x (X - C y) = if x = y then 1 else 0 := by
  split_ifs with hxy
  · rw [hxy]
    exact rootMultiplicity_X_sub_C_self
  exact rootMultiplicity_eq_zero (mt root_X_sub_C.mp (Ne.symm hxy))
set_option linter.uppercaseLean3 false in
#align polynomial.root_multiplicity_X_sub_C Polynomial.rootMultiplicity_X_sub_C

/-- The multiplicity of `p + q` is at least the minimum of the multiplicities. -/
theorem rootMultiplicity_add {p q : R[X]} (a : R) (hzero : p + q ≠ 0) :
    min (rootMultiplicity a p) (rootMultiplicity a q) ≤ rootMultiplicity a (p + q) := by
  rw [le_rootMultiplicity_iff hzero]
  exact min_pow_dvd_add (pow_rootMultiplicity_dvd p a) (pow_rootMultiplicity_dvd q a)
#align polynomial.root_multiplicity_add Polynomial.rootMultiplicity_add

theorem le_rootMultiplicity_mul {p q : R[X]} (x : R) (hpq : p * q ≠ 0) :
    rootMultiplicity x p + rootMultiplicity x q ≤ rootMultiplicity x (p * q) := by
  rw [le_rootMultiplicity_iff hpq, pow_add]
  exact mul_dvd_mul (pow_rootMultiplicity_dvd p x) (pow_rootMultiplicity_dvd q x)

theorem rootMultiplicity_mul' {p q : R[X]} {x : R}
    (hpq : (p /ₘ (X - C x) ^ p.rootMultiplicity x).eval x *
      (q /ₘ (X - C x) ^ q.rootMultiplicity x).eval x ≠ 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q := by
  simp_rw [eval_divByMonic_eq_trailingCoeff_comp] at hpq
  simp_rw [rootMultiplicity_eq_natTrailingDegree, mul_comp, natTrailingDegree_mul' hpq]

variable [IsDomain R] {p q : R[X]}

@[simp]
theorem natDegree_coe_units (u : R[X]ˣ) : natDegree (u : R[X]) = 0 :=
  natDegree_eq_of_degree_eq_some (degree_coe_units u)
#align polynomial.nat_degree_coe_units Polynomial.natDegree_coe_units

theorem coeff_coe_units_zero_ne_zero (u : R[X]ˣ) : coeff (u : R[X]) 0 ≠ 0 := by
  conv in 0 => rw [← natDegree_coe_units u]
  rw [← leadingCoeff, Ne, leadingCoeff_eq_zero]
  exact Units.ne_zero _
#align polynomial.coeff_coe_units_zero_ne_zero Polynomial.coeff_coe_units_zero_ne_zero

theorem degree_eq_degree_of_associated (h : Associated p q) : degree p = degree q := by
  let ⟨u, hu⟩ := h
  simp [hu.symm]
#align polynomial.degree_eq_degree_of_associated Polynomial.degree_eq_degree_of_associated

theorem degree_eq_one_of_irreducible_of_root (hi : Irreducible p) {x : R} (hx : IsRoot p x) :
    degree p = 1 :=
  let ⟨g, hg⟩ := dvd_iff_isRoot.2 hx
  have : IsUnit (X - C x) ∨ IsUnit g := hi.isUnit_or_isUnit hg
  this.elim
    (fun h => by
      have h₁ : degree (X - C x) = 1 := degree_X_sub_C x
      have h₂ : degree (X - C x) = 0 := degree_eq_zero_of_isUnit h
      rw [h₁] at h₂; exact absurd h₂ (by decide))
    fun hgu => by rw [hg, degree_mul, degree_X_sub_C, degree_eq_zero_of_isUnit hgu, add_zero]
#align polynomial.degree_eq_one_of_irreducible_of_root Polynomial.degree_eq_one_of_irreducible_of_root

/-- Division by a monic polynomial doesn't change the leading coefficient. -/
theorem leadingCoeff_divByMonic_of_monic {R : Type u} [CommRing R] {p q : R[X]} (hmonic : q.Monic)
    (hdegree : q.degree ≤ p.degree) : (p /ₘ q).leadingCoeff = p.leadingCoeff := by
  nontriviality
  have h : q.leadingCoeff * (p /ₘ q).leadingCoeff ≠ 0 := by
    simpa [divByMonic_eq_zero_iff hmonic, hmonic.leadingCoeff,
      Nat.WithBot.one_le_iff_zero_lt] using hdegree
  nth_rw 2 [← modByMonic_add_div p hmonic]
  rw [leadingCoeff_add_of_degree_lt, leadingCoeff_monic_mul hmonic]
  rw [degree_mul' h, degree_add_divByMonic hmonic hdegree]
  exact (degree_modByMonic_lt p hmonic).trans_le hdegree
#align polynomial.leading_coeff_div_by_monic_of_monic Polynomial.leadingCoeff_divByMonic_of_monic

theorem leadingCoeff_divByMonic_X_sub_C (p : R[X]) (hp : degree p ≠ 0) (a : R) :
    leadingCoeff (p /ₘ (X - C a)) = leadingCoeff p := by
  nontriviality
  cases' hp.lt_or_lt with hd hd
  · rw [degree_eq_bot.mp <| Nat.WithBot.lt_zero_iff.mp hd, zero_divByMonic]
  refine leadingCoeff_divByMonic_of_monic (monic_X_sub_C a) ?_
  rwa [degree_X_sub_C, Nat.WithBot.one_le_iff_zero_lt]
set_option linter.uppercaseLean3 false in
#align polynomial.leading_coeff_div_by_monic_X_sub_C Polynomial.leadingCoeff_divByMonic_X_sub_C

theorem eq_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q)
    (h₁ : q.natDegree ≤ p.natDegree) (h₂ : p.leadingCoeff = q.leadingCoeff) :
    p = q := by
  by_cases hq : q = 0
  · rwa [hq, leadingCoeff_zero, leadingCoeff_eq_zero, ← hq] at h₂
  replace h₁ := (natDegree_le_of_dvd hpq hq).antisymm h₁
  obtain ⟨u, rfl⟩ := hpq
  replace hq := mul_ne_zero_iff.mp hq
  rw [natDegree_mul hq.1 hq.2, self_eq_add_right] at h₁
  rw [eq_C_of_natDegree_eq_zero h₁, leadingCoeff_mul, leadingCoeff_C,
    eq_comm, mul_eq_left₀ (leadingCoeff_ne_zero.mpr hq.1)] at h₂
  rw [eq_C_of_natDegree_eq_zero h₁, h₂, map_one, mul_one]

theorem associated_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q)
    (h₁ : q.natDegree ≤ p.natDegree) (h₂ : q.leadingCoeff ∣ p.leadingCoeff) :
    Associated p q :=
  have ⟨r, hr⟩ := hpq
  have ⟨u, hu⟩ := associated_of_dvd_dvd ⟨leadingCoeff r, hr ▸ leadingCoeff_mul p r⟩ h₂
  ⟨Units.map C.toMonoidHom u, eq_of_dvd_of_natDegree_le_of_leadingCoeff
    (by rwa [Units.mul_right_dvd]) (by simpa [natDegree_mul_C] using h₁) (by simpa using hu)⟩

theorem associated_of_dvd_of_natDegree_le {K} [Field K] {p q : K[X]} (hpq : p ∣ q) (hq : q ≠ 0)
    (h₁ : q.natDegree ≤ p.natDegree) : Associated p q :=
  associated_of_dvd_of_natDegree_le_of_leadingCoeff hpq h₁
    (IsUnit.dvd (by rwa [← leadingCoeff_ne_zero, ← isUnit_iff_ne_zero] at hq))

theorem associated_of_dvd_of_degree_eq {K} [Field K] {p q : K[X]} (hpq : p ∣ q)
    (h₁ : p.degree = q.degree) : Associated p q :=
  (Classical.em (q = 0)).elim (fun hq ↦ (show p = q by simpa [hq] using h₁) ▸ Associated.refl p)
    (associated_of_dvd_of_natDegree_le hpq · (natDegree_le_natDegree h₁.ge))

theorem eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le {R} [CommRing R] {p q : R[X]}
    (hp : p.Monic) (hdiv : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) :
    q = C q.leadingCoeff * p := by
  obtain ⟨r, hr⟩ := hdiv
  obtain rfl | hq := eq_or_ne q 0; · simp
  have rzero : r ≠ 0 := fun h => by simp [h, hq] at hr
  rw [hr, natDegree_mul'] at hdeg; swap
  · rw [hp.leadingCoeff, one_mul, leadingCoeff_ne_zero]
    exact rzero
  rw [mul_comm, @eq_C_of_natDegree_eq_zero _ _ r] at hr
  · convert hr
    convert leadingCoeff_C (coeff r 0) using 1
    rw [hr, leadingCoeff_mul_monic hp]
  · exact (add_right_inj _).1 (le_antisymm hdeg <| Nat.le.intro rfl)
#align polynomial.eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le

theorem eq_of_monic_of_dvd_of_natDegree_le {R} [CommRing R] {p q : R[X]} (hp : p.Monic)
    (hq : q.Monic) (hdiv : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) : q = p := by
  convert eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hp hdiv hdeg
  rw [hq.leadingCoeff, C_1, one_mul]
#align polynomial.eq_of_monic_of_dvd_of_nat_degree_le Polynomial.eq_of_monic_of_dvd_of_natDegree_le

theorem prime_X_sub_C (r : R) : Prime (X - C r) :=
  ⟨X_sub_C_ne_zero r, not_isUnit_X_sub_C r, fun _ _ => by
    simp_rw [dvd_iff_isRoot, IsRoot.def, eval_mul, mul_eq_zero]
    exact id⟩
set_option linter.uppercaseLean3 false in
#align polynomial.prime_X_sub_C Polynomial.prime_X_sub_C

theorem prime_X : Prime (X : R[X]) := by
  convert prime_X_sub_C (0 : R)
  simp
set_option linter.uppercaseLean3 false in
#align polynomial.prime_X Polynomial.prime_X

theorem Monic.prime_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Prime p :=
  have : p = X - C (-p.coeff 0) := by simpa [hm.leadingCoeff] using eq_X_add_C_of_degree_eq_one hp1
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

@[simp]
theorem natDegree_multiset_prod_X_sub_C_eq_card (s : Multiset R) :
    (s.map fun a => X - C a).prod.natDegree = Multiset.card s := by
  rw [natDegree_multiset_prod_of_monic, Multiset.map_map]
  · simp only [(· ∘ ·), natDegree_X_sub_C, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
      mul_one]
  · exact Multiset.forall_mem_map_iff.2 fun a _ => monic_X_sub_C a
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_multiset_prod_X_sub_C_eq_card Polynomial.natDegree_multiset_prod_X_sub_C_eq_card

theorem Monic.comp (hp : p.Monic) (hq : q.Monic) (h : q.natDegree ≠ 0) : (p.comp q).Monic := by
  rw [Monic.def, leadingCoeff_comp h, Monic.def.1 hp, Monic.def.1 hq, one_pow, one_mul]
#align polynomial.monic.comp Polynomial.Monic.comp

theorem Monic.comp_X_add_C (hp : p.Monic) (r : R) : (p.comp (X + C r)).Monic := by
  refine hp.comp (monic_X_add_C _) fun ha => ?_
  rw [natDegree_X_add_C] at ha
  exact one_ne_zero ha
set_option linter.uppercaseLean3 false in
#align polynomial.monic.comp_X_add_C Polynomial.Monic.comp_X_add_C

theorem Monic.comp_X_sub_C (hp : p.Monic) (r : R) : (p.comp (X - C r)).Monic := by
  simpa using hp.comp_X_add_C (-r)
set_option linter.uppercaseLean3 false in
#align polynomial.monic.comp_X_sub_C Polynomial.Monic.comp_X_sub_C

theorem units_coeff_zero_smul (c : R[X]ˣ) (p : R[X]) : (c : R[X]).coeff 0 • p = c * p := by
  rw [← Polynomial.C_mul', ← Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]
#align polynomial.units_coeff_zero_smul Polynomial.units_coeff_zero_smul

theorem comp_eq_zero_iff : p.comp q = 0 ↔ p = 0 ∨ p.eval (q.coeff 0) = 0 ∧ q = C (q.coeff 0) := by
  constructor
  · intro h
    have key : p.natDegree = 0 ∨ q.natDegree = 0 := by
      rw [← mul_eq_zero, ← natDegree_comp, h, natDegree_zero]
    replace key := Or.imp eq_C_of_natDegree_eq_zero eq_C_of_natDegree_eq_zero key
    cases' key with key key
    · rw [key, C_comp] at h
      exact Or.inl (key.trans h)
    · rw [key, comp_C, C_eq_zero] at h
      exact Or.inr ⟨h, key⟩
  · exact fun h =>
      Or.rec (fun h => by rw [h, zero_comp]) (fun h => by rw [h.2, comp_C, h.1, C_0]) h
#align polynomial.comp_eq_zero_iff Polynomial.comp_eq_zero_iff

theorem isCoprime_X_sub_C_of_isUnit_sub {R} [CommRing R] {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (X - C a) (X - C b) :=
  ⟨-C h.unit⁻¹.val, C h.unit⁻¹.val, by
    rw [neg_mul_comm, ← left_distrib, neg_add_eq_sub, sub_sub_sub_cancel_left, ← C_sub, ← C_mul]
    rw [← C_1]
    congr
    exact h.val_inv_mul⟩
set_option linter.uppercaseLean3 false in
#align polynomial.is_coprime_X_sub_C_of_is_unit_sub Polynomial.isCoprime_X_sub_C_of_isUnit_sub

theorem pairwise_coprime_X_sub_C {K} [Field K] {I : Type v} {s : I → K} (H : Function.Injective s) :
    Pairwise (IsCoprime on fun i : I => X - C (s i)) := fun _ _ hij =>
  isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne <| H.ne hij).isUnit
set_option linter.uppercaseLean3 false in
#align polynomial.pairwise_coprime_X_sub_C Polynomial.pairwise_coprime_X_sub_C

theorem rootMultiplicity_mul {p q : R[X]} {x : R} (hpq : p * q ≠ 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q := by
  classical
  have hp : p ≠ 0 := left_ne_zero_of_mul hpq
  have hq : q ≠ 0 := right_ne_zero_of_mul hpq
  rw [rootMultiplicity_eq_multiplicity (p * q), dif_neg hpq, rootMultiplicity_eq_multiplicity p,
    dif_neg hp, rootMultiplicity_eq_multiplicity q, dif_neg hq,
    multiplicity.mul' (prime_X_sub_C x)]
#align polynomial.root_multiplicity_mul Polynomial.rootMultiplicity_mul

open Multiset in
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
      have wf : degree (p /ₘ (X - C x)) < degree p :=
        degree_divByMonic_lt _ (monic_X_sub_C x) hp ((degree_X_sub_C x).symm ▸ by decide)
      let ⟨t, htd, htr⟩ := @exists_multiset_roots _ (p /ₘ (X - C x)) hd0
      have hdeg : degree (X - C x) ≤ degree p := by
        rw [degree_X_sub_C, degree_eq_natDegree hp]
        rw [degree_eq_natDegree hp] at hpd
        exact WithBot.coe_le_coe.2 (WithBot.coe_lt_coe.1 hpd)
      have hdiv0 : p /ₘ (X - C x) ≠ 0 :=
        mt (divByMonic_eq_zero_iff (monic_X_sub_C x)).1 <| not_lt.2 hdeg
      ⟨x ::ₘ t,
        calc
          (card (x ::ₘ t) : WithBot ℕ) = Multiset.card t + 1 := by
            congr
            exact mod_cast Multiset.card_cons _ _
          _ ≤ degree p := by
            rw [← degree_add_divByMonic (monic_X_sub_C x) hdeg, degree_X_sub_C, add_comm];
              exact add_le_add (le_refl (1 : WithBot ℕ)) htd,
        by
          change ∀ (a : R), count a (x ::ₘ t) = rootMultiplicity a p
          intro a
          conv_rhs => rw [← mul_divByMonic_eq_iff_isRoot.mpr hx]
          rw [rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero x) hdiv0),
            rootMultiplicity_X_sub_C, ← htr a]
          split_ifs with ha
          · rw [ha, count_cons_self, add_comm]
          · rw [count_cons_of_ne ha, zero_add]⟩
    else
      ⟨0, (degree_eq_natDegree hp).symm ▸ WithBot.coe_le_coe.2 (Nat.zero_le _), by
        intro a
        rw [count_zero, rootMultiplicity_eq_zero (not_exists.mp h a)]⟩
termination_by p => natDegree p
decreasing_by {
  simp_wf
  apply (Nat.cast_lt (α := WithBot ℕ)).mp
  simp only [degree_eq_natDegree hp, degree_eq_natDegree hd0] at wf;
  assumption}
#align polynomial.exists_multiset_roots Polynomial.exists_multiset_roots

end CommRing

section

variable [Semiring R] [CommRing S] [IsDomain S] (φ : R →+* S)

theorem isUnit_of_isUnit_leadingCoeff_of_isUnit_map {f : R[X]} (hf : IsUnit f.leadingCoeff)
    (H : IsUnit (map φ f)) : IsUnit f := by
  have dz := degree_eq_zero_of_isUnit H
  rw [degree_map_eq_of_leadingCoeff_ne_zero] at dz
  · rw [eq_C_of_degree_eq_zero dz]
    refine IsUnit.map C ?_
    convert hf
    change coeff f 0 = coeff f (natDegree f)
    rw [(degree_eq_iff_natDegree_eq _).1 dz]
    · rfl
    rintro rfl
    simp at H
  · intro h
    have u : IsUnit (φ f.leadingCoeff) := IsUnit.map φ hf
    rw [h] at u
    simp at u
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
  refine ⟨h_irr.not_unit ∘ IsUnit.map (mapRingHom φ), fun a b h => ?_⟩
  dsimp [Monic] at h_mon
  have q := (leadingCoeff_mul a b).symm
  rw [← h, h_mon] at q
  refine (h_irr.isUnit_or_isUnit <|
    (congr_arg (Polynomial.map φ) h).trans (Polynomial.map_mul φ)).imp ?_ ?_ <;>
      apply isUnit_of_isUnit_leadingCoeff_of_isUnit_map <;>
    apply isUnit_of_mul_eq_one
  · exact q;
  · rw [mul_comm]
    exact q
#align polynomial.monic.irreducible_of_irreducible_map Polynomial.Monic.irreducible_of_irreducible_map

end

end Polynomial
