/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Ashvni Narayanan, Michael Stoll
-/
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Lemmas about units in `ZMod`.
-/

assert_not_exists TwoSidedIdeal

namespace ZMod

variable {n m : ℕ}
/-- `unitsMap` is a group homomorphism that maps units of `ZMod m` to units of `ZMod n` when `n`
divides `m`. -/
def unitsMap (hm : n ∣ m) : (ZMod m)ˣ →* (ZMod n)ˣ := Units.map (castHom hm (ZMod n))

lemma unitsMap_def (hm : n ∣ m) : unitsMap hm = Units.map (castHom hm (ZMod n)) := rfl

lemma unitsMap_comp {d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
    (unitsMap hm).comp (unitsMap hd) = unitsMap (dvd_trans hm hd) := by
  simp only [unitsMap_def]
  rw [← Units.map_comp]
  exact congr_arg Units.map <| congr_arg RingHom.toMonoidHom <| castHom_comp hm hd

@[simp]
lemma unitsMap_self (n : ℕ) : unitsMap (dvd_refl n) = MonoidHom.id _ := by
  simp [unitsMap, castHom_self]

/-- `unitsMap_val` shows that coercing from `(ZMod m)ˣ` to `ZMod n` gives the same result
when going via `(ZMod n)ˣ` and `ZMod m`. -/
lemma unitsMap_val (h : n ∣ m) (a : (ZMod m)ˣ) :
    ↑(unitsMap h a) = ((a : ZMod m).cast : ZMod n) := rfl

lemma isUnit_cast_of_dvd (hm : n ∣ m) (a : Units (ZMod m)) : IsUnit (cast (a : ZMod m) : ZMod n) :=
  Units.isUnit (unitsMap hm a)
@[deprecated (since := "2024-12-16")] alias IsUnit_cast_of_dvd := isUnit_cast_of_dvd

theorem unitsMap_surjective [hm : NeZero m] (h : n ∣ m) :
    Function.Surjective (unitsMap h) := by
  suffices ∀ x : ℕ, x.Coprime n → ∃ k : ℕ, (x + k * n).Coprime m by
    intro x
    have ⟨k, hk⟩ := this x.val.val (val_coe_unit_coprime x)
    refine ⟨unitOfCoprime _ hk, Units.ext ?_⟩
    have : NeZero n := ⟨fun hn ↦ hm.out (eq_zero_of_zero_dvd (hn ▸ h))⟩
    simp [unitsMap_def, - castHom_apply]
  intro x hx
  let ps : Finset ℕ := {p ∈ m.primeFactors | ¬p ∣ x}
  use ps.prod id
  apply Nat.coprime_of_dvd
  intro p pp hp hpn
  by_cases hpx : p ∣ x
  · have h := Nat.dvd_sub hp hpx
    rw [add_comm, Nat.add_sub_cancel] at h
    rcases pp.dvd_mul.mp h with h | h
    · have ⟨q, hq, hq'⟩ := (pp.prime.dvd_finset_prod_iff id).mp h
      rw [Finset.mem_filter, Nat.mem_primeFactors,
        ← (Nat.prime_dvd_prime_iff_eq pp hq.1.1).mp hq'] at hq
      exact hq.2 hpx
    · exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, pp, hpx, h⟩ hx
  · have pps : p ∈ ps := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pp, hpn, hm.out⟩, hpx⟩
    have h := Nat.dvd_sub hp ((Finset.dvd_prod_of_mem id pps).mul_right n)
    rw [Nat.add_sub_cancel] at h
    contradiction

-- This needs `Nat.primeFactors`, so cannot go into `Mathlib/Data/ZMod/Basic.lean`.
open Nat in
lemma not_isUnit_of_mem_primeFactors {n p : ℕ} (h : p ∈ n.primeFactors) :
    ¬ IsUnit (p : ZMod n) := by
  rw [isUnit_iff_coprime]
  exact (Prime.dvd_iff_not_coprime <| prime_of_mem_primeFactors h).mp <| dvd_of_mem_primeFactors h

/-- Any element of `ZMod N` has the form `u * d` where `u` is a unit and `d` is a divisor of `N`. -/
lemma eq_unit_mul_divisor {N : ℕ} (a : ZMod N) :
    ∃ d : ℕ, d ∣ N ∧ ∃ (u : ZMod N), IsUnit u ∧ a = u * d := by
  rcases eq_or_ne N 0 with rfl | hN
  -- Silly special case : N = 0. Of no mathematical interest, but true, so let's prove it.
  · change ℤ at a
    rcases eq_or_ne a 0 with rfl | ha
    · refine ⟨0, dvd_zero _, 1, isUnit_one, by rw [Nat.cast_zero, mul_zero]⟩
    refine ⟨a.natAbs, dvd_zero _, Int.sign a, ?_, (Int.sign_mul_natAbs a).symm⟩
    rcases lt_or_gt_of_ne ha with h | h
    · simp only [Int.sign_eq_neg_one_of_neg h, IsUnit.neg_iff, isUnit_one]
    · simp only [Int.sign_eq_one_of_pos h, isUnit_one]
  -- now the interesting case
  have : NeZero N := ⟨hN⟩
  -- Define `d` as the GCD of a lift of `a` and `N`.
  let d := a.val.gcd N
  have hd : d ≠ 0 := Nat.gcd_ne_zero_right hN
  obtain ⟨a₀, (ha₀ : _ = d * _)⟩ := a.val.gcd_dvd_left N
  obtain ⟨N₀, (hN₀ : _ = d * _)⟩ := a.val.gcd_dvd_right N
  refine ⟨d, ⟨N₀, hN₀⟩, ?_⟩
  -- Show `a` is a unit mod `N / d`.
  have hu₀ : IsUnit (a₀ : ZMod N₀) := by
    refine (isUnit_iff_coprime _ _).mpr (Nat.isCoprime_iff_coprime.mp ?_)
    obtain ⟨p, q, hpq⟩ : ∃ (p q : ℤ), d = a.val * p + N * q := ⟨_, _, Nat.gcd_eq_gcd_ab _ _⟩
    rw [ha₀, hN₀, Nat.cast_mul, Nat.cast_mul, mul_assoc, mul_assoc, ← mul_add, eq_comm,
      mul_comm _ p, mul_comm _ q] at hpq
    exact ⟨p, q, Int.eq_one_of_mul_eq_self_right (Nat.cast_ne_zero.mpr hd) hpq⟩
  -- Lift it arbitrarily to a unit mod `N`.
  obtain ⟨u, hu⟩ := (ZMod.unitsMap_surjective (⟨d, mul_comm d N₀ ▸ hN₀⟩ : N₀ ∣ N)) hu₀.unit
  rw [unitsMap_def, ← Units.eq_iff, Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe] at hu
  refine ⟨u.val, u.isUnit, ?_⟩
  rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val u.1, ha₀, ← Nat.cast_mul,
    ZMod.natCast_eq_natCast_iff, mul_comm _ d, Nat.ModEq]
  simp only [hN₀, Nat.mul_mod_mul_left, Nat.mul_right_inj hd]
  rw [← Nat.ModEq, ← ZMod.natCast_eq_natCast_iff, ← hu, natCast_val, castHom_apply]

end ZMod
