/-
Copyright (c) 2024 Jineon Baek, Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.Radical
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative

/-!
# Radical of a polynomial

This file proves some theorems on `radical` and `divRadical` of polynomials.
See `RingTheory.Radical` for the definition of `radical` and `divRadical`.
-/

open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain EuclideanDomain

variable {k : Type*} [Field k] [DecidableEq k]

theorem degree_radical_le {a : k[X]} (h : a ≠ 0) :
  (radical a).degree ≤ a.degree := degree_le_of_dvd radical_dvd_self h

theorem natDegree_radical_le {a : k[X]} :
    (radical a).natDegree ≤ a.natDegree := by
  by_cases ha : a = 0
  · simp [ha]
  · exact natDegree_le_of_dvd radical_dvd_self ha

theorem divRadical_dvd_derivative (a : k[X]) : divRadical a ∣ derivative a := by
  induction a using induction_on_coprime
  · case h0 =>
    rw [derivative_zero]
    apply dvd_zero
  · case h1 a ha =>
    exact (divRadical_isUnit ha).dvd
  · case hpr p i hp =>
    cases i
    · rw [pow_zero, derivative_one]
      apply dvd_zero
    · case succ i =>
      rw [← mul_dvd_mul_iff_left radical_ne_zero, radical_mul_divRadical,
        radical_pow_of_prime hp i.succ_ne_zero, derivative_pow_succ, ← mul_assoc]
      apply dvd_mul_of_dvd_left
      rw [mul_comm, mul_assoc]
      apply dvd_mul_of_dvd_right
      rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero i hp.ne_zero), dvd_normalize_iff]
  · -- If it holds for coprime pair a and b, then it also holds for a * b.
    case hcp x y hpxy hx hy =>
    have hc : IsCoprime x y :=
      EuclideanDomain.isCoprime_of_dvd
        (fun ⟨hx, hy⟩ => not_isUnit_zero (hpxy (zero_dvd_iff.mpr hx) (zero_dvd_iff.mpr hy)))
        fun p hp _ hpx hpy => hp (hpxy hpx hpy)
    rw [divRadical_mul hc, derivative_mul]
    exact dvd_add (mul_dvd_mul hx (divRadical_dvd_self y)) (mul_dvd_mul (divRadical_dvd_self x) hy)

theorem divRadical_dvd_wronskian_left (a b : k[X]) : divRadical a ∣ wronskian a b := by
  rw [wronskian]
  apply dvd_sub
  · apply dvd_mul_of_dvd_left
    exact divRadical_dvd_self a
  · apply dvd_mul_of_dvd_left
    exact divRadical_dvd_derivative a

theorem divRadical_dvd_wronskian_right (a b : k[X]) : divRadical b ∣ wronskian a b := by
  rw [← wronskian_neg_eq, dvd_neg]
  exact divRadical_dvd_wronskian_left _ _
