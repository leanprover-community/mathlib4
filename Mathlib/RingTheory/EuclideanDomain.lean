/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes
-/
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Lemmas about Euclidean domains

Various about Euclidean domains are proved; all of them seem to be true
more generally for principal ideal domains, so these lemmas should
probably be reproved in more generality and this file perhaps removed?

## Tags

euclidean domain
-/


section

open EuclideanDomain Set Ideal

section GCDMonoid

variable {R : Type*} [EuclideanDomain R] [GCDMonoid R] {p q : R}

theorem left_div_gcd_ne_zero {p q : R} (hp : p ≠ 0) : p / GCDMonoid.gcd p q ≠ 0 := by
  obtain ⟨r, hr⟩ := GCDMonoid.gcd_dvd_left p q
  obtain ⟨pq0, r0⟩ : GCDMonoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hp)
  nth_rw 1 [hr]
  rw [mul_comm, mul_div_cancel_right₀ _ pq0]
  exact r0

theorem right_div_gcd_ne_zero {p q : R} (hq : q ≠ 0) : q / GCDMonoid.gcd p q ≠ 0 := by
  obtain ⟨r, hr⟩ := GCDMonoid.gcd_dvd_right p q
  obtain ⟨pq0, r0⟩ : GCDMonoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hq)
  nth_rw 1 [hr]
  rw [mul_comm, mul_div_cancel_right₀ _ pq0]
  exact r0

theorem isCoprime_div_gcd_div_gcd (hq : q ≠ 0) :
    IsCoprime (p / GCDMonoid.gcd p q) (q / GCDMonoid.gcd p q) :=
  (gcd_isUnit_iff _ _).1 <|
    isUnit_gcd_of_eq_mul_gcd
        (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hq) <| gcd_dvd_left _ _).symm
        (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hq) <| gcd_dvd_right _ _).symm <|
      gcd_ne_zero_of_right hq

/-- This is a version of `isCoprime_div_gcd_div_gcd` which replaces the `q ≠ 0` assumption with
`gcd p q ≠ 0`. -/
theorem isCoprime_div_gcd_div_gcd_of_gcd_ne_zero (hpq : GCDMonoid.gcd p q ≠ 0) :
    IsCoprime (p / GCDMonoid.gcd p q) (q / GCDMonoid.gcd p q) :=
  (gcd_isUnit_iff _ _).1 <|
    isUnit_gcd_of_eq_mul_gcd
        (EuclideanDomain.mul_div_cancel' (hpq) <| gcd_dvd_left _ _).symm
        (EuclideanDomain.mul_div_cancel' (hpq) <| gcd_dvd_right _ _).symm <| hpq

end GCDMonoid

namespace EuclideanDomain

/-- Create a `GCDMonoid` whose `GCDMonoid.gcd` matches `EuclideanDomain.gcd`. -/
def gcdMonoid (R) [EuclideanDomain R] [DecidableEq R] : GCDMonoid R where
  gcd := gcd
  lcm := lcm
  gcd_dvd_left := gcd_dvd_left
  gcd_dvd_right := gcd_dvd_right
  dvd_gcd := dvd_gcd
  gcd_mul_lcm a b := by rw [EuclideanDomain.gcd_mul_lcm]
  lcm_zero_left := lcm_zero_left
  lcm_zero_right := lcm_zero_right

variable {α : Type*} [EuclideanDomain α]

theorem span_gcd [DecidableEq α] (x y : α) :
    span ({gcd x y} : Set α) = span ({x, y} : Set α) :=
  letI := EuclideanDomain.gcdMonoid α
  _root_.span_gcd x y

theorem gcd_isUnit_iff [DecidableEq α] {x y : α} : IsUnit (gcd x y) ↔ IsCoprime x y :=
  letI := EuclideanDomain.gcdMonoid α
  _root_.gcd_isUnit_iff x y

-- this should be proved for UFDs surely?
theorem isCoprime_of_dvd {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z ∈ nonunits α, z ≠ 0 → z ∣ x → ¬z ∣ y) : IsCoprime x y :=
  letI := Classical.decEq α
  letI := EuclideanDomain.gcdMonoid α
  _root_.isCoprime_of_dvd x y nonzero H

-- this should be proved for UFDs surely?
theorem dvd_or_coprime (x y : α) (h : Irreducible x) :
    x ∣ y ∨ IsCoprime x y :=
  letI := Classical.decEq α
  letI := EuclideanDomain.gcdMonoid α
  _root_.dvd_or_isCoprime x y h

end EuclideanDomain

end
