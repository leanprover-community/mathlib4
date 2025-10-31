/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# Prime elements

In this file we define the predicate `Prime p`
saying that an element of a commutative monoid with zero is prime.
Namely, `Prime p` means that `p` isn't zero, it isn't a unit,
and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`;

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Irreducible`
(see `irreducible_iff_prime`), however this is not true in general.

## Main definitions

* `Prime`: a prime element of a commutative monoid with zero

## Main results

* `irreducible_iff_prime`: the two definitions are equivalent in a decomposition monoid.
-/

assert_not_exists IsOrderedMonoid Multiset

variable {M : Type*}

section Prime

variable [CommMonoidWithZero M]

/-- An element `p` of a commutative monoid with zero (e.g., a ring) is called *prime*,
if it's not zero, not a unit, and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`. -/
def Prime (p : M) : Prop :=
  p ≠ 0 ∧ ¬IsUnit p ∧ ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b

namespace Prime

variable {p : M} (hp : Prime p)
include hp

theorem ne_zero : p ≠ 0 :=
  hp.1

theorem not_unit : ¬IsUnit p :=
  hp.2.1

theorem not_dvd_one : ¬p ∣ 1 :=
  mt (isUnit_of_dvd_one ·) hp.not_unit

theorem ne_one : p ≠ 1 := fun h => hp.2.1 (h.symm ▸ isUnit_one)

theorem dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  hp.2.2 a b h

theorem dvd_mul {a b : M} : p ∣ a * b ↔ p ∣ a ∨ p ∣ b :=
  ⟨hp.dvd_or_dvd, (Or.elim · (dvd_mul_of_dvd_left · _) (dvd_mul_of_dvd_right · _))⟩

theorem isPrimal : IsPrimal p := fun _a _b dvd ↦ (hp.dvd_or_dvd dvd).elim
  (fun h ↦ ⟨p, 1, h, one_dvd _, (mul_one p).symm⟩) fun h ↦ ⟨1, p, one_dvd _, h, (one_mul p).symm⟩

theorem not_dvd_mul {a b : M} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ a * b :=
  hp.dvd_mul.not.mpr <| not_or.mpr ⟨ha, hb⟩

theorem dvd_of_dvd_pow {a : M} {n : ℕ} (h : p ∣ a ^ n) : p ∣ a := by
  induction n with
  | zero =>
    rw [pow_zero] at h
    have := isUnit_of_dvd_one h
    have := not_unit hp
    contradiction
  | succ n ih =>
    rw [pow_succ'] at h
    rcases dvd_or_dvd hp h with dvd_a | dvd_pow
    · assumption
    · exact ih dvd_pow

theorem dvd_pow_iff_dvd {a : M} {n : ℕ} (hn : n ≠ 0) : p ∣ a ^ n ↔ p ∣ a :=
  ⟨hp.dvd_of_dvd_pow, (dvd_pow · hn)⟩

end Prime

@[simp]
theorem not_prime_zero : ¬Prime (0 : M) := fun h => h.ne_zero rfl

@[simp]
theorem not_prime_one : ¬Prime (1 : M) := fun h => h.not_unit isUnit_one

end Prime

theorem Irreducible.not_dvd_isUnit [CommMonoid M] {p u : M} (hp : Irreducible p) (hu : IsUnit u) :
    ¬p ∣ u :=
  mt (isUnit_of_dvd_unit · hu) hp.not_isUnit

theorem Irreducible.not_dvd_one [CommMonoid M] {p : M} (hp : Irreducible p) : ¬p ∣ 1 :=
  hp.not_dvd_isUnit isUnit_one

theorem Irreducible.not_dvd_unit [CommMonoid M] {p : M} (u : Mˣ) (hp : Irreducible p) :
    ¬ p ∣ u :=
  hp.not_dvd_isUnit u.isUnit

@[simp]
theorem not_irreducible_zero [MonoidWithZero M] : ¬Irreducible (0 : M)
  | ⟨hn0, h⟩ =>
    have : IsUnit (0 : M) ∨ IsUnit (0 : M) := h (mul_zero 0).symm
    this.elim hn0 hn0

theorem Irreducible.ne_zero [MonoidWithZero M] : ∀ {p : M}, Irreducible p → p ≠ 0
  | _, hp, rfl => not_irreducible_zero hp

/-- If `p` and `q` are irreducible, then `p ∣ q` implies `q ∣ p`. -/
theorem Irreducible.dvd_symm [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irreducible q) :
    p ∣ q → q ∣ p := by
  rintro ⟨q', rfl⟩
  rw [IsUnit.mul_right_dvd (Or.resolve_left (of_irreducible_mul hq) hp.not_isUnit)]

theorem Irreducible.dvd_comm [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irreducible q) :
    p ∣ q ↔ q ∣ p :=
  ⟨hp.dvd_symm hq, hq.dvd_symm hp⟩

section CommMonoidWithZero

variable [CommMonoidWithZero M]

theorem Irreducible.prime_of_isPrimal {a : M}
    (irr : Irreducible a) (primal : IsPrimal a) : Prime a :=
  ⟨irr.ne_zero, irr.not_isUnit, fun a b dvd ↦ by
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := primal dvd
    exact (of_irreducible_mul irr).symm.imp (·.mul_right_dvd.mpr h₁) (·.mul_left_dvd.mpr h₂)⟩

theorem Irreducible.prime [DecompositionMonoid M] {a : M} (irr : Irreducible a) : Prime a :=
  irr.prime_of_isPrimal (DecompositionMonoid.primal a)

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero M] {p : M}

protected theorem Prime.irreducible (hp : Prime p) : Irreducible p :=
  ⟨hp.not_unit, fun a b ↦ by
    rintro rfl
    exact (hp.dvd_or_dvd dvd_rfl).symm.imp
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_right <| right_ne_zero_of_mul hp.ne_zero).mp <|
        dvd_mul_of_dvd_right · _)
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_left <| left_ne_zero_of_mul hp.ne_zero).mp <|
        dvd_mul_of_dvd_left · _)⟩

theorem irreducible_iff_prime [DecompositionMonoid M] {a : M} : Irreducible a ↔ Prime a :=
  ⟨Irreducible.prime, Prime.irreducible⟩

end CancelCommMonoidWithZero
