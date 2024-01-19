/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Nat.Prime

#align_import algebra.char_p.exp_char from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Exponential characteristic

This file defines the exponential characteristic, which is defined to be 1 for a ring with
characteristic 0 and the same as the ordinary characteristic, if the ordinary characteristic is
prime. This concept is useful to simplify some theorem statements.
This file establishes a few basic results relating it to the (ordinary characteristic).
The definition is stated for a semiring, but the actual results are for nontrivial rings
(as far as exponential characteristic one is concerned), respectively a ring without zero-divisors
(for prime characteristic).

## Main results
- `ExpChar`: the definition of exponential characteristic
- `expChar_is_prime_or_one`: the exponential characteristic is a prime or one
- `char_eq_expChar_iff`: the characteristic equals the exponential characteristic iff the
  characteristic is prime

## Tags
exponential characteristic, characteristic
-/


universe u

variable (R : Type u)

section Semiring

variable [Semiring R]

/-- The definition of the exponential characteristic of a semiring. -/
class inductive ExpChar (R : Type u) [Semiring R] : ℕ → Prop
  | zero [CharZero R] : ExpChar R 1
  | prime {q : ℕ} (hprime : q.Prime) [hchar : CharP R q] : ExpChar R q
#align exp_char ExpChar
#align exp_char.prime ExpChar.prime

variable {R} in
/-- The exponential characteristic is unique. -/
theorem ExpChar.eq {p q : ℕ} (hp : ExpChar R p) (hq : ExpChar R q) : p = q := by
  cases' hp with hp _ hp' hp
  · cases' hq with hq _ hq' hq
    exacts [rfl, False.elim (Nat.not_prime_zero (CharP.eq R hq (CharP.ofCharZero R) ▸ hq'))]
  · cases' hq with hq _ hq' hq
    exacts [False.elim (Nat.not_prime_zero (CharP.eq R hp (CharP.ofCharZero R) ▸ hp')),
      CharP.eq R hp hq]

theorem ExpChar.congr {p : ℕ} (q : ℕ) [hq : ExpChar R q] (h : q = p) : ExpChar R p := h ▸ hq

/-- Noncomputable function that outputs the unique exponential characteristic of a semiring. -/
noncomputable def ringExpChar (R : Type*) [NonAssocSemiring R] : ℕ := max (ringChar R) 1

theorem ringExpChar.eq (q : ℕ) [h : ExpChar R q] : ringExpChar R = q := by
  cases' h with _ _ h _
  · haveI := CharP.ofCharZero R
    rw [ringExpChar, ringChar.eq R 0]; rfl
  rw [ringExpChar, ringChar.eq R q]
  exact Nat.max_eq_left h.one_lt.le

@[simp]
theorem ringExpChar.eq_one (R : Type*) [NonAssocSemiring R] [CharZero R] : ringExpChar R = 1 := by
  rw [ringExpChar, ringChar.eq_zero, max_eq_right zero_le_one]

/-- The exponential characteristic is one if the characteristic is zero. -/
theorem expChar_one_of_char_zero (q : ℕ) [hp : CharP R 0] [hq : ExpChar R q] : q = 1 := by
  cases' hq with q hq_one hq_prime hq_hchar
  · rfl
  · exact False.elim <| hq_prime.ne_zero <| hq_hchar.eq R hp
#align exp_char_one_of_char_zero expChar_one_of_char_zero

/-- The characteristic equals the exponential characteristic iff the former is prime. -/
theorem char_eq_expChar_iff (p q : ℕ) [hp : CharP R p] [hq : ExpChar R q] : p = q ↔ p.Prime := by
  cases' hq with q hq_one hq_prime hq_hchar
  · rw [(CharP.eq R hp inferInstance : p = 0)]
    decide
  · exact ⟨fun hpq => hpq.symm ▸ hq_prime, fun _ => CharP.eq R hp hq_hchar⟩
#align char_eq_exp_char_iff char_eq_expChar_iff

section Nontrivial

variable [Nontrivial R]

/-- The exponential characteristic is one if the characteristic is zero. -/
theorem char_zero_of_expChar_one (p : ℕ) [hp : CharP R p] [hq : ExpChar R 1] : p = 0 := by
  cases hq
  · exact CharP.eq R hp inferInstance
  · exact False.elim (CharP.char_ne_one R 1 rfl)
#align char_zero_of_exp_char_one char_zero_of_expChar_one

-- This could be an instance, but there are no `ExpChar R 1` instances in mathlib.
/-- The characteristic is zero if the exponential characteristic is one. -/
theorem charZero_of_expChar_one' [hq : ExpChar R 1] : CharZero R := by
  cases hq
  · assumption
  · exact False.elim (CharP.char_ne_one R 1 rfl)
#align char_zero_of_exp_char_one' charZero_of_expChar_one'

/-- The exponential characteristic is one iff the characteristic is zero. -/
theorem expChar_one_iff_char_zero (p q : ℕ) [CharP R p] [ExpChar R q] : q = 1 ↔ p = 0 := by
  constructor
  · rintro rfl
    exact char_zero_of_expChar_one R p
  · rintro rfl
    exact expChar_one_of_char_zero R q
#align exp_char_one_iff_char_zero expChar_one_iff_char_zero

section NoZeroDivisors

variable [NoZeroDivisors R]

/-- A helper lemma: the characteristic is prime if it is non-zero. -/
theorem char_prime_of_ne_zero {p : ℕ} [hp : CharP R p] (p_ne_zero : p ≠ 0) : Nat.Prime p := by
  cases' CharP.char_is_prime_or_zero R p with h h
  · exact h
  · contradiction
#align char_prime_of_ne_zero char_prime_of_ne_zero

/-- The exponential characteristic is a prime number or one.
See also `CharP.char_is_prime_or_zero`. -/
theorem expChar_is_prime_or_one (q : ℕ) [hq : ExpChar R q] : Nat.Prime q ∨ q = 1 := by
  cases hq with
  | zero => exact .inr rfl
  | prime hp => exact .inl hp
#align exp_char_is_prime_or_one expChar_is_prime_or_one

/-- The exponential characteristic is positive. -/
theorem expChar_pos (q : ℕ) [ExpChar R q] : 0 < q := by
  rcases expChar_is_prime_or_one R q with h | rfl
  exacts [Nat.Prime.pos h, Nat.one_pos]

/-- Any power of the exponential characteristic is positive. -/
theorem expChar_pow_pos (q : ℕ) [ExpChar R q] (n : ℕ) : 0 < q ^ n :=
  Nat.pos_pow_of_pos n (expChar_pos R q)

end NoZeroDivisors

end Nontrivial

end Semiring

theorem ExpChar.exists [Ring R] [IsDomain R] : ∃ q, ExpChar R q := by
  obtain _ | ⟨p, ⟨hp⟩, _⟩ := CharP.exists' R
  exacts [⟨1, .zero⟩, ⟨p, .prime hp⟩]

theorem ExpChar.exists_unique [Ring R] [IsDomain R] : ∃! q, ExpChar R q :=
  let ⟨q, H⟩ := ExpChar.exists R
  ⟨q, H, fun _ H2 ↦ ExpChar.eq H2 H⟩

instance ringExpChar.expChar [Ring R] [IsDomain R] : ExpChar R (ringExpChar R) := by
  obtain ⟨q, _⟩ := ExpChar.exists R
  rwa [ringExpChar.eq R q]

variable {R} in
theorem ringExpChar.of_eq [Ring R] [IsDomain R] {q : ℕ} (h : ringExpChar R = q) : ExpChar R q :=
  h ▸ ringExpChar.expChar R

variable {R} in
theorem ringExpChar.eq_iff [Ring R] [IsDomain R] {q : ℕ} : ringExpChar R = q ↔ ExpChar R q :=
  ⟨ringExpChar.of_eq, fun _ ↦ ringExpChar.eq R q⟩

/-- If a ring homomorphism `R →+* A` is injective then `A` has the same exponential characteristic
as `R`. -/
theorem expChar_of_injective_ringHom {R A : Type*}
    [Semiring R] [Semiring A] {f : R →+* A} (h : Function.Injective f)
    (q : ℕ) [hR : ExpChar R q] : ExpChar A q := by
  cases' hR with _ _ hprime _
  · haveI := charZero_of_injective_ringHom h; exact .zero
  haveI := charP_of_injective_ringHom h q; exact .prime hprime

/-- If the algebra map `R →+* A` is injective then `A` has the same exponential characteristic
as `R`. -/
theorem expChar_of_injective_algebraMap {R A : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A))
    (q : ℕ) [ExpChar R q] : ExpChar A q := expChar_of_injective_ringHom h q

theorem add_pow_expChar_of_commute [Semiring R] {q : ℕ} [hR : ExpChar R q]
    (x y : R) (h : Commute x y) : (x + y) ^ q = x ^ q + y ^ q := by
  cases' hR with _ _ hprime _
  · simp only [pow_one]
  haveI := Fact.mk hprime; exact add_pow_char_of_commute R x y h

theorem add_pow_expChar_pow_of_commute [Semiring R] {q : ℕ} [hR : ExpChar R q]
    {n : ℕ} (x y : R) (h : Commute x y) : (x + y) ^ q ^ n = x ^ q ^ n + y ^ q ^ n := by
  cases' hR with _ _ hprime _
  · simp only [one_pow, pow_one]
  haveI := Fact.mk hprime; exact add_pow_char_pow_of_commute R x y h

theorem sub_pow_expChar_of_commute [Ring R] {q : ℕ} [hR : ExpChar R q]
    (x y : R) (h : Commute x y) : (x - y) ^ q = x ^ q - y ^ q := by
  cases' hR with _ _ hprime _
  · simp only [pow_one]
  haveI := Fact.mk hprime; exact sub_pow_char_of_commute R x y h

theorem sub_pow_expChar_pow_of_commute [Ring R] {q : ℕ} [hR : ExpChar R q]
    {n : ℕ} (x y : R) (h : Commute x y) : (x - y) ^ q ^ n = x ^ q ^ n - y ^ q ^ n := by
  cases' hR with _ _ hprime _
  · simp only [one_pow, pow_one]
  haveI := Fact.mk hprime; exact sub_pow_char_pow_of_commute R x y h

theorem add_pow_expChar [CommSemiring R] {q : ℕ} [hR : ExpChar R q]
    (x y : R) : (x + y) ^ q = x ^ q + y ^ q := by
  cases' hR with _ _ hprime _
  · simp only [pow_one]
  haveI := Fact.mk hprime; exact add_pow_char R x y

theorem add_pow_expChar_pow [CommSemiring R] {q : ℕ} [hR : ExpChar R q]
    {n : ℕ} (x y : R) : (x + y) ^ q ^ n = x ^ q ^ n + y ^ q ^ n := by
  cases' hR with _ _ hprime _
  · simp only [one_pow, pow_one]
  haveI := Fact.mk hprime; exact add_pow_char_pow R x y

theorem sub_pow_expChar [CommRing R] {q : ℕ} [hR : ExpChar R q]
    (x y : R) : (x - y) ^ q = x ^ q - y ^ q := by
  cases' hR with _ _ hprime _
  · simp only [pow_one]
  haveI := Fact.mk hprime; exact sub_pow_char R x y

theorem sub_pow_expChar_pow [CommRing R] {q : ℕ} [hR : ExpChar R q]
    {n : ℕ} (x y : R) : (x - y) ^ q ^ n = x ^ q ^ n - y ^ q ^ n := by
  cases' hR with _ _ hprime _
  · simp only [one_pow, pow_one]
  haveI := Fact.mk hprime; exact sub_pow_char_pow R x y

theorem ExpChar.neg_one_pow_expChar [Ring R] (q : ℕ) [hR : ExpChar R q] :
    (-1 : R) ^ q = -1 := by
  cases' hR with _ _ hprime _
  · simp only [pow_one]
  haveI := Fact.mk hprime; exact CharP.neg_one_pow_char R q

theorem ExpChar.neg_one_pow_expChar_pow [Ring R] (q n : ℕ) [hR : ExpChar R q] :
    (-1 : R) ^ q ^ n = -1 := by
  cases' hR with _ _ hprime _
  · simp only [one_pow, pow_one]
  haveI := Fact.mk hprime; exact CharP.neg_one_pow_char_pow R q n

section BigOperators

open BigOperators

variable {R}

variable [CommSemiring R] (q : ℕ) [hR : ExpChar R q] (n : ℕ)

theorem list_sum_pow_expChar (l : List R) : l.sum ^ q = (l.map (· ^ q : R → R)).sum := by
  cases hR
  case zero => simp_rw [pow_one, List.map_id']
  case prime hprime _ => haveI := Fact.mk hprime; exact list_sum_pow_char q l

theorem multiset_sum_pow_expChar (s : Multiset R) : s.sum ^ q = (s.map (· ^ q : R → R)).sum := by
  cases hR
  case zero => simp_rw [pow_one, Multiset.map_id']
  case prime hprime _ => haveI := Fact.mk hprime; exact multiset_sum_pow_char q s

theorem sum_pow_expChar {ι : Type*} (s : Finset ι) (f : ι → R) :
    (∑ i in s, f i) ^ q = ∑ i in s, f i ^ q := by
  cases hR
  case zero => simp_rw [pow_one]
  case prime hprime _ => haveI := Fact.mk hprime; exact sum_pow_char q s f

theorem list_sum_pow_expChar_pow (l : List R) :
    l.sum ^ q ^ n = (l.map (· ^ q ^ n : R → R)).sum := by
  cases hR
  case zero => simp_rw [one_pow, pow_one, List.map_id']
  case prime hprime _ => haveI := Fact.mk hprime; exact list_sum_pow_char_pow q n l

theorem multiset_sum_pow_expChar_pow (s : Multiset R) :
    s.sum ^ q ^ n = (s.map (· ^ q ^ n : R → R)).sum := by
  cases hR
  case zero => simp_rw [one_pow, pow_one, Multiset.map_id']
  case prime hprime _ => haveI := Fact.mk hprime; exact multiset_sum_pow_char_pow q n s

theorem sum_pow_expChar_pow {ι : Type*} (s : Finset ι) (f : ι → R) :
    (∑ i in s, f i) ^ q ^ n = ∑ i in s, f i ^ q ^ n := by
  cases hR
  case zero => simp_rw [one_pow, pow_one]
  case prime hprime _ => haveI := Fact.mk hprime; exact sum_pow_char_pow q n s f

end BigOperators
