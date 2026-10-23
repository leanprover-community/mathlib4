/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
module

public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Prime.Defs

import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Find

/-!
# Characteristic of semirings

## Main definitions
* `CharP R p` expresses that the ring (additive monoid with one) `R` has characteristic `p`
* `ringChar`: the characteristic of a ring
* `ExpChar R p` expresses that the ring (additive monoid with one) `R` has
  exponential characteristic `p` (which is `1` if `R` has characteristic 0, and `p` if it has
  prime characteristic `p`)
-/

@[expose] public section

assert_not_exists Field Finset OrderHom

variable (R : Type*)

namespace CharP
section AddMonoidWithOne
variable [AddMonoidWithOne R] (p : ℕ)

/-- The generator of the kernel of the unique homomorphism ℕ → R for a semiring R. -/
@[mk_iff]
class _root_.CharP (R : Type*) [AddMonoidWithOne R] (p : outParam ℕ) : Prop where
  cast_eq_iff_mod_eq (R p) : ∀ a b : ℕ, (a : R) = (b : R) ↔ a % p = b % p

variable [CharP R p]

variable {R} in
lemma congr {q : ℕ} (h : p = q) : CharP R q := h ▸ ‹CharP R p›

lemma cast_eq_iff_mod_eq' {a b : ℕ} : (a : R) = (b : R) ↔ a % p = b % p :=
  cast_eq_iff_mod_eq R p a b

lemma cast_eq_zero_iff (x : ℕ) : (x : R) = 0 ↔ p ∣ x := by
  simpa [Nat.dvd_iff_mod_eq_zero] using cast_eq_iff_mod_eq R p x 0

lemma ofNat_eq_zero' (a : ℕ) [a.AtLeastTwo] (h : p ∣ a) : (ofNat(a) : R) = 0 := by
  rwa [← CharP.cast_eq_zero_iff R p] at h

@[simp] lemma cast_eq_zero : (p : R) = 0 :=
  (cast_eq_zero_iff R p p).2 dvd_rfl

-- TODO: This lemma needs to be `@[simp]` for confluence in the presence of `CharP.cast_eq_zero` and
-- `Nat.cast_ofNat`, but with `no_index` on its entire LHS, it matches literally every expression so
-- is too expensive. If https://github.com/leanprover/lean4/issues/2867 is fixed in a performant way, this can be made `@[simp]`.
--
-- @[simp]
lemma ofNat_eq_zero [p.AtLeastTwo] : (ofNat(p) : R) = 0 := cast_eq_zero R p

lemma eq {p q : ℕ} (hp : CharP R p) (hq : CharP R q) : p = q :=
  Nat.dvd_antisymm (have := hp; (cast_eq_zero_iff R p q).1 (@cast_eq_zero _ _ _ hq))
    ((cast_eq_zero_iff R q p).1 (@cast_eq_zero _ _ _ hp))

instance ofCharZero [CharZero R] : CharP R 0 where
  cast_eq_iff_mod_eq := by simp

theorem charP_to_charZero [CharP R 0] : CharZero R where
  cast_injective a b h := by simpa [cast_eq_iff_mod_eq] using h

theorem charP_zero_iff_charZero : CharP R 0 ↔ CharZero R :=
  ⟨fun _ ↦ charP_to_charZero R, fun _ ↦ ofCharZero R⟩

lemma cast_eq_mod (k : ℕ) : (k : R) = (k % p : ℕ) := by
  nth_rw 1 [← Nat.div_add_mod k p]
  rw [Nat.cast_add, (cast_eq_zero_iff R p _).mpr (Nat.dvd_mul_right _ _), zero_add]

lemma of_minimal_cast_eq_zero {p : ℕ} (hp : p ≠ 0) (hp0 : (p : R) = 0)
    (hp1 : ∀ n < p, (n : R) = 0 → n = 0) : CharP R p := by
  have hp2 (k : ℕ) : (k : R) = k % p := by
    nth_rw 1 [← Nat.div_add_mod k p]
    rw [Nat.cast_add, ← nsmul_one, mul_nsmul, nsmul_one, hp0, nsmul_zero, zero_add]
  refine ⟨fun a b => Iff.symm ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hp2 a, hp2 b, h]
  wlog h0 : a ≤ b generalizing a b
  · exact (this b a h.symm (Nat.le_of_not_le h0)).symm
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k := Nat.exists_eq_add_of_le h0
  replace h0 : ((p - 1) * a : ℕ) + (a : R) = 0 := by
    rw [← Nat.cast_add, ← Nat.add_one_mul, Nat.sub_one_add_one hp,
      hp2, Nat.mul_mod_right, Nat.cast_zero]
  replace h : (k % p : R) = 0 := by
    rw [← h0, h, Nat.cast_add, ← add_assoc, h0, zero_add, ← hp2]
  rw [← Nat.add_mod_mod, hp1 _ (Nat.mod_lt _ (Nat.pos_of_ne_zero hp)) h, Nat.add_zero]

lemma _root_.CharP_iff_minimal_cast_eq_zero {p : ℕ} (hp : p ≠ 0) :
    CharP R p ↔ (p : R) = 0 ∧ ∀ n < p, (n : R) = 0 → n = 0 :=
  ⟨fun _ => ⟨cast_eq_zero R p, fun n hnp hn =>
    Nat.eq_zero_of_dvd_of_lt ((cast_eq_zero_iff R p n).mp hn) hnp⟩,
  fun h => of_minimal_cast_eq_zero R hp h.1 h.2⟩

/-- See `CharP.of_cast_eq_zero_iff_dvd` for a version that works for rings, even if `p = 0`. -/
lemma of_cast_eq_zero_iff_dvd' {p : ℕ} (hp : p ≠ 0) (hp0 : ∀ x : ℕ, (x : R) = 0 ↔ p ∣ x) :
    CharP R p :=
  of_minimal_cast_eq_zero R hp ((hp0 p).mpr dvd_rfl) fun n hnp hn =>
    Nat.eq_zero_of_dvd_of_lt ((hp0 n).mp hn) hnp

/-- See `CharP_iff_cast_eq_zero_iff_dvd` for a version that works for rings, even if `p = 0`. -/
lemma _root_.CharP_iff_cast_eq_zero_iff_dvd' {p : ℕ} (hp : p ≠ 0) :
    CharP R p ↔ ∀ x : ℕ, (x : R) = 0 ↔ p ∣ x :=
  ⟨fun _ => cast_eq_zero_iff R p, of_cast_eq_zero_iff_dvd' R hp⟩

lemma exists_of_exists_ne_zero_cast_eq_zero (h : ∃ p : ℕ, (p : R) = 0 ∧ p ≠ 0) :
    ∃ p ≠ 0, CharP R p :=
  let := Classical.decEq R
  let p := Nat.find h
  have hp : p ≠ 0 := (Nat.find_spec h).2
  ⟨p, hp, of_minimal_cast_eq_zero R hp (Nat.find_spec h).1 fun _ hnp hn =>
    by_contra fun hn0 => Nat.find_min h hnp ⟨hn, hn0⟩⟩

lemma exists_CharP_dvd_of_cast_eq_zero {p : ℕ} (hp : p ≠ 0) (hp0 : (p : R) = 0) :
    ∃ q, q ∣ p ∧ CharP R q := by
  obtain ⟨q, -, Hq⟩ := exists_of_exists_ne_zero_cast_eq_zero R ⟨p, hp0, hp⟩
  exact ⟨q, (cast_eq_zero_iff R q p).mp hp0, Hq⟩

variable [IsLeftCancelAdd R]

lemma of_cast_eq_zero_iff_dvd {p : ℕ} (hp : ∀ x : ℕ, (x : R) = 0 ↔ p ∣ x) : CharP R p := by
  obtain rfl | hp0 := eq_or_ne p 0
  exacts [(charP_zero_iff_charZero R).mpr (charZero_of_inj_zero fun n => by simp [hp]),
    of_cast_eq_zero_iff_dvd' R hp0 hp]

lemma _root_.CharP_iff_cast_eq_zero_iff_dvd {p : ℕ} : CharP R p ↔ ∀ x : ℕ, (x : R) = 0 ↔ p ∣ x :=
  ⟨fun _ => cast_eq_zero_iff R p, of_cast_eq_zero_iff_dvd R⟩

lemma «exists» : ∃ p, CharP R p := by
  let := Classical.decEq R
  by_cases! H : ∀ p : ℕ, (p : R) = 0 → p = 0
  · exact ⟨0, (charP_zero_iff_charZero R).mpr (charZero_of_inj_zero H)⟩
  · obtain ⟨p, -, Hp⟩ := exists_of_exists_ne_zero_cast_eq_zero R H
    exact ⟨p, Hp⟩

lemma existsUnique : ∃! p, CharP R p :=
  let ⟨c, H⟩ := CharP.exists R
  ⟨c, H, fun _y H2 => CharP.eq R H2 H⟩

end AddMonoidWithOne

section AddGroupWithOne
variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

lemma intCast_eq_zero_iff (a : ℤ) : (a : R) = 0 ↔ (p : ℤ) ∣ a := by
  rcases lt_trichotomy a 0 with (h | rfl | h)
  · rw [← neg_eq_zero, ← Int.cast_neg, ← Int.dvd_neg]
    lift -a to ℕ using Int.neg_nonneg.mpr (le_of_lt h) with b
    rw [Int.cast_natCast, CharP.cast_eq_zero_iff R p, Int.natCast_dvd_natCast]
  · simp
  · lift a to ℕ using le_of_lt h with b
    rw [Int.cast_natCast, CharP.cast_eq_zero_iff R p, Int.natCast_dvd_natCast]

end AddGroupWithOne
end CharP

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
noncomputable def ringChar [NonAssocSemiring R] [IsLeftCancelAdd R] : ℕ :=
  Classical.choose (CharP.existsUnique R)

namespace ringChar
variable [NonAssocSemiring R] [IsLeftCancelAdd R]

lemma spec : ∀ a b : ℕ, (a : R) = b ↔ a % ringChar R = b % ringChar R := by
  let : CharP R (ringChar R) := (Classical.choose_spec (CharP.existsUnique R)).1
  exact CharP.cast_eq_iff_mod_eq R (ringChar R)

lemma eq (p : ℕ) [C : CharP R p] : ringChar R = p :=
  ((Classical.choose_spec (CharP.existsUnique R)).2 p C).symm

instance (priority := low) charP : CharP R (ringChar R) :=
  ⟨spec R⟩

variable {R}

lemma of_eq {p : ℕ} (h : ringChar R = p) : CharP R p :=
  CharP.congr (ringChar R) h

lemma eq_iff {p : ℕ} : ringChar R = p ↔ CharP R p :=
  ⟨of_eq, @eq R _ _ p⟩

lemma dvd {x : ℕ} (hx : (x : R) = 0) : ringChar R ∣ x :=
  (CharP.cast_eq_zero_iff R _ x).mp hx

@[simp]
lemma eq_zero [CharZero R] : ringChar R = 0 :=
  eq R 0

lemma Nat.cast_ringChar : (ringChar R : R) = 0 := by rw [CharP.cast_eq_zero_iff]

@[simp]
lemma ringChar_eq_one : ringChar R = 1 ↔ Subsingleton R := by
  rw [← Nat.dvd_one, ← CharP.cast_eq_zero_iff R, eq_comm, Nat.cast_one,
    subsingleton_iff_zero_eq_one]

@[nontriviality]
lemma ringChar_subsingleton [Subsingleton R] : ringChar R = 1 := by simpa

end ringChar

lemma CharP.neg_one_ne_one [AddGroupWithOne R] (p : ℕ) [CharP R p] [Fact (2 < p)] :
    (-1 : R) ≠ (1 : R) := by
  rw [ne_comm, ← sub_ne_zero, sub_neg_eq_add, one_add_one_eq_two, ← Nat.cast_two, Ne,
    CharP.cast_eq_zero_iff R p 2]
  exact fun h ↦ (Fact.out : 2 < p).not_ge <| Nat.le_of_dvd Nat.zero_lt_two h

namespace CharP

section

variable [NonAssocRing R]

lemma ringChar_zero_iff_CharZero : ringChar R = 0 ↔ CharZero R := by
  rw [ringChar.eq_iff, charP_zero_iff_charZero]

end

section Semiring

variable [NonAssocSemiring R]

lemma char_ne_one [Nontrivial R] (p : ℕ) [hc : CharP R p] : p ≠ 1 := fun hp : p = 1 =>
  have : (1 : R) = 0 := by simpa using (cast_eq_zero_iff R p 1).mpr (hp ▸ dvd_refl p)
  absurd this one_ne_zero

section NoZeroDivisors

variable [NoZeroDivisors R]

lemma char_is_prime_of_two_le (p : ℕ) [CharP R p] (hp : 2 ≤ p) : Nat.Prime p :=
  suffices ∀ (d) (_ : d ∣ p), d = 1 ∨ d = p from Nat.prime_def.mpr ⟨hp, this⟩
  fun (d : ℕ) (hdvd : ∃ e, p = d * e) =>
  let ⟨e, hmul⟩ := hdvd
  have : (p : R) = 0 := (cast_eq_zero_iff R p p).mpr (dvd_refl p)
  have : (d : R) * e = 0 := @Nat.cast_mul R _ d e ▸ hmul ▸ this
  Or.elim (eq_zero_or_eq_zero_of_mul_eq_zero this)
    (fun hd : (d : R) = 0 =>
      have : p ∣ d := (cast_eq_zero_iff R p d).mp hd
      show d = 1 ∨ d = p from Or.inr (this.antisymm' ⟨e, hmul⟩))
    fun he : (e : R) = 0 =>
    have : p ∣ e := (cast_eq_zero_iff R p e).mp he
    have : e ∣ p := dvd_of_mul_left_eq d (Eq.symm hmul)
    have : e = p := ‹e ∣ p›.antisymm ‹p ∣ e›
    have h₀ : 0 < p := by grind
    have : d * p = 1 * p := by grind
    show d = 1 ∨ d = p from Or.inl (mul_right_cancel₀ h₀.ne' this)

section Nontrivial

variable [Nontrivial R]

lemma char_is_prime_or_zero (p : ℕ) [hc : CharP R p] : Nat.Prime p ∨ p = 0 :=
  match p, hc with
  | 0, _ => Or.inr rfl
  | 1, hc => absurd (Eq.refl (1 : ℕ)) (@char_ne_one R _ _ (1 : ℕ) hc)
  | m + 2, hc => Or.inl (@char_is_prime_of_two_le R _ _ (m + 2) hc (Nat.le_add_left 2 m))

/-- The characteristic is prime if it is non-zero. -/
lemma char_prime_of_ne_zero {p : ℕ} [CharP R p] (hp : p ≠ 0) : p.Prime :=
  (CharP.char_is_prime_or_zero R p).resolve_right hp

lemma exists' (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ∨ ∃ p : ℕ, Fact p.Prime ∧ CharP R p := by
  obtain ⟨p, hchar⟩ := CharP.exists R
  rcases char_is_prime_or_zero R p with h | rfl
  exacts [Or.inr ⟨p, Fact.mk h, hchar⟩, Or.inl (charP_to_charZero R)]

lemma char_is_prime_of_pos (p : ℕ) [NeZero p] [CharP R p] : Fact p.Prime :=
  ⟨(CharP.char_is_prime_or_zero R _).resolve_right <| NeZero.ne p⟩

end Nontrivial

end NoZeroDivisors

end Semiring

section NonAssocSemiring

variable {R} [NonAssocSemiring R]

-- This lemma is not an instance, to make sure that trying to prove `α` is a subsingleton does
-- not try to find a ring structure on `α`, which can be expensive.
lemma CharOne.subsingleton [CharP R 1] : Subsingleton R :=
  Subsingleton.intro <|
    suffices ∀ r : R, r = 0 from fun a b => show a = b by rw [this a, this b]
    fun r =>
    calc
      r = 1 * r := by rw [one_mul]
      _ = (1 : ℕ) * r := by rw [Nat.cast_one]
      _ = 0 * r := by rw [CharP.cast_eq_zero]
      _ = 0 := by rw [zero_mul]

lemma false_of_nontrivial_of_char_one [Nontrivial R] [CharP R 1] : False := by
  have : Subsingleton R := CharOne.subsingleton
  exact false_of_nontrivial_of_subsingleton R

lemma ringChar_ne_one [Nontrivial R] [IsLeftCancelAdd R] : ringChar R ≠ 1 := by
  simpa using not_subsingleton R

lemma nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) [hr : CharP R v] : Nontrivial R :=
  ⟨⟨(1 : ℕ), 0, fun h =>
      hv <| by rwa [CharP.cast_eq_zero_iff _ v, Nat.dvd_one] at h⟩⟩

end NonAssocSemiring
end CharP

namespace NeZero

variable [AddMonoidWithOne R] {n p : ℕ}

lemma of_not_dvd [CharP R p] (h : ¬p ∣ n) : NeZero (n : R) :=
  ⟨(CharP.cast_eq_zero_iff R p n).not.mpr h⟩

lemma not_char_dvd (p : ℕ) [CharP R p] (k : ℕ) [h : NeZero (k : R)] : ¬p ∣ k := by
  rwa [← CharP.cast_eq_zero_iff R p k, ← Ne, ← neZero_iff]

end NeZero

/-!
### Exponential characteristic

This section defines the exponential characteristic, which is defined to be 1 for a ring with
characteristic 0 and the same as the ordinary characteristic, if the ordinary characteristic is
prime. This concept is useful to simplify some theorem statements.
This file establishes a few basic results relating it to the (ordinary characteristic).
The definition is stated for a semiring, but the actual results are for nontrivial rings
(as far as exponential characteristic one is concerned), respectively a ring without zero-divisors
(for prime characteristic).
-/

section AddMonoidWithOne
variable [AddMonoidWithOne R]

/-- The definition of the exponential characteristic of a semiring. -/
@[mk_iff]
class inductive ExpChar : ℕ → Prop
  | zero [CharZero R] : ExpChar 1
  | prime {q : ℕ} (hprime : q.Prime) [hchar : CharP R q] : ExpChar q

instance expChar_prime (p) [CharP R p] [Fact p.Prime] : ExpChar R p := ExpChar.prime Fact.out
instance expChar_one [CharZero R] : ExpChar R 1 := ExpChar.zero

@[simp]
lemma expChar_one_iff : ExpChar R 1 ↔ CharZero R := by simp [expChar_iff, Nat.not_prime_one]

@[simp]
lemma expChar_prime_iff {p} (hp : p.Prime) : ExpChar R p ↔ CharP R p := by
  simp [expChar_iff, hp.ne_one, hp]

lemma expChar_ne_zero (p : ℕ) [hR : ExpChar R p] : p ≠ 0 := by
  cases hR
  · exact one_ne_zero
  · exact ‹p.Prime›.ne_zero

variable {R} in
/-- The exponential characteristic is unique. -/
lemma ExpChar.eq {p q : ℕ} (hp : ExpChar R p) (hq : ExpChar R q) : p = q := by
  rcases hp with ⟨hp⟩ | ⟨hp'⟩
  · rcases hq with hq | hq'
    exacts [rfl, False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hq'))]
  · rcases hq with hq | hq'
    exacts [False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hp')),
      CharP.eq R ‹_› ‹_›]

lemma ExpChar.congr {p : ℕ} (q : ℕ) [hq : ExpChar R q] (h : q = p) : ExpChar R p := h ▸ hq

/-- The exponential characteristic is one if the characteristic is zero. -/
lemma expChar_one_of_char_zero (q : ℕ) [hp : CharP R 0] [hq : ExpChar R q] : q = 1 := by
  rcases hq with q | hq_prime
  · rfl
  · exact False.elim <| hq_prime.ne_zero <| ‹CharP R q›.eq R hp

/-- The characteristic equals the exponential characteristic iff the former is prime. -/
lemma char_eq_expChar_iff (p q : ℕ) [hp : CharP R p] [hq : ExpChar R q] : p = q ↔ p.Prime := by
  rcases hq with q | hq_prime
  · rw [(CharP.eq R hp (.ofCharZero R) : p = 0)]
    decide
  · exact ⟨fun hpq => hpq.symm ▸ hq_prime, fun _ => CharP.eq R hp ‹CharP R q›⟩

/-- The exponential characteristic is a prime number or one.
See also `CharP.char_is_prime_or_zero`. -/
lemma expChar_is_prime_or_one (q : ℕ) [hq : ExpChar R q] : Nat.Prime q ∨ q = 1 := by
  cases hq with
  | zero => exact .inr rfl
  | prime hp => exact .inl hp

/-- The exponential characteristic is positive. -/
lemma expChar_pos (q : ℕ) [ExpChar R q] : 0 < q := by
  rcases expChar_is_prime_or_one R q with h | rfl
  exacts [Nat.Prime.pos h, Nat.one_pos]

/-- Any power of the exponential characteristic is positive. -/
lemma expChar_pow_pos (q : ℕ) [ExpChar R q] (n : ℕ) : 0 < q ^ n :=
  Nat.pow_pos (expChar_pos R q)

-- This could be an instance, but there are no `ExpChar R 1` instances in mathlib.
/-- The characteristic is zero if the exponential characteristic is one. -/
lemma charZero_of_expChar_one' [ExpChar R 1] : CharZero R :=
  (expChar_one_iff _).mp ‹_›

/-- The exponential characteristic is one if the characteristic is zero. -/
lemma char_zero_of_expChar_one (p : ℕ) [hp : CharP R p] [hq : ExpChar R 1] : p = 0 := by
  cases hq
  · exact CharP.eq R hp (.ofCharZero R)
  · exact False.elim (Nat.not_prime_one ‹_›)

/-- The exponential characteristic is one iff the characteristic is zero. -/
lemma expChar_one_iff_char_zero (p q : ℕ) [CharP R p] [ExpChar R q] : q = 1 ↔ p = 0 := by
  constructor
  · rintro rfl
    exact char_zero_of_expChar_one R p
  · rintro rfl
    exact expChar_one_of_char_zero R q

end AddMonoidWithOne

section NonAssocSemiring
variable [NonAssocSemiring R] [IsLeftCancelAdd R]

/-- Noncomputable function that outputs the unique exponential characteristic of a semiring. -/
noncomputable def ringExpChar : ℕ := max (ringChar R) 1

lemma ringExpChar.eq (q : ℕ) [h : ExpChar R q] : ringExpChar R = q := by
  rcases h with _ | h
  · have := CharP.ofCharZero R
    rw [ringExpChar, ringChar.eq R 0]; rfl
  rw [ringExpChar, ringChar.eq R q]
  exact Nat.max_eq_left h.one_lt.le

@[simp] lemma ringExpChar.eq_one [CharZero R] : ringExpChar R = 1 := by
  rw [ringExpChar, ringChar.eq_zero, max_eq_right (Nat.zero_le _)]

end NonAssocSemiring

lemma ExpChar.exists [Ring R] [IsDomain R] : ∃ q, ExpChar R q := by
  obtain _ | ⟨p, ⟨hp⟩, _⟩ := CharP.exists' R
  exacts [⟨1, .zero⟩, ⟨p, .prime hp⟩]

lemma ExpChar.exists_unique [Ring R] [IsDomain R] : ∃! q, ExpChar R q :=
  let ⟨q, H⟩ := ExpChar.exists R
  ⟨q, H, fun _ H2 ↦ ExpChar.eq H2 H⟩

instance ringExpChar.expChar [Ring R] [IsDomain R] : ExpChar R (ringExpChar R) := by
  obtain ⟨q, _⟩ := ExpChar.exists R
  rwa [ringExpChar.eq R q]

variable {R} in
lemma ringExpChar.of_eq [Ring R] [IsDomain R] {q : ℕ} (h : ringExpChar R = q) : ExpChar R q :=
  h ▸ ringExpChar.expChar R

variable {R} in
lemma ringExpChar.eq_iff [Ring R] [IsDomain R] {q : ℕ} : ringExpChar R = q ↔ ExpChar R q :=
  ⟨ringExpChar.of_eq, fun _ ↦ ringExpChar.eq R q⟩
