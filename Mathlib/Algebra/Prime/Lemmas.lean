/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import Mathlib.Algebra.Divisibility.Hom
import Mathlib.Algebra.Group.Irreducible.Lemmas
import Mathlib.Algebra.GroupWithZero.Equiv
import Mathlib.Algebra.Prime.Defs
import Mathlib.Order.Monotone.Defs

/-!
# Associated, prime, and irreducible elements.

In this file we define the predicate `Prime p`
saying that an element of a commutative monoid with zero is prime.
Namely, `Prime p` means that `p` isn't zero, it isn't a unit,
and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`;

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Irreducible`,
however this is not true in general.

We also define an equivalence relation `Associated`
saying that two elements of a monoid differ by a multiplication by a unit.
Then we show that the quotient type `Associates` is a monoid
and prove basic properties of this quotient.
-/

assert_not_exists OrderedCommMonoid Multiset

variable {M N : Type*}

section Prime

variable [CommMonoidWithZero M]

section Map

variable [CommMonoidWithZero N] {F : Type*} {G : Type*} [FunLike F M N]
variable [MonoidWithZeroHomClass F M N] [FunLike G N M] [MulHomClass G N M]
variable (f : F) (g : G) {p : M}

theorem comap_prime (hinv : ∀ a, g (f a : N) = a) (hp : Prime (f p)) : Prime p :=
  ⟨fun h => hp.1 <| by simp [h], fun h => hp.2.1 <| h.map f, fun a b h => by
    refine
        (hp.2.2 (f a) (f b) <| by
              convert map_dvd f h
              simp).imp
          ?_ ?_ <;>
      · intro h
        convert ← map_dvd g h <;> apply hinv⟩

theorem MulEquiv.prime_iff {E : Type*} [EquivLike E M N] [MulEquivClass E M N] (e : E) :
    Prime (e p) ↔ Prime p := by
  let e := MulEquivClass.toMulEquiv e
  exact ⟨comap_prime e e.symm fun a => by simp,
    fun h => (comap_prime e.symm e fun a => by simp) <| (e.symm_apply_apply p).substr h⟩

end Map

end Prime

theorem Prime.left_dvd_or_dvd_right_of_dvd_mul [CancelCommMonoidWithZero M] {p : M} (hp : Prime p)
    {a b : M} : a ∣ p * b → p ∣ a ∨ a ∣ b := by
  rintro ⟨c, hc⟩
  rcases hp.2.2 a c (hc ▸ dvd_mul_right _ _) with (h | ⟨x, rfl⟩)
  · exact Or.inl h
  · rw [mul_left_comm, mul_right_inj' hp.ne_zero] at hc
    exact Or.inr (hc.symm ▸ dvd_mul_right _ _)

theorem Prime.pow_dvd_of_dvd_mul_left [CancelCommMonoidWithZero M] {p a b : M} (hp : Prime p)
    (n : ℕ) (h : ¬p ∣ a) (h' : p ^ n ∣ a * b) : p ^ n ∣ b := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact one_dvd b
  | succ n ih =>
    obtain ⟨c, rfl⟩ := ih (dvd_trans (pow_dvd_pow p n.le_succ) h')
    rw [pow_succ]
    apply mul_dvd_mul_left _ ((hp.dvd_or_dvd _).resolve_left h)
    rwa [← mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero), ← pow_succ, mul_left_comm]

theorem Prime.pow_dvd_of_dvd_mul_right [CancelCommMonoidWithZero M] {p a b : M} (hp : Prime p)
    (n : ℕ) (h : ¬p ∣ b) (h' : p ^ n ∣ a * b) : p ^ n ∣ a := by
  rw [mul_comm] at h'
  exact hp.pow_dvd_of_dvd_mul_left n h h'

theorem Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd [CancelCommMonoidWithZero M] {p a b : M}
    {n : ℕ} (hp : Prime p) (hpow : p ^ n.succ ∣ a ^ n.succ * b ^ n) (hb : ¬p ^ 2 ∣ b) : p ∣ a := by
  -- Suppose `p ∣ b`, write `b = p * x` and `hy : a ^ n.succ * b ^ n = p ^ n.succ * y`.
  rcases hp.dvd_or_dvd ((dvd_pow_self p (Nat.succ_ne_zero n)).trans hpow) with H | hbdiv
  · exact hp.dvd_of_dvd_pow H
  obtain ⟨x, rfl⟩ := hp.dvd_of_dvd_pow hbdiv
  obtain ⟨y, hy⟩ := hpow
  -- Then we can divide out a common factor of `p ^ n` from the equation `hy`.
  have : a ^ n.succ * x ^ n = p * y := by
    refine mul_left_cancel₀ (pow_ne_zero n hp.ne_zero) ?_
    rw [← mul_assoc _ p, ← pow_succ, ← hy, mul_pow, ← mul_assoc (a ^ n.succ), mul_comm _ (p ^ n),
      mul_assoc]
  -- So `p ∣ a` (and we're done) or `p ∣ x`, which can't be the case since it implies `p^2 ∣ b`.
  refine hp.dvd_of_dvd_pow ((hp.dvd_or_dvd ⟨_, this⟩).resolve_right fun hdvdx => hb ?_)
  obtain ⟨z, rfl⟩ := hp.dvd_of_dvd_pow hdvdx
  rw [pow_two, ← mul_assoc]
  exact dvd_mul_right _ _

theorem prime_pow_succ_dvd_mul {M : Type*} [CancelCommMonoidWithZero M] {p x y : M} (h : Prime p)
    {i : ℕ} (hxy : p ^ (i + 1) ∣ x * y) : p ^ (i + 1) ∣ x ∨ p ∣ y := by
  rw [or_iff_not_imp_right]
  exact fun a ↦ Prime.pow_dvd_of_dvd_mul_right h (i + 1) a hxy

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero M] {a p : M}

theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul (hp : Prime p) {a b : M} {k l : ℕ} :
    p ^ k ∣ a → p ^ l ∣ b → p ^ (k + l + 1) ∣ a * b → p ^ (k + 1) ∣ a ∨ p ^ (l + 1) ∣ b :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ =>
  have h : p ^ (k + l) * (x * y) = p ^ (k + l) * (p * z) := by
    simpa [mul_comm, pow_add, hx, hy, mul_assoc, mul_left_comm] using hz
  have hp0 : p ^ (k + l) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hpd : p ∣ x * y := ⟨z, by rwa [mul_right_inj' hp0] at h⟩
  (hp.dvd_or_dvd hpd).elim
    (fun ⟨d, hd⟩ => Or.inl ⟨d, by simp [*, pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩)
    fun ⟨d, hd⟩ => Or.inr ⟨d, by simp [*, pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩

theorem Prime.not_isSquare (hp : Prime p) : ¬IsSquare p :=
  hp.irreducible.not_isSquare

theorem IsSquare.not_prime (ha : IsSquare a) : ¬Prime a := fun h => h.not_isSquare ha

theorem not_prime_pow {n : ℕ} (hn : n ≠ 1) : ¬Prime (a ^ n) := fun hp =>
  not_irreducible_pow hn hp.irreducible

end CancelCommMonoidWithZero

section CommMonoidWithZero

theorem DvdNotUnit.isUnit_of_irreducible_right [CommMonoidWithZero M] {p q : M}
    (h : DvdNotUnit p q) (hq : Irreducible q) : IsUnit p := by
  obtain ⟨_, x, hx, hx'⟩ := h
  exact ((irreducible_iff.1 hq).right hx').resolve_right hx

theorem not_irreducible_of_not_unit_dvdNotUnit [CommMonoidWithZero M] {p q : M} (hp : ¬IsUnit p)
    (h : DvdNotUnit p q) : ¬Irreducible q :=
  mt h.isUnit_of_irreducible_right hp

theorem DvdNotUnit.not_unit [CommMonoidWithZero M] {p q : M} (hp : DvdNotUnit p q) : ¬IsUnit q := by
  obtain ⟨-, x, hx, rfl⟩ := hp
  exact fun hc => hx (isUnit_iff_dvd_one.mpr (dvd_of_mul_left_dvd (isUnit_iff_dvd_one.mp hc)))

end CommMonoidWithZero

section CancelCommMonoidWithZero

theorem DvdNotUnit.ne [CancelCommMonoidWithZero M] {p q : M} (h : DvdNotUnit p q) : p ≠ q := by
  by_contra hcontra
  obtain ⟨hp, x, hx', hx''⟩ := h
  simp_all

theorem pow_injective_of_not_isUnit [CancelCommMonoidWithZero M] {q : M} (hq : ¬IsUnit q)
    (hq' : q ≠ 0) : Function.Injective fun n : ℕ => q ^ n := by
  refine injective_of_lt_imp_ne fun n m h => DvdNotUnit.ne ⟨pow_ne_zero n hq', q ^ (m - n), ?_, ?_⟩
  · exact not_isUnit_of_not_isUnit_dvd hq (dvd_pow (dvd_refl _) (Nat.sub_pos_of_lt h).ne')
  · exact (pow_mul_pow_sub q h.le).symm

theorem pow_inj_of_not_isUnit [CancelCommMonoidWithZero M] {q : M} (hq : ¬IsUnit q)
    (hq' : q ≠ 0) {m n : ℕ} : q ^ m = q ^ n ↔ m = n :=
  (pow_injective_of_not_isUnit hq hq').eq_iff

end CancelCommMonoidWithZero
