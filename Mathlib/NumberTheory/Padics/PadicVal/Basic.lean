/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Matthew Robert Ballard
-/
module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.Nat.Prime.Int

/-!
# `p`-adic Valuation

This file defines the `p`-adic valuation on `ℕ`, `ℤ`, and `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`. The `p`-adic valuations on `ℕ` and `ℤ` agree with that on `ℚ`.

The valuation induces a norm on `ℚ`. This norm is defined in
`Mathlib/NumberTheory/Padics/PadicNorm.lean`.

## Notation

This file uses the local notation `/.` for `Rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## Calculations with `p`-adic valuations

* `padicValNat_factorial`: Legendre's Theorem. The `p`-adic valuation of `n!` is the sum of the
  quotients `n / p ^ i`. This sum is expressed over the finset `Ico 1 b` where `b` is any bound
  greater than `log p n`. See `Nat.Prime.multiplicity_factorial` for the same result but stated in
  the language of prime multiplicity.

* `sub_one_mul_padicValNat_factorial`: Legendre's Theorem.  Taking (`p - 1`) times
  the `p`-adic valuation of `n!` equals `n` minus the sum of base `p` digits of `n`.

* `padicValNat_choose`: Kummer's Theorem. The `p`-adic valuation of `n.choose k` is the number
  of carries when `k` and `n - k` are added in base `p`. This sum is expressed over the finset
  `Ico 1 b` where `b` is any bound greater than `log p n`. See `Nat.Prime.multiplicity_choose` for
  the same result but stated in the language of prime multiplicity.

* `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`: Kummer's Theorem. Taking (`p - 1`) times the
  `p`-adic valuation of the binomial `n` over `k` equals the sum of the digits of `k` plus the sum
  of the digits of `n - k` minus the sum of digits of `n`, all base `p`.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/

@[expose] public section


universe u

open Nat Rat
open scoped Finset

namespace padicValNat

variable {p : ℕ}

/-- If `p ≠ 0` and `p ≠ 1`, then `padicValNat p p` is `1`. -/
@[simp]
theorem self (hp : 1 < p) : padicValNat p p = 1 := by
  simp [padicValNat_def', ne_zero_of_lt hp, hp.ne']

theorem eq_zero_of_not_dvd {n : ℕ} (h : ¬p ∣ n) : padicValNat p n = 0 :=
  eq_zero_iff.2 <| Or.inr <| Or.inr h

open Nat.maxPowDiv

theorem maxPowDiv_eq_emultiplicity {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    p.maxPowDiv n = emultiplicity p n := by
  apply (emultiplicity_eq_of_dvd_of_not_dvd (pow_dvd p n) _).symm
  intro h
  apply Nat.not_lt.mpr <| le_of_dvd hp hn h
  simp

set_option backward.isDefEq.respectTransparency false in
theorem maxPowDiv_eq_multiplicity {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) (h : FiniteMultiplicity p n) :
    p.maxPowDiv n = multiplicity p n := by
  exact_mod_cast h.emultiplicity_eq_multiplicity ▸ maxPowDiv_eq_emultiplicity hp hn

/-- Allows for more efficient code for `padicValNat` -/
@[csimp]
theorem padicValNat_eq_maxPowDiv : @padicValNat = @maxPowDiv := by
  ext p n
  by_cases! +distrib h : 1 < p ∧ 0 < n
  · rw [padicValNat_def' h.1.ne' h.2.ne', maxPowDiv_eq_multiplicity h.1 h.2.ne']
    exact Nat.finiteMultiplicity_iff.2 ⟨h.1.ne', h.2⟩
  · rcases h with (h | h)
    · interval_cases p
      · simp [Classical.em]
      · dsimp [padicValNat, maxPowDiv]
        rw [go, if_neg]; simp
    · simp [Nat.le_zero.mp h]

end padicValNat

/-- For `p ≠ 1`, the `p`-adic valuation of an integer `z ≠ 0` is the largest natural number `k` such
that `p^k` divides `z`. If `x = 0` or `p = 1`, then `padicValInt p q` defaults to `0`. -/
def padicValInt (p : ℕ) (z : ℤ) : ℕ :=
  padicValNat p z.natAbs

namespace padicValInt

variable {p : ℕ}

theorem of_ne_one_ne_zero {z : ℤ} (hp : p ≠ 1) (hz : z ≠ 0) :
    padicValInt p z = multiplicity (p : ℤ) z := by
  rw [padicValInt, padicValNat_def' hp (Int.natAbs_ne_zero.mpr hz)]
  apply Int.multiplicity_natAbs

/-- `padicValInt p 0` is `0` for any `p`. -/
@[simp]
protected theorem zero : padicValInt p 0 = 0 := by simp [padicValInt]

/-- `padicValInt p 1` is `0` for any `p`. -/
@[simp]
protected theorem one : padicValInt p 1 = 0 := by simp [padicValInt]

/-- The `p`-adic value of a natural is its `p`-adic value as an integer. -/
@[simp]
theorem of_nat {n : ℕ} : padicValInt p n = padicValNat p n := by simp [padicValInt]

/-- If `p ≠ 0` and `p ≠ 1`, then `padicValInt p p` is `1`. -/
theorem self (hp : 1 < p) : padicValInt p p = 1 := by simp [padicValNat.self hp]

@[simp]
theorem eq_zero_iff {z : ℤ} : padicValInt p z = 0 ↔ p = 1 ∨ z = 0 ∨ ¬(p : ℤ) ∣ z := by
  rw [padicValInt, padicValNat.eq_zero_iff, Int.natAbs_eq_zero, ← Int.ofNat_dvd_left]

theorem eq_zero_of_not_dvd {z : ℤ} (h : ¬(p : ℤ) ∣ z) : padicValInt p z = 0 := by
  simp [h]

end padicValInt

/-- `padicValRat` defines the valuation of a rational `q` to be the valuation of `q.num` minus the
valuation of `q.den`. If `q = 0` or `p = 1`, then `padicValRat p q` defaults to `0`. -/
def padicValRat (p : ℕ) (q : ℚ) : ℤ :=
  padicValInt p q.num - padicValNat p q.den

lemma padicValRat_def (p : ℕ) (q : ℚ) :
    padicValRat p q = padicValInt p q.num - padicValNat p q.den :=
  rfl

namespace padicValRat

variable {p : ℕ}

/-- `padicValRat p q` is symmetric in `q`. -/
@[simp]
protected theorem neg (q : ℚ) : padicValRat p (-q) = padicValRat p q := by
  simp [padicValRat, padicValInt]

/-- `padicValRat p 0` is `0` for any `p`. -/
@[simp]
protected theorem zero : padicValRat p 0 = 0 := by simp [padicValRat]

/-- `padicValRat p 1` is `0` for any `p`. -/
@[simp]
protected theorem one : padicValRat p 1 = 0 := by simp [padicValRat]

/-- The `p`-adic value of an integer `z ≠ 0` is its `p`-adic_value as a rational. -/
@[simp]
theorem of_int {z : ℤ} : padicValRat p z = padicValInt p z := by simp [padicValRat]

/-- The `p`-adic value of an integer `z ≠ 0` is the multiplicity of `p` in `z`. -/
theorem of_int_multiplicity {z : ℤ} (hp : p ≠ 1) (hz : z ≠ 0) :
    padicValRat p (z : ℚ) = multiplicity (p : ℤ) z := by
  rw [of_int, padicValInt.of_ne_one_ne_zero hp hz]

theorem multiplicity_sub_multiplicity {q : ℚ} (hp : p ≠ 1) (hq : q ≠ 0) :
    padicValRat p q = multiplicity (p : ℤ) q.num - multiplicity p q.den := by
  rw [padicValRat, padicValInt.of_ne_one_ne_zero hp (Rat.num_ne_zero.2 hq),
    padicValNat_def' hp q.den_ne_zero]

/-- The `p`-adic value of an integer `z ≠ 0` is its `p`-adic value as a rational. -/
@[simp]
theorem of_nat {n : ℕ} : padicValRat p n = padicValNat p n := by simp [padicValRat]

/-- If `p ≠ 0` and `p ≠ 1`, then `padicValRat p p` is `1`. -/
theorem self (hp : 1 < p) : padicValRat p p = 1 := by simp [hp]

end padicValRat

section padicValNat

variable {p : ℕ}

theorem zero_le_padicValRat_of_nat (n : ℕ) : 0 ≤ padicValRat p n := by simp

/-- `padicValRat` coincides with `padicValNat`. -/
@[norm_cast]
theorem padicValRat_of_nat (n : ℕ) : ↑(padicValNat p n) = padicValRat p n := by simp

@[simp]
theorem padicValNat_self [Fact p.Prime] : padicValNat p p = 1 := by
  rw [padicValNat_def (@Fact.out p.Prime).ne_zero]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem one_le_padicValNat_of_dvd {n : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0) (div : p ∣ n) :
    1 ≤ padicValNat p n := by
  rwa [← WithTop.coe_le_coe, ENat.some_eq_coe, padicValNat_eq_emultiplicity hn,
    ← pow_dvd_iff_le_emultiplicity, pow_one]

theorem dvd_iff_padicValNat_ne_zero {p n : ℕ} [Fact p.Prime] (hn0 : n ≠ 0) :
    p ∣ n ↔ padicValNat p n ≠ 0 :=
  ⟨fun h => one_le_iff_ne_zero.mp (one_le_padicValNat_of_dvd hn0 h), fun h =>
    Classical.not_not.1 (mt padicValNat.eq_zero_of_not_dvd h)⟩

end padicValNat

namespace padicValRat

variable {p : ℕ} [hp : Fact p.Prime]

/-- The multiplicity of `p : ℕ` in `a : ℤ` is finite exactly when `a ≠ 0`. -/
theorem finite_int_prime_iff {a : ℤ} : FiniteMultiplicity (p : ℤ) a ↔ a ≠ 0 := by
  simp [Int.finiteMultiplicity_iff, hp.1.ne_one]

/-- A rewrite lemma for `padicValRat p q` when `q` is expressed in terms of `Rat.mk`. -/
protected theorem defn (p : ℕ) [hp : Fact p.Prime] {q : ℚ} {n d : ℤ} (hqz : q ≠ 0)
    (qdf : q = n /. d) :
    padicValRat p q = multiplicity (p : ℤ) n - multiplicity (p : ℤ) d := by
  have hd : d ≠ 0 := Rat.mk_denom_ne_zero_of_ne_zero hqz qdf
  let ⟨c, hc1, hc2⟩ := Rat.num_den_mk hd qdf
  rw [padicValRat.multiplicity_sub_multiplicity hp.1.ne_one hqz]
  simp only [hc1, hc2]
  rw [multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1),
    multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1)]
  · rw [Nat.cast_add, Nat.cast_add]
    simp_rw [Int.natCast_multiplicity p q.den]
    ring
  · simpa [finite_int_prime_iff, hc2] using hd
  · simpa [finite_int_prime_iff, hqz, hc2] using hd

/-- A rewrite lemma for `padicValRat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`. -/
protected theorem mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValRat p (q * r) = padicValRat p q + padicValRat p r := by
  have : q * r = (q.num * r.num) /. (q.den * r.den) := by
    rw [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt, Nat.cast_mul]
  have hq' : q.num /. q.den ≠ 0 := by rwa [Rat.num_divInt_den]
  have hr' : r.num /. r.den ≠ 0 := by rwa [Rat.num_divInt_den]
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.1
  rw [padicValRat.defn p (mul_ne_zero hq hr) this]
  conv_rhs =>
    rw [← q.num_divInt_den, padicValRat.defn p hq', ← r.num_divInt_den, padicValRat.defn p hr']
  rw [multiplicity_mul hp', multiplicity_mul hp', Nat.cast_add, Nat.cast_add]
  · ring
  · simp [finite_int_prime_iff]
  · simp [finite_int_prime_iff, hq, hr]

/-- A rewrite lemma for `padicValRat p (q^k)` with condition `q ≠ 0`. -/
protected theorem pow {q : ℚ} (hq : q ≠ 0) {k : ℕ} :
    padicValRat p (q ^ k) = k * padicValRat p q := by
  induction k <;>
    simp [*, padicValRat.mul hq (pow_ne_zero _ hq), _root_.pow_succ', add_mul, add_comm]

/-- A rewrite lemma for `padicValRat p (q⁻¹)` with condition `q ≠ 0`. -/
protected theorem inv (q : ℚ) : padicValRat p q⁻¹ = -padicValRat p q := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [eq_neg_iff_add_eq_zero, ← padicValRat.mul (inv_ne_zero hq) hq, inv_mul_cancel₀ hq,
      padicValRat.one]

/-- A rewrite lemma for `padicValRat p (q / r)` with conditions `q ≠ 0`, `r ≠ 0`. -/
protected theorem div {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValRat p (q / r) = padicValRat p q - padicValRat p r := by
  rw [div_eq_mul_inv, padicValRat.mul hq (inv_ne_zero hr), padicValRat.inv r, sub_eq_add_neg]

/-- A condition for `padicValRat p (n₁ / d₁) ≤ padicValRat p (n₂ / d₂)`, in terms of
divisibility by `p^n`. -/
theorem padicValRat_le_padicValRat_iff {n₁ n₂ d₁ d₂ : ℤ} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    padicValRat p (n₁ /. d₁) ≤ padicValRat p (n₂ /. d₂) ↔
      ∀ n : ℕ, (p : ℤ) ^ n ∣ n₁ * d₂ → (p : ℤ) ^ n ∣ n₂ * d₁ := by
  have hf1 : FiniteMultiplicity (p : ℤ) (n₁ * d₂) := finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂)
  have hf2 : FiniteMultiplicity (p : ℤ) (n₂ * d₁) := finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁)
  conv =>
    lhs
    rw [padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₁ hd₁) rfl,
      padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₂ hd₂) rfl, sub_le_iff_le_add', ←
      add_sub_assoc, le_sub_iff_add_le]
    norm_cast
    rw [← multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1) hf1, add_comm,
        ← multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1) hf2,
        hf1.multiplicity_le_multiplicity_iff hf2]

/-- Sufficient conditions to show that the `p`-adic valuation of `q` is less than or equal to the
`p`-adic valuation of `q + r`. -/
theorem le_padicValRat_add_of_le {q r : ℚ} (hqr : q + r ≠ 0)
    (h : padicValRat p q ≤ padicValRat p r) : padicValRat p q ≤ padicValRat p (q + r) :=
  if hq : q = 0 then by simpa [hq] using h
  else
    if hr : r = 0 then by simp [hr]
    else by
      have hqn : q.num ≠ 0 := Rat.num_ne_zero.2 hq
      have hqd : (q.den : ℤ) ≠ 0 := mod_cast Rat.den_nz _
      have hrn : r.num ≠ 0 := Rat.num_ne_zero.2 hr
      have hrd : (r.den : ℤ) ≠ 0 := mod_cast Rat.den_nz _
      have hqreq : q + r = (q.num * r.den + q.den * r.num) /. (q.den * r.den) := Rat.add_num_den _ _
      have hqrd : q.num * r.den + q.den * r.num ≠ 0 := Rat.mk_num_ne_zero_of_ne_zero hqr hqreq
      conv_lhs => rw [← q.num_divInt_den]
      rw [hqreq, padicValRat_le_padicValRat_iff hqn hqrd hqd (mul_ne_zero hqd hrd), ←
        emultiplicity_le_emultiplicity_iff, mul_left_comm,
        emultiplicity_mul (Nat.prime_iff_prime_int.1 hp.1), add_mul]
      rw [← q.num_divInt_den, ← r.num_divInt_den, padicValRat_le_padicValRat_iff hqn hrn hqd hrd, ←
        emultiplicity_le_emultiplicity_iff] at h
      calc
        _ ≤ min (emultiplicity ↑p (q.num * r.den * q.den))
                (emultiplicity ↑p (q.den * r.num * q.den)) :=
          le_min
            (by rw [emultiplicity_mul (a := _ * _) (Nat.prime_iff_prime_int.1 hp.1), add_comm])
            (by grw [mul_assoc, emultiplicity_mul (b := _ * _) (Nat.prime_iff_prime_int.1 hp.1), h])
        _ ≤ _ := min_le_emultiplicity_add

/-- The minimum of the valuations of `q` and `r` is at most the valuation of `q + r`. -/
theorem min_le_padicValRat_add {q r : ℚ} (hqr : q + r ≠ 0) :
    min (padicValRat p q) (padicValRat p r) ≤ padicValRat p (q + r) :=
  (le_total (padicValRat p q) (padicValRat p r)).elim
  (fun h => by rw [min_eq_left h]; exact le_padicValRat_add_of_le hqr h)
  (fun h => by rw [min_eq_right h, add_comm]; exact le_padicValRat_add_of_le (by rwa [add_comm]) h)

/-- Ultrametric property of a p-adic valuation. -/
lemma add_eq_min {q r : ℚ} (hqr : q + r ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hval : padicValRat p q ≠ padicValRat p r) :
    padicValRat p (q + r) = min (padicValRat p q) (padicValRat p r) := by
  have h1 := min_le_padicValRat_add (p := p) hqr
  have h2 := min_le_padicValRat_add (p := p) (ne_of_eq_of_ne (add_neg_cancel_right q r) hq)
  have h3 := min_le_padicValRat_add (p := p) (ne_of_eq_of_ne (add_neg_cancel_right r q) hr)
  rw [add_neg_cancel_right, padicValRat.neg] at h2 h3
  rw [add_comm] at h3
  omega

lemma add_eq_of_lt {q r : ℚ} (hqr : q + r ≠ 0)
    (hq : q ≠ 0) (hr : r ≠ 0) (hval : padicValRat p q < padicValRat p r) :
    padicValRat p (q + r) = padicValRat p q := by
  rw [add_eq_min hqr hq hr (ne_of_lt hval), min_eq_left (le_of_lt hval)]

lemma lt_add_of_lt {q r₁ r₂ : ℚ} (hqr : r₁ + r₂ ≠ 0)
    (hval₁ : padicValRat p q < padicValRat p r₁) (hval₂ : padicValRat p q < padicValRat p r₂) :
    padicValRat p q < padicValRat p (r₁ + r₂) :=
  lt_of_lt_of_le (lt_min hval₁ hval₂) (padicValRat.min_le_padicValRat_add hqr)

@[simp]
lemma self_pow_inv (r : ℕ) : padicValRat p ((p : ℚ) ^ r)⁻¹ = -r := by
  rw [padicValRat.inv, neg_inj, padicValRat.pow (Nat.cast_ne_zero.mpr hp.elim.ne_zero),
      padicValRat.self hp.elim.one_lt, mul_one]

/-- A finite sum of rationals with positive `p`-adic valuation has positive `p`-adic valuation
(if the sum is non-zero). -/
theorem sum_pos_of_pos {n : ℕ} {F : ℕ → ℚ} (hF : ∀ i, i < n → 0 < padicValRat p (F i))
    (hn0 : ∑ i ∈ Finset.range n, F i ≠ 0) : 0 < padicValRat p (∑ i ∈ Finset.range n, F i) := by
  induction n with
  | zero => exact False.elim (hn0 rfl)
  | succ d hd =>
    rw [Finset.sum_range_succ] at hn0 ⊢
    by_cases h : ∑ x ∈ Finset.range d, F x = 0
    · rw [h, zero_add]
      exact hF d (lt_add_one _)
    · refine lt_of_lt_of_le ?_ (min_le_padicValRat_add hn0)
      refine lt_min (hd (fun i hi => ?_) h) (hF d (lt_add_one _))
      exact hF _ (lt_trans hi (lt_add_one _))

/-- If the p-adic valuation of a finite set of positive rationals is greater than a given rational
number, then the p-adic valuation of their sum is also greater than the same rational number. -/
theorem lt_sum_of_lt {p j : ℕ} [hp : Fact (Nat.Prime p)] {F : ℕ → ℚ} {S : Finset ℕ}
    (hS : S.Nonempty) (hF : ∀ i, i ∈ S → padicValRat p (F j) < padicValRat p (F i))
    (hn1 : ∀ i : ℕ, 0 < F i) : padicValRat p (F j) < padicValRat p (∑ i ∈ S, F i) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton k =>
    rw [Finset.sum_singleton]
    exact hF k (by simp)
  | cons s S' Hnot Hne Hind =>
    rw [Finset.cons_eq_insert, Finset.sum_insert Hnot]
    exact padicValRat.lt_add_of_lt
      (ne_of_gt (add_pos (hn1 s) (Finset.sum_pos (fun i _ => hn1 i) Hne)))
      (hF _ (by simp [Finset.mem_insert, true_or]))
      (Hind (fun i hi => hF _ (by rw [Finset.cons_eq_insert, Finset.mem_insert]; exact Or.inr hi)))

end padicValRat

namespace padicValNat

variable {p a b : ℕ} [hp : Fact p.Prime]

/-- A rewrite lemma for `padicValNat p (a * b)` with conditions `a ≠ 0`, `b ≠ 0`. -/
protected theorem mul : a ≠ 0 → b ≠ 0 → padicValNat p (a * b) = padicValNat p a + padicValNat p b :=
  mod_cast padicValRat.mul (p := p) (q := a) (r := b)

protected theorem div_of_dvd (h : b ∣ a) :
    padicValNat p (a / b) = padicValNat p a - padicValNat p b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  obtain ⟨k, rfl⟩ := h
  obtain ⟨hb, hk⟩ := mul_ne_zero_iff.mp ha
  rw [mul_comm, k.mul_div_cancel hb.bot_lt, padicValNat.mul hk hb, Nat.add_sub_cancel]

/-- Dividing out by a prime factor reduces the `padicValNat` by `1`. -/
protected theorem div (dvd : p ∣ b) : padicValNat p (b / p) = padicValNat p b - 1 := by
  rw [padicValNat.div_of_dvd dvd, padicValNat_self]

/-- A version of `padicValRat.pow` for `padicValNat`. -/
protected theorem pow (n : ℕ) (ha : a ≠ 0) : padicValNat p (a ^ n) = n * padicValNat p a := by
  simpa only [← @Nat.cast_inj ℤ, push_cast] using padicValRat.pow (Nat.cast_ne_zero.mpr ha)

@[simp]
protected theorem prime_pow (n : ℕ) : padicValNat p (p ^ n) = n := by
  rw [padicValNat.pow _ (@Fact.out p.Prime).ne_zero, padicValNat_self, mul_one]

protected theorem div_pow (dvd : p ^ a ∣ b) : padicValNat p (b / p ^ a) = padicValNat p b - a := by
  rw [padicValNat.div_of_dvd dvd, padicValNat.prime_pow]

protected theorem div' {m : ℕ} (cpm : Coprime p m) {b : ℕ} (dvd : m ∣ b) :
    padicValNat p (b / m) = padicValNat p b := by
  rw [padicValNat.div_of_dvd dvd, eq_zero_of_not_dvd (hp.out.coprime_iff_not_dvd.mp cpm),
    Nat.sub_zero]

end padicValNat

section padicValNat

variable {p : ℕ}

theorem dvd_of_one_le_padicValNat {n : ℕ} (hp : 1 ≤ padicValNat p n) : p ∣ n := by
  by_contra h
  rw [padicValNat.eq_zero_of_not_dvd h] at hp
  exact lt_irrefl 0 (lt_of_lt_of_le zero_lt_one hp)

theorem pow_padicValNat_dvd {n : ℕ} : p ^ padicValNat p n ∣ n := by
  rcases eq_or_ne n 0 with (rfl | hn); · simp
  rcases eq_or_ne p 1 with (rfl | hp); · simp
  apply pow_dvd_of_le_multiplicity
  rw [padicValNat_def'] <;> assumption

set_option backward.isDefEq.respectTransparency false in
theorem padicValNat_dvd_iff_le_of_ne_one {p : ℕ} (hp : p ≠ 1) {a n : ℕ} (ha : a ≠ 0) :
    p ^ n ∣ a ↔ n ≤ padicValNat p a := by
  rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity_of_ne_one hp ha, Nat.cast_le]

theorem padicValNat_dvd_iff_le [hp : Fact p.Prime] {a n : ℕ} (ha : a ≠ 0) :
    p ^ n ∣ a ↔ n ≤ padicValNat p a :=
  padicValNat_dvd_iff_le_of_ne_one hp.out.ne_one ha

theorem padicValNat_dvd_iff_of_ne_one {p : ℕ} (hp : p ≠ 1) (n a : ℕ) :
    p ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValNat p a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact iff_of_true (dvd_zero _) (Or.inl rfl)
  · rw [padicValNat_dvd_iff_le_of_ne_one hp ha, or_iff_right ha]

theorem padicValNat_dvd_iff (n : ℕ) [hp : Fact p.Prime] (a : ℕ) :
    p ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValNat p a :=
  padicValNat_dvd_iff_of_ne_one hp.out.ne_one n a

theorem pow_succ_padicValNat_not_dvd {n : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0) :
    ¬p ^ (padicValNat p n + 1) ∣ n := by
  rw [padicValNat_dvd_iff_le hn, not_le]
  exact Nat.lt_succ_self _

theorem padicValNat_primes {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (ne : p ≠ q) :
    padicValNat p q = 0 :=
  @padicValNat.eq_zero_of_not_dvd p q <|
    (not_congr (Iff.symm (prime_dvd_prime_iff_eq hp.1 hq.1))).mp ne

theorem padicValNat_prime_prime_pow {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n : ℕ) (ne : p ≠ q) : padicValNat p (q ^ n) = 0 := by
  rw [padicValNat.pow _ <| Nat.Prime.ne_zero hq.elim, padicValNat_primes ne, mul_zero]

theorem padicValNat_mul_pow_left {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n m : ℕ) (ne : p ≠ q) : padicValNat p (p ^ n * q ^ m) = n := by
  rw [padicValNat.mul (NeZero.ne' (p ^ n)).symm (NeZero.ne' (q ^ m)).symm,
    padicValNat.prime_pow, padicValNat_prime_prime_pow m ne, add_zero]

theorem padicValNat_mul_pow_right {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n m : ℕ) (ne : q ≠ p) : padicValNat q (p ^ n * q ^ m) = m := by
  rw [mul_comm (p ^ n) (q ^ m)]
  exact padicValNat_mul_pow_left m n ne

/-- The p-adic valuation of `n` is less than or equal to its logarithm w.r.t. `p`. -/
lemma padicValNat_le_nat_log (n : ℕ) : padicValNat p n ≤ Nat.log p n := by
  rcases n with _ | n
  · simp
  rcases p with _ | _ | p
  · simp
  · simp
  exact Nat.le_log_of_pow_le p.one_lt_succ_succ (le_of_dvd n.succ_pos pow_padicValNat_dvd)

lemma padicValNat_add_le_self {a : ℕ} [hp : Fact p.Prime] (ha : p < a) :
    padicValNat p a + p ≤ a := by
  by_cases dvd : p ∣ a
  · rcases dvd with ⟨k, hk⟩
    have : padicValNat p k < k := by calc
      _ ≤ log p k := padicValNat_le_nat_log k
      _ < _ := log_lt_self p (by lia)
    rw [hk, padicValNat.mul (by lia) (by lia), padicValNat_self]
    calc
      _ ≤ p + k := by lia
      _ ≤ _ := Nat.add_le_mul hp.out.two_le (by lia)
  · rw [padicValNat.eq_zero_of_not_dvd dvd]
    lia

/-- The p-adic valuation of `n` is equal to the logarithm w.r.t. `p` iff
`n` is less than `p` raised to one plus the p-adic valuation of `n`. -/
lemma nat_log_eq_padicValNat_iff {n : ℕ} [hp : Fact (Nat.Prime p)] (hn : n ≠ 0) :
    Nat.log p n = padicValNat p n ↔ n < p ^ (padicValNat p n + 1) := by
  rw [Nat.log_eq_iff (Or.inr ⟨(Nat.Prime.one_lt' p).out, by lia⟩), and_iff_right_iff_imp]
  exact fun _ => Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hn) pow_padicValNat_dvd

/-- This is false for prime numbers other than 2:
for `p = 3`, `n = 1`, one has `log 3 1 = padicValNat 3 2 = 0`. -/
lemma Nat.log_ne_padicValNat_succ {n : ℕ} (hn : n ≠ 0) : log 2 n ≠ padicValNat 2 (n + 1) := by
  rw [Ne, log_eq_iff (by simp [hn])]
  rintro ⟨h1, h2⟩
  rw [← Nat.lt_add_one_iff, ← mul_one (2 ^ _)] at h1
  rw [← add_one_le_iff, Nat.pow_succ] at h2
  refine not_dvd_of_lt_of_lt_mul_succ h1 (lt_of_le_of_ne' h2 ?_) pow_padicValNat_dvd
  -- TODO(kmill): Why is this `p := 2` necessary?
  exact pow_succ_padicValNat_not_dvd (p := 2) n.succ_ne_zero ∘ dvd_of_eq

lemma Nat.max_log_padicValNat_succ_eq_log_succ (n : ℕ) [hp : Fact p.Prime] :
    max (log p n) (padicValNat p (n + 1)) = log p (n + 1) := by
  apply le_antisymm (max_le (le_log_of_pow_le hp.out.one_lt (pow_log_le_add_one p n))
    (padicValNat_le_nat_log (n + 1)))
  rw [le_max_iff, or_iff_not_imp_left, not_le]
  intro h
  replace h := le_antisymm (add_one_le_iff.mpr (lt_pow_of_log_lt hp.out.one_lt h))
    (pow_log_le_self p n.succ_ne_zero)
  rw [h, padicValNat.prime_pow, ← h]

theorem range_pow_padicValNat_subset_divisors {n : ℕ} (hn : n ≠ 0) :
    (Finset.range (padicValNat p n + 1)).image (p ^ ·) ⊆ n.divisors := by
  intro t ht
  simp only [Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Nat.mem_divisors]
  exact ⟨(pow_dvd_pow p <| by lia).trans pow_padicValNat_dvd, hn⟩

theorem range_pow_padicValNat_subset_divisors' {n : ℕ} [hp : Fact p.Prime] :
    ((Finset.range (padicValNat p n)).image fun t => p ^ (t + 1)) ⊆ n.divisors.erase 1 := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  intro t ht
  simp only [Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Finset.mem_erase, Nat.mem_divisors]
  refine ⟨?_, (pow_dvd_pow p <| succ_le_iff.2 hk).trans pow_padicValNat_dvd, hn⟩
  exact (Nat.one_lt_pow k.succ_ne_zero hp.out.one_lt).ne'

set_option backward.isDefEq.respectTransparency false in
/-- The `p`-adic valuation of `(p * n)!` is `n` more than that of `n!`. -/
theorem padicValNat_factorial_mul (n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (p * n)! = padicValNat p n ! + n := by
  apply Nat.cast_injective (R := ℕ∞)
  rw [padicValNat_eq_emultiplicity <| factorial_ne_zero (p * n), Nat.cast_add,
      padicValNat_eq_emultiplicity <| factorial_ne_zero n]
  exact Prime.emultiplicity_factorial_mul hp.out

/-- The `p`-adic valuation of `m` equals zero if it is between `p * k` and `p * (k + 1)` for
some `k`. -/
theorem padicValNat_eq_zero_of_mem_Ioo {m k : ℕ}
    (hm : m ∈ Set.Ioo (p * k) (p * (k + 1))) : padicValNat p m = 0 :=
  padicValNat.eq_zero_of_not_dvd <| not_dvd_of_lt_of_lt_mul_succ hm.1 hm.2

theorem padicValNat_factorial_mul_add {n : ℕ} (m : ℕ) [hp : Fact p.Prime] (h : n < p) :
    padicValNat p (p * m + n)! = padicValNat p (p * m)! := by
  induction n with
  | zero => rw [add_zero]
  | succ n hn =>
    rw [add_succ, factorial_succ,
      padicValNat.mul (succ_ne_zero (p * m + n)) <| factorial_ne_zero (p * m + _),
      hn <| lt_of_succ_lt h, ← add_succ,
      padicValNat_eq_zero_of_mem_Ioo ⟨(Nat.lt_add_of_pos_right <| succ_pos n),
        (Nat.mul_add _ _ _▸ Nat.mul_one _ ▸ ((add_lt_add_iff_left (p * m)).mpr h))⟩,
      zero_add]

/-- The `p`-adic valuation of `n!` is equal to the `p`-adic valuation of the factorial of the
largest multiple of `p` below `n`, i.e. `(p * ⌊n / p⌋)!`. -/
@[simp] theorem padicValNat_mul_div_factorial (n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (p * (n / p))! = padicValNat p n ! := by
  nth_rw 2 [← div_add_mod n p]
  exact (padicValNat_factorial_mul_add (n / p) <| mod_lt n hp.out.pos).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Legendre's Theorem**

The `p`-adic valuation of `n!` is the sum of the quotients `n / p ^ i`. This sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`. -/
theorem padicValNat_factorial {n b : ℕ} [hp : Fact p.Prime] (hnb : log p n < b) :
    padicValNat p (n !) = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := by
  exact_mod_cast ((padicValNat_eq_emultiplicity (p := p) <| factorial_ne_zero _) ▸
      Prime.emultiplicity_factorial hp.out hnb)

/-- **Legendre's Theorem**

Taking (`p - 1`) times the `p`-adic valuation of `n!` equals `n` minus the sum of base `p` digits
of `n`. -/
theorem sub_one_mul_padicValNat_factorial [hp : Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (n !) = n - (p.digits n).sum := by
  rw [padicValNat_factorial <| lt_succ_of_lt <| lt_add_one (log p n)]
  nth_rw 2 [← zero_add 1]
  rw [Nat.succ_eq_add_one, ← Finset.sum_Ico_add' _ 0 _ 1,
    Ico_zero_eq_range, ← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits, Nat.succ_eq_add_one]

variable (p)

theorem sub_one_mul_padicValNat_factorial_lt_of_ne_zero [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    (p - 1) * padicValNat p n.factorial < n := by
  rw [sub_one_mul_padicValNat_factorial n]
  refine Nat.sub_lt_self ?_ (digit_sum_le p n)
  have hnil : p.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  exact List.sum_pos_iff_exists_pos_nat.mpr
    ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hn)⟩

theorem padicValNat_factorial_lt_of_ne_zero [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n.factorial < n := by
  apply lt_of_le_of_lt _ (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn)
  conv_lhs => rw [← one_mul (padicValNat p n !)]
  gcongr
  exact le_sub_one_of_lt (Nat.Prime.one_lt hp.elim)

theorem padicValNat_factorial_le [hp : Fact p.Prime] (n : ℕ) : padicValNat p n.factorial ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact le_of_lt (padicValNat_factorial_lt_of_ne_zero p hn)

variable {p}

set_option backward.isDefEq.respectTransparency false in
/-- **Kummer's Theorem**

The `p`-adic valuation of `n.choose k` is the number of carries when `k` and `n - k` are added
in base `p`. This sum is expressed over the finset `Ico 1 b` where `b` is any bound greater than
`log p n`. -/
theorem padicValNat_choose {n k b : ℕ} [hp : Fact p.Prime] (hkn : k ≤ n) (hnb : log p n < b) :
    padicValNat p (choose n k) = #{i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} := by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| (choose_ne_zero hkn)) ▸
    Prime.emultiplicity_choose hp.out hkn hnb

set_option backward.isDefEq.respectTransparency false in
/-- **Kummer's Theorem**

The `p`-adic valuation of `(n + k).choose k` is the number of carries when `k` and `n` are added
in base `p`. This sum is expressed over the finset `Ico 1 b` where `b` is any bound greater than
`log p (n + k)`. -/
theorem padicValNat_choose' {n k b : ℕ} [hp : Fact p.Prime] (hnb : log p (n + k) < b) :
    padicValNat p (choose (n + k) k) = #{i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} := by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| choose_ne_zero <|
    Nat.le_add_left k n) ▸ Prime.emultiplicity_choose' hp.out hnb

/-- **Kummer's Theorem**
Taking (`p - 1`) times the `p`-adic valuation of the binomial `n + k` over `k` equals the sum of the
digits of `k` plus the sum of the digits of `n` minus the sum of digits of `n + k`, all base `p`.
-/
theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits' {k n : ℕ} [hp : Fact p.Prime] :
    (p - 1) * padicValNat p (choose (n + k) k) =
    (p.digits k).sum + (p.digits n).sum - (p.digits (n + k)).sum := by
  have h : k ≤ n + k := by exact Nat.le_add_left k n
  simp only [Nat.choose_eq_factorial_div_factorial h]
  rw [padicValNat.div_of_dvd <| factorial_mul_factorial_dvd_factorial h, Nat.mul_sub_left_distrib,
      padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _), Nat.mul_add]
  simp only [sub_one_mul_padicValNat_factorial]
  rw [← Nat.sub_add_comm <| digit_sum_le p k, Nat.add_sub_cancel n k, ← Nat.add_sub_assoc <|
      digit_sum_le p n, Nat.sub_sub (k + n), ← Nat.sub_right_comm, Nat.sub_sub, sub_add_eq,
      add_comm, tsub_tsub_assoc (Nat.le_refl (k + n)) <| (add_comm k n) ▸ (Nat.add_le_add
      (digit_sum_le p n) (digit_sum_le p k)), Nat.sub_self (k + n), zero_add, add_comm]

/-- **Kummer's Theorem**
Taking (`p - 1`) times the `p`-adic valuation of the binomial `n` over `k` equals the sum of the
digits of `k` plus the sum of the digits of `n - k` minus the sum of digits of `n`, all base `p`.
-/
theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits {k n : ℕ} [hp : Fact p.Prime]
    (h : k ≤ n) : (p - 1) * padicValNat p (choose n k) =
    (p.digits k).sum + (p.digits (n - k)).sum - (p.digits n).sum := by
  convert @sub_one_mul_padicValNat_choose_eq_sub_sum_digits' _ _ _ ‹_›
  all_goals lia

end padicValNat

section padicValInt

variable {p : ℕ}

theorem padicValInt_dvd_iff_of_ne_one (hp : p ≠ 1) (n : ℕ) (a : ℤ) :
    (p : ℤ) ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValInt p a := by
  rw [padicValInt, ← Int.natAbs_eq_zero, ← padicValNat_dvd_iff_of_ne_one hp, ← Int.natCast_dvd,
    Int.natCast_pow]

theorem padicValInt_dvd_iff [hp : Fact p.Prime] (n : ℕ) (a : ℤ) :
    (p : ℤ) ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValInt p a :=
  padicValInt_dvd_iff_of_ne_one hp.out.ne_one n a

theorem padicValInt_dvd (a : ℤ) : (p : ℤ) ^ padicValInt p a ∣ a := by
  by_cases hp : p = 1
  · rw [hp, Nat.cast_one, one_pow]; exact one_dvd _
  rw [padicValInt_dvd_iff_of_ne_one hp]
  exact Or.inr le_rfl

theorem padicValInt_self [hp : Fact p.Prime] : padicValInt p p = 1 :=
  padicValInt.self hp.out.one_lt

theorem padicValInt.mul [hp : Fact p.Prime] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValInt p (a * b) = padicValInt p a + padicValInt p b := by
  simp_rw [padicValInt]
  rw [Int.natAbs_mul, padicValNat.mul] <;> rwa [Int.natAbs_ne_zero]

theorem padicValInt_mul_eq_succ [hp : Fact p.Prime] (a : ℤ) (ha : a ≠ 0) :
    padicValInt p (a * p) = padicValInt p a + 1 := by
  rw [padicValInt.mul ha (Int.natCast_ne_zero.mpr hp.out.ne_zero)]
  simp only [padicValInt.of_nat, padicValNat_self]

end padicValInt
