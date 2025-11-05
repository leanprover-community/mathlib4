/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Characteristic and cardinality

We prove some results relating characteristic and cardinality of finite rings

## Tags
characteristic, cardinality, ring
-/


/-- A prime `p` is a unit in a commutative ring `R` of nonzero characteristic iff it does not divide
the characteristic. -/
theorem isUnit_iff_not_dvd_char_of_ringChar_ne_zero (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : ringChar R ≠ 0) : IsUnit (p : R) ↔ ¬p ∣ ringChar R := by
  have hch := CharP.cast_eq_zero R (ringChar R)
  have hp : p.Prime := Fact.out
  constructor
  · rintro h₁ ⟨q, hq⟩
    rcases IsUnit.exists_left_inv h₁ with ⟨a, ha⟩
    have h₃ : ¬ringChar R ∣ q := by
      rintro ⟨r, hr⟩
      rw [hr, ← mul_assoc, mul_comm p, mul_assoc] at hq
      nth_rw 1 [← mul_one (ringChar R)] at hq
      exact Nat.Prime.not_dvd_one hp ⟨r, mul_left_cancel₀ hR hq⟩
    have h₄ := mt (CharP.intCast_eq_zero_iff R (ringChar R) q).mp
    apply_fun ((↑) : ℕ → R) at hq
    apply_fun (· * ·) a at hq
    rw [Nat.cast_mul, hch, mul_zero, ← mul_assoc, ha, one_mul] at hq
    norm_cast at h₄
    exact h₄ h₃ hq.symm
  · intro h
    rcases (hp.coprime_iff_not_dvd.mpr h).isCoprime with ⟨a, b, hab⟩
    apply_fun ((↑) : ℤ → R) at hab
    push_cast at hab
    rw [hch, mul_zero, add_zero, mul_comm] at hab
    exact isUnit_of_mul_eq_one (p : R) a hab

/-- A prime `p` is a unit in a finite commutative ring `R`
iff it does not divide the characteristic. -/
theorem isUnit_iff_not_dvd_char (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [Finite R] :
    IsUnit (p : R) ↔ ¬p ∣ ringChar R :=
  isUnit_iff_not_dvd_char_of_ringChar_ne_zero R p <| CharP.char_ne_zero_of_finite R (ringChar R)

/-- The prime divisors of the characteristic of a finite commutative ring are exactly
the prime divisors of its cardinality. -/
theorem prime_dvd_char_iff_dvd_card {R : Type*} [CommRing R] [Fintype R] (p : ℕ) [Fact p.Prime] :
    p ∣ ringChar R ↔ p ∣ Fintype.card R := by
  refine
    ⟨fun h =>
      h.trans <|
        Int.natCast_dvd_natCast.mp <|
          (CharP.intCast_eq_zero_iff R (ringChar R) (Fintype.card R)).mp <|
            mod_cast Nat.cast_card_eq_zero R,
      fun h => ?_⟩
  by_contra h₀
  rcases exists_prime_addOrderOf_dvd_card p h with ⟨r, hr⟩
  have hr₁ := addOrderOf_nsmul_eq_zero r
  rw [hr, nsmul_eq_mul] at hr₁
  rcases IsUnit.exists_left_inv ((isUnit_iff_not_dvd_char R p).mpr h₀) with ⟨u, hu⟩
  apply_fun (· * ·) u at hr₁
  rw [mul_zero, ← mul_assoc, hu, one_mul] at hr₁
  exact mt AddMonoid.addOrderOf_eq_one_iff.mpr (ne_of_eq_of_ne hr (Nat.Prime.ne_one Fact.out)) hr₁

/-- A prime that divides the cardinality of a finite commutative ring `R`
isn't a unit in `R`. -/
theorem not_isUnit_prime_of_dvd_card {R : Type*} [CommRing R] [Fintype R] {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Fintype.card R) : ¬IsUnit (p : R) :=
  mt (isUnit_iff_not_dvd_char R p).mp
    (Classical.not_not.mpr ((prime_dvd_char_iff_dvd_card p).mpr hp))

lemma charP_of_card_eq_prime {R : Type*} [NonAssocRing R] [Fintype R] {p : ℕ} [hp : Fact p.Prime]
    (hR : Fintype.card R = p) : CharP R p :=
  have := Fintype.one_lt_card_iff_nontrivial.1 (hR ▸ hp.1.one_lt)
  (CharP.charP_iff_prime_eq_zero hp.1).2 (hR ▸ Nat.cast_card_eq_zero R)

lemma charP_of_card_eq_prime_pow {R : Type*} [CommRing R] [IsDomain R] [Fintype R] {p f : ℕ}
    [hp : Fact p.Prime] (hR : Fintype.card R = p ^ f) : CharP R p :=
  have hf : f ≠ 0 := fun h0 ↦ not_subsingleton R <|
    Fintype.card_le_one_iff_subsingleton.mp <| by simpa [h0] using hR.le
  (CharP.charP_iff_prime_eq_zero hp.out).mpr
    (by simpa [hf, hR] using Nat.cast_card_eq_zero R)
