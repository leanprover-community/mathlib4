/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.ZMod.Units
import Mathlib.Data.ZMod.Zero
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.RingTheory.Prime
import Mathlib.Algebra.Order.Star.Basic

/-! # Cyclicity of the units of `ZMod n`

`ZMod.isCyclic_units_iff` : `(ZMod n)ˣ` is cyclic iff
one of the following mutually exclusive cases happens:
  - `n = 0` (then `ZMod 0 ≃+* ℤ` and the group of units is cyclic of order 2);
  - `n = `1`,  `2`  or `4`
  - `n` is a power `p ^ e` of an odd prime number, or twice such a power
  (with `1 ≤ e`).

The individual cases are proved by `inferInstance` and are
also directly provided by :

* `ZMod.isCyclic_units_zero`
* `ZMod.isCyclic_units_one`
* `ZMod.isCyclic_units_two`
* `ZMod.isCyclic_units_four`

The case of prime numbers is also an instance:

* `ZMod.isCyclic_units_prime`

* `ZMod.not_isCyclic_units_eight`: `(ZMod 8)ˣ` is not cyclic

* `ZMod.orderOf_one_add_mul_prime`: the order of `1 + a * p`
modulo `p ^ (n + 1)` is `p ^ n` when `p` does not divide `a`.

* `ZMod.orderOf_five` : the order of `5` modulo `2 ^ (n + 3)` is `2 ^ (n + 1)`.

* `ZMod.isCyclic_units_of_prime_pow` : the case of odd prime powers

* `ZMod.isCyclic_units_two_pow_iff` : `(ZMod (2 ^ n))ˣ` is cyclic iff `n ≤ 2`.

The proofs follow [Ireland and Rosen,
  *A classical introduction to modern number theory*, chapter 4]
  [IrelandRosen1990]
but build on a general induction divisibility lemma suggested by Junyan Xu.

-/

open scoped Nat

namespace ZMod

section EasyCases

theorem isCyclic_units_zero :
    IsCyclic (ZMod 0)ˣ := inferInstance

theorem isCyclic_units_one :
    IsCyclic (ZMod 1)ˣ := inferInstance

theorem isCyclic_units_two :
    IsCyclic (ZMod 2)ˣ := inferInstance

theorem isCyclic_units_four :
    IsCyclic (ZMod 4)ˣ := by
  apply isCyclic_of_prime_card (p := 2)
  simp only [Nat.card_eq_fintype_card, card_units_eq_totient]
  rfl

/- The multiplicative group of `ZMod p` is cyclic. -/
theorem isCyclic_units_prime {p : ℕ} (hp : p.Prime) :
    IsCyclic (ZMod p)ˣ :=
  have : Fact (p.Prime) := ⟨hp⟩
  inferInstance

theorem not_isCyclic_units_eight :
    ¬ IsCyclic (ZMod 8)ˣ := by
  rw [IsCyclic.iff_exponent_eq_card, Nat.card_eq_fintype_card, card_units_eq_totient]
  have h : Monoid.exponent (ZMod 8)ˣ ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one (by decide)
  intro (h' : Monoid.exponent (ZMod 8)ˣ = 4)
  simp [h'] at h

end EasyCases

section Divisibility

variable {R : Type*} [CommSemiring R] {u v : R}
  {p : ℕ}

/- This lemma is due to Junyan Xu -/

lemma exists_of_one_add_mul_pow_prime_eq
    (hp : p.Prime) (hvu : v ∣ u) (hpuv : p * u * v ∣ u ^ p) (x : R) :
    ∃ y, (1 + u * x) ^ p = 1 + p * u * (x + v * y) := by
  rw [add_comm, add_pow]
  simp [← Finset.add_sum_erase (a := 0) (Finset.range (p + 1)) _ (by simp)]
  rw [← Finset.add_sum_erase (a := 1) _ _ (by simp [hp.pos])]
  rw [← Finset.sum_erase_add (a := p) _ _ (by
      simp only [Finset.mem_erase]
      rw [← and_assoc, and_comm (a := ¬ _), ← Nat.two_le_iff]
      simp [hp.two_le])]
  obtain ⟨a, ha⟩ := hvu
  obtain ⟨b, hb⟩ := hpuv
  use a * x ^ 2 * ∑ i ∈ (((Finset.range (p + 1)).erase 0).erase 1).erase p,
    (u * x) ^ (i - 2) * (p.choose i / p : ℕ) + b * x ^ p
  rw [mul_add]
  apply congr_arg₂ _ rfl
  apply congr_arg₂ _ (by simp [Nat.choose_one_right]; ring)
  simp only [mul_add, Finset.mul_sum]
  apply congr_arg₂ _
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_erase, ne_eq, Finset.mem_range] at hi
    have hi' : 2 ≤ i := by simp [Nat.two_le_iff, hi]
    calc
      (u * x) ^ i * p.choose i =
        (u * x) ^ (2 + (i - 2)) * p.choose i := by rw [Nat.add_sub_of_le hi']
      _ = u ^ 2 * x ^ 2 * (u * x) ^ (i - 2) * p.choose i := by ring_nf
      _ = u ^ 2 * x ^ 2 * (u * x) ^ (i - 2) * (p * (p.choose i / p) : ℕ) := by
        congr; symm
        apply Nat.mul_div_cancel'
        apply Nat.Prime.dvd_choose_self hp hi.2.2.1
        refine Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi.2.2.2) hi.1
      _ = u ^ 2 * x ^ 2 * (u * x) ^ (i - 2) * p * (p.choose i / p : ℕ) := by
        simp only [Nat.cast_mul]; ring_nf
      _ = p * u * (v * (a * x ^ 2 * ((u * x) ^ (i - 2) * (p.choose i / p : ℕ)))) := by
          rw [ha]; ring
  · calc
     (u * x) ^ p * ↑(p.choose p) = u ^ p * x ^ p := by rw [Nat.choose_self, mul_pow]; simp
    _ = p * u * v * b * x ^ p := by rw [hb]
    _ = p * u * (v * (b * x ^ p)) := by ring_nf

lemma exists_of_one_add_mul_pow_prime_pow_eq {u v : R}
    (hp : p.Prime) (hvu : v ∣ u) (hpuv : p * u * v ∣ u ^ p) (x : R) (m : ℕ) :
    ∃ y, (1 + u * x) ^ (p ^ m) = 1 + p ^ m * u * (x + v * y) :=
  match m with
  | 0 => ⟨0, by simp⟩
  | m + 1 => by
    rw [pow_succ', pow_mul]
    obtain ⟨y, hy⟩ := exists_of_one_add_mul_pow_prime_eq hp hvu hpuv x
    rw [hy]
    obtain ⟨z, hz⟩ :=
      exists_of_one_add_mul_pow_prime_pow_eq (u := p * u) (v := p * v) hp
      (mul_dvd_mul_left _ hvu)
      (by
        rw [mul_pow]
        simp only [← mul_assoc, mul_comm _ ↑p]
        rw [mul_assoc, mul_assoc, ← mul_assoc u,
          mul_comm u]
        apply mul_dvd_mul _ hpuv
        rw [← pow_two]
        exact pow_dvd_pow _ hp.two_le)
      ((x + v * y)) m
    use y + p * z
    rw [hz]
    ring

end Divisibility

section PrimePow

theorem orderOf_one_add_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (n : ℕ) :
    orderOf (1 + a * p : ZMod (p ^ (n + 1))) = p ^ n := by
  match n with
  | 0 => simp [(ZMod.natCast_zmod_eq_zero_iff_dvd p (p ^ 1)).mpr ?_, mul_zero]
  | n + 1 =>
    have _ : Fact (p.Prime) := ⟨hp⟩
    have := exists_of_one_add_mul_pow_prime_pow_eq
      (R := ZMod (p ^ (n + 1 + 1))) (u := p) (v := p) hp (by simp) ?_ a
    · apply orderOf_eq_prime_pow
      · obtain ⟨y, hy⟩ := this n
        rw [mul_comm, hy, ← pow_succ]
        simp only [add_eq_left, ne_eq, mul_add, ← mul_assoc, ← pow_succ]
        simp only [← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]
        rw [← Int.cast_natCast, ← Int.cast_mul]
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd, pow_succ]
        rintro ⟨b, hb⟩
        apply ha
        use b
        apply Or.resolve_right _ hp.ne_zero
        simpa [mul_assoc] using hb
      · obtain ⟨y, hy⟩ := this (n + 1)
        rw [mul_comm, hy, ← pow_succ, ← Nat.cast_pow]
        simp [ZMod.natCast_self]
    · rw [← pow_two,← pow_succ]
      apply pow_dvd_pow
      rw [Nat.add_one_le_iff, Nat.lt_iff_le_and_ne]
      exact ⟨hp.two_le, Ne.symm hp2⟩

theorem orderOf_one_add_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    orderOf (1 + p : ZMod (p ^ (n + 1))) = p ^ n := by
  convert orderOf_one_add_mul_prime hp hp2 1 _ n
  · simp
  · intro H
    apply hp.ne_one
    simpa using Int.eq_one_of_dvd_one (Int.natCast_nonneg p) H

/-- If `p` is an odd prime, then `(ZMod (p ^ n))ˣ` is cyclic for all n -/
theorem isCyclic_units_of_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    IsCyclic (ZMod (p ^ n))ˣ := by
  have _ : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have _ : Fact (p.Prime) := ⟨hp⟩
  rcases n with _ | n
  · rw [pow_zero]; infer_instance
  -- We first consider the element `1 + p` of order `p ^ n`
  set a := (1 + p : ZMod (p ^ (n + 1))) with ha_def
  have ha : IsUnit a := by
    rw [ha_def, ← Nat.cast_one (R := ZMod _), ← Nat.cast_add, ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    simp only [Nat.coprime_add_self_left, Nat.coprime_one_left_eq_true]
  have ha' : orderOf ha.unit = p ^ n := by
    simp only [←
      orderOf_injective _ Units.coeHom_injective ha.unit,
      Units.coeHom_apply, IsUnit.unit_spec]
    simp only [ha_def]
    exact orderOf_one_add_prime hp hp2 n
  -- We lift a primitive root of unity mod `p`, an adequate power of which has order `p - 1`.
  obtain ⟨c, hc⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (isCyclic_units_prime hp)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hc
  obtain ⟨(b : (ZMod (p ^ (n + 1)))ˣ), rfl⟩ :=
    ZMod.unitsMap_surjective (Dvd.intro_left (p ^ n) rfl) c
  have : p - 1 ∣ orderOf b := by
    rw [← hc]
    exact orderOf_map_dvd _ b
  let k := orderOf b / (p - 1)
  have : orderOf (b ^ k) = p - 1 := orderOf_pow_orderOf_div (orderOf_pos b).ne' this
  rw [isCyclic_iff_exists_orderOf_eq_natCard]
  -- The product of `ha.unit` and `b ^ k` has the required order
  use ha.unit * b ^ k
  rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (Commute.all _ _),
    this, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ hp, ← ha']
  rw [ha', this]
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_self_sub_right hp.pos]
  simp

theorem isCyclic_units_two_pow_iff (n : ℕ) :
    IsCyclic (ZMod (2 ^ n))ˣ ↔ n ≤ 2 := by
  match n with
  | 0 => simp [isCyclic_units_one]
  | 1 => simp [isCyclic_units_prime Nat.prime_two]
  | 2 => simp [isCyclic_units_four]
  | n + 3 =>
    simp only [Nat.reduceLeDiff, iff_false]
    intro H
    apply not_isCyclic_units_eight
    have h : 2 ^ 3 ∣ 2 ^ (n + 3) := by
      rw [pow_add]
      exact Nat.dvd_mul_left (2 ^ 3) (2 ^ n)
    exact isCyclic_of_surjective _ (unitsMap_surjective h)

lemma orderOf_one_add_four_mul (a : ℤ) (ha : Odd a) (n : ℕ) :
    orderOf (1 + 4 * a : ZMod (2 ^ (n + 2))) = 2 ^ n := by
  match n with
  | 0 =>
    rw [pow_zero, orderOf_eq_one_iff]
    rw [show (4 : ZMod 4) = (4 : ℕ) by rfl, ZMod.natCast_self]
    simp
  | n + 1 =>
    have h24 : (2 : ZMod (2 ^ (n + 2 + 1))) ^ 2 = 4 := by norm_num
    have huv : (2 : ZMod (2 ^ (n + 2 + 1))) ∣ 4 := ⟨2, by norm_num⟩
    have huv' : (2 : ZMod (2 ^ (n + 2 + 1))) * 4 * 2 ∣ 4 ^ 2 := by norm_num
    have := exists_of_one_add_mul_pow_prime_pow_eq Nat.prime_two huv huv' a
    apply orderOf_eq_prime_pow
    · obtain ⟨y, hy⟩ := this n
      rw [hy, add_eq_left]
      simp only [Nat.cast_ofNat]
      rw [← h24, ← pow_add, ← Nat.cast_two (R := ZMod _), ← Nat.cast_pow, mul_add, ← mul_assoc]
      rw [Nat.cast_pow, ← pow_succ, ← Nat.cast_pow,
        ← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]
      rw [← Int.cast_natCast, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
      rintro ⟨b, hb⟩
      apply Int.not_even_iff_odd.mpr ha
      use b
      simpa [← two_mul, pow_succ _ (n + 2), mul_assoc] using hb
    · obtain ⟨y, hy⟩ := this (n + 1)
      simp only [hy, Nat.cast_ofNat, add_eq_left]
      rw [← h24, ← pow_add, ← Nat.cast_two (R := ZMod _),
        ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

theorem orderOf_five (n : ℕ) :
    orderOf (5 : ZMod (2 ^ (n + 2))) = 2 ^ n := by
  convert orderOf_one_add_four_mul 1 (by norm_num) n
  norm_num

end PrimePow

section Products

theorem isCyclic_units_four_mul_iff (n : ℕ) :
    IsCyclic ((ZMod (4 * n))ˣ) ↔ n = 0 ∨ n = 1 := by
  rcases Nat.eq_zero_or_pos n with ⟨rfl⟩ | hn0
  · simp [isCyclic_units_zero]
  rcases Nat.eq_or_lt_of_le hn0 with ⟨rfl⟩ | hn1
  · simp [isCyclic_units_four]
  have hn2' : 2 ≤ n := by
    simp only [Nat.succ_eq_add_one, zero_add] at hn1
    exact Nat.succ_le_of_lt hn1
  simp only [Nat.ne_zero_of_lt hn0, Ne.symm (Nat.ne_of_lt hn1), or_self, iff_false]
  intro H
  set m := n.factorization 2
  set q := n / (2 ^ n.factorization 2) with hq
  have hn : n = 2 ^ m * q := (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  rw [hn, show 4 = 2 ^ 2 by rfl, ← mul_assoc, ← pow_add] at H
  have hq0 : q ≠ 0 := fun hq ↦ by simp [hn, hq, mul_zero] at hn1
  have _ : NeZero q := ⟨hq0⟩
  have hq2 : (2 ^ (2 + m)).Coprime q := by
    rw [Nat.coprime_pow_left_iff (Nat.pos_of_neZero _), Nat.prime_two.coprime_iff_not_dvd, hq]
    apply Nat.not_dvd_ordCompl Nat.prime_two (Nat.ne_zero_of_lt hn0)
  let f := (Units.mapEquiv (chineseRemainder hq2).toMulEquiv).trans  MulEquiv.prodUnits
  rw [f.isCyclic, Group.isCyclic_prod_iff, isCyclic_units_two_pow_iff] at H
  simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, Nat.card_eq_fintype_card,
    card_units_eq_totient] at H
  let H' := H.2.2
  simp [H.1, show φ 4 = 2 by rfl, Nat.odd_totient_iff] at H'
  rcases H' with (hq_eq1 | hq_eq2)
  · suffices n = 1 by
      simp [this] at hn2'
    simp [hn, hq_eq1, H]
  · rw [hq_eq2, Nat.coprime_two_right, ← Nat.not_even_iff_odd, Nat.even_pow] at hq2
    apply hq2
    simp

theorem isCyclic_units_of_two_mul_odd_iff (n : ℕ) (hn : Odd n) :
    IsCyclic (ZMod (2 * n))ˣ ↔ IsCyclic (ZMod n)ˣ := by
  rw [← Nat.coprime_two_left] at hn
  let e := (Units.mapEquiv (chineseRemainder hn).toMulEquiv).trans MulEquiv.prodUnits
  rw [e.isCyclic, Group.isCyclic_prod_iff]
  simp [isCyclic_units_two]

theorem not_isCyclic_units_of_mul_coprime (m n : ℕ)
    (hm : Odd m) (hm1 : m ≠ 1) (hn : Odd n) (hn1 : n ≠ 1) (hmn : m.Coprime n) :
    ¬ (IsCyclic (ZMod (m * n))ˣ) := by
  classical
  have _ : NeZero m := ⟨by exact Nat.ne_of_odd_add hm⟩
  have _ : NeZero n := ⟨by exact Nat.ne_of_odd_add hn⟩
  let e := (Units.mapEquiv (chineseRemainder hmn).toMulEquiv).trans MulEquiv.prodUnits
  rw [e.isCyclic, Group.isCyclic_prod_iff]
  rintro ⟨_, _, h⟩
  simp [Nat.card_eq_fintype_card, card_units_eq_totient,
    Nat.totient_coprime_totient_iff, hm1, hn1] at h
  rcases h with (h | h)
  · simp [← Nat.not_even_iff_odd, h] at hm
  · simp [← Nat.not_even_iff_odd, h] at hn

theorem isCyclic_units_of_odd_iff {n : ℕ} (hn : Odd n) :
    IsCyclic (ZMod n)ˣ ↔ ∃ (p m : ℕ), p.Prime ∧ Odd p ∧ n = p ^ m := by
  by_cases h1 : n = 1
  · rw [h1]
    simp [isCyclic_units_one]
    refine ⟨3, Nat.prime_three, by simp [Nat.odd_iff], 0, by rw [pow_zero]⟩
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime h1
  have hoddp : p ≠ 2 := fun h2 ↦ by
    apply Odd.not_two_dvd_nat hn
    rw [← h2]
    exact Nat.minFac_dvd n
  set m1 := p ^ (n.factorization p) with hm1
  have hnp : n.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization,
      Nat.mem_primeFactors]
    exact ⟨hp, n.minFac_dvd, Nat.ne_of_odd_add hn⟩
  set m2 := n / m1
  have hm : n = m1 * m2 := by
    simp only [m1, Nat.ordCompl_of_not_prime]
    exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  rw [hm]
  have hm' : m1.Coprime m2 := by
    rw [hm1]
    rw [Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hnp),
      hp.coprime_iff_not_dvd]
    intro hp2
    obtain ⟨m2', hm2'⟩ := hp2
    apply Nat.not_succ_le_self (n.factorization p)
    conv_rhs => rw [hm, hm2', hm1, ← mul_assoc, ← pow_succ]
    rw [Nat.factorization_mul]
    · simp [hp.factorization_self]
    · simp [hp.ne_zero]
    · intro H
      apply Nat.not_odd_zero
      simp only [hm2', H, mul_zero] at hm
      rwa [← hm]
  have hm1_ne_one : m1 ≠ 1 := by
    simp only [hm1, ne_eq, Nat.pow_eq_one, m1, not_or]
    refine ⟨hp.ne_one, ?_⟩
    exact hnp
  by_cases hm2_eq_one : m2 = 1
  · rw [hm2_eq_one, mul_one]
    rw [hm1]
    simp [isCyclic_units_of_prime_pow p hp hoddp (n.factorization p)]
    refine ⟨p, hp, ?_, n.factorization p, rfl⟩
    exact Nat.Prime.odd_of_ne_two hp hoddp
  · simp [hm, Nat.odd_mul] at hn
    have := not_isCyclic_units_of_mul_coprime m1 m2 hn.1 hm1_ne_one hn.2 hm2_eq_one hm'
    simp [this]
    intro l hl hol a ha
    replace ha : m1 * m2 = 1 * l ^ a := by simp [ha]
    obtain ⟨i, j, b, c, ha, hbc, hm1i, hm2j⟩ := mul_eq_mul_prime_pow (Nat.prime_iff.mp hl) ha
    simp only [eq_comm, mul_eq_one] at hbc
    rw [hbc.1, one_mul] at hm1i
    rw [hbc.2, one_mul] at hm2j
    rw [hm1i] at hm1_ne_one
    rw [hm2j] at hm2_eq_one
    simp only [ne_eq, Nat.pow_eq_one, not_or] at hm1_ne_one hm2_eq_one
    simp [hl.ne_one] at hm1_ne_one hm2_eq_one
    simp only [hm1i, hm2j] at hm'
    rw [Nat.coprime_pow_left_iff ?_,
      Nat.coprime_pow_right_iff ?_, Nat.coprime_self] at hm'
    · exact hl.ne_one hm'
    · exact Nat.zero_lt_of_ne_zero hm2_eq_one
    · exact Nat.zero_lt_of_ne_zero hm1_ne_one

end Products

/-- `(ZMod n)ˣ` is cyclic iff `n` is of the form
`0`, `1`, `2`, `4`, `p ^ m`, or `2 * p ^ m`,
where `p` is an odd prime and `1 ≤ m`. -/
theorem isCyclic_units_iff (n : ℕ) :
    IsCyclic (ZMod n)ˣ ↔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4 ∨
      ∃ (p m : ℕ), p.Prime ∧ Odd p ∧ 1 ≤ m ∧ (n = p ^ m ∨ n = 2 * p ^ m) := by
  by_cases h0 : n = 0
  · rw [h0]; simp [isCyclic_units_zero]
  by_cases h1 : n = 1
  · rw [h1]
    simp [isCyclic_units_one]
  by_cases h2 : n = 2
  · rw [h2]; simp [isCyclic_units_two]
  by_cases h4 : n = 4
  · rw [h4]; simp [isCyclic_units_four]
  simp [h0, h1, h2, h4]
  rcases (n.even_or_odd).symm with hn | hn
  · simp only [isCyclic_units_of_odd_iff hn]
    apply exists_congr
    simp only [exists_and_left, and_congr_right_iff]
    intro p hp ho
    apply exists_congr
    intro m
    constructor
    · intro hnpm
      refine ⟨?_, Or.inl hnpm⟩
      simp only [← not_lt, Nat.lt_one_iff]
      rintro ⟨rfl⟩
      rw [pow_zero] at hnpm
      exact h1 hnpm
    · rintro ⟨_, (h | h)⟩
      · exact h
      · exfalso
        apply Nat.not_even_iff_odd.mpr hn
        simp [h]
  · set a := n.factorization 2 with ha
    set m := n / 2 ^ a with hm
    have hm : n = 2 ^ a * m := by
      simp only [m, Nat.ordCompl_of_not_prime]
      exact (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
    by_cases ha0 : a = 0
    · exfalso
      rw [ha0, eq_comm, ← Finsupp.notMem_support_iff,
        Nat.support_factorization] at ha
      simp only [Nat.mem_primeFactors, ne_eq, not_and, Decidable.not_not] at ha
      apply h0
      exact ha Nat.prime_two (even_iff_two_dvd.mp hn)
    by_cases hn4 : 4 ∣ n
    · obtain ⟨q, rfl⟩ := hn4
      rw [isCyclic_units_four_mul_iff]
      simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or, ne_eq, not_false_eq_true,
        mul_eq_left₀] at h0 h4
      simp only [h0, h4, or_self, false_iff, not_exists, not_and, not_or]
      intro l hl hol e he
      have : ¬ Even (l ^ e) := by
        simp only [Nat.not_even_iff_odd, hol.pow]
      refine ⟨fun H ↦ this ?_, fun H ↦ this ?_⟩
      · rwa [← H]
      · suffices 2 * q = l ^ e by
          simp only [← this, even_two_mul]
        apply Nat.mul_left_cancel Nat.two_pos
        simp [← H, ← mul_assoc]
    · have ha1 : a = 1 := by
        apply le_antisymm _ (Nat.one_le_iff_ne_zero.mpr ha0)
        rw [← not_lt]
        intro (ha: 2 ≤ a)
        apply hn4
        rw [hm]
        apply Dvd.dvd.mul_right
        change 2 ^2 ∣ _
        exact Nat.pow_dvd_pow_iff_le_right'.mpr ha
      rw [ha1, pow_one] at hm
      have hoddm : Odd m := by
        rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
        rintro ⟨q, hq⟩
        apply hn4
        rw [hm, hq, ← mul_assoc]
        exact Nat.dvd_mul_right 4 q
      rw [hm, isCyclic_units_of_two_mul_odd_iff _ hoddm, isCyclic_units_of_odd_iff hoddm]
      apply exists_congr
      intro l
      simp only [exists_and_left, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false,
        and_congr_right_iff]
      intro hl hol
      apply exists_congr
      intro e
      constructor
      · intro he
        refine ⟨Nat.pos_of_ne_zero ?_, Or.inr he⟩
        rintro ⟨rfl⟩
        apply h2
        simp [hm, he]
      · rintro ⟨h1e, (he | he)⟩
        · exfalso
          apply Nat.not_odd_iff_even.mpr (even_two_mul m)
          simp only [he, hol.pow]
        · exact he

end ZMod
