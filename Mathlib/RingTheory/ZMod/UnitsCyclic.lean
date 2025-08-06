/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Junyan Xu
-/
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic

/-! # Cyclicity of the units of `ZMod n`

`ZMod.isCyclic_units_iff` : `(ZMod n)ˣ` is cyclic iff
one of the following mutually exclusive cases happens:
  - `n = 0` (then `ZMod 0 ≃+* ℤ` and the group of units is cyclic of order 2);
  - `n = 1`, `2` or `4`
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

The proofs mostly follow [Ireland and Rosen,
  *A classical introduction to modern number theory*, chapter 4]
  [IrelandRosen1990].

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
  decide

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

variable {R : Type*} [CommSemiring R] {u v : R} {p : ℕ}

lemma exists_one_add_mul_pow_prime_eq
    (hp : p.Prime) (hvu : v ∣ u) (hpuv : p * u * v ∣ u ^ p) (x : R) :
    ∃ y, (1 + u * x) ^ p = 1 + p * u * (x + v * y) := by
  rw [add_comm, add_pow]
  rw [← Finset.add_sum_erase (a := 0) _ _ (by simp)]
  simp_rw [one_pow, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [← Finset.add_sum_erase (a := 1) _ _ (by simp [hp.pos])]
  rw [← Finset.sum_erase_add (a := p) _ _ (by -- aesop works but is slow
      simp only [Finset.mem_erase]
      rw [← and_assoc, and_comm (a := ¬ _), ← Nat.two_le_iff]
      simp [hp.two_le])]
  obtain ⟨a, ha⟩ := hvu
  obtain ⟨b, hb⟩ := hpuv
  use a * x ^ 2 * ∑ i ∈ (((Finset.range (p + 1)).erase 0).erase 1).erase p,
    (u * x) ^ (i - 2) * (p.choose i / p : ℕ) + b * x ^ p
  rw [mul_add]
  congr 2
  · rw [Nat.choose_one_right]; ring
  simp only [mul_add, Finset.mul_sum]
  congr 1
  · congr! 1 with i hi
    simp only [Finset.mem_erase, ne_eq, Finset.mem_range] at hi
    have hi' : 2 ≤ i := by omega
    calc
      (u * x) ^ i * p.choose i =
        (u * x) ^ (2 + (i - 2)) * p.choose i := by rw [Nat.add_sub_of_le hi']
      _ = u ^ 2 * x ^ 2 * (u * x) ^ (i - 2) * p.choose i := by ring_nf
      _ = u ^ 2 * x ^ 2 * (u * x) ^ (i - 2) * (p * (p.choose i / p) : ℕ) := by
        rw [Nat.mul_div_cancel' (hp.dvd_choose_self hi.2.2.1 <| by omega)]
      _ = u ^ 2 * x ^ 2 * (u * x) ^ (i - 2) * p * (p.choose i / p : ℕ) := by
        simp only [Nat.cast_mul]; ring_nf
      _ = p * u * (v * (a * x ^ 2 * ((u * x) ^ (i - 2) * (p.choose i / p : ℕ)))) := by
        rw [ha]; ring
  · calc
      (u * x) ^ p * (p.choose p) = u ^ p * x ^ p := by simp [Nat.choose_self, mul_pow]
    _ = p * u * v * b * x ^ p := by rw [hb]
    _ = p * u * (v * (b * x ^ p)) := by ring_nf

lemma exists_one_add_mul_pow_prime_pow_eq {u v : R}
    (hp : p.Prime) (hvu : v ∣ u) (hpuv : p * u * v ∣ u ^ p) (x : R) (m : ℕ) :
    ∃ y, (1 + u * x) ^ (p ^ m) = 1 + p ^ m * u * (x + v * y) :=
  match m with
  | 0 => ⟨0, by simp⟩
  | m + 1 => by
    rw [pow_succ', pow_mul]
    obtain ⟨y, hy⟩ := exists_one_add_mul_pow_prime_eq hp hvu hpuv x
    rw [hy]
    obtain ⟨z, hz⟩ :=
      exists_one_add_mul_pow_prime_pow_eq (u := p * u) (v := p * v) hp
      (mul_dvd_mul_left _ hvu)
      (by
        rw [mul_pow]
        simp only [← mul_assoc]
        rw [mul_assoc, mul_assoc, ← mul_assoc u, mul_comm u]
        apply mul_dvd_mul _ hpuv
        rw [← pow_two]
        exact pow_dvd_pow _ hp.two_le)
      (x + v * y) m
    use y + p * z
    rw [hz]
    ring

end Divisibility

section PrimePow

theorem orderOf_one_add_mul_prime_pow {p : ℕ} (hp : p.Prime) (m : ℕ) (hm0 : m ≠ 0)
    (hpm : m + 2 ≤ p * m) (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) (n : ℕ) :
    orderOf (1 + p ^ m * a : ZMod (p ^ (n + m))) = p ^ n := by
  match n with
  | 0 => rw [← Nat.cast_pow, zero_add m, ZMod.natCast_self]; simp
  | n + 1 =>
    have := Fact.mk hp
    have := exists_one_add_mul_pow_prime_pow_eq
      (R := ZMod (p ^ (n + 1 + m))) (u := p ^ m) (v := p) hp (dvd_pow_self _ hm0) ?_ a
    · apply orderOf_eq_prime_pow
      · obtain ⟨y, hy⟩ := this n
        rw [hy, ← pow_add, add_eq_left, mul_add, ← mul_assoc, ← pow_succ]
        simp_rw [add_right_comm n _ 1, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]
        rwa [← Int.cast_natCast, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd, add_right_comm,
          pow_succ, Nat.cast_mul, Int.mul_dvd_mul_iff_left (by simp [hp.ne_zero])]
      · obtain ⟨y, hy⟩ := this (n + 1)
        rw [hy, ← pow_add, ← Nat.cast_pow]
        simp
    · rw [← pow_succ', ← pow_succ, ← pow_mul, mul_comm]
      exact pow_dvd_pow _ hpm

theorem orderOf_one_add_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (n : ℕ) :
    orderOf (1 + p * a : ZMod (p ^ (n + 1))) = p ^ n := by
  convert orderOf_one_add_mul_prime_pow hp 1 one_ne_zero _ a ha n using 1
  · rw [pow_one]
  · have := hp.two_le; omega

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
  have := Fact.mk hp
  rcases n with _ | n
  · rw [pow_zero]; infer_instance
  -- We first consider the element `1 + p` of order `p ^ n`
  set a := (1 + p : ZMod (p ^ (n + 1))) with ha_def
  have ha : IsUnit a := by
    rw [ha_def, ← Nat.cast_one (R := ZMod _), ← Nat.cast_add, ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    simp only [Nat.coprime_add_self_left, Nat.coprime_one_left_eq_true]
  have ha' : orderOf ha.unit = p ^ n := by
    rw [← orderOf_injective _ Units.coeHom_injective ha.unit, Units.coeHom_apply, IsUnit.unit_spec]
    exact orderOf_one_add_prime hp hp2 n
  -- We lift a primitive root of unity mod `p`, an adequate power of which has order `p - 1`.
  obtain ⟨c, hc⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (isCyclic_units_prime hp)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hc
  obtain ⟨(b : (ZMod (p ^ (n + 1)))ˣ), rfl⟩ :=
    ZMod.unitsMap_surjective (Dvd.intro_left (p ^ n) rfl) c
  have : p - 1 ∣ orderOf b := hc ▸ orderOf_map_dvd _ b
  let k := orderOf b / (p - 1)
  have : orderOf (b ^ k) = p - 1 := orderOf_pow_orderOf_div (orderOf_pos b).ne' this
  rw [isCyclic_iff_exists_orderOf_eq_natCard]
  -- The product of `ha.unit` and `b ^ k` has the required order
  use ha.unit * b ^ k
  rw [(Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime, this, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp, ← ha']
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
    have h : 2 ^ 3 ∣ 2 ^ (n + 3) := pow_dvd_pow _ (by omega)
    exact isCyclic_of_surjective _ (unitsMap_surjective h)

lemma orderOf_one_add_four_mul (a : ℤ) (ha : Odd a) (n : ℕ) :
    orderOf (1 + 4 * a : ZMod (2 ^ (n + 2))) = 2 ^ n := by
  convert orderOf_one_add_mul_prime_pow Nat.prime_two 2 two_ne_zero le_rfl a ?_ n using 1
  · norm_num
  · rwa [← Int.not_even_iff_odd, even_iff_two_dvd] at ha

theorem orderOf_five (n : ℕ) :
    orderOf (5 : ZMod (2 ^ (n + 2))) = 2 ^ n := by
  convert orderOf_one_add_four_mul 1 (by simp) n
  norm_num

end PrimePow

section Products

theorem isCyclic_units_four_mul_iff (n : ℕ) :
    IsCyclic (ZMod (4 * n))ˣ ↔ n = 0 ∨ n = 1 := by
  obtain rfl | hn0 := eq_or_ne n 0
  · simp [isCyclic_units_zero]
  obtain rfl | hn1 := eq_or_ne n 1
  · simp [isCyclic_units_four]
  refine iff_of_false ?_ (by simp [hn0, hn1])
  obtain ⟨n, rfl⟩ | h2n := em (2 ∣ n)
  · rw [← mul_assoc]
    have : NeZero n := ⟨by simpa using hn0⟩
    refine mt (fun _ ↦ ?_) not_isCyclic_units_eight
    exact isCyclic_of_surjective _ (ZMod.unitsMap_surjective (m := 4 * 2 * n) (dvd_mul_right 8 _))
  have : Nat.Coprime 4 n := (Nat.prime_two.coprime_iff_not_dvd.mpr h2n).pow_left 2
  rw [((Units.mapEquiv (chineseRemainder this).toMulEquiv).trans .prodUnits).isCyclic,
    Group.isCyclic_prod_iff]
  rintro ⟨-, -, h⟩
  have : NeZero n := ⟨hn0⟩
  have : Odd (φ n) := by simpa [show φ 4 = 2 from rfl] using h
  rw [Nat.odd_totient_iff] at this
  omega

theorem isCyclic_units_two_mul_iff_of_odd (n : ℕ) (hn : Odd n) :
    IsCyclic (ZMod (2 * n))ˣ ↔ IsCyclic (ZMod n)ˣ := by
  simp [((Units.mapEquiv (chineseRemainder <| Nat.coprime_two_left.mpr hn).toMulEquiv).trans
    .prodUnits).isCyclic, Group.isCyclic_prod_iff, isCyclic_units_two]

theorem not_isCyclic_units_of_mul_coprime (m n : ℕ)
    (hm : Odd m) (hm1 : m ≠ 1) (hn : Odd n) (hn1 : n ≠ 1) (hmn : m.Coprime n) :
    ¬ IsCyclic (ZMod (m * n))ˣ := by
  classical
  have _ : NeZero m := ⟨Nat.ne_of_odd_add hm⟩
  have _ : NeZero n := ⟨Nat.ne_of_odd_add hn⟩
  let e := (Units.mapEquiv (chineseRemainder hmn).toMulEquiv).trans .prodUnits
  rw [e.isCyclic, Group.isCyclic_prod_iff]
  rintro ⟨-, -, h⟩
  simp_rw [Nat.card_eq_fintype_card, card_units_eq_totient,
    Nat.totient_coprime_totient_iff, hm1, hn1, false_or] at h
  rcases h with (rfl | rfl)
  · simp [← Nat.not_even_iff_odd] at hm
  · simp [← Nat.not_even_iff_odd] at hn

theorem isCyclic_units_iff_of_odd {n : ℕ} (hn : Odd n) :
    IsCyclic (ZMod n)ˣ ↔ ∃ (p m : ℕ), p.Prime ∧ Odd p ∧ n = p ^ m := by
  have hn0 : n ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hn
  obtain rfl | h1 := eq_or_ne n 1
  · simp_rw [isCyclic_units_one, true_iff]
    exact ⟨3, 0, Nat.prime_three, by simp [Nat.odd_iff], by rw [pow_zero]⟩
  have ⟨p, hp, dvd⟩ := n.exists_prime_and_dvd h1
  have odd := hn.of_dvd_nat dvd
  by_cases hnp : n = p ^ n.factorization p
  · exact hnp ▸ iff_of_true (isCyclic_units_of_prime_pow p hp (odd.ne_two_of_dvd_nat dvd_rfl) _)
      ⟨p, _, hp, odd, rfl⟩
  refine iff_of_false ?_ (mt ?_ hnp)
  · have := n.ordProj_dvd p
    rw [← Nat.mul_div_cancel' this]
    refine not_isCyclic_units_of_mul_coprime _ _ (hn.of_dvd_nat this) ?_
      (hn.of_dvd_nat (Nat.div_dvd_of_dvd this)) ?_ ((Nat.coprime_ordCompl hp hn0).pow_left ..)
    · simpa only [Ne, pow_eq_one_iff (hp.factorization_pos_of_dvd hn0 dvd).ne'] using hp.ne_one
    · contrapose! hnp
      conv_lhs => rw [← Nat.div_mul_cancel this, hnp, one_mul]
  rintro ⟨q, m, hq, -, rfl⟩
  cases (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow dvd)
  simp [hp.factorization_self] at hnp

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
  · rw [h1]; simp [isCyclic_units_one]
  by_cases h2 : n = 2
  · rw [h2]; simp [isCyclic_units_two]
  by_cases h4 : n = 4
  · rw [h4]; simp [isCyclic_units_four]
  simp only [h0, h1, h2, h4, false_or, and_or_left, exists_or]
  rcases (n.even_or_odd).symm with hn | hn
  · rw [isCyclic_units_iff_of_odd hn, or_iff_left]
    · congr! with p m
      rw [and_iff_right_of_imp]
      rintro rfl
      contrapose! h1
      cases Nat.lt_one_iff.mp h1
      apply pow_zero
    · rintro ⟨p, m, -, -, -, rfl⟩
      simp [← Nat.not_even_iff_odd] at hn
  obtain ⟨n, rfl⟩ := hn.two_dvd
  rcases (n.even_or_odd).symm with hn | hn
  · rw [isCyclic_units_two_mul_iff_of_odd _ hn, isCyclic_units_iff_of_odd hn, or_iff_right]
    · congr! with p m
      rw [Nat.mul_left_cancel_iff zero_lt_two, and_iff_right_of_imp]
      rintro rfl
      contrapose! h2
      cases Nat.lt_one_iff.mp h2
      rw [pow_zero, mul_one]
    · rintro ⟨p, m, -, odd, -, eq⟩
      have := eq ▸ odd.pow
      simp [← Nat.not_even_iff_odd] at this
  obtain ⟨n, rfl⟩ := hn.two_dvd
  apply iff_of_false
  · rw [← mul_assoc, show 2 * 2 = 4 from rfl, isCyclic_units_four_mul_iff]
    omega
  rintro (⟨p, m, -, odd, -, eq⟩ | ⟨p, m, -, odd, -, eq⟩)
  on_goal 1 => have := eq ▸ odd.pow
  on_goal 2 => have := (Nat.mul_left_cancel_iff zero_lt_two).mp eq ▸ odd.pow
  all_goals simp [← Nat.not_even_iff_odd] at this

end ZMod
