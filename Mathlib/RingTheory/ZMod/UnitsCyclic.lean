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

* `ZMod.isCyclic_units_of_prime_pow` : the case of odd prime powers

* `ZMod.isCyclic_units_two_pow_iff` : `(ZMod (2 ^ n))ˣ` is cyclic iff `n ≤ 2`.

* `ZMod.units_orderOf_five` : the order of `5` modulo `2 ^ (n + 3)` is `2 ^ (n + 1)`.

The proofs follow [Ireland and Rosen,
  *A classical introduction to modern number theory*, chapter 4]
  [IrelandRosen1990].

-/

open scoped Nat

namespace ZMod

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

-- Ireland & Rosen, 4.1, Lemma 3
theorem pow_modEq_pow_succ_of_modEq_pow (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n)
    (a b : ℤ) (h : Int.ModEq (p ^ n) a b) :
    Int.ModEq (p ^ (n + 1)) (a ^ p) (b ^ p) := by
  rw [← Nat.cast_pow, ← intCast_eq_intCast_iff] at h ⊢
  set c := b - a with hc
  replace hc : b = a + c := Int.sub_eq_iff_eq_add'.mp hc
  have hc' : (p ^ n : ℤ) ∣ c := by
    rw [← Nat.cast_pow, ← intCast_zmod_eq_zero_iff_dvd]
    simp [c, sub_eq_zero, h]
  obtain ⟨k, hk⟩ := hc'
  simp only [Int.cast_pow, hc, add_pow, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  rw [← Finset.sum_erase_add (a := p)]
  · rw [← Finset.sum_erase_add (a := 0)]
    · simp only [pow_zero, tsub_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one,
      tsub_self, Nat.choose_self, right_eq_add]
      convert add_zero _
      · simp [hk, mul_pow, ← pow_mul]
        convert zero_mul _
        rw [← Nat.cast_pow, natCast_zmod_eq_zero_iff_dvd]
        apply Nat.pow_dvd_pow p
        trans n * 2
        · rw [mul_two]
          exact Nat.add_le_add_iff_left.mpr hn
        · exact Nat.mul_le_mul_left n (Nat.Prime.two_le hp)
      · rw [eq_comm]
        apply Finset.sum_eq_zero
        intro i hi
        simp at hi
        have hi' : i < p := by
          refine Nat.lt_of_le_of_ne ?_ hi.2.1
          exact Nat.le_of_lt_succ hi.2.2
        rw [mul_assoc, hk]
        convert mul_zero _
        simp [mul_pow, mul_comm, mul_assoc]
        convert mul_zero _
        rw [← pow_mul, ← Nat.cast_pow, mul_comm, ← Nat.cast_mul]
        rw [natCast_zmod_eq_zero_iff_dvd]
        rw [pow_succ']
        apply Nat.mul_dvd_mul
        · apply Nat.Prime.dvd_choose_self hp hi.1 hi'
        · apply Nat.pow_dvd_pow p
          apply Nat.le_mul_of_pos_right
          simpa
    · simp only [Finset.mem_erase, ne_eq, eq_comm, Finset.mem_range, lt_add_iff_pos_left,
      add_pos_iff, zero_lt_one, or_true, and_true]
      exact Nat.Prime.ne_zero hp
  · simp

-- Ireland & Rosen, 4.1, Corollary 1 of Lemma 3 (a sublemma)
theorem pow_add_mul_pow_modeq
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a c : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    Int.ModEq (p ^ (m + 2)) ((a + c * p ^ m) ^ p) (a ^ p + a ^ (p - 1) * c * p ^ (m + 1)) := by
  rw [← Nat.cast_pow, ← intCast_eq_intCast_iff]
  simp
  rw [add_comm (a : ZMod (p ^ (m + 2)))]
  rw [add_pow]
  rw [← Finset.add_sum_erase (a := 0)]
  · rw [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one,
      Nat.sub_zero]
    apply congr_arg₂ _ rfl
    rw [← Finset.add_sum_erase (a := 1)]
    · rw [pow_one, Nat.choose_one_right]
      rw [show (c : ZMod (p ^ (m + 2))) * p ^m * a ^ (p - 1) * p =
        a ^(p - 1) * c * p ^(m + 1) by ring,
        add_eq_left]
      apply Finset.sum_eq_zero
      · intro i hi
        simp only [Finset.mem_erase, ne_eq, Finset.mem_range] at hi
        by_cases hip : i = p
        · rw [hip, Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self,
          pow_zero, mul_one]
          rw [mul_pow]
          convert mul_zero _
          rw [← pow_mul]
          apply natCast_pow_eq_zero_of_le
          trans m * 3
          · rw [mul_add m 1 2, mul_one, Nat.add_le_add_iff_left]
            exact Nat.le_mul_of_pos_left 2 hm
          · rw [Nat.mul_le_mul_left_iff hm, Nat.succ_le_iff]
            exact Nat.lt_of_le_of_ne (Nat.Prime.two_le hp) (Ne.symm hp2)
        rw [mul_assoc, mul_comm, mul_assoc]
        convert mul_zero _
        have : p ∣ p.choose i := by
          apply Nat.Prime.dvd_choose_self hp hi.2.1
          apply Nat.lt_of_le_of_ne _ hip
          exact Nat.le_of_lt_succ hi.2.2
        obtain ⟨k, hk⟩ := this
        rw [hk, Nat.cast_mul, mul_right_comm] --  mul_assoc, mul_pow]
        convert zero_mul _
        rw [mul_pow, mul_comm, mul_assoc]
        convert mul_zero _
        rw [← pow_mul, ← pow_succ]
        apply natCast_pow_eq_zero_of_le
        simp only [Nat.reduceLeDiff]
        trans m * 2
        · simp [mul_two, add_le_add_iff_left, hm]
        · rw [Nat.mul_le_mul_left_iff hm]
          apply Nat.succ_le_of_lt
          apply Nat.lt_of_le_of_ne
          · refine Nat.one_le_iff_ne_zero.mpr hi.2.1
          · exact Ne.symm hi.1
    · simp [Nat.Prime.pos hp]
  · simp

-- Ireland & Rosen, 4.1, Corollary 1 of Lemma 3 (a sublemma)
theorem pow_one_add_mul_pow_prime_modeq
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    Int.ModEq (p ^ (m + 2)) ((1 + c * p ^ m) ^ p) (1 + c * p ^ (m + 1)) := by
  convert pow_add_mul_pow_modeq p hp hp2 1 c m hm
  · simp
  · simp

-- Ireland & Rosen, 4.1, Corollary 1 of Lemma 3
theorem one_add_mul_prime_pow_modeq
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℤ) (n : ℕ) :
    Int.ModEq (p ^ (n + 2)) ((1 + a * p) ^ (p ^ n)) (1 + a * p ^ (n + 1)) := by
  induction n with
  | zero => simp
  | succ n hrec =>
    nth_rewrite 2 [pow_succ]
    rw [pow_mul]
    have := pow_modEq_pow_succ_of_modEq_pow  p hp (n + 2) (Nat.le_add_left 1 (n + 1))
      _ _ hrec
    simp only [add_assoc, Nat.reduceAdd] at this ⊢
    apply Int.ModEq.trans this
    apply pow_one_add_mul_pow_prime_modeq p hp hp2
    exact Nat.le_add_left 1 n

/-- Ireland & Rosen, §4.1, Corollary 2 of Lemma 3 -/
theorem orderOf_one_add_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (n : ℕ) :
    orderOf (1 + a * p : ZMod (p ^ (n + 1))) = p ^ n := by
  letI : Fact (p.Prime) := ⟨hp⟩
  by_cases hn : n = 0
  · simp [hn]
    convert mul_zero _
    simp [natCast_zmod_eq_zero_iff_dvd, hn]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
    apply orderOf_eq_prime_pow
    · rw [← Int.cast_natCast, ← Int.cast_mul, ← Int.cast_one, ← Int.cast_add,
        ← Int.cast_pow, intCast_eq_intCast_iff]
      rw [Nat.cast_pow, add_assoc]
      intro H
      apply ha
      suffices Int.ModEq p a 0 by
        exact Int.dvd_of_emod_eq_zero this
      apply Int.ModEq.mul_left_cancel' (c := p ^ (n + 1))
        (by simp [hp.ne_zero])
      apply Int.ModEq.add_left_cancel' 1
      simp only [mul_zero, add_zero, ← pow_succ, add_assoc]
      rw [mul_comm]
      apply Int.ModEq.trans _ H
      exact (one_add_mul_prime_pow_modeq hp hp2 a n).symm
    · rw [← Int.cast_natCast, ← Int.cast_mul, ← Int.cast_one, ← Int.cast_add,
        ← Int.cast_pow, intCast_eq_intCast_iff]
      have := one_add_mul_prime_pow_modeq hp hp2 a (n + 1)
      rw [add_assoc _ 1 2, add_comm 1 2, ← add_assoc, pow_succ] at this
      replace this := Int.ModEq.of_mul_right _ this
      rw [← Nat.cast_pow, ← intCast_eq_intCast_iff] at this
      rw [add_assoc _ 1 1]
      simp only [Nat.reduceAdd]
      rw [←intCast_eq_intCast_iff]
      rw [this]
      simp only [Int.cast_add, add_eq_left, Int.cast_mul]
      convert mul_zero _
      rw [Int.cast_natCast]
      exact natCast_self (p ^ (n + 2))

/-- If `p` is an odd prime, then `(ZMod (p ^ n))ˣ` is cyclic for all n -/
theorem isCyclic_units_of_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    IsCyclic (ZMod (p ^ n))ˣ := by
  have _ : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have _ : Fact (p.Prime) := ⟨hp⟩
  rcases n with _ | n
  · rw [pow_zero]; infer_instance
  -- We first consider the element `1 + p` of order `p ^ n`
  let a := (((1 + p) : ℕ) : ZMod (p ^ (n + 1)))
  have ha : IsUnit a := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    simp only [Nat.coprime_add_self_left, Nat.coprime_one_left_eq_true]
  have ha' : orderOf ha.unit = p ^ n := by
    simp only [←
      orderOf_injective _ Units.coeHom_injective ha.unit,
      Units.coeHom_apply, IsUnit.unit_spec]
    simp only [a, Nat.cast_add, Nat.cast_one]
    convert orderOf_one_add_mul_prime hp hp2 1 _ _ using 1
    · simp
    · exact Prime.not_dvd_one (Nat.prime_iff_prime_int.mp hp)
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

lemma Int.modEq_pow_five (n : ℕ) :
    Int.ModEq (2 ^ (n + 2)) (5 ^ (2 ^ n)) 1 := by
  induction n with
  | zero => simp; rfl
  | succ n hrec =>
    convert pow_modEq_pow_succ_of_modEq_pow 2 Nat.prime_two _ ?_ _ _ hrec using 1
    · rw [pow_succ, pow_mul]
    · exact Nat.le_add_left 1 (n + 1)

lemma Int.modEq_pow_five' (n : ℕ) :
    Int.ModEq (2 ^ (n + 3)) (5 ^ (2 ^ n)) (1 + 2 ^ (n + 2)) := by
  induction n with
  | zero => simp
  | succ n hrec =>
    have := pow_modEq_pow_succ_of_modEq_pow 2 Nat.prime_two _ (Nat.le_add_left 1 _) _ _ hrec
    rw [← pow_mul, ← pow_succ] at this
    apply this.trans
    rw [add_sq, mul_one, one_pow, ← pow_succ',
      ← pow_mul, add_assoc n 2 1]
    conv_rhs => rw [← add_zero (1 + _)]
    apply Int.ModEq.add rfl
    rw [Int.modEq_zero_iff_dvd]
    simp only [Nat.cast_ofNat, Nat.reduceAdd]
    apply pow_dvd_pow
    simp only [mul_two, add_assoc, Nat.reduceAdd, add_le_add_iff_left]
    rw [add_comm, add_assoc]
    simp

theorem units_orderOf_five (n : ℕ) :
    orderOf (5 : ZMod (2 ^ (n + 2))) = 2 ^ n := by
  rcases n with _ | n
  · norm_num; decide
  suffices h : (5 : ZMod (2 ^ (n + 3))) ^ (2 ^ n) = 1 + 2 ^ (n + 2) by
    apply Nat.eq_prime_pow_of_dvd_least_prime_pow Nat.prime_two
    · rw [orderOf_dvd_iff_pow_eq_one, h, add_eq_left]
      norm_cast
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.pow_dvd_pow_iff_le_right']
      simp
    · rw [orderOf_dvd_iff_pow_eq_one, pow_succ 2 n, pow_mul, h]
      calc ((1 + 2 ^ (n + 2)) ^ 2 : ZMod (2 ^ (n + 3))) =
          (1 + (2 ^ (n + 3) : ℕ) * (1 + 2 ^ (n + 1)) : ZMod (2 ^ (n + 3))) := by push_cast; ring
        _ = 1 := by rw [natCast_self]; ring
  norm_cast
  rw [natCast_eq_natCast_iff, ← Int.natCast_modEq_iff]
  push_cast
  exact Int.modEq_pow_five' n

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

section Refactor
variable {R : Type*} [CommSemiring R] {p : ℕ}
  {n : ℕ} {a b : R}
  (hp : p.Prime) (hn : 1 ≤ n)

lemma lemma_1 (hp : p.Prime) (hn : 1 ≤ n)
    (h : ∃ x, b = a + p ^ n * x) :
    ∃ y, b ^ p = a ^ p + p ^ (n + 1) * y := by
  obtain ⟨x, hx⟩ := h
  rw [hx, add_comm a, add_pow]
  rw [← Finset.sum_erase_add (a := 0) _ _ (by simp)]
  rw [← Finset.sum_erase_add (a := p) _ _ (by simp [hp.ne_zero])]
  simp only [add_comm (a ^ p)]
  use ∑ i ∈ ((Finset.range (p + 1)).erase 0).erase p,
    (p ^ n * x) ^ (i - 1) * x * a ^ (p - i) * (p.choose i / p : ℕ) + p ^ (n * p - n - 1) * x ^ p
  simp only [tsub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, tsub_zero, one_mul,
    Nat.choose_zero_right]
  apply congr_arg₂ _ _ rfl
  rw [mul_add, Finset.mul_sum]
  apply congr_arg₂
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_erase, ne_eq, Finset.mem_range] at hi
    have hi' : i < p :=
      Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi.2.2) hi.1
    have hi'' : i - 1 + 1 = i :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi.2.1)
    have : p ∣ p.choose i :=
      Nat.Prime.dvd_choose_self hp hi.2.1 hi'
    obtain ⟨q, hq⟩ := this
    rw [hq, mul_comm p q, Nat.mul_div_cancel _ hp.pos, Nat.cast_mul, mul_pow, pow_succ]
    ring_nf
    congr 1
    apply congr_arg₂ _ _ rfl
    rw [mul_assoc _ x]
    simp only [← pow_succ', ← pow_add]
    rw [add_assoc, add_comm 1, ← add_assoc, add_comm n, ← Nat.mul_add_one, hi'']
  · rw [mul_pow, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    simp only [← pow_add, ← pow_mul]
    congr
    rw [add_comm, Nat.sub_sub, eq_comm]
    refine Nat.sub_add_cancel ?_
    trans n * 2
    · simp [mul_two, Nat.add_le_add_iff_left.mpr hn]
    · refine Nat.mul_le_mul_left n hp.two_le

-- Ireland & Rosen, 4.1, Corollary 1 of Lemma 3 (a sublemma)
theorem pow_add_mul_pow_modeq
    (hp : p.Prime) (hp2 : p ≠ 2) (c : R)
    (hn : 1 ≤ n)
    (h : ∃ x, b = a + p ^ n * (c + p * x)) :
    ∃ y : R, b ^ p = a ^ p + p ^ (n + 1) * (a ^ (p - 1) * c + p * y) := by
  obtain ⟨x, hx⟩ := h
  set c' := c + p * x with hc'
  rw [hx, add_comm a  (p ^n * c'), add_pow, ← Finset.add_sum_erase (a := 0) _ _ (by simp)]
  rw [← Finset.add_sum_erase (a := 1) _ _ (by simp [hp.pos])]
  simp
  nth_rewrite 1 [hc']
  rw [mul_add _ c, add_mul, mul_comm _ (p : R), mul_add,
    ← add_assoc, ← add_assoc, ← mul_assoc, ← mul_assoc,
    ← pow_succ']
  rw [← mul_add, ← hc', ← Nat.cast_pow p n]
  use  x * a ^ (p - 1) +
    ∑ i ∈ (((Finset.range (p + 1)).erase 0).erase 1).erase p,
      (p ^ (n * i - n - 1) * p.choose i / p : ℕ) * c' ^ i * a ^ (p - i)
    + p ^ (n * p - n - 2) * c' ^ p
  simp only [add_assoc, mul_add]
  congr 2
  · ring
  apply congr_arg₂ _
  · simp only [Nat.cast_pow]; ring
  · simp only [Finset.mul_sum]
    rw [← Finset.sum_erase_add (a := p)]
    · congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_erase, ne_eq, Finset.mem_range] at hi
        rw [mul_pow _ c', mul_assoc, mul_comm (a ^ _), ← mul_assoc]
        rw [mul_assoc _ (c' ^ _), mul_comm (c' ^ _), ← mul_assoc]
        simp only [← Nat.cast_mul, ← Nat.cast_pow, ← mul_assoc]
        congr 2
        apply congr_arg
        rw [← pow_succ, ← pow_mul, add_assoc]
        have : p ∣ p.choose i := by
          apply Nat.Prime.dvd_choose_self hp hi.2.2.1
          apply Nat.lt_of_le_of_ne _ hi.1
          exact Nat.le_of_lt_succ hi.2.2.2
        obtain ⟨q, hq⟩ := this
        rw [hq]
        simp only [← mul_assoc, ← pow_succ]
        conv_rhs => rw [mul_comm _ q, pow_succ, ← mul_assoc,
          Nat.mul_div_cancel _ hp.pos, mul_comm q, ← mul_assoc]
        congr
        rw [← pow_add]
        apply congr_arg₂ _ rfl
        rw [add_comm (n + _), ← add_assoc, Nat.sub_sub,
          ← add_assoc]
        congr
        rw [add_assoc]
        rw [Nat.sub_add_cancel]
        trans n * 2
        · linarith
        · refine Nat.mul_le_mul_left n ?_
          rw [Nat.two_le_iff]
          exact ⟨hi.2.2.1, hi.2.1⟩
      · simp [mul_pow, ← mul_assoc]
        congr
        simp only [← Nat.cast_pow, ← Nat.cast_mul, ← pow_mul,
        ← pow_succ, ← pow_add]
        congr
        rw [add_assoc n 1, add_comm]
        refine Nat.eq_add_of_sub_eq ?_ rfl
        trans n * 3
        · linarith
        · refine Nat.mul_le_mul_left n ?_
          rw [Nat.succ_le_iff]
          exact Nat.lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    · simp [hp.ne_zero, hp.ne_one]






end Refactor
