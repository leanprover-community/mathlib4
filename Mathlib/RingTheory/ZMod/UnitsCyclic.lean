/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.RingTheory.Prime
import Mathlib.RingTheory.Int.Basic

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

theorem coe_int_isUnit_iff_isCoprime (n : ℤ) (m : ℕ) :
    IsUnit (n : ZMod m) ↔ IsCoprime (m : ℤ) n := by
  rw [Int.isCoprime_iff_nat_coprime, Nat.coprime_comm,
    ← isUnit_iff_coprime, Associated.isUnit_iff]
  simpa only [eq_intCast, @Int.cast_natCast] using
    Associated.map (Int.castRingHom _) (Int.associated_natAbs _)

instance : IsDomain (ZMod 0) :=
  Equiv.isDomain (RingEquiv.refl ℤ).symm

theorem isCyclic_units_zero :
    IsCyclic (ZMod 0)ˣ := inferInstance

theorem isCyclic_units_one :
    IsCyclic (ZMod 1)ˣ := inferInstance

theorem isCyclic_units_two :
    IsCyclic (ZMod 2)ˣ := inferInstance

theorem isCyclic_units_four :
    IsCyclic (ZMod 4)ˣ :=
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nat.card (ZMod 4)ˣ = 2 := by
    simp only [Nat.card_eq_fintype_card, card_units_eq_totient]
    rfl
  isCyclic_of_prime_card this

/- The multiplicative group of `ZMod p` is cyclic. -/
theorem isCyclic_units_prime {p : ℕ} (hp : p.Prime) :
    IsCyclic (ZMod p)ˣ :=
  have : Fact (p.Prime) := ⟨hp⟩
  inferInstance

theorem not_isCyclic_units_eight :
    ¬ IsCyclic (ZMod 8)ˣ := by
  rw [isCyclic_iff_exists_orderOf_eq_natCard]
  push_neg
  simp
  rw [show φ 8 = 4 from rfl]
  suffices ∀ (g : (ZMod 8)ˣ), orderOf g ∣ 2 by
    intro g hg
    specialize this g
    rw [hg] at this
    revert this
    decide
  simp only [orderOf_dvd_iff_pow_eq_one]
  decide

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
      intro H
      apply ha
      rw [← intCast_zmod_eq_zero_iff_dvd]
      rw [← Int.cast_zero]
      rw [intCast_eq_intCast_iff]
      have := one_add_mul_prime_pow_modeq hp hp2 a n
      simp [Nat.cast_pow, add_assoc] at H
      replace this := Int.ModEq.trans (Int.ModEq.symm this) H
      rw [← Nat.cast_pow, ← intCast_eq_intCast_iff, Int.cast_add, add_eq_left] at this
      rw [← Int.cast_zero] at this
      rw [intCast_eq_intCast_iff] at this
      rw [← add_assoc n 1 1, pow_succ _ (n + 1), mul_comm a, Nat.cast_mul] at this
      rw [← mul_zero ((p : ℤ) ^ (n + 1)), Nat.cast_pow] at this
      apply Int.ModEq.mul_left_cancel' _ this
      simp [hp.ne_zero]
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

/-- If p is an odd prime, then `(ZMod (p ^ n))ˣ` is cyclic for all n -/
theorem isCyclic_units_of_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    IsCyclic (ZMod (p ^ n))ˣ := by
  haveI _ : Fact (p.Prime) := ⟨hp⟩
  have H1 : IsCyclic (ZMod p)ˣ :=
    isCyclic_of_subgroup_isDomain (Units.coeHom _) Units.coeHom_injective
  match n with
  | 0 => simp [isCyclic_of_subsingleton]
  | 1 => rw [pow_one]; exact H1
  | n + 2 =>
    rw [isCyclic_iff_exists_zpowers_eq_top] at H1
    obtain ⟨g, hg⟩ := H1
    replace hg := orderOf_eq_card_of_zpowers_eq_top hg
    simp only [Nat.card_eq_fintype_card, card_units_eq_totient,
      Nat.totient_prime hp] at hg
    set x : ℤ := g.val.cast
    replace hx : (x : ZMod p) = g := by simp [x]
    have hxp : Int.ModEq p (x ^ (p - 1)) 1 := by
      simp [← intCast_eq_intCast_iff, hx, ← hg, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one]
    set a := if Int.ModEq (p ^ 2) (x ^ (p - 1)) 1 then x + p else x with a_def
    have hxa : Int.ModEq p a x := by
      rw [a_def]; split_ifs
      · exact Int.add_modEq_right
      · simp
    have hap : Int.ModEq p (a ^ (p - 1)) 1 :=
      (Int.ModEq.pow (p - 1) hxa).trans hxp
    have hap2 : ¬ Int.ModEq (p ^ 2) (a ^ (p - 1)) 1 := by
      rw [a_def]; split_ifs with H
      · intro H'
        have := Int.ModEq.trans H' (Int.ModEq.symm H)
        rw [← Nat.cast_pow, ← intCast_eq_intCast_iff] at this
        simp only [Int.cast_pow, Int.cast_add, Int.cast_natCast] at this
        rw [add_comm, add_pow, ← Finset.sum_erase_add (a := 0)] at this
        rw [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right,
          Nat.cast_one, mul_one, add_eq_right] at this
        rw [Finset.sum_eq_single 1] at this
        · simp only [pow_one, Nat.sub_sub, Nat.reduceAdd, Nat.choose_one_right] at this
          rw [← Int.cast_natCast p, ← Int.cast_natCast (p - 1),
            ← Int.cast_pow, ← Int.cast_mul, ← Int.cast_mul] at this
          rw [intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow, pow_two, mul_assoc] at this
          replace this := Int.dvd_of_mul_dvd_mul_left (a := p)
            (by simp [hp.ne_zero]) this
          rw [← intCast_zmod_eq_zero_iff_dvd] at this
          simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast,
            mul_eq_zero, pow_eq_zero_iff', ne_eq] at this
          rcases this with this | this
          · replace this := this.1
            simp only [this, eq_comm, Units.ne_zero] at hx
          · replace this : (((p - 1) : ℕ) : ZMod p) + 1 = 1 := by
              rw [this, zero_add]
            nth_rewrite 2 [← Nat.cast_one] at this
            rw [← Nat.cast_add] at this
            apply Nat.Prime.ne_one hp
            rw [← one_eq_zero_iff, ← this, Nat.sub_add_cancel (NeZero.one_le)]
            exact natCast_self p
        · intro i hi hi1
          convert zero_mul _
          convert zero_mul _
          simp only [Finset.mem_erase, ne_eq, Finset.mem_range, a] at hi
          suffices 2 ≤ i by
            obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le this
            rw [hj, pow_add, ← Nat.cast_pow, natCast_self, zero_mul]
          rw [Nat.two_le_iff]
          exact ⟨hi.1, hi1⟩
        · intro H; exfalso
          apply not_lt.mpr (Nat.Prime.two_le hp)
          apply Nat.lt_succ_of_le
          simpa using H
        · simp
      exact H
    replace hx : (a : ZMod p) = g := by
      rw [← intCast_eq_intCast_iff] at hxa
      rw [hxa, hx]
    have hb' : ∃ c : ℤ, ¬ ↑p ∣ c ∧ a ^ (p - 1) = 1 + p * c := by
      obtain ⟨c, hc⟩ := Int.modEq_iff_add_fac.mp hap.symm
      refine ⟨c, ?_, hc⟩
      intro hpc
      apply hap2
      apply Int.ModEq.symm
      rw [Int.modEq_iff_add_fac]
      obtain ⟨c, rfl⟩ := hpc
      use c
      rw [hc]; ring
    rw [isCyclic_iff_exists_zpowers_eq_top]
    let hau : (ZMod (p ^ (n + 2)))ˣ := by
      apply coe_int_unitOfIsCoprime a
      rw [Nat.cast_pow, IsCoprime.pow_right_iff (Nat.zero_lt_succ _)]
      · rw [isCoprime_comm, ← ZMod.coe_int_isUnit_iff_isCoprime]
        rw [← intCast_eq_intCast_iff] at hxa
        rw [hx]
        exact Units.isUnit g
    use hau
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers]
    simp only [Nat.card_eq_fintype_card, card_units_eq_totient]
    rw [Nat.totient_prime_pow hp (Nat.zero_lt_succ _)]
    simp only [Nat.succ_eq_add_one, add_tsub_cancel_right, x]
    simp [← orderOf_injective (Units.coeHom _) Units.coeHom_injective]
    simp only [coe_unitOfIsCoprime, Units.val_one, hau]
    have H0 : orderOf (a : ZMod p) = p - 1 := by
      rw [hx, ← hg]
      exact orderOf_injective (Units.coeHom _) Units.coeHom_injective g
    have H1 : p - 1 ∣ orderOf (a : ZMod (p ^ (n + 2))) := by
      rw [← H0, orderOf_dvd_iff_pow_eq_one]
      suffices (a : ZMod p) =
        castHom (Dvd.intro_left (p.pow (n + 1)) rfl) _ (a : ZMod (p ^ (n + 2))) by
        rw [this, ← map_pow, pow_orderOf_eq_one, map_one]
      simp
    have H2 : orderOf ((a : ZMod (p ^ (n + 2))) ^ (p - 1)) = p ^ (n + 1) := by
      obtain ⟨c, hpc, hca⟩ := hb'
      rw [← Int.cast_pow, hca]
      simp only [Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_natCast, x, hau]
      rw [mul_comm]
      exact orderOf_one_add_mul_prime hp hp2 _ hpc _
    have H2' := orderOf_pow_dvd (x := (a : ZMod (p ^ (n + 2)))) (p - 1)
    rw [H2] at H2'
    apply Nat.dvd_antisymm
    · rw [orderOf_dvd_iff_pow_eq_one, mul_comm, pow_mul]
      rw [← orderOf_dvd_iff_pow_eq_one, H2]
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ H2' H1
      simp
      refine (Nat.coprime_self_sub_right ?_).mpr ?_
      · exact NeZero.one_le
      exact Nat.gcd_one_right p

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
    orderOf (5 : ZMod (2 ^ (n + 3))) = 2 ^ (n + 1) := by
  have H : orderOf (5 :ZMod (2 ^ (n + 3))) ∣ 2 ^ (n + 1) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    suffices ((5 ^ (2 ^ (n + 1)) : ℤ) : ZMod (2 ^ (n +3))) = (1 : ℤ) by
      simpa
    rw [intCast_eq_intCast_iff]
    simpa using Int.modEq_pow_five (n + 1)
  have H' : ¬ (orderOf (5 : ZMod (2 ^ (n + 3)))) ∣ 2 ^ n:= by
    rw [orderOf_dvd_iff_pow_eq_one]
    suffices ¬ ((5 ^ (2 ^ n) : ℤ) : ZMod (2 ^ (n + 3))) = (1 : ℤ) by
      simpa
    rw [intCast_eq_intCast_iff, Nat.cast_pow, Nat.cast_two]
    intro H'
    have := (Int.modEq_pow_five' n).symm.trans H'
    nth_rewrite 2 [← add_zero 1] at this
    replace this := Int.ModEq.add_left_cancel' _ this
    rw [Int.modEq_zero_iff_dvd] at this
    rw [pow_dvd_pow_iff] at this
    · simp only [add_le_add_iff_left, Nat.reduceLeDiff] at this
    · decide
    · decide
  rw [Nat.dvd_prime_pow Nat.prime_two] at H
  obtain ⟨k, hk, ho⟩ := H
  suffices k = n + 1 by rw [ho, this]
  apply le_antisymm hk
  rw [← not_lt]
  intro hk'
  apply H'
  rw [ho]
  exact Nat.pow_dvd_pow _ (Nat.le_of_lt_succ hk')

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
  set m := n.factorization 2 with hm
  set q := n / (2 ^ n.factorization 2) with hq
  have hn : n = 2 ^ m * q := (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  rw [hn, show 4 = 2 ^ 2 by rfl, ← mul_assoc, ← pow_add] at H
  -- obtain ⟨q, hn : n = 2 ^ m * q⟩ := n.ordProj_dvd 2
  have hq0 : q ≠ 0 := fun hq ↦ by simp [hn, hq, mul_zero] at hn1
  have _ : NeZero q := ⟨hq0⟩
  have hq2 : (2 ^ (2 + m)).Coprime q := by
    rw [Nat.coprime_pow_left_iff (Nat.pos_of_neZero _)]
    rw [Nat.prime_two.coprime_iff_not_dvd]
    rw [hq]
    apply Nat.not_dvd_ordCompl Nat.prime_two (Nat.ne_zero_of_lt hn0)
  let e := chineseRemainder hq2
  let f := (Units.mapEquiv e.toMulEquiv).trans  MulEquiv.prodUnits
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
      simp at h0 h4
      simp [h0, h4]
      intro l hl hol e he
      have : ¬ Even (l ^ e) := by
        rw [Nat.not_even_iff_odd]
        apply Nat.odd_pow hol
      constructor
      · intro H
        apply this
        rw [← H]
        exact hn
      · intro H
        rw [show 4 = 2 * 2 by rfl, mul_assoc] at H
        simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at H
        apply this
        rw [← H]
        exact even_two_mul q
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
        intro ha1' ; apply hn4
        obtain ⟨q, hq⟩ := ha1'
        rw [hm, hq, ← mul_assoc]
        exact Nat.dvd_mul_right 4 q
      rw [hm]
      rw [isCyclic_units_of_two_mul_odd_iff _ hoddm]
      rw [isCyclic_units_of_odd_iff hoddm]
      apply exists_congr
      intro l
      simp only [exists_and_left, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false,
        and_congr_right_iff]
      intro hl hol
      apply exists_congr
      intro e
      constructor
      · intro he
        refine ⟨?_, Or.inr he⟩
        apply Nat.pos_of_ne_zero
        rintro ⟨rfl⟩
        apply h2
        simp [hm, he]
      · rintro ⟨h1e, (he | he)⟩
        · exfalso
          suffices Odd (l ^ e) by
            rw [← Nat.not_even_iff_odd] at this
            apply this
            rw [← he]
            exact even_two_mul m
          apply Nat.odd_pow hol
        · exact he

end ZMod
