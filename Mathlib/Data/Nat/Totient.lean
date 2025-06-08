/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Periodic

/-!
# Euler's totient function

This file defines [Euler's totient function](https://en.wikipedia.org/wiki/Euler's_totient_function)
`Nat.totient n` which counts the number of naturals less than `n` that are coprime with `n`.
We prove the divisor sum formula, namely that `n` equals `φ` summed over the divisors of `n`. See
`sum_totient`. We also prove two lemmas to help compute totients, namely `totient_mul` and
`totient_prime_pow`.
-/

assert_not_exists Algebra LinearMap

open Finset

namespace Nat

/-- Euler's totient function. This counts the number of naturals strictly less than `n` which are
coprime with `n`. -/
def totient (n : ℕ) : ℕ := #{a ∈ range n | n.Coprime a}

@[inherit_doc]
scoped notation "φ" => Nat.totient

@[simp]
theorem totient_zero : φ 0 = 0 :=
  rfl

@[simp]
theorem totient_one : φ 1 = 1 := rfl

theorem totient_eq_card_coprime (n : ℕ) : φ n = #{a ∈ range n | n.Coprime a} := rfl

/-- A characterisation of `Nat.totient` that avoids `Finset`. -/
theorem totient_eq_card_lt_and_coprime (n : ℕ) : φ n = Nat.card { m | m < n ∧ n.Coprime m } := by
  let e : { m | m < n ∧ n.Coprime m } ≃ {x ∈ range n | n.Coprime x} :=
    { toFun := fun m => ⟨m, by simpa only [Finset.mem_filter, Finset.mem_range] using m.property⟩
      invFun := fun m => ⟨m, by simpa only [Finset.mem_filter, Finset.mem_range] using m.property⟩
      left_inv := fun m => by simp only [Subtype.coe_mk, Subtype.coe_eta]
      right_inv := fun m => by simp only [Subtype.coe_mk, Subtype.coe_eta] }
  rw [totient_eq_card_coprime, card_congr e, card_eq_fintype_card, Fintype.card_coe]

theorem totient_le (n : ℕ) : φ n ≤ n :=
  ((range n).card_filter_le _).trans_eq (card_range n)

theorem totient_lt (n : ℕ) (hn : 1 < n) : φ n < n :=
  (card_lt_card (filter_ssubset.2 ⟨0, by simp [hn.ne', pos_of_gt hn]⟩)).trans_eq (card_range n)

@[simp]
theorem totient_eq_zero : ∀ {n : ℕ}, φ n = 0 ↔ n = 0
  | 0 => by decide
  | n + 1 =>
    suffices ∃ x < n + 1, (n + 1).gcd x = 1 by simpa [totient, filter_eq_empty_iff]
    ⟨1 % (n + 1), mod_lt _ n.succ_pos, by rw [gcd_comm, ← gcd_rec, gcd_one_right]⟩

@[simp] theorem totient_pos {n : ℕ} : 0 < φ n ↔ 0 < n := by simp [pos_iff_ne_zero]

instance neZero_totient {n : ℕ} [NeZero n] : NeZero n.totient :=
  ⟨(totient_pos.mpr <| NeZero.pos n).ne'⟩

theorem filter_coprime_Ico_eq_totient (a n : ℕ) :
    #{x ∈ Ico n (n + a) | a.Coprime x} = totient a := by
  rw [totient, filter_Ico_card_eq_of_periodic, count_eq_card_filter_range]
  exact periodic_coprime a

theorem Ico_filter_coprime_le {a : ℕ} (k n : ℕ) (a_pos : 0 < a) :
    #{x ∈ Ico k (k + n) | a.Coprime x} ≤ totient a * (n / a + 1) := by
  conv_lhs => rw [← Nat.mod_add_div n a]
  induction' n / a with i ih
  · rw [← filter_coprime_Ico_eq_totient a k]
    simp only [add_zero, mul_one, mul_zero, le_of_lt (mod_lt n a_pos), zero_add]
    gcongr
    exact le_of_lt (mod_lt n a_pos)
  simp only [mul_succ]
  simp_rw [← add_assoc] at ih ⊢
  calc
    #{x ∈ Ico k (k + n % a + a * i + a) | a.Coprime x}
      ≤ #{x ∈ Ico k (k + n % a + a * i) ∪
        Ico (k + n % a + a * i) (k + n % a + a * i + a) | a.Coprime x} := by
      gcongr
      apply Ico_subset_Ico_union_Ico
    _ ≤ #{x ∈ Ico k (k + n % a + a * i) | a.Coprime x} + a.totient := by
      rw [filter_union, ← filter_coprime_Ico_eq_totient a (k + n % a + a * i)]
      apply card_union_le
    _ ≤ a.totient * i + a.totient + a.totient := add_le_add_right ih (totient a)

open ZMod

/-- Note this takes an explicit `Fintype ((ZMod n)ˣ)` argument to avoid trouble with instance
diamonds. -/
@[simp]
theorem _root_.ZMod.card_units_eq_totient (n : ℕ) [NeZero n] [Fintype (ZMod n)ˣ] :
    Fintype.card (ZMod n)ˣ = φ n :=
  calc
    Fintype.card (ZMod n)ˣ = Fintype.card { x : ZMod n // x.val.Coprime n } :=
      Fintype.card_congr ZMod.unitsEquivCoprime
    _ = φ n := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := exists_eq_succ_of_ne_zero NeZero.out
      simp only [totient, Finset.card_eq_sum_ones, Fintype.card_subtype, Finset.sum_filter, ←
        Fin.sum_univ_eq_sum_range, @Nat.coprime_comm (m + 1)]
      rfl

theorem totient_even {n : ℕ} (hn : 2 < n) : Even n.totient := by
  haveI : Fact (1 < n) := ⟨one_lt_two.trans hn⟩
  haveI : NeZero n := NeZero.of_gt hn
  suffices 2 = orderOf (-1 : (ZMod n)ˣ) by
    rw [← ZMod.card_units_eq_totient, even_iff_two_dvd, this]
    exact orderOf_dvd_card
  rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one, ringChar.eq (ZMod n) n, if_neg hn.ne']

theorem totient_mul {m n : ℕ} (h : m.Coprime n) : φ (m * n) = φ m * φ n :=
  if hmn0 : m * n = 0 then by
    rcases Nat.mul_eq_zero.1 hmn0 with h | h <;>
      simp only [totient_zero, mul_zero, zero_mul, h]
  else by
    haveI : NeZero (m * n) := ⟨hmn0⟩
    haveI : NeZero m := ⟨left_ne_zero_of_mul hmn0⟩
    haveI : NeZero n := ⟨right_ne_zero_of_mul hmn0⟩
    simp only [← ZMod.card_units_eq_totient]
    rw [Fintype.card_congr (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).toEquiv,
      Fintype.card_congr (@MulEquiv.prodUnits (ZMod m) (ZMod n) _ _).toEquiv, Fintype.card_prod]

/-- For `d ∣ n`, the totient of `n/d` equals the number of values `k < n` such that `gcd n k = d` -/
theorem totient_div_of_dvd {n d : ℕ} (hnd : d ∣ n) :
    φ (n / d) = #{k ∈ range n | n.gcd k = d} := by
  rcases d.eq_zero_or_pos with (rfl | hd0); · simp [eq_zero_of_zero_dvd hnd]
  rcases hnd with ⟨x, rfl⟩
  rw [Nat.mul_div_cancel_left x hd0]
  apply Finset.card_bij fun k _ => d * k
  · simp only [mem_filter, mem_range, and_imp, Coprime]
    refine fun a ha1 ha2 => ⟨(mul_lt_mul_left hd0).2 ha1, ?_⟩
    rw [gcd_mul_left, ha2, mul_one]
  · simp [hd0.ne']
  · simp only [mem_filter, mem_range, exists_prop, and_imp]
    refine fun b hb1 hb2 => ?_
    have : d ∣ b := by
      rw [← hb2]
      apply gcd_dvd_right
    rcases this with ⟨q, rfl⟩
    refine ⟨q, ⟨⟨(mul_lt_mul_left hd0).1 hb1, ?_⟩, rfl⟩⟩
    rwa [gcd_mul_left, mul_eq_left hd0.ne'] at hb2

theorem sum_totient (n : ℕ) : n.divisors.sum φ = n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← sum_div_divisors n φ]
  have : n = ∑ d ∈ n.divisors, #{k ∈ range n | n.gcd k = d} := by
    nth_rw 1 [← card_range n]
    refine card_eq_sum_card_fiberwise fun x _ => mem_divisors.2 ⟨?_, hn.ne'⟩
    apply gcd_dvd_left
  nth_rw 3 [this]
  exact sum_congr rfl fun x hx => totient_div_of_dvd (dvd_of_mem_divisors hx)

theorem sum_totient' (n : ℕ) : ∑ m ∈ range n.succ with m ∣ n, φ m = n := by
  convert sum_totient _ using 1
  simp only [Nat.divisors, sum_filter, range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot] <;> simp

/-- When `p` is prime, then the totient of `p ^ (n + 1)` is `p ^ n * (p - 1)` -/
theorem totient_prime_pow_succ {p : ℕ} (hp : p.Prime) (n : ℕ) : φ (p ^ (n + 1)) = p ^ n * (p - 1) :=
  calc
    φ (p ^ (n + 1)) = #{a ∈ range (p ^ (n + 1)) | (p ^ (n + 1)).Coprime a} :=
      totient_eq_card_coprime _
    _ = #(range (p ^ (n + 1)) \ (range (p ^ n)).image (· * p)) :=
      congr_arg card
        (by
          rw [sdiff_eq_filter]
          apply filter_congr
          simp only [mem_range, mem_filter, coprime_pow_left_iff n.succ_pos, mem_image, not_exists,
            hp.coprime_iff_not_dvd]
          intro a ha
          constructor
          · intro hap b h; rcases h with ⟨_, rfl⟩
            exact hap (dvd_mul_left _ _)
          · rintro h ⟨b, rfl⟩
            rw [pow_succ'] at ha
            exact h b ⟨lt_of_mul_lt_mul_left ha (zero_le _), mul_comm _ _⟩)
    _ = _ := by
      have h1 : Function.Injective (· * p) := mul_left_injective₀ hp.ne_zero
      have h2 : (range (p ^ n)).image (· * p) ⊆ range (p ^ (n + 1)) := fun a => by
        simp only [mem_image, mem_range, exists_imp]
        rintro b ⟨h, rfl⟩
        rw [Nat.pow_succ]
        exact (mul_lt_mul_right hp.pos).2 h
      rw [card_sdiff h2, Finset.card_image_of_injective _ h1, card_range, card_range, ←
        one_mul (p ^ n), pow_succ', ← tsub_mul, one_mul, mul_comm]

/-- When `p` is prime, then the totient of `p ^ n` is `p ^ (n - 1) * (p - 1)` -/
theorem totient_prime_pow {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) :
    φ (p ^ n) = p ^ (n - 1) * (p - 1) := by
  rcases exists_eq_succ_of_ne_zero (pos_iff_ne_zero.1 hn) with ⟨m, rfl⟩
  exact totient_prime_pow_succ hp _

theorem totient_prime {p : ℕ} (hp : p.Prime) : φ p = p - 1 := by
  rw [← pow_one p, totient_prime_pow hp] <;> simp

theorem totient_eq_iff_prime {p : ℕ} (hp : 0 < p) : p.totient = p - 1 ↔ p.Prime := by
  refine ⟨fun h => ?_, totient_prime⟩
  replace hp : 1 < p := by
    apply lt_of_le_of_ne
    · rwa [succ_le_iff]
    · rintro rfl
      rw [totient_one, tsub_self] at h
      exact one_ne_zero h
  rw [totient_eq_card_coprime, range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico hp.le,
    Finset.filter_insert, if_neg (not_coprime_of_dvd_of_dvd hp (dvd_refl p) (dvd_zero p)),
    ← Nat.card_Ico 1 p] at h
  refine
    p.prime_of_coprime hp fun n hn hnz => Finset.filter_card_eq h n <| Finset.mem_Ico.mpr ⟨?_, hn⟩
  omega

theorem card_units_zmod_lt_sub_one {p : ℕ} (hp : 1 < p) [Fintype (ZMod p)ˣ] :
    Fintype.card (ZMod p)ˣ ≤ p - 1 := by
  haveI : NeZero p := ⟨(pos_of_gt hp).ne'⟩
  rw [ZMod.card_units_eq_totient p]
  exact Nat.le_sub_one_of_lt (Nat.totient_lt p hp)

theorem prime_iff_card_units (p : ℕ) [Fintype (ZMod p)ˣ] :
    p.Prime ↔ Fintype.card (ZMod p)ˣ = p - 1 := by
  rcases eq_zero_or_neZero p with hp | hp
  · subst hp
    simp only [ZMod, not_prime_zero, false_iff, zero_tsub]
    -- the subst created a non-defeq but subsingleton instance diamond; resolve it
    suffices Fintype.card ℤˣ ≠ 0 by convert this
    simp
  rw [ZMod.card_units_eq_totient, Nat.totient_eq_iff_prime <| NeZero.pos p]

@[simp]
theorem totient_two : φ 2 = 1 :=
  (totient_prime prime_two).trans rfl

theorem totient_eq_one_iff : ∀ {n : ℕ}, n.totient = 1 ↔ n = 1 ∨ n = 2
  | 0 => by simp
  | 1 => by simp
  | 2 => by simp
  | n + 3 => by
    have : 3 ≤ n + 3 := le_add_self
    simp only [succ_succ_ne_one, false_or]
    exact ⟨fun h => not_even_one.elim <| h ▸ totient_even this, by rintro ⟨⟩⟩

theorem dvd_two_of_totient_le_one {a : ℕ} (han : 0 < a) (ha : a.totient ≤ 1) : a ∣ 2 := by
  rcases totient_eq_one_iff.mp <| le_antisymm ha <| totient_pos.2 han with rfl | rfl <;> norm_num

/-! ### Euler's product formula for the totient function

We prove several different statements of this formula. -/


/-- Euler's product formula for the totient function. -/
theorem totient_eq_prod_factorization {n : ℕ} (hn : n ≠ 0) :
    φ n = n.factorization.prod fun p k => p ^ (k - 1) * (p - 1) := by
  rw [multiplicative_factorization φ (@totient_mul) totient_one hn]
  apply Finsupp.prod_congr _
  intro p hp
  have h := zero_lt_iff.mpr (Finsupp.mem_support_iff.mp hp)
  rw [totient_prime_pow (prime_of_mem_primeFactors hp) h]

/-- Euler's product formula for the totient function. -/
theorem totient_mul_prod_primeFactors (n : ℕ) :
    (φ n * ∏ p ∈ n.primeFactors, p) = n * ∏ p ∈ n.primeFactors, (p - 1) := by
  by_cases hn : n = 0; · simp [hn]
  rw [totient_eq_prod_factorization hn]
  nth_rw 3 [← factorization_prod_pow_eq_self hn]
  simp only [prod_primeFactors_prod_factorization, ← Finsupp.prod_mul]
  refine Finsupp.prod_congr (M := ℕ) (N := ℕ) fun p hp => ?_
  rw [Finsupp.mem_support_iff, ← zero_lt_iff] at hp
  rw [mul_comm, ← mul_assoc, ← pow_succ', Nat.sub_one, Nat.succ_pred_eq_of_pos hp]

/-- Euler's product formula for the totient function. -/
theorem totient_eq_div_primeFactors_mul (n : ℕ) :
    φ n = (n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p - 1) := by
  rw [← mul_div_left n.totient, totient_mul_prod_primeFactors, mul_comm,
    Nat.mul_div_assoc _ (prod_primeFactors_dvd n), mul_comm]
  exact prod_pos (fun p => pos_of_mem_primeFactors)

/-- Euler's product formula for the totient function. -/
theorem totient_eq_mul_prod_factors (n : ℕ) :
    (φ n : ℚ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n : ℚ) ≠ 0 := by simp [hn]
  have hpQ : (∏ p ∈ n.primeFactors, (p : ℚ)) ≠ 0 := by
    rw [← cast_prod, cast_ne_zero, ← zero_lt_iff, prod_primeFactors_prod_factorization]
    exact prod_pos fun p hp => pos_of_mem_primeFactors hp
  simp only [totient_eq_div_primeFactors_mul n, prod_primeFactors_dvd n, cast_mul, cast_prod,
    cast_div_charZero, mul_comm_div, mul_right_inj' hn', div_eq_iff hpQ, ← prod_mul_distrib]
  refine prod_congr rfl fun p hp => ?_
  have hp := pos_of_mem_primeFactorsList (List.mem_toFinset.mp hp)
  have hp' : (p : ℚ) ≠ 0 := cast_ne_zero.mpr hp.ne.symm
  rw [sub_mul, one_mul, mul_comm, mul_inv_cancel₀ hp', cast_pred hp]

theorem totient_gcd_mul_totient_mul (a b : ℕ) : φ (a.gcd b) * φ (a * b) = φ a * φ b * a.gcd b := by
  have shuffle :
    ∀ a1 a2 b1 b2 c1 c2 : ℕ,
      b1 ∣ a1 → b2 ∣ a2 → a1 / b1 * c1 * (a2 / b2 * c2) = a1 * a2 / (b1 * b2) * (c1 * c2) := by
    intro a1 a2 b1 b2 c1 c2 h1 h2
    calc
      a1 / b1 * c1 * (a2 / b2 * c2) = a1 / b1 * (a2 / b2) * (c1 * c2) := by apply mul_mul_mul_comm
      _ = a1 * a2 / (b1 * b2) * (c1 * c2) := by
        congr 1
        exact div_mul_div_comm h1 h2
  simp only [totient_eq_div_primeFactors_mul]
  rw [shuffle, shuffle]
  rotate_left
  repeat' apply prod_primeFactors_dvd
  simp only [prod_primeFactors_gcd_mul_prod_primeFactors_mul]
  rw [eq_comm, mul_comm, ← mul_assoc, ← Nat.mul_div_assoc]
  exact mul_dvd_mul (prod_primeFactors_dvd a) (prod_primeFactors_dvd b)

theorem totient_super_multiplicative (a b : ℕ) : φ a * φ b ≤ φ (a * b) := by
  let d := a.gcd b
  rcases (zero_le a).eq_or_lt with (rfl | ha0)
  · simp
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ ha0
  apply le_of_mul_le_mul_right _ hd0
  rw [← totient_gcd_mul_totient_mul a b, mul_comm]
  apply mul_le_mul_left' (Nat.totient_le d)

theorem totient_dvd_of_dvd {a b : ℕ} (h : a ∣ b) : φ a ∣ φ b := by
  rcases eq_or_ne a 0 with (rfl | ha0)
  · simp [zero_dvd_iff.1 h]
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  have hab' := primeFactors_mono h hb0
  rw [totient_eq_prod_factorization ha0, totient_eq_prod_factorization hb0]
  refine Finsupp.prod_dvd_prod_of_subset_of_dvd hab' fun p _ => mul_dvd_mul ?_ dvd_rfl
  exact pow_dvd_pow p (tsub_le_tsub_right ((factorization_le_iff_dvd ha0 hb0).2 h p) 1)

theorem totient_mul_of_prime_of_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) :
    (p * n).totient = p * n.totient := by
  have h1 := totient_gcd_mul_totient_mul p n
  rw [gcd_eq_left h, mul_assoc] at h1
  simpa [(totient_pos.2 hp.pos).ne', mul_comm] using h1

theorem totient_mul_of_prime_of_not_dvd {p n : ℕ} (hp : p.Prime) (h : ¬p ∣ n) :
    (p * n).totient = (p - 1) * n.totient := by
  rw [totient_mul _, totient_prime hp]
  simpa [h] using coprime_or_dvd_of_prime hp n

end Nat
