/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Monotonicity

#align_import data.nat.totient from "leanprover-community/mathlib"@"5cc2dfdd3e92f340411acea4427d701dc7ed26f8"

/-!
# Euler's totient function

This file defines [Euler's totient function](https://en.wikipedia.org/wiki/Euler's_totient_function)
`Nat.totient n` which counts the number of naturals less than `n` that are coprime with `n`.
We prove the divisor sum formula, namely that `n` equals `φ` summed over the divisors of `n`. See
`sum_totient`. We also prove two lemmas to help compute totients, namely `totient_mul` and
`totient_prime_pow`.
-/

open Finset

open BigOperators

namespace Nat

/-- Euler's totient function. This counts the number of naturals strictly less than `n` which are
coprime with `n`. -/
def totient (n : ℕ) : ℕ :=
  ((range n).filter n.coprime).card
#align nat.totient Nat.totient

@[inherit_doc]
scoped notation "φ" => Nat.totient

@[simp]
theorem totient_zero : φ 0 = 0 :=
  rfl
#align nat.totient_zero Nat.totient_zero

@[simp]
theorem totient_one : φ 1 = 1 := by simp [totient]
                                    -- 🎉 no goals
#align nat.totient_one Nat.totient_one

theorem totient_eq_card_coprime (n : ℕ) : φ n = ((range n).filter n.coprime).card :=
  rfl
#align nat.totient_eq_card_coprime Nat.totient_eq_card_coprime

/-- A characterisation of `Nat.totient` that avoids `Finset`. -/
theorem totient_eq_card_lt_and_coprime (n : ℕ) : φ n = Nat.card { m | m < n ∧ n.coprime m } := by
  let e : { m | m < n ∧ n.coprime m } ≃ Finset.filter n.coprime (Finset.range n) :=
    { toFun := fun m => ⟨m, by simpa only [Finset.mem_filter, Finset.mem_range] using m.property⟩
      invFun := fun m => ⟨m, by simpa only [Finset.mem_filter, Finset.mem_range] using m.property⟩
      left_inv := fun m => by simp only [Subtype.coe_mk, Subtype.coe_eta]
      right_inv := fun m => by simp only [Subtype.coe_mk, Subtype.coe_eta] }
  rw [totient_eq_card_coprime, card_congr e, card_eq_fintype_card, Fintype.card_coe]
  -- 🎉 no goals
#align nat.totient_eq_card_lt_and_coprime Nat.totient_eq_card_lt_and_coprime

theorem totient_le (n : ℕ) : φ n ≤ n :=
  ((range n).card_filter_le _).trans_eq (card_range n)
#align nat.totient_le Nat.totient_le

theorem totient_lt (n : ℕ) (hn : 1 < n) : φ n < n :=
  (card_lt_card (filter_ssubset.2 ⟨0, by simp [hn.ne', pos_of_gt hn]⟩)).trans_eq (card_range n)
                                         -- 🎉 no goals
#align nat.totient_lt Nat.totient_lt

theorem totient_pos : ∀ {n : ℕ}, 0 < n → 0 < φ n
  | 0 => by decide
            -- 🎉 no goals
  | 1 => by simp [totient]
            -- 🎉 no goals
  | n + 2 => fun _ => card_pos.2 ⟨1, mem_filter.2 ⟨mem_range.2 (by simp), coprime_one_right _⟩⟩
                                                                   -- 🎉 no goals
#align nat.totient_pos Nat.totient_pos

theorem filter_coprime_Ico_eq_totient (a n : ℕ) :
    ((Ico n (n + a)).filter (coprime a)).card = totient a := by
  rw [totient, filter_Ico_card_eq_of_periodic, count_eq_card_filter_range]
  -- ⊢ Function.Periodic (coprime a) a
  exact periodic_coprime a
  -- 🎉 no goals
#align nat.filter_coprime_Ico_eq_totient Nat.filter_coprime_Ico_eq_totient

theorem Ico_filter_coprime_le {a : ℕ} (k n : ℕ) (a_pos : 0 < a) :
    ((Ico k (k + n)).filter (coprime a)).card ≤ totient a * (n / a + 1) := by
  conv_lhs => rw [← Nat.mod_add_div n a]
  -- ⊢ card (filter (coprime a) (Ico k (k + (n % a + a * (n / a))))) ≤ φ a * (n / a …
  induction' n / a with i ih
  -- ⊢ card (filter (coprime a) (Ico k (k + (n % a + a * zero)))) ≤ φ a * (zero + 1)
  · rw [← filter_coprime_Ico_eq_totient a k]
    -- ⊢ card (filter (coprime a) (Ico k (k + (n % a + a * zero)))) ≤ card (filter (c …
    simp only [add_zero, mul_one, mul_zero, le_of_lt (mod_lt n a_pos),
      Nat.zero_eq, zero_add]
    --Porting note: below line was `mono`
    refine Finset.card_mono ?_
    -- ⊢ filter (coprime a) (Ico k (k + n % a)) ≤ filter (coprime a) (Ico k (k + a))
    refine' monotone_filter_left a.coprime _
    -- ⊢ Ico k (k + n % a) ≤ Ico k (k + a)
    simp only [Finset.le_eq_subset]
    -- ⊢ Ico k (k + n % a) ⊆ Ico k (k + a)
    exact Ico_subset_Ico rfl.le (add_le_add_left (le_of_lt (mod_lt n a_pos)) k)
    -- 🎉 no goals
  simp only [mul_succ]
  -- ⊢ card (filter (coprime a) (Ico k (k + (n % a + (a * i + a))))) ≤ φ a * i + φ  …
  simp_rw [← add_assoc] at ih ⊢
  -- ⊢ card (filter (coprime a) (Ico k (k + n % a + a * i + a))) ≤ φ a * i + φ a +  …
  calc
    (filter a.coprime (Ico k (k + n % a + a * i + a))).card = (filter a.coprime
        (Ico k (k + n % a + a * i) ∪ Ico (k + n % a + a * i) (k + n % a + a * i + a))).card := by
      congr
      rw [Ico_union_Ico_eq_Ico]
      rw [add_assoc]
      exact le_self_add
      exact le_self_add
    _ ≤ (filter a.coprime (Ico k (k + n % a + a * i))).card + a.totient := by
      rw [filter_union, ← filter_coprime_Ico_eq_totient a (k + n % a + a * i)]
      apply card_union_le
    _ ≤ a.totient * i + a.totient + a.totient := add_le_add_right ih (totient a)
#align nat.Ico_filter_coprime_le Nat.Ico_filter_coprime_le

open ZMod

/-- Note this takes an explicit `Fintype ((ZMod n)ˣ)` argument to avoid trouble with instance
diamonds. -/
@[simp]
theorem _root_.ZMod.card_units_eq_totient (n : ℕ) [NeZero n] [Fintype (ZMod n)ˣ] :
    Fintype.card (ZMod n)ˣ = φ n :=
  calc
    Fintype.card (ZMod n)ˣ = Fintype.card { x : ZMod n // x.val.coprime n } :=
      Fintype.card_congr ZMod.unitsEquivCoprime
    _ = φ n := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := exists_eq_succ_of_ne_zero NeZero.out
      -- ⊢ Fintype.card { x // coprime (ZMod.val x) (m + 1) } = φ (m + 1)
      simp only [totient, Finset.card_eq_sum_ones, Fintype.card_subtype, Finset.sum_filter, ←
        Fin.sum_univ_eq_sum_range, @Nat.coprime_comm (m + 1)]
      rfl
      -- 🎉 no goals
#align zmod.card_units_eq_totient ZMod.card_units_eq_totient

theorem totient_even {n : ℕ} (hn : 2 < n) : Even n.totient := by
  haveI : Fact (1 < n) := ⟨one_lt_two.trans hn⟩
  -- ⊢ Even (φ n)
  haveI : NeZero n := NeZero.of_gt hn
  -- ⊢ Even (φ n)
  suffices 2 = orderOf (-1 : (ZMod n)ˣ) by
    rw [← ZMod.card_units_eq_totient, even_iff_two_dvd, this]
    exact orderOf_dvd_card_univ
  rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one, ringChar.eq (ZMod n) n, if_neg hn.ne']
  -- 🎉 no goals
#align nat.totient_even Nat.totient_even

theorem totient_mul {m n : ℕ} (h : m.coprime n) : φ (m * n) = φ m * φ n :=
  if hmn0 : m * n = 0 then by
    cases' Nat.mul_eq_zero.1 hmn0 with h h <;>
    -- ⊢ φ (m * n) = φ m * φ n
      simp only [totient_zero, mul_zero, zero_mul, h]
      -- 🎉 no goals
      -- 🎉 no goals
  else by
    haveI : NeZero (m * n) := ⟨hmn0⟩
    -- ⊢ φ (m * n) = φ m * φ n
    haveI : NeZero m := ⟨left_ne_zero_of_mul hmn0⟩
    -- ⊢ φ (m * n) = φ m * φ n
    haveI : NeZero n := ⟨right_ne_zero_of_mul hmn0⟩
    -- ⊢ φ (m * n) = φ m * φ n
    simp only [← ZMod.card_units_eq_totient]
    -- ⊢ Fintype.card (ZMod (m * n))ˣ = Fintype.card (ZMod m)ˣ * Fintype.card (ZMod n)ˣ
    rw [Fintype.card_congr (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).toEquiv,
      Fintype.card_congr (@MulEquiv.prodUnits (ZMod m) (ZMod n) _ _).toEquiv, Fintype.card_prod]
#align nat.totient_mul Nat.totient_mul

/-- For `d ∣ n`, the totient of `n/d` equals the number of values `k < n` such that `gcd n k = d` -/
theorem totient_div_of_dvd {n d : ℕ} (hnd : d ∣ n) :
    φ (n / d) = (filter (fun k : ℕ => n.gcd k = d) (range n)).card := by
  rcases d.eq_zero_or_pos with (rfl | hd0); · simp [eq_zero_of_zero_dvd hnd]
  -- ⊢ φ (n / 0) = Finset.card (filter (fun k => gcd n k = 0) (range n))
                                              -- 🎉 no goals
  rcases hnd with ⟨x, rfl⟩
  -- ⊢ φ (d * x / d) = Finset.card (filter (fun k => gcd (d * x) k = d) (range (d * …
  rw [Nat.mul_div_cancel_left x hd0]
  -- ⊢ φ x = Finset.card (filter (fun k => gcd (d * x) k = d) (range (d * x)))
  apply Finset.card_congr fun k _ => d * k
  · simp only [mem_filter, mem_range, and_imp, coprime]
    -- ⊢ ∀ (a : ℕ), a < x → gcd x a = 1 → d * a < d * x ∧ gcd (d * x) (d * a) = d
    refine' fun a ha1 ha2 => ⟨(mul_lt_mul_left hd0).2 ha1, _⟩
    -- ⊢ gcd (d * x) (d * a) = d
    rw [gcd_mul_left, ha2, mul_one]
    -- 🎉 no goals
  · simp [hd0.ne']
    -- 🎉 no goals
  · simp only [mem_filter, mem_range, exists_prop, and_imp]
    -- ⊢ ∀ (b : ℕ), b < d * x → gcd (d * x) b = d → ∃ a, (a < x ∧ coprime x a) ∧ d *  …
    refine' fun b hb1 hb2 => _
    -- ⊢ ∃ a, (a < x ∧ coprime x a) ∧ d * a = b
    have : d ∣ b := by
      rw [← hb2]
      apply gcd_dvd_right
    rcases this with ⟨q, rfl⟩
    -- ⊢ ∃ a, (a < x ∧ coprime x a) ∧ d * a = d * q
    refine' ⟨q, ⟨⟨(mul_lt_mul_left hd0).1 hb1, _⟩, rfl⟩⟩
    -- ⊢ coprime x q
    rwa [gcd_mul_left, mul_right_eq_self_iff hd0] at hb2
    -- 🎉 no goals
#align nat.totient_div_of_dvd Nat.totient_div_of_dvd

theorem sum_totient (n : ℕ) : n.divisors.sum φ = n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  -- ⊢ Finset.sum (divisors 0) φ = 0
  · simp
    -- 🎉 no goals
  rw [← sum_div_divisors n φ]
  -- ⊢ ∑ d in divisors n, φ (n / d) = n
  have : n = ∑ d : ℕ in n.divisors, (filter (fun k : ℕ => n.gcd k = d) (range n)).card := by
    nth_rw 1 [← card_range n]
    refine' card_eq_sum_card_fiberwise fun x _ => mem_divisors.2 ⟨_, hn.ne'⟩
    apply gcd_dvd_left
  nth_rw 3 [this]
  -- ⊢ ∑ d in divisors n, φ (n / d) = ∑ d in divisors n, Finset.card (filter (fun k …
  exact sum_congr rfl fun x hx => totient_div_of_dvd (dvd_of_mem_divisors hx)
  -- 🎉 no goals
#align nat.sum_totient Nat.sum_totient

theorem sum_totient' (n : ℕ) : (∑ m in (range n.succ).filter (· ∣ n), φ m) = n := by
  convert sum_totient _ using 1
  -- ⊢ ∑ m in filter (fun x => x ∣ n) (range (succ n)), φ m = Finset.sum (divisors  …
  simp only [Nat.divisors, sum_filter, range_eq_Ico]
  -- ⊢ (∑ a in Ico 0 (succ n), if a ∣ n then φ a else 0) = ∑ a in Ico 1 (n + 1), if …
  rw [sum_eq_sum_Ico_succ_bot] <;> simp
  -- ⊢ ((if 0 ∣ n then φ 0 else 0) + ∑ k in Ico (0 + 1) (succ n), if k ∣ n then φ k …
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align nat.sum_totient' Nat.sum_totient'

/-- When `p` is prime, then the totient of `p ^ (n + 1)` is `p ^ n * (p - 1)` -/
theorem totient_prime_pow_succ {p : ℕ} (hp : p.Prime) (n : ℕ) : φ (p ^ (n + 1)) = p ^ n * (p - 1) :=
  calc
    φ (p ^ (n + 1)) = ((range (p ^ (n + 1))).filter (coprime (p ^ (n + 1)))).card :=
      totient_eq_card_coprime _
    _ = (range (p ^ (n + 1)) \ (range (p ^ n)).image (· * p)).card :=
      (congr_arg card
        (by
          rw [sdiff_eq_filter]
          -- ⊢ filter (coprime (p ^ (n + 1))) (range (p ^ (n + 1))) = filter (fun x => ¬x ∈ …
          apply filter_congr
          -- ⊢ ∀ (x : ℕ), x ∈ range (p ^ (n + 1)) → (coprime (p ^ (n + 1)) x ↔ ¬x ∈ image ( …
          simp only [mem_range, mem_filter, coprime_pow_left_iff n.succ_pos, mem_image, not_exists,
            hp.coprime_iff_not_dvd]
          intro a ha
          -- ⊢ ¬p ∣ a ↔ ∀ (x : ℕ), ¬(x < p ^ n ∧ x * p = a)
          constructor
          -- ⊢ ¬p ∣ a → ∀ (x : ℕ), ¬(x < p ^ n ∧ x * p = a)
          · intro hap b h; rcases h with ⟨_, rfl⟩
            -- ⊢ False
                           -- ⊢ False
            exact hap (dvd_mul_left _ _)
            -- 🎉 no goals
          · rintro h ⟨b, rfl⟩
            -- ⊢ False
            rw [pow_succ'] at ha
            -- ⊢ False
            exact h b ⟨lt_of_mul_lt_mul_left ha (zero_le _), mul_comm _ _⟩))
            -- 🎉 no goals
    _ = _ := by
      have h1 : Function.Injective (· * p) := mul_left_injective₀ hp.ne_zero
      -- ⊢ Finset.card (range (p ^ (n + 1)) \ image (fun x => x * p) (range (p ^ n))) = …
      have h2 : (range (p ^ n)).image (· * p) ⊆ range (p ^ (n + 1)) := fun a => by
        simp only [mem_image, mem_range, exists_imp]
        rintro b ⟨h, rfl⟩
        rw [pow_succ]
        exact (mul_lt_mul_right hp.pos).2 h
      rw [card_sdiff h2, card_image_of_injOn (h1.injOn _), card_range, card_range, ←
        one_mul (p ^ n), pow_succ', ← tsub_mul, one_mul, mul_comm]
#align nat.totient_prime_pow_succ Nat.totient_prime_pow_succ

/-- When `p` is prime, then the totient of `p ^ n` is `p ^ (n - 1) * (p - 1)` -/
theorem totient_prime_pow {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) :
    φ (p ^ n) = p ^ (n - 1) * (p - 1) := by
  rcases exists_eq_succ_of_ne_zero (pos_iff_ne_zero.1 hn) with ⟨m, rfl⟩
  -- ⊢ φ (p ^ succ m) = p ^ (succ m - 1) * (p - 1)
  exact totient_prime_pow_succ hp _
  -- 🎉 no goals
#align nat.totient_prime_pow Nat.totient_prime_pow

theorem totient_prime {p : ℕ} (hp : p.Prime) : φ p = p - 1 := by
  rw [← pow_one p, totient_prime_pow hp] <;> simp
  -- ⊢ p ^ (1 - 1) * (p - 1) = p ^ 1 - 1
                                             -- 🎉 no goals
                                             -- 🎉 no goals
#align nat.totient_prime Nat.totient_prime

theorem totient_eq_iff_prime {p : ℕ} (hp : 0 < p) : p.totient = p - 1 ↔ p.Prime := by
  refine' ⟨fun h => _, totient_prime⟩
  -- ⊢ Prime p
  replace hp : 1 < p
  -- ⊢ 1 < p
  · apply lt_of_le_of_ne
    -- ⊢ 1 ≤ p
    · rwa [succ_le_iff]
      -- 🎉 no goals
    · rintro rfl
      -- ⊢ False
      rw [totient_one, tsub_self] at h
      -- ⊢ False
      exact one_ne_zero h
      -- 🎉 no goals
  rw [totient_eq_card_coprime, range_eq_Ico, ← Ico_insert_succ_left hp.le, Finset.filter_insert,
    if_neg (not_coprime_of_dvd_of_dvd hp (dvd_refl p) (dvd_zero p)), ← Nat.card_Ico 1 p] at h
  refine'
    p.prime_of_coprime hp fun n hn hnz => Finset.filter_card_eq h n <| Finset.mem_Ico.mpr ⟨_, hn⟩
  rwa [succ_le_iff, pos_iff_ne_zero]
  -- 🎉 no goals
#align nat.totient_eq_iff_prime Nat.totient_eq_iff_prime

theorem card_units_zmod_lt_sub_one {p : ℕ} (hp : 1 < p) [Fintype (ZMod p)ˣ] :
    Fintype.card (ZMod p)ˣ ≤ p - 1 := by
  haveI : NeZero p := ⟨(pos_of_gt hp).ne'⟩
  -- ⊢ Fintype.card (ZMod p)ˣ ≤ p - 1
  rw [ZMod.card_units_eq_totient p]
  -- ⊢ φ p ≤ p - 1
  exact Nat.le_pred_of_lt (Nat.totient_lt p hp)
  -- 🎉 no goals
#align nat.card_units_zmod_lt_sub_one Nat.card_units_zmod_lt_sub_one

theorem prime_iff_card_units (p : ℕ) [Fintype (ZMod p)ˣ] :
    p.Prime ↔ Fintype.card (ZMod p)ˣ = p - 1 := by
  cases' eq_zero_or_neZero p with hp hp
  -- ⊢ Prime p ↔ Fintype.card (ZMod p)ˣ = p - 1
  · subst hp
    -- ⊢ Prime 0 ↔ Fintype.card (ZMod 0)ˣ = 0 - 1
    simp only [ZMod, not_prime_zero, false_iff_iff, zero_tsub]
    -- ⊢ ¬Fintype.card ℤˣ = 0
    -- the subst created a non-defeq but subsingleton instance diamond; resolve it
    suffices Fintype.card ℤˣ ≠ 0 by convert this
    -- ⊢ Fintype.card ℤˣ ≠ 0
    simp
    -- 🎉 no goals
  rw [ZMod.card_units_eq_totient, Nat.totient_eq_iff_prime <| NeZero.pos p]
  -- 🎉 no goals
#align nat.prime_iff_card_units Nat.prime_iff_card_units

@[simp]
theorem totient_two : φ 2 = 1 :=
  (totient_prime prime_two).trans rfl
#align nat.totient_two Nat.totient_two

theorem totient_eq_one_iff : ∀ {n : ℕ}, n.totient = 1 ↔ n = 1 ∨ n = 2
  | 0 => by simp
            -- 🎉 no goals
  | 1 => by simp
            -- 🎉 no goals
  | 2 => by simp
            -- 🎉 no goals
  | n + 3 => by
    have : 3 ≤ n + 3 := le_add_self
    -- ⊢ φ (n + 3) = 1 ↔ n + 3 = 1 ∨ n + 3 = 2
    simp only [succ_succ_ne_one, false_or_iff]
    -- ⊢ φ (n + 3) = 1 ↔ n + 3 = 2
    exact ⟨fun h => not_even_one.elim <| h ▸ totient_even this, by rintro ⟨⟩⟩
    -- 🎉 no goals
#align nat.totient_eq_one_iff Nat.totient_eq_one_iff

/-! ### Euler's product formula for the totient function

We prove several different statements of this formula. -/


/-- Euler's product formula for the totient function. -/
theorem totient_eq_prod_factorization {n : ℕ} (hn : n ≠ 0) :
    φ n = n.factorization.prod fun p k => p ^ (k - 1) * (p - 1) := by
  rw [multiplicative_factorization φ (@totient_mul) totient_one hn]
  -- ⊢ (Finsupp.prod (factorization n) fun p k => φ (p ^ k)) = Finsupp.prod (factor …
  apply Finsupp.prod_congr _
  -- ⊢ ∀ (x : ℕ), x ∈ (factorization n).support → φ (x ^ ↑(factorization n) x) = x  …
  intro p hp
  -- ⊢ φ (p ^ ↑(factorization n) p) = p ^ (↑(factorization n) p - 1) * (p - 1)
  have h := zero_lt_iff.mpr (Finsupp.mem_support_iff.mp hp)
  -- ⊢ φ (p ^ ↑(factorization n) p) = p ^ (↑(factorization n) p - 1) * (p - 1)
  rw [totient_prime_pow (prime_of_mem_factorization hp) h]
  -- 🎉 no goals
#align nat.totient_eq_prod_factorization Nat.totient_eq_prod_factorization

/-- Euler's product formula for the totient function. -/
theorem totient_mul_prod_factors (n : ℕ) :
    (φ n * ∏ p in n.factors.toFinset, p) = n * ∏ p in n.factors.toFinset, (p - 1) := by
  by_cases hn : n = 0; · simp [hn]
  -- ⊢ φ n * ∏ p in List.toFinset (factors n), p = n * ∏ p in List.toFinset (factor …
                         -- 🎉 no goals
  rw [totient_eq_prod_factorization hn]
  -- ⊢ (Finsupp.prod (factorization n) fun p k => p ^ (k - 1) * (p - 1)) * ∏ p in L …
  nth_rw 3 [← factorization_prod_pow_eq_self hn]
  -- ⊢ (Finsupp.prod (factorization n) fun p k => p ^ (k - 1) * (p - 1)) * ∏ p in L …
  simp only [← prod_factorization_eq_prod_factors, ← Finsupp.prod_mul]
  -- ⊢ (Finsupp.prod (factorization n) fun a b => a ^ (b - 1) * (a - 1) * a) = Fins …
  refine' Finsupp.prod_congr (M := ℕ) (N := ℕ) fun p hp => _
  -- ⊢ p ^ (↑(factorization n) p - 1) * (p - 1) * p = p ^ ↑(factorization n) p * (p …
  rw [Finsupp.mem_support_iff, ← zero_lt_iff] at hp
  -- ⊢ p ^ (↑(factorization n) p - 1) * (p - 1) * p = p ^ ↑(factorization n) p * (p …
  rw [mul_comm, ← mul_assoc, ← pow_succ', Nat.sub_one, Nat.succ_pred_eq_of_pos hp]
  -- 🎉 no goals
#align nat.totient_mul_prod_factors Nat.totient_mul_prod_factors

/-- Euler's product formula for the totient function. -/
theorem totient_eq_div_factors_mul (n : ℕ) :
    φ n = (n / ∏ p in n.factors.toFinset, p) * ∏ p in n.factors.toFinset, (p - 1) := by
  rw [← mul_div_left n.totient, totient_mul_prod_factors, mul_comm,
    Nat.mul_div_assoc _ (prod_prime_factors_dvd n), mul_comm]
  have := prod_pos (fun p => pos_of_mem_factorization (n := n))
  -- ⊢ 0 < ∏ p in List.toFinset (factors n), p
  simpa [prod_factorization_eq_prod_factors] using this
  -- 🎉 no goals
#align nat.totient_eq_div_factors_mul Nat.totient_eq_div_factors_mul

/-- Euler's product formula for the totient function. -/
theorem totient_eq_mul_prod_factors (n : ℕ) :
    (φ n : ℚ) = n * ∏ p in n.factors.toFinset, (1 - (p : ℚ)⁻¹) := by
  by_cases hn : n = 0
  -- ⊢ ↑(φ n) = ↑n * ∏ p in List.toFinset (factors n), (1 - (↑p)⁻¹)
  · simp [hn]
    -- 🎉 no goals
  have hn' : (n : ℚ) ≠ 0 := by simp [hn]
  -- ⊢ ↑(φ n) = ↑n * ∏ p in List.toFinset (factors n), (1 - (↑p)⁻¹)
  have hpQ : (∏ p in n.factors.toFinset, (p : ℚ)) ≠ 0 := by
    rw [← cast_prod, cast_ne_zero, ← zero_lt_iff, ← prod_factorization_eq_prod_factors]
    exact prod_pos fun p hp => pos_of_mem_factorization hp
  simp only [totient_eq_div_factors_mul n, prod_prime_factors_dvd n, cast_mul, cast_prod,
    cast_div_charZero, mul_comm_div, mul_right_inj' hn', div_eq_iff hpQ, ← prod_mul_distrib]
  refine' prod_congr rfl fun p hp => _
  -- ⊢ ↑(p - 1) = (1 - (↑p)⁻¹) * ↑p
  have hp := pos_of_mem_factors (List.mem_toFinset.mp hp)
  -- ⊢ ↑(p - 1) = (1 - (↑p)⁻¹) * ↑p
  have hp' : (p : ℚ) ≠ 0 := cast_ne_zero.mpr hp.ne.symm
  -- ⊢ ↑(p - 1) = (1 - (↑p)⁻¹) * ↑p
  rw [sub_mul, one_mul, mul_comm, mul_inv_cancel hp', cast_pred hp]
  -- 🎉 no goals
#align nat.totient_eq_mul_prod_factors Nat.totient_eq_mul_prod_factors

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
  simp only [totient_eq_div_factors_mul]
  -- ⊢ ((gcd a b / ∏ p in List.toFinset (factors (gcd a b)), p) * ∏ p in List.toFin …
  rw [shuffle, shuffle]
  rotate_left
  repeat' apply prod_prime_factors_dvd
  -- ⊢ gcd a b * (a * b) / ((∏ p in List.toFinset (factors (gcd a b)), p) * ∏ p in  …
  · simp only [prod_factors_gcd_mul_prod_factors_mul]
    -- ⊢ gcd a b * (a * b) / ((∏ p in List.toFinset (factors a), p) * ∏ p in List.toF …
    rw [eq_comm, mul_comm, ← mul_assoc, ← Nat.mul_div_assoc]
    -- ⊢ (∏ p in List.toFinset (factors a), p) * ∏ p in List.toFinset (factors b), p  …
    exact mul_dvd_mul (prod_prime_factors_dvd a) (prod_prime_factors_dvd b)
    -- 🎉 no goals
#align nat.totient_gcd_mul_totient_mul Nat.totient_gcd_mul_totient_mul

theorem totient_super_multiplicative (a b : ℕ) : φ a * φ b ≤ φ (a * b) := by
  let d := a.gcd b
  -- ⊢ φ a * φ b ≤ φ (a * b)
  rcases(zero_le a).eq_or_lt with (rfl | ha0)
  -- ⊢ φ 0 * φ b ≤ φ (0 * b)
  · simp
    -- 🎉 no goals
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ ha0
  -- ⊢ φ a * φ b ≤ φ (a * b)
  apply le_of_mul_le_mul_right _ hd0
  -- ⊢ φ a * φ b * d ≤ φ (a * b) * d
  rw [← totient_gcd_mul_totient_mul a b, mul_comm]
  -- ⊢ φ (a * b) * φ (gcd a b) ≤ φ (a * b) * d
  apply mul_le_mul_left' (Nat.totient_le d)
  -- 🎉 no goals
#align nat.totient_super_multiplicative Nat.totient_super_multiplicative

theorem totient_dvd_of_dvd {a b : ℕ} (h : a ∣ b) : φ a ∣ φ b := by
  rcases eq_or_ne a 0 with (rfl | ha0)
  -- ⊢ φ 0 ∣ φ b
  · simp [zero_dvd_iff.1 h]
    -- 🎉 no goals
  rcases eq_or_ne b 0 with (rfl | hb0)
  -- ⊢ φ a ∣ φ 0
  · simp
    -- 🎉 no goals
  have hab' : a.factorization.support ⊆ b.factorization.support := by
    intro p
    simp only [support_factorization, List.mem_toFinset]
    apply factors_subset_of_dvd h hb0
  rw [totient_eq_prod_factorization ha0, totient_eq_prod_factorization hb0]
  -- ⊢ (Finsupp.prod (factorization a) fun p k => p ^ (k - 1) * (p - 1)) ∣ Finsupp. …
  refine' Finsupp.prod_dvd_prod_of_subset_of_dvd hab' fun p _ => mul_dvd_mul _ dvd_rfl
  -- ⊢ p ^ (↑(factorization a) p - 1) ∣ p ^ (↑(factorization b) p - 1)
  exact pow_dvd_pow p (tsub_le_tsub_right ((factorization_le_iff_dvd ha0 hb0).2 h p) 1)
  -- 🎉 no goals
#align nat.totient_dvd_of_dvd Nat.totient_dvd_of_dvd

theorem totient_mul_of_prime_of_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) :
    (p * n).totient = p * n.totient := by
  have h1 := totient_gcd_mul_totient_mul p n
  -- ⊢ φ (p * n) = p * φ n
  rw [gcd_eq_left h, mul_assoc] at h1
  -- ⊢ φ (p * n) = p * φ n
  simpa [(totient_pos hp.pos).ne', mul_comm] using h1
  -- 🎉 no goals
#align nat.totient_mul_of_prime_of_dvd Nat.totient_mul_of_prime_of_dvd

theorem totient_mul_of_prime_of_not_dvd {p n : ℕ} (hp : p.Prime) (h : ¬p ∣ n) :
    (p * n).totient = (p - 1) * n.totient := by
  rw [totient_mul _, totient_prime hp]
  -- ⊢ coprime p n
  simpa [h] using coprime_or_dvd_of_prime hp n
  -- 🎉 no goals
#align nat.totient_mul_of_prime_of_not_dvd Nat.totient_mul_of_prime_of_not_dvd

end Nat
