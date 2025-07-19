/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shing Tak Lam, Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Digits.Defs


/-!
# Digits of a natural number

This provides lemma about the digits of natural numbers.
-/

namespace Nat

variable {n : ℕ}

theorem ofDigits_eq_sum_mapIdx_aux (b : ℕ) (l : List ℕ) :
    (l.zipWith ((fun a i : ℕ => a * b ^ (i + 1))) (List.range l.length)).sum =
      b * (l.zipWith (fun a i => a * b ^ i) (List.range l.length)).sum := by
  suffices
    l.zipWith (fun a i : ℕ => a * b ^ (i + 1)) (List.range l.length) =
      l.zipWith (fun a i=> b * (a * b ^ i)) (List.range l.length)
    by simp [this]
  congr; ext; simp [pow_succ]; ring

theorem ofDigits_eq_sum_mapIdx (b : ℕ) (L : List ℕ) :
    ofDigits b L = (L.mapIdx fun i a => a * b ^ i).sum := by
  rw [List.mapIdx_eq_zipIdx_map, List.zipIdx_eq_zip_range', List.map_zip_eq_zipWith,
    ofDigits_eq_foldr, ← List.range_eq_range']
  induction' L with hd tl hl
  · simp
  · simpa [List.range_succ_eq_map, List.zipWith_map_right, ofDigits_eq_sum_mapIdx_aux] using
      Or.inl hl

/-!
### Properties

This section contains various lemmas of properties relating to `digits` and `ofDigits`.
-/

theorem digits_len (b n : ℕ) (hb : 1 < b) (hn : n ≠ 0) : (b.digits n).length = b.log n + 1 := by
  induction' n using Nat.strong_induction_on with n IH
  rw [digits_eq_cons_digits_div hb hn, List.length]
  by_cases h : n / b = 0
  · simp [h]
    aesop
  · have : n / b < n := div_lt_self (Nat.pos_of_ne_zero hn) hb
    rw [IH _ this h, log_div_base, tsub_add_cancel_of_le]
    refine Nat.succ_le_of_lt (log_pos hb ?_)
    contrapose! h
    exact div_eq_of_lt h

theorem getLast_digit_ne_zero (b : ℕ) {m : ℕ} (hm : m ≠ 0) :
    (digits b m).getLast (digits_ne_nil_iff_ne_zero.mpr hm) ≠ 0 := by
  rcases b with (_ | _ | b)
  · cases m
    · cases hm rfl
    · simp
  · cases m
    · cases hm rfl
    simp only [zero_add, digits_one, List.getLast_replicate_succ]
    exact Nat.one_ne_zero
  revert hm
  induction m using Nat.strongRecOn with | ind n IH => ?_
  intro hn
  by_cases hnb : n < b + 2
  · simpa only [digits_of_lt (b + 2) n hn hnb]
  · rw [digits_getLast n (le_add_left 2 b)]
    refine IH _ (Nat.div_lt_self hn.bot_lt (one_lt_succ_succ b)) ?_
    rw [← pos_iff_ne_zero]
    exact Nat.div_pos (le_of_not_gt hnb) (zero_lt_succ (succ b))

theorem digits_append_digits {b m n : ℕ} (hb : 0 < b) :
    digits b n ++ digits b m = digits b (n + b ^ (digits b n).length * m) := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hb) with (rfl | hb)
  · simp
  rw [← ofDigits_digits_append_digits]
  refine (digits_ofDigits b hb _ (fun l hl => ?_) (fun h_append => ?_)).symm
  · rcases (List.mem_append.mp hl) with (h | h) <;> exact digits_lt_base hb h
  · by_cases h : digits b m = []
    · simp only [h, List.append_nil] at h_append ⊢
      exact getLast_digit_ne_zero b <| digits_ne_nil_iff_ne_zero.mp h_append
    · exact (List.getLast_append_of_right_ne_nil _ _ h) ▸
          (getLast_digit_ne_zero _ <| digits_ne_nil_iff_ne_zero.mp h)

theorem digits_append_zeroes_append_digits {b k m n : ℕ} (hb : 1 < b) (hm : 0 < m) :
    digits b n ++ List.replicate k 0 ++ digits b m =
    digits b (n + b ^ ((digits b n).length + k) * m) := by
  rw [List.append_assoc, ← digits_base_pow_mul hb hm]
  simp only [digits_append_digits (zero_lt_of_lt hb), digits_inj_iff, add_right_inj]
  ring

theorem digits_len_le_digits_len_succ (b n : ℕ) :
    (digits b n).length ≤ (digits b (n + 1)).length := by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  · simp
  rcases le_or_gt b 1 with hb | hb
  · interval_cases b <;> simp +arith [digits_zero_succ', hn]
  simpa [digits_len, hb, hn] using log_mono_right (le_succ _)

theorem le_digits_len_le (b n m : ℕ) (h : n ≤ m) : (digits b n).length ≤ (digits b m).length :=
  monotone_nat_of_le_succ (digits_len_le_digits_len_succ b) h

theorem pow_length_le_mul_ofDigits {b : ℕ} {l : List ℕ} (hl : l ≠ []) (hl2 : l.getLast hl ≠ 0) :
    (b + 2) ^ l.length ≤ (b + 2) * ofDigits (b + 2) l := by
  rw [← List.dropLast_append_getLast hl]
  simp only [List.length_append, List.length, zero_add, List.length_dropLast, ofDigits_append,
    List.length_dropLast, ofDigits_singleton, add_comm (l.length - 1), pow_add, pow_one]
  apply Nat.mul_le_mul_left
  refine le_trans ?_ (Nat.le_add_left _ _)
  have : 0 < l.getLast hl := by rwa [pos_iff_ne_zero]
  convert Nat.mul_le_mul_left ((b + 2) ^ (l.length - 1)) this using 1
  rw [Nat.mul_one]

/-- Any non-zero natural number `m` is greater than
(b+2)^((number of digits in the base (b+2) representation of m) - 1)
-/
theorem base_pow_length_digits_le' (b m : ℕ) (hm : m ≠ 0) :
    (b + 2) ^ (digits (b + 2) m).length ≤ (b + 2) * m := by
  have : digits (b + 2) m ≠ [] := digits_ne_nil_iff_ne_zero.mpr hm
  convert @pow_length_le_mul_ofDigits b (digits (b+2) m)
    this (getLast_digit_ne_zero _ hm)
  rw [ofDigits_digits]

/-- Any non-zero natural number `m` is greater than
b^((number of digits in the base b representation of m) - 1)
-/
theorem base_pow_length_digits_le (b m : ℕ) (hb : 1 < b) :
    m ≠ 0 → b ^ (digits b m).length ≤ b * m := by
  rcases b with (_ | _ | b) <;> try simp_all
  exact base_pow_length_digits_le' b m

/-- The sum of the digits of a number less than its base is the number itself.
-/
@[simp]
theorem digits_sum_eq_self {x b : ℕ} (hxb : x < b) : (b.digits x).sum = x := by
  by_cases x_eq : x = 0
  · simp [x_eq]
  simp [Nat.digits_of_lt b x x_eq hxb]

/-- Multiplying by the base does not change the digit sum.
-/
@[simp]
theorem digits_sum_base_mul_cancel {n b : ℕ} (pos_b : 0 < b) :
    (b.digits (b * n)).sum = (b.digits n).sum := by
  obtain _ | n := n
  · simp
  by_cases hb : b = 1
  · simp [hb]
  push_neg at hb
  conv_lhs => rhs; rhs; rw [<- pow_one b]
  rw [Nat.digits_base_pow_mul (Nat.lt_of_le_of_ne pos_b hb.symm)
    (zero_lt_succ n)]
  simp

/-- Closed form formula for summing digit sums up to a power of the base. This
is equivalent to applying Gauss's formula across digit columns.
-/
theorem sum_digit_sum_base_pow_eq {k b : ℕ} :
    2 * ∑ n ∈ Finset.range (b^k), (b.digits n).sum = (b-1) * k * b^k := by
  by_cases k0 : k = 0
  · simp [mul_comm, k0]
  by_cases hb : b = 0 ∨ b = 1
  · rcases hb with (h | h) <;> simp [h, k0]
  replace hb : 1 < b := by omega
  have sum_sum_digits : 2 * ∑ x ∈ Finset.range b, (b.digits x).sum = b * (b - 1) := by
    rw [mul_comm, <- Finset.sum_range_id_mul_two]
    congr! with x x_in
    simp at x_in
    simp [digits_sum_eq_self x_in]
  induction' k, (by omega : 1 ≤ k) using Nat.le_induction with m pos_m ih
  · simp [sum_sum_digits, mul_comm]
  · specialize ih (Nat.ne_zero_of_lt pos_m)
    have digits_eq_cons := Nat.digits_eq_cons_digits_div
      hb (by positivity)
    have pos_n : ∀ n ∈ Finset.Ico 1 (b^m), 0 < n := by
      intro n n_in
      simp at n_in
      exact n_in.left
    have sum_pow_add_eq_sum_pair {f : ℕ → ℕ} {i j b : ℕ} :
      ∑ x ∈ Finset.range (b^(i+j)), f x =
      ∑ p ∈ Finset.range (b^i) ×ˢ Finset.range (b^j),
        f (b^j * p.fst + p.snd) := by
      have sum_range_mul_eq_sum_pair (i j) : ∑ x ∈ Finset.range (i*j), f x =
        ∑ p ∈ Finset.range i ×ˢ Finset.range j, f (j * p.fst + p.snd) := by
        have sum_add_eq_sum_pair : ∑ x : Fin (i * j), f x =
          ∑ p : Fin i × Fin j, f (j * p.fst + p.snd : ℕ) := by
          simp [add_comm, <- Equiv.sum_comp (e := finProdFinEquiv)]
        simp [sum_add_eq_sum_pair, Finset.sum_range, Fintype.sum_prod_type,
          Finset.sum_product]
      convert sum_range_mul_eq_sum_pair (b^i) (b^j) using 1
      rw [<- Nat.pow_add]
    rw [sum_pow_add_eq_sum_pair]
    have : ∑ p ∈ Finset.range (b ^ m) ×ˢ Finset.range b, (Nat.digits b (b * p.fst + p.snd)).sum =
        ∑ p ∈ Finset.range (b ^ m) ×ˢ Finset.range b,
        ((Nat.digits b (b * p.fst)).sum + (Nat.digits b p.snd).sum) := by
      apply Finset.sum_congr rfl
      intro p hp
      have h : p.snd < b := by
        rw [Finset.mem_product] at hp
        exact Finset.mem_range.mp hp.right
      have digit_sum_add_single_digit (n d : ℕ) (hd : d < b) :
        (Nat.digits b (b * n + d)).sum = (Nat.digits b (b * n)).sum + (Nat.digits b d).sum := by
        rcases d
        · simp
        · rw [add_comm, Nat.digits_add b hb _ _ hd (by omega)]
          simp [add_comm, List.sum_cons, digits_sum_eq_self hd]
          symm
          exact digits_sum_base_mul_cancel (Nat.zero_lt_of_lt hb)
      exact digit_sum_add_single_digit p.1 p.2 h
    simp [this]
    clear this
    rw [@Finset.sum_product]
    simp [Finset.sum_add_distrib, mul_add, <- Finset.mul_sum]
    conv_lhs => rhs; rw [<- mul_assoc, mul_comm 2, mul_assoc, sum_sum_digits]
    simp [digits_sum_base_mul_cancel (Nat.zero_lt_of_lt hb)]
    rw [<- mul_assoc, mul_comm 2, mul_assoc, ih]
    ring

/-- A specialization of `sum_digit_sum_base_pow_eq` to base 10.
-/
theorem sum_digit_sum_ten_pow_eq {k : ℕ} :
  (∑ n ∈ Finset.range (10^k), (Nat.digits 10 n).sum) =
    45 * k * 10^(k-1) := by
  by_cases pos_k : k = 0
  · simp [pos_k]
  replace pos_k : 0 < k := by omega
  have := @sum_digit_sum_base_pow_eq k 10
  have : ∑ n ∈ Finset.range (10 ^ k), (Nat.digits 10 n).sum = (10 - 1) * k * 10 ^ k / 2 := by
    omega
  rw [this]
  simp [show 10^k = 10 * 10^(k-1) by
    simp [<- Nat.pow_add_one']
    exact (Nat.sub_eq_iff_eq_add pos_k).mp rfl
  ]
  norm_num [<- Nat.mul_assoc, mul_comm]
  rw [show k * 9 * 10 * 10 ^ (k - 1) = 2 * k * 45 * 10 ^ (k - 1) by
    linarith
  ]
  simp [mul_assoc]
  omega

open Finset

theorem sub_one_mul_sum_div_pow_eq_sub_sum_digits {p : ℕ}
    (L : List ℕ) {h_nonempty} (h_ne_zero : L.getLast h_nonempty ≠ 0) (h_lt : ∀ l ∈ L, l < p) :
    (p - 1) * ∑ i ∈ range L.length, (ofDigits p L) / p ^ i.succ = (ofDigits p L) - L.sum := by
  obtain h | rfl | h : 1 < p ∨ 1 = p ∨ p < 1 := trichotomous 1 p
  · induction' L with hd tl ih
    · simp [ofDigits]
    · simp only [List.length_cons, List.sum_cons, self_div_pow_eq_ofDigits_drop _ _ h,
          digits_ofDigits p h (hd :: tl) h_lt (fun _ => h_ne_zero)]
      simp only [ofDigits]
      rw [sum_range_succ, Nat.cast_id]
      simp only [List.drop, List.drop_length]
      obtain rfl | h' := em <| tl = []
      · simp [ofDigits]
      · have w₁' := fun l hl ↦ h_lt l <| List.mem_cons_of_mem hd hl
        have w₂' := fun (h : tl ≠ []) ↦ (List.getLast_cons h) ▸ h_ne_zero
        have ih := ih (w₂' h') w₁'
        simp only [self_div_pow_eq_ofDigits_drop _ _ h, digits_ofDigits p h tl w₁' w₂',
          ← Nat.one_add] at ih
        have := sum_singleton (fun x ↦ ofDigits p <| tl.drop x) tl.length
        rw [← Ico_succ_singleton, List.drop_length, ofDigits] at this
        have h₁ : 1 ≤ tl.length := List.length_pos_iff.mpr h'
        rw [← sum_range_add_sum_Ico _ <| h₁, ← add_zero (∑ x ∈ Ico _ _, ofDigits p (tl.drop x)),
            ← this, sum_Ico_consecutive _  h₁ <| (le_add_right tl.length 1),
            ← sum_Ico_add _ 0 tl.length 1,
            Ico_zero_eq_range, mul_add, mul_add, ih, range_one, sum_singleton, List.drop, ofDigits,
            mul_zero, add_zero, ← Nat.add_sub_assoc <| sum_le_ofDigits _ <| Nat.le_of_lt h]
        nth_rw 2 [← one_mul <| ofDigits p tl]
        rw [← add_mul, Nat.sub_add_cancel (one_le_of_lt h), Nat.add_sub_add_left]
  · simp [ofDigits_one]
  · simp [lt_one_iff.mp h]
    cases L
    · rfl
    · simp [ofDigits]

theorem sub_one_mul_sum_log_div_pow_eq_sub_sum_digits {p : ℕ} (n : ℕ) :
    (p - 1) * ∑ i ∈ range (log p n).succ, n / p ^ i.succ = n - (p.digits n).sum := by
  obtain h | rfl | h : 1 < p ∨ 1 = p ∨ p < 1 := trichotomous 1 p
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · convert sub_one_mul_sum_div_pow_eq_sub_sum_digits (p.digits n) (getLast_digit_ne_zero p hn) <|
          (fun l a ↦ digits_lt_base h a)
      · refine (digits_len p n h hn).symm
      all_goals exact (ofDigits_digits p n).symm
  · simp
  · simp [lt_one_iff.mp h]
    cases n
    all_goals simp


/-! ### Binary -/


theorem digits_two_eq_bits (n : ℕ) : digits 2 n = n.bits.map fun b => cond b 1 0 := by
  induction' n using Nat.binaryRecFromOne with b n h ih
  · simp
  · simp
  rw [bits_append_bit _ _ fun hn => absurd hn h]
  cases b
  · rw [digits_def' one_lt_two]
    · simpa [Nat.bit]
    · simpa [Nat.bit, pos_iff_ne_zero]
  · simpa [Nat.bit, add_comm, digits_add 2 one_lt_two 1 n, Nat.add_mul_div_left]

/-! ### Modular Arithmetic -/


-- This is really a theorem about polynomials.
theorem dvd_ofDigits_sub_ofDigits {α : Type*} [CommRing α] {a b k : α} (h : k ∣ a - b)
    (L : List ℕ) : k ∣ ofDigits a L - ofDigits b L := by
  induction' L with d L ih
  · change k ∣ 0 - 0
    simp
  · simp only [ofDigits, add_sub_add_left_eq_sub]
    exact dvd_mul_sub_mul h ih

theorem ofDigits_modEq' (b b' : ℕ) (k : ℕ) (h : b ≡ b' [MOD k]) (L : List ℕ) :
    ofDigits b L ≡ ofDigits b' L [MOD k] := by
  induction' L with d L ih
  · rfl
  · dsimp [ofDigits]
    dsimp [Nat.ModEq] at *
    conv_lhs => rw [Nat.add_mod, Nat.mul_mod, h, ih]
    conv_rhs => rw [Nat.add_mod, Nat.mul_mod]

theorem ofDigits_modEq (b k : ℕ) (L : List ℕ) : ofDigits b L ≡ ofDigits (b % k) L [MOD k] :=
  ofDigits_modEq' b (b % k) k (b.mod_modEq k).symm L

theorem ofDigits_mod (b k : ℕ) (L : List ℕ) : ofDigits b L % k = ofDigits (b % k) L % k :=
  ofDigits_modEq b k L

theorem ofDigits_mod_eq_head! (b : ℕ) (l : List ℕ) : ofDigits b l % b = l.head! % b := by
  induction l <;> simp [Nat.ofDigits]

theorem head!_digits {b n : ℕ} (h : b ≠ 1) : (Nat.digits b n).head! = n % b := by
  by_cases hb : 1 < b
  · rcases n with _ | n
    · simp
    · nth_rw 2 [← Nat.ofDigits_digits b (n + 1)]
      rw [Nat.ofDigits_mod_eq_head! _ _]
      exact (Nat.mod_eq_of_lt (Nat.digits_lt_base hb <| List.head!_mem_self <|
          Nat.digits_ne_nil_iff_ne_zero.mpr <| Nat.succ_ne_zero n)).symm
  · rcases n with _ | _ <;> simp_all [show b = 0 by omega]

theorem ofDigits_zmodeq' (b b' : ℤ) (k : ℕ) (h : b ≡ b' [ZMOD k]) (L : List ℕ) :
    ofDigits b L ≡ ofDigits b' L [ZMOD k] := by
  induction' L with d L ih
  · rfl
  · dsimp [ofDigits]
    dsimp [Int.ModEq] at *
    conv_lhs => rw [Int.add_emod, Int.mul_emod, h, ih]
    conv_rhs => rw [Int.add_emod, Int.mul_emod]

theorem ofDigits_zmodeq (b : ℤ) (k : ℕ) (L : List ℕ) : ofDigits b L ≡ ofDigits (b % k) L [ZMOD k] :=
  ofDigits_zmodeq' b (b % k) k (b.mod_modEq ↑k).symm L

theorem ofDigits_zmod (b : ℤ) (k : ℕ) (L : List ℕ) : ofDigits b L % k = ofDigits (b % k) L % k :=
  ofDigits_zmodeq b k L

theorem modEq_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) : n ≡ (digits b' n).sum [MOD b] := by
  rw [← ofDigits_one]
  conv =>
    congr
    · skip
    · rw [← ofDigits_digits b' n]
  convert ofDigits_modEq b' b (digits b' n)
  exact h.symm

theorem zmodeq_ofDigits_digits (b b' : ℕ) (c : ℤ) (h : b' ≡ c [ZMOD b]) (n : ℕ) :
    n ≡ ofDigits c (digits b' n) [ZMOD b] := by
  conv =>
    congr
    · skip
    · rw [← ofDigits_digits b' n]
  rw [coe_int_ofDigits]
  apply ofDigits_zmodeq' _ _ _ h

theorem ofDigits_neg_one :
    ∀ L : List ℕ, ofDigits (-1 : ℤ) L = (L.map fun n : ℕ => (n : ℤ)).alternatingSum
  | [] => rfl
  | [n] => by simp [ofDigits, List.alternatingSum]
  | a :: b :: t => by
    simp only [ofDigits, List.alternatingSum, List.map_cons, ofDigits_neg_one t]
    ring

end Nat
