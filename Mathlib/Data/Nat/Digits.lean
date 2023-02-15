/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Shing Tak Lam, Mario Carneiro

! This file was ported from Lean 3 source module data.nat.digits
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Modeq
import Mathbin.Data.Nat.Bits
import Mathbin.Data.Nat.Log
import Mathbin.Data.List.Indexes
import Mathbin.Data.List.Palindrome
import Mathbin.Algebra.Parity
import Mathbin.Tactic.IntervalCases
import Mathbin.Tactic.Linarith.Default

/-!
# Digits of a natural number

This provides a basic API for extracting the digits of a natural number in a given base,
and reconstructing numbers from their digits.

We also prove some divisibility tests based on digits, in particular completing
Theorem #85 from https://www.cs.ru.nl/~freek/100/.

A basic `norm_digits` tactic is also provided for proving goals of the form
`nat.digits a b = l` where `a` and `b` are numerals.
-/


namespace Nat

variable {n : ℕ}

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digitsAux0 : ℕ → List ℕ
  | 0 => []
  | n + 1 => [n + 1]
#align nat.digits_aux_0 Nat.digitsAux0

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digitsAux1 (n : ℕ) : List ℕ :=
  List.replicate n 1
#align nat.digits_aux_1 Nat.digitsAux1

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digitsAux (b : ℕ) (h : 2 ≤ b) : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    have : (n + 1) / b < n + 1 := Nat.div_lt_self (Nat.succ_pos _) h
    ((n + 1) % b)::digits_aux ((n + 1) / b)
#align nat.digits_aux Nat.digitsAux

@[simp]
theorem digitsAux_zero (b : ℕ) (h : 2 ≤ b) : digitsAux b h 0 = [] := by rw [digits_aux]
#align nat.digits_aux_zero Nat.digitsAux_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem digitsAux_def (b : ℕ) (h : 2 ≤ b) (n : ℕ) (w : 0 < n) :
    digitsAux b h n = (n % b)::digitsAux b h (n / b) :=
  by
  cases n
  · cases w
  · rw [digits_aux]
#align nat.digits_aux_def Nat.digitsAux_def

/-- `digits b n` gives the digits, in little-endian order,
of a natural number `n` in a specified base `b`.

In any base, we have `of_digits b L = L.foldr (λ x y, x + b * y) 0`.
* For any `2 ≤ b`, we have `l < b` for any `l ∈ digits b n`,
  and the last digit is not zero.
  This uniquely specifies the behaviour of `digits b`.
* For `b = 1`, we define `digits 1 n = list.replicate n 1`.
* For `b = 0`, we define `digits 0 n = [n]`, except `digits 0 0 = []`.

Note this differs from the existing `nat.to_digits` in core, which is used for printing numerals.
In particular, `nat.to_digits b 0 = [0]`, while `digits b 0 = []`.
-/
def digits : ℕ → ℕ → List ℕ
  | 0 => digitsAux0
  | 1 => digitsAux1
  | b + 2 => digitsAux (b + 2) (by norm_num)
#align nat.digits Nat.digits

@[simp]
theorem digits_zero (b : ℕ) : digits b 0 = [] := by
  rcases b with (_ | ⟨_ | ⟨_⟩⟩) <;> simp [digits, digits_aux_0, digits_aux_1]
#align nat.digits_zero Nat.digits_zero

@[simp]
theorem digits_zero_zero : digits 0 0 = [] :=
  rfl
#align nat.digits_zero_zero Nat.digits_zero_zero

@[simp]
theorem digits_zero_succ (n : ℕ) : digits 0 n.succ = [n + 1] :=
  rfl
#align nat.digits_zero_succ Nat.digits_zero_succ

theorem digits_zero_succ' : ∀ {n : ℕ}, n ≠ 0 → digits 0 n = [n]
  | 0, h => (h rfl).elim
  | n + 1, _ => rfl
#align nat.digits_zero_succ' Nat.digits_zero_succ'

@[simp]
theorem digits_one (n : ℕ) : digits 1 n = List.replicate n 1 :=
  rfl
#align nat.digits_one Nat.digits_one

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem digits_one_succ (n : ℕ) : digits 1 (n + 1) = 1::digits 1 n :=
  rfl
#align nat.digits_one_succ Nat.digits_one_succ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem digits_add_two_add_one (b n : ℕ) :
    digits (b + 2) (n + 1) = ((n + 1) % (b + 2))::digits (b + 2) ((n + 1) / (b + 2)) :=
  by
  rw [digits, digits_aux_def]
  exact succ_pos n
#align nat.digits_add_two_add_one Nat.digits_add_two_add_one

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem digits_def' :
    ∀ {b : ℕ} (h : 1 < b) {n : ℕ} (w : 0 < n), digits b n = (n % b)::digits b (n / b)
  | 0, h => absurd h (by decide)
  | 1, h => absurd h (by decide)
  | b + 2, h => digitsAux_def _ _
#align nat.digits_def' Nat.digits_def'

@[simp]
theorem digits_of_lt (b x : ℕ) (hx : x ≠ 0) (hxb : x < b) : digits b x = [x] :=
  by
  rcases exists_eq_succ_of_ne_zero hx with ⟨x, rfl⟩
  rcases exists_eq_add_of_le' ((Nat.le_add_left 1 x).trans_lt hxb) with ⟨b, rfl⟩
  rw [digits_add_two_add_one, div_eq_of_lt hxb, digits_zero, mod_eq_of_lt hxb]
#align nat.digits_of_lt Nat.digits_of_lt

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem digits_add (b : ℕ) (h : 1 < b) (x y : ℕ) (hxb : x < b) (hxy : x ≠ 0 ∨ y ≠ 0) :
    digits b (x + b * y) = x::digits b y :=
  by
  rcases exists_eq_add_of_le' h with ⟨b, rfl : _ = _ + 2⟩
  cases y
  · simp [hxb, hxy.resolve_right (absurd rfl)]
  dsimp [digits]
  rw [digits_aux_def]
  · congr
    · simp [Nat.add_mod, mod_eq_of_lt hxb]
    · simp [add_mul_div_left, div_eq_of_lt hxb]
  · apply Nat.succ_pos
#align nat.digits_add Nat.digits_add

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- If we had a function converting a list into a polynomial,
-- and appropriate lemmas about that function,
-- we could rewrite this in terms of that.
/-- `of_digits b L` takes a list `L` of natural numbers, and interprets them
as a number in semiring, as the little-endian digits in base `b`.
-/
def ofDigits {α : Type _} [Semiring α] (b : α) : List ℕ → α
  | [] => 0
  | h::t => h + b * of_digits t
#align nat.of_digits Nat.ofDigits

theorem ofDigits_eq_foldr {α : Type _} [Semiring α] (b : α) (L : List ℕ) :
    ofDigits b L = L.foldr (fun x y => x + b * y) 0 :=
  by
  induction' L with d L ih
  · rfl
  · dsimp [of_digits]
    rw [ih]
#align nat.of_digits_eq_foldr Nat.ofDigits_eq_foldr

theorem of_digits_eq_sum_map_with_index_aux (b : ℕ) (l : List ℕ) :
    ((List.range l.length).zipWith ((fun i a : ℕ => a * b ^ i) ∘ succ) l).Sum =
      b * ((List.range l.length).zipWith (fun i a => a * b ^ i) l).Sum :=
  by
  suffices
    (List.range l.length).zipWith ((fun i a : ℕ => a * b ^ i) ∘ succ) l =
      (List.range l.length).zipWith (fun i a => b * (a * b ^ i)) l
    by simp [this]
  congr
  ext
  simp [pow_succ]
  ring
#align nat.of_digits_eq_sum_map_with_index_aux Nat.of_digits_eq_sum_map_with_index_aux

theorem ofDigits_eq_sum_mapIdx (b : ℕ) (L : List ℕ) :
    ofDigits b L = (L.mapIdx fun i a => a * b ^ i).Sum :=
  by
  rw [List.mapIdx_eq_enum_map, List.enum_eq_zip_range, List.map_uncurry_zip_eq_zipWith,
    of_digits_eq_foldr]
  induction' L with hd tl hl
  · simp
  ·
    simpa [List.range_succ_eq_map, List.zipWith_map_left, of_digits_eq_sum_map_with_index_aux] using
      Or.inl hl
#align nat.of_digits_eq_sum_map_with_index Nat.ofDigits_eq_sum_mapIdx

@[simp]
theorem ofDigits_singleton {b n : ℕ} : ofDigits b [n] = n := by simp [of_digits]
#align nat.of_digits_singleton Nat.ofDigits_singleton

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem ofDigits_one_cons {α : Type _} [Semiring α] (h : ℕ) (L : List ℕ) :
    ofDigits (1 : α) (h::L) = h + ofDigits 1 L := by simp [of_digits]
#align nat.of_digits_one_cons Nat.ofDigits_one_cons

theorem ofDigits_append {b : ℕ} {l1 l2 : List ℕ} :
    ofDigits b (l1 ++ l2) = ofDigits b l1 + b ^ l1.length * ofDigits b l2 :=
  by
  induction' l1 with hd tl IH
  · simp [of_digits]
  · rw [of_digits, List.cons_append, of_digits, IH, List.length_cons, pow_succ']
    ring
#align nat.of_digits_append Nat.ofDigits_append

@[norm_cast]
theorem coe_ofDigits (α : Type _) [Semiring α] (b : ℕ) (L : List ℕ) :
    ((ofDigits b L : ℕ) : α) = ofDigits (b : α) L :=
  by
  induction' L with d L ih
  · simp [of_digits]
  · dsimp [of_digits]
    push_cast
    rw [ih]
#align nat.coe_of_digits Nat.coe_ofDigits

@[norm_cast]
theorem coe_int_ofDigits (b : ℕ) (L : List ℕ) : ((ofDigits b L : ℕ) : ℤ) = ofDigits (b : ℤ) L :=
  by
  induction' L with d L ih
  · rfl
  · dsimp [of_digits]
    push_cast
#align nat.coe_int_of_digits Nat.coe_int_ofDigits

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem digits_zero_of_eq_zero {b : ℕ} (h : b ≠ 0) :
    ∀ {L : List ℕ} (h0 : ofDigits b L = 0), ∀ l ∈ L, l = 0
  | a::L, h0, l, Or.inl rfl => Nat.eq_zero_of_add_eq_zero_right h0
  | a::L, h0, l, Or.inr hL =>
    digits_zero_of_eq_zero (mul_right_injective₀ h (Nat.eq_zero_of_add_eq_zero_left h0)) _ hL
#align nat.digits_zero_of_eq_zero Nat.digits_zero_of_eq_zero

theorem digits_ofDigits (b : ℕ) (h : 1 < b) (L : List ℕ) (w₁ : ∀ l ∈ L, l < b)
    (w₂ : ∀ h : L ≠ [], L.getLast h ≠ 0) : digits b (ofDigits b L) = L :=
  by
  induction' L with d L ih
  · dsimp [of_digits]
    simp
  · dsimp [of_digits]
    replace w₂ := w₂ (by simp)
    rw [digits_add b h]
    · rw [ih]
      · intro l m
        apply w₁
        exact List.mem_cons_of_mem _ m
      · intro h
        · rw [List.getLast_cons h] at w₂
          convert w₂
    · exact w₁ d (List.mem_cons_self _ _)
    · by_cases h' : L = []
      · rcases h' with rfl
        left
        simpa using w₂
      · right
        contrapose! w₂
        refine' digits_zero_of_eq_zero h.ne_bot w₂ _ _
        rw [List.getLast_cons h']
        exact List.getLast_mem h'
#align nat.digits_of_digits Nat.digits_ofDigits

theorem ofDigits_digits (b n : ℕ) : ofDigits b (digits b n) = n :=
  by
  cases' b with b
  · cases' n with n
    · rfl
    · change of_digits 0 [n + 1] = n + 1
      dsimp [of_digits]
      simp
  · cases' b with b
    · induction' n with n ih
      · rfl
      · simp only [ih, add_comm 1, of_digits_one_cons, Nat.cast_id, digits_one_succ]
    · apply Nat.strong_induction_on n _
      clear n
      intro n h
      cases n
      · rw [digits_zero]
        rfl
      · simp only [Nat.succ_eq_add_one, digits_add_two_add_one]
        dsimp [of_digits]
        rw [h _ (Nat.div_lt_self' n b)]
        rw [Nat.mod_add_div]
#align nat.of_digits_digits Nat.ofDigits_digits

theorem ofDigits_one (L : List ℕ) : ofDigits 1 L = L.Sum :=
  by
  induction' L with d L ih
  · rfl
  · simp [of_digits, List.sum_cons, ih]
#align nat.of_digits_one Nat.ofDigits_one

/-!
### Properties

This section contains various lemmas of properties relating to `digits` and `of_digits`.
-/


theorem digits_eq_nil_iff_eq_zero {b n : ℕ} : digits b n = [] ↔ n = 0 :=
  by
  constructor
  · intro h
    have : of_digits b (digits b n) = of_digits b [] := by rw [h]
    convert this
    rw [of_digits_digits]
  · rintro rfl
    simp
#align nat.digits_eq_nil_iff_eq_zero Nat.digits_eq_nil_iff_eq_zero

theorem digits_ne_nil_iff_ne_zero {b n : ℕ} : digits b n ≠ [] ↔ n ≠ 0 :=
  not_congr digits_eq_nil_iff_eq_zero
#align nat.digits_ne_nil_iff_ne_zero Nat.digits_ne_nil_iff_ne_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem digits_eq_cons_digits_div {b n : ℕ} (h : 1 < b) (w : n ≠ 0) :
    digits b n = (n % b)::digits b (n / b) :=
  by
  rcases b with (_ | _ | b)
  · rw [digits_zero_succ' w, Nat.mod_zero, Nat.div_zero, Nat.digits_zero_zero]
  · norm_num at h
  rcases n with (_ | n)
  · norm_num at w
  simp
#align nat.digits_eq_cons_digits_div Nat.digits_eq_cons_digits_div

theorem digits_getLast {b : ℕ} (m : ℕ) (h : 1 < b) (p q) :
    (digits b m).getLast p = (digits b (m / b)).getLast q :=
  by
  by_cases hm : m = 0
  · simp [hm]
  simp only [digits_eq_cons_digits_div h hm]
  rw [List.getLast_cons]
#align nat.digits_last Nat.digits_getLast

theorem digits.injective (b : ℕ) : Function.Injective b.digits :=
  Function.LeftInverse.injective (ofDigits_digits b)
#align nat.digits.injective Nat.digits.injective

@[simp]
theorem digits_inj_iff {b n m : ℕ} : b.digits n = b.digits m ↔ n = m :=
  (digits.injective b).eq_iff
#align nat.digits_inj_iff Nat.digits_inj_iff

theorem digits_len (b n : ℕ) (hb : 1 < b) (hn : n ≠ 0) : (b.digits n).length = b.log n + 1 :=
  by
  induction' n using Nat.strong_induction_on with n IH
  rw [digits_eq_cons_digits_div hb hn, List.length]
  by_cases h : n / b = 0
  · have hb0 : b ≠ 0 := (Nat.succ_le_iff.1 hb).ne_bot
    simp [h, log_eq_zero_iff, ← Nat.div_eq_zero_iff hb0.bot_lt]
  · have hb' : 1 < b := one_lt_two.trans_le hb
    have : n / b < n := div_lt_self (Nat.pos_of_ne_zero hn) hb'
    rw [IH _ this h, log_div_base, tsub_add_cancel_of_le]
    refine' Nat.succ_le_of_lt (log_pos hb' _)
    contrapose! h
    exact div_eq_of_lt h
#align nat.digits_len Nat.digits_len

theorem getLast_digit_ne_zero (b : ℕ) {m : ℕ} (hm : m ≠ 0) :
    (digits b m).getLast (digits_ne_nil_iff_ne_zero.mpr hm) ≠ 0 :=
  by
  rcases b with (_ | _ | b)
  · cases m
    · cases hm rfl
    · simp
  · cases m
    · cases hm rfl
    simpa only [digits_one, List.getLast_replicate_succ m 1] using one_ne_zero
  revert hm
  apply Nat.strong_induction_on m
  intro n IH hn
  by_cases hnb : n < b + 2
  · simpa only [digits_of_lt (b + 2) n hn hnb]
  · rw [digits_last n (show 2 ≤ b + 2 by decide)]
    refine' IH _ (Nat.div_lt_self hn.bot_lt (by decide)) _
    · rw [← pos_iff_ne_zero]
      exact Nat.div_pos (le_of_not_lt hnb) (by decide)
#align nat.last_digit_ne_zero Nat.getLast_digit_ne_zero

/-- The digits in the base b+2 expansion of n are all less than b+2 -/
theorem digits_lt_base' {b m : ℕ} : ∀ {d}, d ∈ digits (b + 2) m → d < b + 2 :=
  by
  apply Nat.strong_induction_on m
  intro n IH d hd
  cases' n with n
  · rw [digits_zero] at hd
    cases hd
  -- base b+2 expansion of 0 has no digits
  rw [digits_add_two_add_one] at hd
  cases hd
  · rw [hd]
    exact n.succ.mod_lt (by linarith)
  · exact IH _ (Nat.div_lt_self (Nat.succ_pos _) (by linarith)) hd
#align nat.digits_lt_base' Nat.digits_lt_base'

/-- The digits in the base b expansion of n are all less than b, if b ≥ 2 -/
theorem digits_lt_base {b m d : ℕ} (hb : 1 < b) (hd : d ∈ digits b m) : d < b :=
  by
  rcases b with (_ | _ | b) <;> try linarith
  exact digits_lt_base' hd
#align nat.digits_lt_base Nat.digits_lt_base

/-- an n-digit number in base b + 2 is less than (b + 2)^n -/
theorem ofDigits_lt_base_pow_length' {b : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, x < b + 2) :
    ofDigits (b + 2) l < (b + 2) ^ l.length :=
  by
  induction' l with hd tl IH
  · simp [of_digits]
  · rw [of_digits, List.length_cons, pow_succ]
    have : (of_digits (b + 2) tl + 1) * (b + 2) ≤ (b + 2) ^ tl.length * (b + 2) :=
      mul_le_mul (IH fun x hx => hl _ (List.mem_cons_of_mem _ hx)) (by rfl) (by decide)
        (Nat.zero_le _)
    suffices ↑hd < b + 2 by linarith
    norm_cast
    exact hl hd (List.mem_cons_self _ _)
#align nat.of_digits_lt_base_pow_length' Nat.ofDigits_lt_base_pow_length'

/-- an n-digit number in base b is less than b^n if b > 1 -/
theorem ofDigits_lt_base_pow_length {b : ℕ} {l : List ℕ} (hb : 1 < b) (hl : ∀ x ∈ l, x < b) :
    ofDigits b l < b ^ l.length :=
  by
  rcases b with (_ | _ | b) <;> try linarith
  exact of_digits_lt_base_pow_length' hl
#align nat.of_digits_lt_base_pow_length Nat.ofDigits_lt_base_pow_length

/-- Any number m is less than (b+2)^(number of digits in the base b + 2 representation of m) -/
theorem lt_base_pow_length_digits' {b m : ℕ} : m < (b + 2) ^ (digits (b + 2) m).length :=
  by
  convert of_digits_lt_base_pow_length' fun _ => digits_lt_base'
  rw [of_digits_digits (b + 2) m]
#align nat.lt_base_pow_length_digits' Nat.lt_base_pow_length_digits'

/-- Any number m is less than b^(number of digits in the base b representation of m) -/
theorem lt_base_pow_length_digits {b m : ℕ} (hb : 1 < b) : m < b ^ (digits b m).length :=
  by
  rcases b with (_ | _ | b) <;> try linarith
  exact lt_base_pow_length_digits'
#align nat.lt_base_pow_length_digits Nat.lt_base_pow_length_digits

theorem ofDigits_digits_append_digits {b m n : ℕ} :
    ofDigits b (digits b n ++ digits b m) = n + b ^ (digits b n).length * m := by
  rw [of_digits_append, of_digits_digits, of_digits_digits]
#align nat.of_digits_digits_append_digits Nat.ofDigits_digits_append_digits

theorem digits_len_le_digits_len_succ (b n : ℕ) : (digits b n).length ≤ (digits b (n + 1)).length :=
  by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  · simp
  cases' le_or_lt b 1 with hb hb
  · interval_cases <;> simp [digits_zero_succ', hn]
  simpa [digits_len, hb, hn] using log_mono_right (le_succ _)
#align nat.digits_len_le_digits_len_succ Nat.digits_len_le_digits_len_succ

theorem le_digits_len_le (b n m : ℕ) (h : n ≤ m) : (digits b n).length ≤ (digits b m).length :=
  monotone_nat_of_le_succ (digits_len_le_digits_len_succ b) h
#align nat.le_digits_len_le Nat.le_digits_len_le

theorem pow_length_le_mul_ofDigits {b : ℕ} {l : List ℕ} (hl : l ≠ []) (hl2 : l.getLast hl ≠ 0) :
    (b + 2) ^ l.length ≤ (b + 2) * ofDigits (b + 2) l :=
  by
  rw [← List.dropLast_append_getLast hl]
  simp only [List.length_append, List.length, zero_add, List.length_dropLast, of_digits_append,
    List.length_dropLast, of_digits_singleton, add_comm (l.length - 1), pow_add, pow_one]
  apply Nat.mul_le_mul_left
  refine' le_trans _ (Nat.le_add_left _ _)
  have : 0 < l.last hl := by rwa [pos_iff_ne_zero]
  convert Nat.mul_le_mul_left _ this
  rw [mul_one]
#align nat.pow_length_le_mul_of_digits Nat.pow_length_le_mul_ofDigits

/-- Any non-zero natural number `m` is greater than
(b+2)^((number of digits in the base (b+2) representation of m) - 1)
-/
theorem base_pow_length_digits_le' (b m : ℕ) (hm : m ≠ 0) :
    (b + 2) ^ (digits (b + 2) m).length ≤ (b + 2) * m :=
  by
  have : digits (b + 2) m ≠ [] := digits_ne_nil_iff_ne_zero.mpr hm
  convert pow_length_le_mul_of_digits this (last_digit_ne_zero _ hm)
  rwa [of_digits_digits]
#align nat.base_pow_length_digits_le' Nat.base_pow_length_digits_le'

/-- Any non-zero natural number `m` is greater than
b^((number of digits in the base b representation of m) - 1)
-/
theorem base_pow_length_digits_le (b m : ℕ) (hb : 1 < b) :
    m ≠ 0 → b ^ (digits b m).length ≤ b * m :=
  by
  rcases b with (_ | _ | b) <;> try linarith
  exact base_pow_length_digits_le' b m
#align nat.base_pow_length_digits_le Nat.base_pow_length_digits_le

/-! ### Binary -/


theorem digits_two_eq_bits (n : ℕ) : digits 2 n = n.bits.map fun b => cond b 1 0 :=
  by
  induction' n using Nat.binaryRecFromOne with b n h ih
  · simp
  · simp
  rw [bits_append_bit _ _ fun hn => absurd hn h]
  cases b
  · rw [digits_def' one_lt_two]
    · simpa [Nat.bit, Nat.bit0_val n]
    · simpa [pos_iff_ne_zero, bit_eq_zero_iff]
  · simpa [Nat.bit, Nat.bit1_val n, add_comm, digits_add 2 one_lt_two 1 n]
#align nat.digits_two_eq_bits Nat.digits_two_eq_bits

/-! ### Modular Arithmetic -/


-- This is really a theorem about polynomials.
theorem dvd_ofDigits_sub_ofDigits {α : Type _} [CommRing α] {a b k : α} (h : k ∣ a - b)
    (L : List ℕ) : k ∣ ofDigits a L - ofDigits b L :=
  by
  induction' L with d L ih
  · change k ∣ 0 - 0
    simp
  · simp only [of_digits, add_sub_add_left_eq_sub]
    exact dvd_mul_sub_mul h ih
#align nat.dvd_of_digits_sub_of_digits Nat.dvd_ofDigits_sub_ofDigits

theorem ofDigits_modeq' (b b' : ℕ) (k : ℕ) (h : b ≡ b' [MOD k]) (L : List ℕ) :
    ofDigits b L ≡ ofDigits b' L [MOD k] :=
  by
  induction' L with d L ih
  · rfl
  · dsimp [of_digits]
    dsimp [Nat.ModEq] at *
    conv_lhs => rw [Nat.add_mod, Nat.mul_mod, h, ih]
    conv_rhs => rw [Nat.add_mod, Nat.mul_mod]
#align nat.of_digits_modeq' Nat.ofDigits_modeq'

theorem ofDigits_modEq (b k : ℕ) (L : List ℕ) : ofDigits b L ≡ ofDigits (b % k) L [MOD k] :=
  ofDigits_modeq' b (b % k) k (b.mod_modEq k).symm L
#align nat.of_digits_modeq Nat.ofDigits_modEq

theorem ofDigits_mod (b k : ℕ) (L : List ℕ) : ofDigits b L % k = ofDigits (b % k) L % k :=
  ofDigits_modEq b k L
#align nat.of_digits_mod Nat.ofDigits_mod

theorem ofDigits_zmodeq' (b b' : ℤ) (k : ℕ) (h : b ≡ b' [ZMOD k]) (L : List ℕ) :
    ofDigits b L ≡ ofDigits b' L [ZMOD k] :=
  by
  induction' L with d L ih
  · rfl
  · dsimp [of_digits]
    dsimp [Int.ModEq] at *
    conv_lhs => rw [Int.add_emod, Int.mul_emod, h, ih]
    conv_rhs => rw [Int.add_emod, Int.mul_emod]
#align nat.of_digits_zmodeq' Nat.ofDigits_zmodeq'

theorem ofDigits_zmodeq (b : ℤ) (k : ℕ) (L : List ℕ) : ofDigits b L ≡ ofDigits (b % k) L [ZMOD k] :=
  ofDigits_zmodeq' b (b % k) k (b.mod_modEq ↑k).symm L
#align nat.of_digits_zmodeq Nat.ofDigits_zmodeq

theorem ofDigits_zmod (b : ℤ) (k : ℕ) (L : List ℕ) : ofDigits b L % k = ofDigits (b % k) L % k :=
  ofDigits_zmodeq b k L
#align nat.of_digits_zmod Nat.ofDigits_zmod

theorem modEq_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) : n ≡ (digits b' n).Sum [MOD b] :=
  by
  rw [← of_digits_one]
  conv =>
    congr
    skip
    rw [← of_digits_digits b' n]
  convert of_digits_modeq _ _ _
  exact h.symm
#align nat.modeq_digits_sum Nat.modEq_digits_sum

theorem modEq_three_digits_sum (n : ℕ) : n ≡ (digits 10 n).Sum [MOD 3] :=
  modEq_digits_sum 3 10 (by norm_num) n
#align nat.modeq_three_digits_sum Nat.modEq_three_digits_sum

theorem modEq_nine_digits_sum (n : ℕ) : n ≡ (digits 10 n).Sum [MOD 9] :=
  modEq_digits_sum 9 10 (by norm_num) n
#align nat.modeq_nine_digits_sum Nat.modEq_nine_digits_sum

theorem zmodeq_ofDigits_digits (b b' : ℕ) (c : ℤ) (h : b' ≡ c [ZMOD b]) (n : ℕ) :
    n ≡ ofDigits c (digits b' n) [ZMOD b] :=
  by
  conv =>
    congr
    skip
    rw [← of_digits_digits b' n]
  rw [coe_int_of_digits]
  apply of_digits_zmodeq' _ _ _ h
#align nat.zmodeq_of_digits_digits Nat.zmodeq_ofDigits_digits

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem ofDigits_neg_one :
    ∀ L : List ℕ, ofDigits (-1 : ℤ) L = (L.map fun n : ℕ => (n : ℤ)).alternatingSum
  | [] => rfl
  | [n] => by simp [of_digits, List.alternatingSum]
  | a::b::t =>
    by
    simp only [of_digits, List.alternatingSum, List.map_cons, of_digits_neg_one t]
    ring
#align nat.of_digits_neg_one Nat.ofDigits_neg_one

theorem modEq_eleven_digits_sum (n : ℕ) :
    n ≡ ((digits 10 n).map fun n : ℕ => (n : ℤ)).alternatingSum [ZMOD 11] :=
  by
  have t := zmodeq_of_digits_digits 11 10 (-1 : ℤ) (by unfold Int.ModEq <;> norm_num) n
  rwa [of_digits_neg_one] at t
#align nat.modeq_eleven_digits_sum Nat.modEq_eleven_digits_sum

/-! ## Divisibility  -/


theorem dvd_iff_dvd_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) :
    b ∣ n ↔ b ∣ (digits b' n).Sum := by
  rw [← of_digits_one]
  conv_lhs => rw [← of_digits_digits b' n]
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, of_digits_mod, h]
#align nat.dvd_iff_dvd_digits_sum Nat.dvd_iff_dvd_digits_sum

/-- **Divisibility by 3 Rule** -/
theorem three_dvd_iff (n : ℕ) : 3 ∣ n ↔ 3 ∣ (digits 10 n).Sum :=
  dvd_iff_dvd_digits_sum 3 10 (by norm_num) n
#align nat.three_dvd_iff Nat.three_dvd_iff

theorem nine_dvd_iff (n : ℕ) : 9 ∣ n ↔ 9 ∣ (digits 10 n).Sum :=
  dvd_iff_dvd_digits_sum 9 10 (by norm_num) n
#align nat.nine_dvd_iff Nat.nine_dvd_iff

theorem dvd_iff_dvd_ofDigits (b b' : ℕ) (c : ℤ) (h : (b : ℤ) ∣ (b' : ℤ) - c) (n : ℕ) :
    b ∣ n ↔ (b : ℤ) ∣ ofDigits c (digits b' n) :=
  by
  rw [← Int.coe_nat_dvd]
  exact
    dvd_iff_dvd_of_dvd_sub (zmodeq_of_digits_digits b b' c (Int.modEq_iff_dvd.2 h).symm _).symm.Dvd
#align nat.dvd_iff_dvd_of_digits Nat.dvd_iff_dvd_ofDigits

theorem eleven_dvd_iff :
    11 ∣ n ↔ (11 : ℤ) ∣ ((digits 10 n).map fun n : ℕ => (n : ℤ)).alternatingSum :=
  by
  have t := dvd_iff_dvd_of_digits 11 10 (-1 : ℤ) (by norm_num) n
  rw [of_digits_neg_one] at t
  exact t
#align nat.eleven_dvd_iff Nat.eleven_dvd_iff

theorem eleven_dvd_of_palindrome (p : (digits 10 n).Palindrome) (h : Even (digits 10 n).length) :
    11 ∣ n := by
  let dig := (digits 10 n).map (coe : ℕ → ℤ)
  replace h : Even dig.length := by rwa [List.length_map]
  refine' eleven_dvd_iff.2 ⟨0, (_ : dig.alternating_sum = 0)⟩
  have := dig.alternating_sum_reverse
  rw [(p.map _).reverse_eq, pow_succ, h.neg_one_pow, mul_one, neg_one_zsmul] at this
  exact eq_zero_of_neg_eq this.symm
#align nat.eleven_dvd_of_palindrome Nat.eleven_dvd_of_palindrome

/-! ### `norm_digits` tactic -/


namespace NormDigits

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem digits_succ (b n m r l) (e : r + b * m = n) (hr : r < b)
    (h : Nat.digits b m = l ∧ 1 < b ∧ 0 < m) : (Nat.digits b n = r::l) ∧ 1 < b ∧ 0 < n :=
  by
  rcases h with ⟨h, b2, m0⟩
  have b0 : 0 < b := by linarith
  have n0 : 0 < n := by linarith [mul_pos b0 m0]
  refine' ⟨_, b2, n0⟩
  obtain ⟨rfl, rfl⟩ := (Nat.div_mod_unique b0).2 ⟨e, hr⟩
  subst h; exact Nat.digits_def' b2 n0
#align nat.norm_digits.digits_succ Nat.NormDigits.digits_succ

theorem digits_one (b n) (n0 : 0 < n) (nb : n < b) : Nat.digits b n = [n] ∧ 1 < b ∧ 0 < n :=
  by
  have b2 : 1 < b := by linarith
  refine' ⟨_, b2, n0⟩
  rw [Nat.digits_def' b2 n0, Nat.mod_eq_of_lt nb,
    (Nat.div_eq_zero_iff ((zero_le n).trans_lt nb)).2 nb, Nat.digits_zero]
#align nat.norm_digits.digits_one Nat.NormDigits.digits_one

open Tactic

-- failed to format: unknown constant 'term.pseudo.antiquot'
/-- Helper function for the `norm_digits` tactic. -/ unsafe
  def
    eval_aux
    ( eb : expr ) ( b : ℕ ) : expr → ℕ → instance_cache → tactic ( instance_cache × expr × expr )
    |
      en , n , ic
      =>
      do
        let m := n / b
          let r := n % b
          let ( ic , er ) ← ic . ofNat r
          let ( ic , pr ) ← norm_num.prove_lt_nat ic er eb
          if
            m = 0
            then
            do
              let ( _ , pn0 ) ← norm_num.prove_pos ic en
                return
                  (
                    ic
                      ,
                      q( ( [ $ ( en ) ] : List Nat ) )
                        ,
                        q( digits_one $ ( eb ) $ ( en ) $ ( pn0 ) $ ( pr ) )
                    )
            else
            do
              let em ← expr.of_nat q( ℕ ) m
                let ( _ , pe ) ← norm_num.derive q( ( $ ( er ) + $ ( eb ) * $ ( em ) : ℕ ) )
                let ( ic , el , p ) ← eval_aux em m ic
                return
                  (
                    ic
                      ,
                      q( @ List.cons ℕ $ ( er ) $ ( el ) )
                        ,
                        q(
                          digits_succ
                            $ ( eb ) $ ( en ) $ ( em ) $ ( er ) $ ( el ) $ ( pe ) $ ( pr ) $ ( p )
                          )
                    )
#align nat.norm_digits.eval_aux nat.norm_digits.eval_aux

/-- A tactic for normalizing expressions of the form `nat.digits a b = l` where
`a` and `b` are numerals.

```
example : nat.digits 10 123 = [3,2,1] := by norm_num
```
-/
@[norm_num]
unsafe def eval : expr → tactic (expr × expr)
  | q(Nat.digits $(eb) $(en)) => do
    let b ← expr.to_nat eb
    let n ← expr.to_nat en
    if n = 0 then return (q(([] : List ℕ)), q(Nat.digits_zero $(eb)))
      else
        if b = 0 then do
          let ic ← mk_instance_cache q(ℕ)
          let (_, pn0) ← norm_num.prove_ne_zero' ic en
          return (q(([$(en)] : List ℕ)), q(@Nat.digits_zero_succ' $(en) $(pn0)))
        else
          if b = 1 then do
            let ic ← mk_instance_cache q(ℕ)
            let s ← simp_lemmas.add_simp simp_lemmas.mk `list.replicate
            let (rhs, p2, _) ← simplify s [] q(List.replicate $(en) 1)
            let p ← mk_eq_trans q(Nat.digits_one $(en)) p2
            return (rhs, p)
          else do
            let ic ← mk_instance_cache q(ℕ)
            let (_, l, p) ← eval_aux eb b en n ic
            let p ← mk_app `` And.left [p]
            return (l, p)
  | _ => failed
#align nat.norm_digits.eval nat.norm_digits.eval

end NormDigits

end Nat

