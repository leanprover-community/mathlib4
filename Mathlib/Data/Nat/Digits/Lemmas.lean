/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shing Tak Lam, Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Digits.Defs

/-!
# Digits of a natural number

This provides lemma about the digits of natural numbers.
-/

public section

namespace Nat

variable {n : ℕ}

theorem ofDigits_eq_sum_mapIdx_aux (b : ℕ) (l : List ℕ) :
    (l.zipWith ((fun a i : ℕ => a * b ^ (i + 1))) (List.range l.length)).sum =
      b * (l.zipWith (fun a i => a * b ^ i) (List.range l.length)).sum := by
  suffices
    l.zipWith (fun a i : ℕ => a * b ^ (i + 1)) (List.range l.length) =
      l.zipWith (fun a i => b * (a * b ^ i)) (List.range l.length)
    by simp [this]
  congr; ext; ring

theorem ofDigits_eq_sum_mapIdx (b : ℕ) (L : List ℕ) :
    ofDigits b L = (L.mapIdx fun i a => a * b ^ i).sum := by
  rw [List.mapIdx_eq_zipIdx_map, List.zipIdx_eq_zip_range', List.map_zip_eq_zipWith,
    ofDigits_eq_foldr, ← List.range_eq_range']
  induction L with
  | nil => simp
  | cons hd tl hl =>
    simpa [List.range_succ_eq_map, List.zipWith_map_right, ofDigits_eq_sum_mapIdx_aux] using
      Or.inl hl

/-!
### Properties

This section contains various lemmas of properties relating to `digits` and `ofDigits`.
-/

theorem digits_len (b n : ℕ) (hb : 1 < b) (hn : n ≠ 0) : (b.digits n).length = b.log n + 1 := by
  induction n using Nat.strong_induction_on with | _ n IH
  rw [digits_eq_cons_digits_div hb hn, List.length]
  by_cases h : n / b = 0
  · simp [h]
    aesop
  · have : n / b < n := div_lt_self (Nat.pos_of_ne_zero hn) hb
    rw [IH _ this h, log_div_base, tsub_add_cancel_of_le]
    refine Nat.succ_le_of_lt (log_pos hb ?_)
    contrapose! h
    exact div_eq_of_lt h

theorem digits_length_le_iff {b k : ℕ} (hb : 1 < b) (n : ℕ) :
    (b.digits n).length ≤ k ↔ n < b ^ k := by
  by_cases h : n = 0
  · have : 0 < b ^ k := by positivity
    simpa [h]
  rw [digits_len b n hb h, ← log_lt_iff_lt_pow hb h]
  exact add_one_le_iff

theorem lt_digits_length_iff {b k : ℕ} (hb : 1 < b) (n : ℕ) :
    k < (b.digits n).length ↔ b ^ k ≤ n := by
  contrapose!
  exact digits_length_le_iff hb n

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
  by_cases! hnb : n < b + 2
  · simpa only [digits_of_lt (b + 2) n hn hnb]
  · rw [digits_getLast n (le_add_left 2 b)]
    refine IH _ (Nat.div_lt_self hn.bot_lt (one_lt_succ_succ b)) ?_
    rw [← pos_iff_ne_zero]
    exact Nat.div_pos hnb (zero_lt_succ (succ b))

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
  convert @pow_length_le_mul_ofDigits b (digits (b + 2) m)
    this (getLast_digit_ne_zero _ hm)
  rw [ofDigits_digits]

-- TODO: fix the non-terminal simp_all; it runs on three goals, leaving only one
set_option linter.flexible false in
/-- Any non-zero natural number `m` is greater than
b^((number of digits in the base b representation of m) - 1)
-/
theorem base_pow_length_digits_le (b m : ℕ) (hb : 1 < b) :
    m ≠ 0 → b ^ (digits b m).length ≤ b * m := by
  rcases b with (_ | _ | b) <;> try simp_all
  exact base_pow_length_digits_le' b m

open Finset

theorem sub_one_mul_sum_div_pow_eq_sub_sum_digits {p : ℕ}
    (L : List ℕ) {h_nonempty} (h_ne_zero : L.getLast h_nonempty ≠ 0) (h_lt : ∀ l ∈ L, l < p) :
    (p - 1) * ∑ i ∈ range L.length, (ofDigits p L) / p ^ i.succ = (ofDigits p L) - L.sum := by
  obtain h | rfl | h : 1 < p ∨ 1 = p ∨ p < 1 := trichotomous 1 p
  · induction L with
    | nil => simp [ofDigits]
    | cons hd tl ih =>
      simp only [List.length_cons, List.sum_cons, self_div_pow_eq_ofDigits_drop _ _ h,
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
            ← this, sum_Ico_consecutive _ h₁ <| (le_add_right tl.length 1),
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
  induction n using Nat.binaryRecFromOne with
  | zero => simp
  | one => simp
  | bit b n h ih =>
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
  induction L with
  | nil => change k ∣ 0 - 0; simp
  | cons d L ih =>
    simp only [ofDigits, add_sub_add_left_eq_sub]
    exact dvd_mul_sub_mul h ih

theorem ofDigits_modEq' (b b' : ℕ) (k : ℕ) (h : b ≡ b' [MOD k]) (L : List ℕ) :
    ofDigits b L ≡ ofDigits b' L [MOD k] := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    dsimp [ofDigits]
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
  · rcases n with _ | _ <;> simp_all [show b = 0 by lia]

theorem ofDigits_zmodeq' (b b' : ℤ) (k : ℕ) (h : b ≡ b' [ZMOD k]) (L : List ℕ) :
    ofDigits b L ≡ ofDigits b' L [ZMOD k] := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    dsimp [ofDigits]
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
  rw [coe_ofDigits]
  apply ofDigits_zmodeq' _ _ _ h

theorem ofDigits_neg_one :
    ∀ L : List ℕ, ofDigits (-1 : ℤ) L = (L.map fun n : ℕ => (n : ℤ)).alternatingSum
  | [] => rfl
  | [n] => by simp [ofDigits, List.alternatingSum]
  | a :: b :: t => by
    simp only [ofDigits, List.alternatingSum, List.map_cons, ofDigits_neg_one t]
    ring

/-- Explicit computation of the `i`-th digit of `n` in base `b`. -/
theorem getD_digits (n i : ℕ) {b : ℕ} (h : 2 ≤ b) : (digits b n).getD i 0 = n / b ^ i % b := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' h
  clear h
  rw [List.getD_eq_getElem?_getD]
  induction n using Nat.caseStrongRecOn generalizing i with
  | zero => simp
  | ind n IH =>
    rcases i with _ | i
    · rw [← List.head?_eq_getElem?, ← default_eq_zero, ← List.head!_eq_head?_getD,
        head!_digits (by grind)]
      simp
    · simp [IH _ (le_of_lt_succ (div_lt_self' n b)), pow_succ', Nat.div_div_eq_div_mul]

/-! ### Bijection -/

open List

/--
The list of digits of `n` in base `b` with some `0`'s appended so that its length is equal to `l`
if it is `< l`. This is an inverse function of `Nat.ofDigits` for `n < b ^ l`,
see `Nat.setInvOn_digitsAppend_ofDigits`.
If `n ≥ b ^ l`, then the list of digits of `n` in base `b` is of length at least `l` and
this function just return `b.digits n`.
-/
def digitsAppend (b l n : ℕ) : List ℕ :=
  b.digits n ++ replicate (l - (b.digits n).length) 0

theorem length_digitsAppend {b : ℕ} (hb : 1 < b) (l : ℕ) (hn : n < b ^ l) :
    (digitsAppend b l n).length = l := by
  rw [digitsAppend, length_append, length_replicate, Nat.add_sub_cancel']
  rwa [digits_length_le_iff hb]

theorem lt_of_mem_digitsAppend {b : ℕ} (hb : 1 < b) (l i : ℕ)
    (hi : i ∈ digitsAppend b l n) : i < b := by
  rw [digitsAppend, mem_append, mem_replicate] at hi
  obtain hi | ⟨_, rfl⟩ := hi
  · exact digits_lt_base hb hi
  · linarith

theorem mapsTo_ofDigits {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.MapsTo (ofDigits b) {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b} {n | n < b ^ l} :=
  fun _ h ↦ Set.mem_setOf.mpr h.1 ▸ Nat.ofDigits_lt_base_pow_length hb h.2

theorem mapsTo_digitsAppend {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.MapsTo (digitsAppend b l) {n | n < b ^ l} {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b} :=
  fun _ h ↦ ⟨by rw [length_digitsAppend hb _ h], fun _ hi ↦ lt_of_mem_digitsAppend hb l _ hi⟩

theorem injOn_ofDigits {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.InjOn (ofDigits b) {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b} :=
  fun _ _ _ _ h ↦ ofDigits_inj_of_len_eq hb (by aesop) (by aesop) (by aesop) h

theorem setInvOn_digitsAppend_ofDigits {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.InvOn (digitsAppend b l) (ofDigits b) {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b}
      {n | n < b ^ l} := by
  refine ⟨fun L hL ↦ ?_, fun _ _ ↦ by rw [digitsAppend, ofDigits_append_replicate_zero,
    ofDigits_digits]⟩
  refine (injOn_ofDigits hb l) ⟨?_, ?_⟩ hL
    (by rw [digitsAppend, ofDigits_append_replicate_zero, ofDigits_digits])
  · rw [length_digitsAppend hb _ (mapsTo_ofDigits hb _ hL)]
  · exact fun x hx ↦ lt_of_mem_digitsAppend hb l x hx

/--
The map `L ↦ Nat.ofDigits b L` is bijection between the set of lists of natural integers of
length `l` with coefficients `< b` to the set of natural integers `< b ^ l`.
-/
theorem bijOn_ofDigits {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.BijOn (ofDigits b) {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b} {n | n < b ^ l} :=
  (setInvOn_digitsAppend_ofDigits hb l).bijOn (mapsTo_ofDigits hb l) (mapsTo_digitsAppend hb l)

/--
The map `n ↦ Nat.digitsAppend b L` is bijection between the set of natural integers `< b ^ l`
to the set of lists of natural integers of length `l` with coefficients `< b` to .
-/
theorem bijOn_digitsAppend {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.BijOn (digitsAppend b l) {n | n < b ^ l} {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b} :=
  (bijOn_ofDigits hb l).symm (setInvOn_digitsAppend_ofDigits hb l).symm

theorem sum_digits_ofDigits_eq_sum {b : ℕ} (hb : 1 < b) {l : ℕ} {L : List ℕ}
    (hL : L ∈ {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b}) :
    (b.digits (ofDigits b L)).sum = L.sum := by
  nth_rewrite 2 [← (setInvOn_digitsAppend_ofDigits hb l).1 hL]
  rw [digitsAppend, List.sum_append_nat, List.sum_replicate, nsmul_zero, add_zero]

end Nat

namespace List

open Nat

/--
The set of lists of natural integers of length `l` with coefficients `< b` as a `Finset`.
This can be seen as the set of lists of length `l` of the digits in base `b` of
the integers `< b ^ l`.
Having this set as a `Finset` can be helpful for some proofs.
-/
noncomputable def fixedLengthDigits {b : ℕ} (hb : 1 < b) (l : ℕ) : Finset (List ℕ) := by
  have : Fintype {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b} :=
    Fintype.ofInjective (Set.MapsTo.restrict _ _ _ (mapsTo_ofDigits hb l))
      <| (Set.MapsTo.restrict_inj (mapsTo_ofDigits hb l)).mpr <| injOn_ofDigits hb l
  exact {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b}.toFinset

theorem mem_fixedLengthDigits_iff {b : ℕ} (hb : 1 < b) {l : ℕ} {L : List ℕ} :
    L ∈ fixedLengthDigits hb l ↔ L.length = l ∧ ∀ x ∈ L, x < b := by
  simp [fixedLengthDigits]

/--
The bijection `Nat.bijOn_ofDigits` stated as a bijection between `Finset`.
This spelling can be helpful for some proofs.
-/
theorem _root_.Nat.bijOn_ofDigits' {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.BijOn (ofDigits b) (fixedLengthDigits hb l) (Finset.range (b ^ l)) := by
  rw [fixedLengthDigits, Set.coe_toFinset]
  convert bijOn_ofDigits hb l
  ext; simp

/--
The bijection `Nat.bijOn_digitsAppend` stated as a bijection between `Finset`.
This spelling can be helpful for some proofs.
-/
theorem _root_.Nat.bijOn_digitsAppend' {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.BijOn (digitsAppend b l) (Finset.range (b ^ l)) (fixedLengthDigits hb l) := by
  rw [fixedLengthDigits, Set.coe_toFinset]
  convert bijOn_digitsAppend hb l
  ext; simp

@[simp]
theorem fixedLengthDigits_zero {b : ℕ} (hb : 1 < b) :
    fixedLengthDigits hb 0 = {[]} := by
  ext
  simpa [eq_comm, fixedLengthDigits] using by grind

@[simp]
theorem fixedLengthDigits_one {b : ℕ} (hb : 1 < b) :
    fixedLengthDigits hb 1 = Finset.image (fun x : ℕ ↦ [x]) (Finset.range b) := by
  ext
  rw [mem_fixedLengthDigits_iff, List.length_eq_one_iff]
  grind

theorem card_fixedLengthDigits {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Finset.card (fixedLengthDigits hb l) = b ^ l := by
  rw [Set.BijOn.finsetCard_eq (ofDigits b) (bijOn_ofDigits' hb l), Finset.card_range]

/--
The `Finset` of lists whose head is a fixed integer `d` and tail is a list
in `List.fixedLengthDigits b l`.
-/
noncomputable def consFixedLengthDigits {b : ℕ} (hb : 1 < b) (l d : ℕ) :
    Finset (List ℕ) := Finset.image (fun L ↦ d :: L) (fixedLengthDigits hb l)

theorem ne_empty_of_mem_consFixedLengthDigits {b : ℕ} (hb : 1 < b) {l d : ℕ} {L : List ℕ}
    (hL : L ∈ consFixedLengthDigits hb l d) : L ≠ [] := by
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hL
  exact cons_ne_nil d _

theorem consFixedLengthDigits_head {b : ℕ} (hb : 1 < b) {l d : ℕ} {L : List ℕ}
    (hL : L ∈ consFixedLengthDigits hb l d) :
    List.head L (ne_empty_of_mem_consFixedLengthDigits hb hL) = d := by
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hL
  rw [head_cons]

/--
If `L` is a list in `List.fixedLengthDigits b l` and `d` is an integer `< b`, then
`d :: L` is a list in `List.fixedLengthDigits b (l + 1).`
-/
theorem cons_mem_fixedLengthDigits_succ {b : ℕ} (hb : 1 < b) (l d : ℕ) (hd : d < b) {L : List ℕ}
    (hL : L ∈ fixedLengthDigits hb l) :
    d :: L ∈ fixedLengthDigits hb (l + 1) := by
  refine (mem_fixedLengthDigits_iff hb).mpr ⟨?_, ?_⟩
  · simpa using ((mem_fixedLengthDigits_iff hb).mp hL).1
  · intro x hx
    obtain rfl | hx := mem_cons.mp hx
    · exact hd
    · exact ((mem_fixedLengthDigits_iff hb).mp hL).2 _ hx

theorem pairwiseDisjoint_consFixedLengthDigits {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.PairwiseDisjoint (Finset.range b : Set ℕ) (fun d ↦ consFixedLengthDigits hb l d) := by
  refine Finset.pairwiseDisjoint_iff.mpr fun i _ j _ ⟨L, hL⟩ ↦ ?_
  rw [Finset.mem_inter] at hL
  exact (consFixedLengthDigits_head hb hL.1).symm.trans (consFixedLengthDigits_head hb hL.2)

/--
The set `List.fixedLengthDigits b (l + 1)` is the disjoint union of the sets
`List.consFixedLengthDigits b l d` where `d` ranges through the natural integers `< d`.
-/
theorem fixedLengthDigits_succ_eq_disjiUnion {b : ℕ} (hb : 1 < b) (l : ℕ) :
    fixedLengthDigits hb (l + 1) = Finset.disjiUnion (Finset.range b)
      (consFixedLengthDigits hb l) (pairwiseDisjoint_consFixedLengthDigits hb l) := by
  ext L
  simp_rw [Finset.disjiUnion_eq_biUnion, Finset.mem_biUnion, Finset.mem_range,
    consFixedLengthDigits, Finset.mem_image]
  refine ⟨fun hL ↦ ?_, ?_⟩
  · have hL₁ : L.length = l + 1 := ((mem_fixedLengthDigits_iff hb).mp hL).1
    have hL₂ : ∀ x ∈ L, x < b := ((mem_fixedLengthDigits_iff hb).mp hL).2
    have hL₃ : L ≠ [] := by simp [ne_nil_iff_length_pos, hL₁]
    refine ⟨L.head hL₃, hL₂ _ (L.head_mem hL₃), L.tail, ?_, cons_head_tail hL₃⟩
    refine (mem_fixedLengthDigits_iff hb).mpr ⟨?_, ?_⟩
    · rw [length_tail, hL₁, Nat.add_sub_cancel_right]
    · exact fun x hx ↦ hL₂ _ <| mem_of_mem_tail hx
  · rintro ⟨d, hd₁, T, hT, rfl⟩
    exact cons_mem_fixedLengthDigits_succ hb l d hd₁ hT

theorem sum_fixedLengthDigits_sum {b : ℕ} (hb : 1 < b) (l : ℕ) :
    ∑ L ∈ fixedLengthDigits hb l, L.sum = l * b ^ (l - 1) * b.choose 2 := by
  induction l with
  | zero => simp
  | succ l hr =>
      by_cases hl : l = 0
      · simp [hl, fixedLengthDigits_one, Finset.sum_range_id, choose_two_right]
      rw [fixedLengthDigits_succ_eq_disjiUnion, Finset.sum_disjiUnion]
      simp only [consFixedLengthDigits, cons.injEq, true_and, implies_true, Set.injOn_of_eq_iff_eq,
        Finset.sum_image, sum_cons]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_nsmul, Finset.sum_range_id, hr,
        nsmul_eq_mul, Finset.card_range, add_tsub_cancel_right, cast_id, card_fixedLengthDigits,
        choose_two_right]
      rw [show b ^ l = b * b ^ (l - 1) by rw [← Nat.pow_succ', Nat.sub_one, Nat.succ_pred hl]]
      ring

end List

/--
The formula for the sum of the sum of the digits in base `b` over the natural integers `< b ^ l`.
-/
theorem Nat.sum_sum_digits_eq {b : ℕ} (hb : 1 < b) (l : ℕ) :
    ∑ x ∈ Finset.range (b ^ l), (b.digits x).sum = l * b ^ (l - 1) * b.choose 2 := by
  rw [← List.sum_fixedLengthDigits_sum hb]
  refine (Finset.sum_nbij (ofDigits b) (by exact (bijOn_ofDigits' hb l).1)
    (bijOn_ofDigits' hb l).2.1 (bijOn_ofDigits' hb l).2.2 fun L hL ↦ ?_).symm
  rw [sum_digits_ofDigits_eq_sum hb ((List.mem_fixedLengthDigits_iff hb).mp hL)]
