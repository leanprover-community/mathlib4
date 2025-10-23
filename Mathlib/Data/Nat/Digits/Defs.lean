/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shing Tak Lam, Mario Carneiro
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Group.Nat

/-!
# Digits of a natural number

This provides a basic API for extracting the digits of a natural number in a given base,
and reconstructing numbers from their digits.

We also prove some divisibility tests based on digits, in particular completing
Theorem #85 from https://www.cs.ru.nl/~freek/100/.

Also included is a bound on the length of `Nat.toDigits` from core.

## TODO

A basic `norm_digits` tactic for proving goals of the form `Nat.digits a b = l` where `a` and `b`
are numerals is not yet ported.
-/

assert_not_exists Finset

namespace Nat

variable {n : ℕ}

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digitsAux0 : ℕ → List ℕ
  | 0 => []
  | n + 1 => [n+1]

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digitsAux1 (n : ℕ) : List ℕ :=
  List.replicate n 1

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digitsAux (b : ℕ) (h : 2 ≤ b) (n : ℕ) : List ℕ :=
  go n (n + 2) init
where
  init : (if n = 0 then 0 else n + 1) < n + 2 := by
    split_ifs <;> simp
  decreasing (n f : ℕ) (hf : (if n + 1 = 0 then 0 else n + 2) < f + 1) :
      (if (n + 1) / b = 0 then 0 else ((n + 1) / b) + 1) < f := by
    rw [if_neg n.add_one_ne_zero] at hf
    split_ifs with hn
    · exact zero_lt_of_lt (lt_of_succ_lt_succ hf)
    · rw [Nat.div_eq_zero_iff, or_iff_right (by omega), not_lt] at hn
      refine Nat.lt_of_le_of_lt (succ_le_succ ?_) (succ_lt_succ_iff.1 hf)
      refine Nat.div_le_of_le_mul (Nat.le_trans ?_ (Nat.mul_le_mul_right n h))
      omega
  /-- Auxiliary function performing recursion for `Nat.digitsAux`. -/
  go (n fuel : ℕ) (hfuel : (if n = 0 then 0 else n + 1) < fuel) : List ℕ :=
    match n, fuel, hfuel with
    | 0, _, _ => []
    | n + 1, f + 1, hf =>
      ((n + 1) % b) :: go ((n + 1) / b) f (decreasing n f hf)

theorem digitsAux.go_zero (b : ℕ) (h : 2 ≤ b) (fuel : ℕ)
    (hfuel : (if 0 = 0 then 0 else n + 1) < fuel) :
    digitsAux.go b h 0 fuel hfuel = [] := by
  rw [digitsAux.go]

theorem digitsAux.go_succ (b : ℕ) (h : 2 ≤ b) (n fuel : ℕ)
    (hfuel : (if n + 1 = 0 then 0 else n + 2) < fuel + 1) :
    digitsAux.go b h (n + 1) (fuel + 1) hfuel = ((n + 1) % b) ::
      digitsAux.go b h ((n + 1) / b) fuel (decreasing b h n fuel hfuel) :=
  rfl

theorem digitsAux.go_fuel_irrel (b : ℕ) (h : 2 ≤ b) (n fuel fuel' : ℕ)
    (hfuel : (if n = 0 then 0 else n + 1) < fuel)
    (hfuel' : (if n = 0 then 0 else n + 1) < fuel') :
    digitsAux.go b h n fuel hfuel = digitsAux.go b h n fuel' hfuel' := by
  fun_induction go b h n fuel hfuel generalizing fuel'
  · rw [go_zero]
  · cases fuel'
    · simp at hfuel'
    · rw [go_succ]
      solve_by_elim

@[simp]
theorem digitsAux_zero (b : ℕ) (h : 2 ≤ b) :
    digitsAux b h 0 = [] := by rw [digitsAux, digitsAux.go]

theorem digitsAux_def (b : ℕ) (h : 2 ≤ b) (n : ℕ) (w : 0 < n) :
    digitsAux b h n = (n % b) :: digitsAux b h (n / b) := by
  cases n
  · cases w
  · rw [digitsAux, digitsAux.go, digitsAux, digitsAux.go_fuel_irrel]

/-- `digits b n` gives the digits, in little-endian order,
of a natural number `n` in a specified base `b`.

In any base, we have `ofDigits b L = L.foldr (fun x y ↦ x + b * y) 0`.
* For any `2 ≤ b`, we have `l < b` for any `l ∈ digits b n`,
  and the last digit is not zero.
  This uniquely specifies the behaviour of `digits b`.
* For `b = 1`, we define `digits 1 n = List.replicate n 1`.
* For `b = 0`, we define `digits 0 n = [n]`, except `digits 0 0 = []`.

Note this differs from the existing `Nat.toDigits` in core, which is used for printing numerals.
In particular, `Nat.toDigits b 0 = ['0']`, while `digits b 0 = []`.
-/
def digits : ℕ → ℕ → List ℕ
  | 0 => digitsAux0
  | 1 => digitsAux1
  | b + 2 => digitsAux (b + 2) (by simp)

@[simp]
theorem digits_zero (b : ℕ) : digits b 0 = [] := by
  rcases b with (_ | ⟨_ | ⟨_⟩⟩) <;> simp [digits, digitsAux0, digitsAux1]

theorem digits_zero_zero : digits 0 0 = [] :=
  rfl

@[simp]
theorem digits_zero_succ (n : ℕ) : digits 0 n.succ = [n+1] :=
  rfl

theorem digits_zero_succ' : ∀ {n : ℕ}, n ≠ 0 → digits 0 n = [n]
  | 0, h => (h rfl).elim
  | _ + 1, _ => rfl

@[simp]
theorem digits_one (n : ℕ) : digits 1 n = List.replicate n 1 :=
  rfl

-- no `@[simp]`: dsimp can prove this
theorem digits_one_succ (n : ℕ) : digits 1 (n + 1) = 1 :: digits 1 n :=
  rfl

theorem digits_add_two_add_one (b n : ℕ) :
    digits (b + 2) (n + 1) = ((n + 1) % (b + 2)) :: digits (b + 2) ((n + 1) / (b + 2)) := by
  simp [digits, digitsAux_def]

@[simp]
lemma digits_of_two_le_of_pos {b : ℕ} (hb : 2 ≤ b) (hn : 0 < n) :
    Nat.digits b n = n % b :: Nat.digits b (n / b) := by
  rw [Nat.eq_add_of_sub_eq hb rfl, Nat.eq_add_of_sub_eq hn rfl, Nat.digits_add_two_add_one]

theorem digits_def' :
    ∀ {b : ℕ} (_ : 1 < b) {n : ℕ} (_ : 0 < n), digits b n = (n % b) :: digits b (n / b)
  | 0, h => absurd h (by decide)
  | 1, h => absurd h (by decide)
  | b + 2, _ => digitsAux_def _ (by simp) _

@[simp]
theorem digits_of_lt (b x : ℕ) (hx : x ≠ 0) (hxb : x < b) : digits b x = [x] := by
  rcases exists_eq_succ_of_ne_zero hx with ⟨x, rfl⟩
  rcases Nat.exists_eq_add_of_le' ((Nat.le_add_left 1 x).trans_lt hxb) with ⟨b, rfl⟩
  rw [digits_add_two_add_one, div_eq_of_lt hxb, digits_zero, mod_eq_of_lt hxb]

theorem digits_add (b : ℕ) (h : 1 < b) (x y : ℕ) (hxb : x < b) (hxy : x ≠ 0 ∨ y ≠ 0) :
    digits b (x + b * y) = x :: digits b y := by
  rcases Nat.exists_eq_add_of_le' h with ⟨b, rfl : _ = _ + 2⟩
  cases y
  · simp [hxb, hxy.resolve_right (absurd rfl)]
  dsimp [digits]
  rw [digitsAux_def]
  · congr
    · simp [Nat.add_mod, mod_eq_of_lt hxb]
    · simp [add_mul_div_left, div_eq_of_lt hxb]
  · apply Nat.succ_pos

-- If we had a function converting a list into a polynomial,
-- and appropriate lemmas about that function,
-- we could rewrite this in terms of that.
/-- `ofDigits b L` takes a list `L` of natural numbers, and interprets them
as a number in semiring, as the little-endian digits in base `b`.
-/
def ofDigits {α : Type*} [Semiring α] (b : α) : List ℕ → α
  | [] => 0
  | h :: t => h + b * ofDigits b t

theorem ofDigits_eq_foldr {α : Type*} [Semiring α] (b : α) (L : List ℕ) :
    ofDigits b L = List.foldr (fun x y => ↑x + b * y) 0 L := by
  induction L with
  | nil => rfl
  | cons d L ih => dsimp [ofDigits]; rw [ih]

@[simp]
theorem ofDigits_nil {b : ℕ} : ofDigits b [] = 0 := rfl

@[simp]
theorem ofDigits_singleton {b n : ℕ} : ofDigits b [n] = n := by simp [ofDigits]

@[simp]
theorem ofDigits_one_cons {α : Type*} [Semiring α] (h : ℕ) (L : List ℕ) :
    ofDigits (1 : α) (h :: L) = h + ofDigits 1 L := by simp [ofDigits]

theorem ofDigits_cons {b hd} {tl : List ℕ} :
    ofDigits b (hd :: tl) = hd + b * ofDigits b tl := rfl

theorem ofDigits_append {b : ℕ} {l1 l2 : List ℕ} :
    ofDigits b (l1 ++ l2) = ofDigits b l1 + b ^ l1.length * ofDigits b l2 := by
  induction l1 with
  | nil => simp [ofDigits]
  | cons hd tl IH =>
    rw [ofDigits, List.cons_append, ofDigits, IH, List.length_cons, pow_succ']
    ring

@[simp]
theorem ofDigits_append_zero {b : ℕ} (l : List ℕ) :
    ofDigits b (l ++ [0]) = ofDigits b l := by
  rw [ofDigits_append, ofDigits_singleton, mul_zero, add_zero]

@[simp]
theorem ofDigits_replicate_zero {b k : ℕ} : ofDigits b (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate, ofDigits_cons, ih]

@[simp]
theorem ofDigits_append_replicate_zero {b k : ℕ} (l : List ℕ) :
    ofDigits b (l ++ List.replicate k 0) = ofDigits b l := by
  rw [ofDigits_append]
  simp

theorem ofDigits_reverse_cons {b : ℕ} (l : List ℕ) (d : ℕ) :
    ofDigits b (d :: l).reverse = ofDigits b l.reverse + b^l.length * d := by
  simp only [List.reverse_cons]
  rw [ofDigits_append]
  simp

theorem ofDigits_reverse_zero_cons {b : ℕ} (l : List ℕ) :
    ofDigits b (0 :: l).reverse = ofDigits b l.reverse := by
  simp only [List.reverse_cons, ofDigits_append_zero]

@[norm_cast]
theorem coe_ofDigits (α : Type*) [Semiring α] (b : ℕ) (L : List ℕ) :
    ((ofDigits b L : ℕ) : α) = ofDigits (b : α) L := by
  induction L with
  | nil => simp [ofDigits]
  | cons d L ih => dsimp [ofDigits]; push_cast; rw [ih]

@[deprecated (since := "2025-08-14")] alias coe_int_ofDigits := coe_ofDigits

theorem digits_zero_of_eq_zero {b : ℕ} (h : b ≠ 0) :
    ∀ {L : List ℕ} (_ : ofDigits b L = 0), ∀ l ∈ L, l = 0
  | _ :: _, h0, _, List.Mem.head .. => Nat.eq_zero_of_add_eq_zero_right h0
  | _ :: _, h0, _, List.Mem.tail _ hL =>
    digits_zero_of_eq_zero h (mul_right_injective₀ h (Nat.eq_zero_of_add_eq_zero_left h0)) _ hL

theorem digits_ofDigits (b : ℕ) (h : 1 < b) (L : List ℕ) (w₁ : ∀ l ∈ L, l < b)
    (w₂ : ∀ h : L ≠ [], L.getLast h ≠ 0) : digits b (ofDigits b L) = L := by
  induction L with
  | nil => simp
  | cons d L ih =>
    dsimp [ofDigits]
    replace w₂ := w₂ (by simp)
    rw [digits_add b h]
    · rw [ih]
      · intro l m
        apply w₁
        exact List.mem_cons_of_mem _ m
      · intro h
        rw [List.getLast_cons h] at w₂
        convert w₂
    · exact w₁ d List.mem_cons_self
    · by_cases h' : L = []
      · rcases h' with rfl
        left
        simpa using w₂
      · right
        contrapose! w₂
        refine digits_zero_of_eq_zero h.ne_bot w₂ _ ?_
        rw [List.getLast_cons h']
        exact List.getLast_mem h'

theorem ofDigits_digits (b n : ℕ) : ofDigits b (digits b n) = n := by
  rcases b with - | b
  · rcases n with - | n
    · rfl
    · simp
  · rcases b with - | b
    · induction n with
      | zero => rfl
      | succ n ih =>
        rw [Nat.zero_add] at ih ⊢
        simp only [ih, add_comm 1, ofDigits_one_cons, Nat.cast_id, digits_one_succ]
    · induction n using Nat.strongRecOn with | ind n h => ?_
      cases n
      · rw [digits_zero]
        rfl
      · simp only [digits_add_two_add_one]
        dsimp [ofDigits]
        rw [h _ (Nat.div_lt_self' _ b)]
        rw [Nat.mod_add_div]

theorem ofDigits_one (L : List ℕ) : ofDigits 1 L = L.sum := by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp [ofDigits, List.sum_cons, ih]

/-!
### Properties

This section contains various lemmas of properties relating to `digits` and `ofDigits`.
-/


theorem digits_eq_nil_iff_eq_zero {b n : ℕ} : digits b n = [] ↔ n = 0 := by
  constructor
  · intro h
    have : ofDigits b (digits b n) = ofDigits b [] := by rw [h]
    convert this
    rw [ofDigits_digits]
  · rintro rfl
    simp

theorem digits_ne_nil_iff_ne_zero {b n : ℕ} : digits b n ≠ [] ↔ n ≠ 0 :=
  not_congr digits_eq_nil_iff_eq_zero

theorem digits_eq_cons_digits_div {b n : ℕ} (h : 1 < b) (w : n ≠ 0) :
    digits b n = (n % b) :: digits b (n / b) :=
  digits_def' h (Nat.pos_of_ne_zero w)

theorem digits_getLast {b : ℕ} (m : ℕ) (h : 1 < b) (p q) :
    (digits b m).getLast p = (digits b (m / b)).getLast q := by
  by_cases hm : m = 0
  · simp [hm]
  simp only [digits_eq_cons_digits_div h hm]
  rw [List.getLast_cons]

theorem digits.injective (b : ℕ) : Function.Injective b.digits :=
  Function.LeftInverse.injective (ofDigits_digits b)

@[simp]
theorem digits_inj_iff {b n m : ℕ} : b.digits n = b.digits m ↔ n = m :=
  (digits.injective b).eq_iff

theorem mul_ofDigits (n : ℕ) {b : ℕ} {l : List ℕ} :
    n * ofDigits b l = ofDigits b (l.map (n * ·)) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, ofDigits_cons, ofDigits_cons, ← ih]
    ring

lemma ofDigits_inj_of_len_eq {b : ℕ} (hb : 1 < b) {L1 L2 : List ℕ}
    (len : L1.length = L2.length) (w1 : ∀ l ∈ L1, l < b) (w2 : ∀ l ∈ L2, l < b)
    (h : ofDigits b L1 = ofDigits b L2) : L1 = L2 := by
  induction L1 generalizing L2 with
  | nil =>
    simp only [List.length_nil] at len
    exact (List.length_eq_zero_iff.mp len.symm).symm
  | cons D L ih => ?_
  obtain ⟨d, l, rfl⟩ := List.exists_cons_of_length_eq_add_one len.symm
  simp only [List.length_cons, add_left_inj] at len
  simp only [ofDigits_cons] at h
  have eqd : D = d := by
    have H : (D + b * ofDigits b L) % b = (d + b * ofDigits b l) % b := by rw [h]
    simpa [mod_eq_of_lt (w2 d List.mem_cons_self),
      mod_eq_of_lt (w1 D List.mem_cons_self)] using H
  simp only [eqd, add_right_inj, mul_left_cancel_iff_of_pos (zero_lt_of_lt hb)] at h
  have := ih len (fun a ha ↦ w1 a <| List.mem_cons_of_mem D ha)
    (fun a ha ↦ w2 a <| List.mem_cons_of_mem d ha) h
  rw [eqd, this]

/-- The addition of ofDigits of two lists is equal to ofDigits of digit-wise addition of them -/
theorem ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq {b : ℕ} {l1 l2 : List ℕ}
    (h : l1.length = l2.length) :
    ofDigits b l1 + ofDigits b l2 = ofDigits b (l1.zipWith (· + ·) l2) := by
  induction l1 generalizing l2 with
  | nil => simp_all [eq_comm, List.length_eq_zero_iff, ofDigits]
  | cons hd₁ tl₁ ih₁ =>
    induction l2 generalizing tl₁ with
    | nil => simp_all
    | cons hd₂ tl₂ ih₂ =>
      simp_all only [List.length_cons, ofDigits_cons, add_left_inj,
        eq_comm, List.zipWith_cons_cons]
      rw [← ih₁ h.symm, mul_add]
      ac_rfl

/-- The digits in the base b+2 expansion of n are all less than b+2 -/
theorem digits_lt_base' {b m : ℕ} : ∀ {d}, d ∈ digits (b + 2) m → d < b + 2 := by
  induction m using Nat.strongRecOn with | ind n IH => ?_
  intro d hd
  rcases n with - | n
  · rw [digits_zero] at hd
    cases hd
  -- base b+2 expansion of 0 has no digits
  rw [digits_add_two_add_one] at hd
  cases hd
  · exact n.succ.mod_lt (by linarith)
  · apply IH ((n + 1) / (b + 2))
    · apply Nat.div_lt_self <;> omega
    · assumption

/-- The digits in the base b expansion of n are all less than b, if b ≥ 2 -/
theorem digits_lt_base {b m d : ℕ} (hb : 1 < b) (hd : d ∈ digits b m) : d < b := by
  rcases b with (_ | _ | b) <;> try simp_all
  exact digits_lt_base' hd

/-- an n-digit number in base b + 2 is less than (b + 2)^n -/
theorem ofDigits_lt_base_pow_length' {b : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, x < b + 2) :
    ofDigits (b + 2) l < (b + 2) ^ l.length := by
  induction l with
  | nil => simp [ofDigits]
  | cons hd tl IH =>
    rw [ofDigits, List.length_cons, pow_succ]
    have : (ofDigits (b + 2) tl + 1) * (b + 2) ≤ (b + 2) ^ tl.length * (b + 2) :=
      mul_le_mul (IH fun x hx => hl _ (List.mem_cons_of_mem _ hx)) (by rfl) (by simp only [zero_le])
        (Nat.zero_le _)
    suffices ↑hd < b + 2 by linarith
    exact hl hd List.mem_cons_self

/-- an n-digit number in base b is less than b^n if b > 1 -/
theorem ofDigits_lt_base_pow_length {b : ℕ} {l : List ℕ} (hb : 1 < b) (hl : ∀ x ∈ l, x < b) :
    ofDigits b l < b ^ l.length := by
  rcases b with (_ | _ | b) <;> try simp_all
  exact ofDigits_lt_base_pow_length' hl

/-- Any number m is less than (b+2)^(number of digits in the base b + 2 representation of m) -/
theorem lt_base_pow_length_digits' {b m : ℕ} : m < (b + 2) ^ (digits (b + 2) m).length := by
  convert @ofDigits_lt_base_pow_length' b (digits (b + 2) m) fun _ => digits_lt_base'
  rw [ofDigits_digits (b + 2) m]

/-- Any number m is less than b^(number of digits in the base b representation of m) -/
theorem lt_base_pow_length_digits {b m : ℕ} (hb : 1 < b) : m < b ^ (digits b m).length := by
  rcases b with (_ | _ | b) <;> try simp_all
  exact lt_base_pow_length_digits'

theorem digits_base_mul {b m : ℕ} (hb : 1 < b) (hm : 0 < m) :
    b.digits (b * m) = 0 :: b.digits m := by
  rw [digits_def' hb (by positivity)]
  simp [mul_div_right m (by positivity)]

theorem digits_base_pow_mul {b k m : ℕ} (hb : 1 < b) (hm : 0 < m) :
    digits b (b ^ k * m) = List.replicate k 0 ++ digits b m := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, digits_base_mul hb (by positivity), ih hm, List.replicate_succ,
      List.cons_append]

theorem ofDigits_digits_append_digits {b m n : ℕ} :
    ofDigits b (digits b n ++ digits b m) = n + b ^ (digits b n).length * m := by
  rw [ofDigits_append, ofDigits_digits, ofDigits_digits]

@[mono]
theorem ofDigits_monotone {p q : ℕ} (L : List ℕ) (h : p ≤ q) : ofDigits p L ≤ ofDigits q L := by
  induction L with
  | nil => rfl
  | cons _ _ hi =>
    simp only [ofDigits, cast_id, add_le_add_iff_left]
    exact Nat.mul_le_mul h hi

theorem sum_le_ofDigits {p : ℕ} (L : List ℕ) (h : 1 ≤ p) : L.sum ≤ ofDigits p L :=
  (ofDigits_one L).symm ▸ ofDigits_monotone L h

theorem digit_sum_le (p n : ℕ) : List.sum (digits p n) ≤ n := by
  induction n with
  | zero => exact digits_zero _ ▸ Nat.le_refl (List.sum [])
  | succ n =>
    induction p with
    | zero => rw [digits_zero_succ, List.sum_cons, List.sum_nil, add_zero]
    | succ p =>
      nth_rw 2 [← ofDigits_digits p.succ (n + 1)]
      rw [← ofDigits_one <| digits p.succ n.succ]
      exact ofDigits_monotone (digits p.succ n.succ) <| Nat.succ_pos p

/-- Interpreting as a base `p` number and dividing by `p` is the same as interpreting the tail.
-/
lemma ofDigits_div_eq_ofDigits_tail {p : ℕ} (hpos : 0 < p) (digits : List ℕ)
    (w₁ : ∀ l ∈ digits, l < p) : ofDigits p digits / p = ofDigits p digits.tail := by
  induction digits with
  | nil => simp [ofDigits]
  | cons hd tl =>
    refine Eq.trans (add_mul_div_left hd _ hpos) ?_
    rw [Nat.div_eq_of_lt <| w₁ _ List.mem_cons_self, zero_add, List.tail_cons]

/-- Interpreting as a base `p` number and dividing by `p^i` is the same as dropping `i`.
-/
lemma ofDigits_div_pow_eq_ofDigits_drop
    {p : ℕ} (i : ℕ) (hpos : 0 < p) (digits : List ℕ) (w₁ : ∀ l ∈ digits, l < p) :
    ofDigits p digits / p ^ i = ofDigits p (digits.drop i) := by
  induction i with
  | zero => simp
  | succ i hi =>
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hi, ofDigits_div_eq_ofDigits_tail hpos
      (List.drop i digits) fun x hx ↦ w₁ x <| List.mem_of_mem_drop hx, ← List.drop_one,
      List.drop_drop, add_comm]

/-- Dividing `n` by `p^i` is like truncating the first `i` digits of `n` in base `p`.
-/
lemma self_div_pow_eq_ofDigits_drop {p : ℕ} (i n : ℕ) (h : 2 ≤ p) :
    n / p ^ i = ofDigits p ((p.digits n).drop i) := by
  convert ofDigits_div_pow_eq_ofDigits_drop i (zero_lt_of_lt h) (p.digits n)
    (fun l hl ↦ digits_lt_base h hl)
  exact (ofDigits_digits p n).symm

/-- Interpreting as a base `p` number and modulo `p^i` is the same as taking the first `i` digits.
-/
lemma ofDigits_mod_pow_eq_ofDigits_take
    {p : ℕ} (i : ℕ) (hpos : 0 < p) (digits : List ℕ) (w₁ : ∀ l ∈ digits, l < p) :
    ofDigits p digits % p ^ i = ofDigits p (digits.take i) := by
  induction i generalizing digits with
  | zero => simp [mod_one]
  | succ i ih =>
    cases digits with
    | nil => simp
    | cons hd tl =>
      rw [List.take_succ_cons, ofDigits_cons, ofDigits_cons,
        ← ih _ fun x hx ↦ w₁ x <| List.mem_cons_of_mem hd hx, add_mod,
        mod_eq_of_lt <| lt_of_lt_of_le (w₁ hd List.mem_cons_self) (le_pow <| add_one_pos i),
        pow_succ', mul_mod_mul_left, mod_eq_of_lt]
      apply add_lt_of_lt_sub
      apply lt_of_lt_of_le (b := p)
      · exact w₁ hd List.mem_cons_self
      · rw [← Nat.mul_sub]
        exact Nat.le_mul_of_pos_right _ <| Nat.sub_pos_of_lt <| mod_lt _ <| pow_pos hpos i

/-- `n` modulo `p^i` is like taking the least significant `i` digits of `n` in base `p`.
-/
lemma self_mod_pow_eq_ofDigits_take {p : ℕ} (i n : ℕ) (h : 2 ≤ p) :
    n % p ^ i = ofDigits p ((p.digits n).take i) := by
  convert ofDigits_mod_pow_eq_ofDigits_take i (zero_lt_of_lt h) (p.digits n)
    (fun l hl ↦ digits_lt_base h hl)
  exact (ofDigits_digits p n).symm

/-! ### `Nat.toDigits` length -/

lemma toDigitsCore_lens_eq_aux (b f : Nat) :
    ∀ (n : Nat) (l1 l2 : List Char), l1.length = l2.length →
    (Nat.toDigitsCore b f n l1).length = (Nat.toDigitsCore b f n l2).length := by
  induction f with (simp only [Nat.toDigitsCore]; intro n l1 l2 hlen)
  | zero => assumption
  | succ f ih =>
    if hx : n / b = 0 then
      simp only [hx, if_true, List.length, congrArg (fun l ↦ l + 1) hlen]
    else
      simp only [hx, if_false]
      specialize ih (n / b) (Nat.digitChar (n % b) :: l1) (Nat.digitChar (n % b) :: l2)
      simp only [List.length, congrArg (fun l ↦ l + 1) hlen] at ih
      exact ih trivial

lemma toDigitsCore_lens_eq (b f : Nat) : ∀ (n : Nat) (c : Char) (tl : List Char),
    (Nat.toDigitsCore b f n (c :: tl)).length = (Nat.toDigitsCore b f n tl).length + 1 := by
  induction f with (intro n c tl; simp only [Nat.toDigitsCore, List.length])
  | succ f ih =>
    grind

lemma nat_repr_len_aux (n b e : Nat) (h_b_pos : 0 < b) :  n < b ^ e.succ → n / b < b ^ e := by
  simp only [Nat.pow_succ]
  exact (@Nat.div_lt_iff_lt_mul b n (b ^ e) h_b_pos).mpr

/-- The String representation produced by toDigitsCore has the proper length relative to
the number of digits in `n < e` for some base `b`. Since this works with any base,
it can be used for binary, decimal, and hex. -/
lemma toDigitsCore_length (b f n e : Nat) (h_e_pos : 0 < e) (hlt : n < b ^ e) :
    (Nat.toDigitsCore b f n []).length ≤ e := by
  induction f generalizing n e hlt h_e_pos with
  | zero => simp only [toDigitsCore, List.length, zero_le]
  | succ f ih =>
    simp only [toDigitsCore]
    cases e with
    | zero => exact False.elim (Nat.lt_irrefl 0 h_e_pos)
    | succ e =>
      cases e with
      | zero =>
        rw [zero_add, pow_one] at hlt
        simp [Nat.div_eq_of_lt hlt]
      | succ e =>
        specialize ih (n / b) _ (add_one_pos e) (Nat.div_lt_of_lt_mul <| by rwa [← pow_add_one'])
        split_ifs
        · simp only [List.length_singleton, _root_.zero_le, succ_le_succ]
        · simp only [toDigitsCore_lens_eq b f (n / b) (Nat.digitChar <| n % b),
            Nat.succ_le_succ_iff, ih]

/-- The core implementation of `Nat.toDigits` returns a String with length less than or equal to the
number of digits in the base-`b` number (represented by `e`). For example, the string
representation of any number less than `b ^ 3` has a length less than or equal to 3. -/
lemma toDigits_length (b n e : Nat) : 0 < e → n < b ^ e → (Nat.toDigits b n).length ≤ e :=
  toDigitsCore_length _ _ _ _

/-- The core implementation of `Nat.repr` returns a String with length less than or equal to the
number of digits in the decimal number (represented by `e`). For example, the decimal string
representation of any number less than 1000 (10 ^ 3) has a length less than or equal to 3. -/
lemma repr_length (n e : Nat) : 0 < e → n < 10 ^ e → (Nat.repr n).length ≤ e :=
  toDigits_length _ _ _

/-! ### `norm_digits` tactic -/


namespace NormDigits

theorem digits_succ (b n m r l) (e : r + b * m = n) (hr : r < b)
    (h : Nat.digits b m = l ∧ 1 < b ∧ 0 < m) : (Nat.digits b n = r :: l) ∧ 1 < b ∧ 0 < n := by
  rcases h with ⟨h, b2, m0⟩
  have b0 : 0 < b := by omega
  have n0 : 0 < n := by linarith [mul_pos b0 m0]
  refine ⟨?_, b2, n0⟩
  obtain ⟨rfl, rfl⟩ := (Nat.div_mod_unique b0).2 ⟨e, hr⟩
  subst h; exact Nat.digits_def' b2 n0

theorem digits_one (b n) (n0 : 0 < n) (nb : n < b) : Nat.digits b n = [n] ∧ 1 < b ∧ 0 < n := by
  have b2 : 1 < b :=
    lt_iff_add_one_le.mpr (le_trans (add_le_add_right (lt_iff_add_one_le.mp n0) 1) nb)
  refine ⟨?_, b2, n0⟩
  rw [Nat.digits_def' b2 n0, Nat.mod_eq_of_lt nb, Nat.div_eq_zero_iff.2 <| .inr nb, Nat.digits_zero]

/-
Porting note: this part of the file is tactic related.

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

/-- A tactic for normalizing expressions of the form `Nat.digits a b = l` where
`a` and `b` are numerals.

```
example : Nat.digits 10 123 = [3,2,1] := by norm_num
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
-/

end NormDigits

end Nat
