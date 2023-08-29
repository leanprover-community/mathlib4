/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Shing Tak Lam, Mario Carneiro
-/
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.BigOperators.Lemmas
import Mathlib.Data.List.Indexes
import Mathlib.Data.List.Palindrome
import Mathlib.Algebra.Parity
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

#align_import data.nat.digits from "leanprover-community/mathlib"@"369525b73f229ccd76a6ec0e0e0bf2be57599768"

/-!
# Digits of a natural number

This provides a basic API for extracting the digits of a natural number in a given base,
and reconstructing numbers from their digits.

We also prove some divisibility tests based on digits, in particular completing
Theorem #85 from https://www.cs.ru.nl/~freek/100/.

A basic `norm_digits` tactic is also provided for proving goals of the form
`Nat.digits a b = l` where `a` and `b` are numerals.
-/

set_option autoImplicit true


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

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digitsAux (b : ℕ) (h : 2 ≤ b) : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    ((n + 1) % b) :: digitsAux b h ((n + 1) / b)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) h
              -- 🎉 no goals
#align nat.digits_aux Nat.digitsAux

@[simp]
theorem digitsAux_zero (b : ℕ) (h : 2 ≤ b) : digitsAux b h 0 = [] := by rw [digitsAux]
                                                                        -- 🎉 no goals
#align nat.digits_aux_zero Nat.digitsAux_zero

theorem digitsAux_def (b : ℕ) (h : 2 ≤ b) (n : ℕ) (w : 0 < n) :
    digitsAux b h n = (n % b) :: digitsAux b h (n / b) := by
  cases n
  -- ⊢ digitsAux b h zero = zero % b :: digitsAux b h (zero / b)
  · cases w
    -- 🎉 no goals
  · rw [digitsAux]
    -- 🎉 no goals
#align nat.digits_aux_def Nat.digitsAux_def

/-- `digits b n` gives the digits, in little-endian order,
of a natural number `n` in a specified base `b`.

In any base, we have `ofDigits b L = L.foldr (fun x y ↦ x + b * y) 0`.
* For any `2 ≤ b`, we have `l < b` for any `l ∈ digits b n`,
  and the last digit is not zero.
  This uniquely specifies the behaviour of `digits b`.
* For `b = 1`, we define `digits 1 n = List.replicate n 1`.
* For `b = 0`, we define `digits 0 n = [n]`, except `digits 0 0 = []`.

Note this differs from the existing `Nat.to_digits` in core, which is used for printing numerals.
In particular, `Nat.to_digits b 0 = [0]`, while `digits b 0 = []`.
-/
def digits : ℕ → ℕ → List ℕ
  | 0 => digitsAux0
  | 1 => digitsAux1
  | b + 2 => digitsAux (b + 2) (by norm_num)
                                   -- 🎉 no goals
#align nat.digits Nat.digits

@[simp]
theorem digits_zero (b : ℕ) : digits b 0 = [] := by
  rcases b with (_ | ⟨_ | ⟨_⟩⟩) <;> simp [digits, digitsAux0, digitsAux1]
                                    -- 🎉 no goals
                                    -- 🎉 no goals
                                    -- 🎉 no goals
#align nat.digits_zero Nat.digits_zero

-- @[simp] -- Porting note: simp can prove this
theorem digits_zero_zero : digits 0 0 = [] :=
  rfl
#align nat.digits_zero_zero Nat.digits_zero_zero

@[simp]
theorem digits_zero_succ (n : ℕ) : digits 0 n.succ = [n + 1] :=
  rfl
#align nat.digits_zero_succ Nat.digits_zero_succ

theorem digits_zero_succ' : ∀ {n : ℕ}, n ≠ 0 → digits 0 n = [n]
  | 0, h => (h rfl).elim
  | _ + 1, _ => rfl
#align nat.digits_zero_succ' Nat.digits_zero_succ'

@[simp]
theorem digits_one (n : ℕ) : digits 1 n = List.replicate n 1 :=
  rfl
#align nat.digits_one Nat.digits_one

-- @[simp] -- Porting note: dsimp can prove this
theorem digits_one_succ (n : ℕ) : digits 1 (n + 1) = 1 :: digits 1 n :=
  rfl
#align nat.digits_one_succ Nat.digits_one_succ

@[simp]
theorem digits_add_two_add_one (b n : ℕ) :
    digits (b + 2) (n + 1) = ((n + 1) % (b + 2)) :: digits (b + 2) ((n + 1) / (b + 2)) := by
  simp [digits, digitsAux_def]
  -- 🎉 no goals
#align nat.digits_add_two_add_one Nat.digits_add_two_add_one

theorem digits_def' :
    ∀ {b : ℕ} (_ : 1 < b) {n : ℕ} (_ : 0 < n), digits b n = (n % b) :: digits b (n / b)
  | 0, h => absurd h (by decide)
                         -- 🎉 no goals
  | 1, h => absurd h (by decide)
                         -- 🎉 no goals
  | b + 2, _ => digitsAux_def _ (by simp) _
                                    -- 🎉 no goals
#align nat.digits_def' Nat.digits_def'

@[simp]
theorem digits_of_lt (b x : ℕ) (hx : x ≠ 0) (hxb : x < b) : digits b x = [x] := by
  rcases exists_eq_succ_of_ne_zero hx with ⟨x, rfl⟩
  -- ⊢ digits b (succ x) = [succ x]
  rcases exists_eq_add_of_le' ((Nat.le_add_left 1 x).trans_lt hxb) with ⟨b, rfl⟩
  -- ⊢ digits (b + succ 1) (succ x) = [succ x]
  rw [digits_add_two_add_one, div_eq_of_lt hxb, digits_zero, mod_eq_of_lt hxb]
  -- 🎉 no goals
#align nat.digits_of_lt Nat.digits_of_lt

theorem digits_add (b : ℕ) (h : 1 < b) (x y : ℕ) (hxb : x < b) (hxy : x ≠ 0 ∨ y ≠ 0) :
    digits b (x + b * y) = x :: digits b y := by
  rcases exists_eq_add_of_le' h with ⟨b, rfl : _ = _ + 2⟩
  -- ⊢ digits (b + 2) (x + (b + 2) * y) = x :: digits (b + 2) y
  cases y
  -- ⊢ digits (b + 2) (x + (b + 2) * zero) = x :: digits (b + 2) zero
  · simp [hxb, hxy.resolve_right (absurd rfl)]
    -- 🎉 no goals
  dsimp [digits]
  -- ⊢ digitsAux (b + 2) (_ : 2 ≤ b + 2) (x + (b + 2) * succ n✝) = x :: digitsAux ( …
  rw [digitsAux_def]
  -- ⊢ (x + (b + 2) * succ n✝) % (b + 2) :: digitsAux (b + 2) (_ : 2 ≤ b + 2) ((x + …
  · congr
    -- ⊢ (x + (b + 2) * succ n✝) % (b + 2) = x
    · simp [Nat.add_mod, mod_eq_of_lt hxb]
      -- 🎉 no goals
    · simp [add_mul_div_left, div_eq_of_lt hxb]
      -- 🎉 no goals
  · apply Nat.succ_pos
    -- 🎉 no goals
#align nat.digits_add Nat.digits_add

-- If we had a function converting a list into a polynomial,
-- and appropriate lemmas about that function,
-- we could rewrite this in terms of that.
/-- `ofDigits b L` takes a list `L` of natural numbers, and interprets them
as a number in semiring, as the little-endian digits in base `b`.
-/
def ofDigits {α : Type*} [Semiring α] (b : α) : List ℕ → α
  | [] => 0
  | h :: t => h + b * ofDigits b t
#align nat.of_digits Nat.ofDigits

theorem ofDigits_eq_foldr {α : Type*} [Semiring α] (b : α) (L : List ℕ) :
    ofDigits b L = List.foldr (fun x y => ↑x + b * y) 0 L := by
  induction' L with d L ih
  -- ⊢ ofDigits b [] = List.foldr (fun x y => ↑x + b * y) 0 []
  · rfl
    -- 🎉 no goals
  · dsimp [ofDigits]
    -- ⊢ ↑d + b * ofDigits b L = ↑d + b * List.foldr (fun x y => ↑x + b * y) 0 L
    rw [ih]
    -- 🎉 no goals
#align nat.of_digits_eq_foldr Nat.ofDigits_eq_foldr

theorem ofDigits_eq_sum_map_with_index_aux (b : ℕ) (l : List ℕ) :
    ((List.range l.length).zipWith ((fun i a : ℕ => a * b ^ i) ∘ succ) l).sum =
      b * ((List.range l.length).zipWith (fun i a => a * b ^ i) l).sum := by
  suffices
    (List.range l.length).zipWith ((fun i a : ℕ => a * b ^ i) ∘ succ) l =
      (List.range l.length).zipWith (fun i a => b * (a * b ^ i)) l
    by simp [this]
  congr; ext; simp [pow_succ]; ring
  -- ⊢ (fun i a => a * b ^ i) ∘ succ = fun i a => b * (a * b ^ i)
         -- ⊢ ((fun i a => a * b ^ i) ∘ succ) x✝¹ x✝ = b * (x✝ * b ^ x✝¹)
              -- ⊢ x✝ * (b ^ x✝¹ * b) = b * (x✝ * b ^ x✝¹)
                               -- 🎉 no goals
#align nat.of_digits_eq_sum_map_with_index_aux Nat.ofDigits_eq_sum_map_with_index_aux

theorem ofDigits_eq_sum_mapIdx (b : ℕ) (L : List ℕ) :
    ofDigits b L = (L.mapIdx fun i a => a * b ^ i).sum := by
  rw [List.mapIdx_eq_enum_map, List.enum_eq_zip_range, List.map_uncurry_zip_eq_zipWith,
    ofDigits_eq_foldr]
  induction' L with hd tl hl
  -- ⊢ List.foldr (fun x y => ↑x + b * y) 0 [] = List.sum (List.zipWith (fun i a => …
  · simp
    -- 🎉 no goals
  · simpa [List.range_succ_eq_map, List.zipWith_map_left, ofDigits_eq_sum_map_with_index_aux] using
      Or.inl hl
#align nat.of_digits_eq_sum_map_with_index Nat.ofDigits_eq_sum_mapIdx

@[simp]
theorem ofDigits_singleton {b n : ℕ} : ofDigits b [n] = n := by simp [ofDigits]
                                                                -- 🎉 no goals
#align nat.of_digits_singleton Nat.ofDigits_singleton

@[simp]
theorem ofDigits_one_cons {α : Type*} [Semiring α] (h : ℕ) (L : List ℕ) :
    ofDigits (1 : α) (h :: L) = h + ofDigits 1 L := by simp [ofDigits]
                                                       -- 🎉 no goals
#align nat.of_digits_one_cons Nat.ofDigits_one_cons

theorem ofDigits_append {b : ℕ} {l1 l2 : List ℕ} :
    ofDigits b (l1 ++ l2) = ofDigits b l1 + b ^ l1.length * ofDigits b l2 := by
  induction' l1 with hd tl IH
  -- ⊢ ofDigits b ([] ++ l2) = ofDigits b [] + b ^ List.length [] * ofDigits b l2
  · simp [ofDigits]
    -- 🎉 no goals
  · rw [ofDigits, List.cons_append, ofDigits, IH, List.length_cons, pow_succ']
    -- ⊢ ↑hd + b * (ofDigits b tl + b ^ List.length tl * ofDigits b l2) = ↑hd + b * o …
    ring
    -- 🎉 no goals
#align nat.of_digits_append Nat.ofDigits_append

@[norm_cast]
theorem coe_ofDigits (α : Type*) [Semiring α] (b : ℕ) (L : List ℕ) :
    ((ofDigits b L : ℕ) : α) = ofDigits (b : α) L := by
  induction' L with d L ih
  -- ⊢ ↑(ofDigits b []) = ofDigits ↑b []
  · simp [ofDigits]
    -- 🎉 no goals
  · dsimp [ofDigits]; push_cast; rw [ih]
    -- ⊢ ↑(d + b * ofDigits b L) = ↑d + ↑b * ofDigits (↑b) L
                      -- ⊢ ↑d + ↑b * ↑(ofDigits b L) = ↑d + ↑b * ofDigits (↑b) L
                                 -- 🎉 no goals
#align nat.coe_of_digits Nat.coe_ofDigits

@[norm_cast]
theorem coe_int_ofDigits (b : ℕ) (L : List ℕ) : ((ofDigits b L : ℕ) : ℤ) = ofDigits (b : ℤ) L := by
  induction' L with d L _
  -- ⊢ ↑(ofDigits b []) = ofDigits ↑b []
  · rfl
    -- 🎉 no goals
  · dsimp [ofDigits]; push_cast; simp only
    -- ⊢ ↑(d + b * ofDigits b L) = ↑d + ↑b * ofDigits (↑b) L
                      -- ⊢ ↑d + ↑b * ofDigits (↑b) L = ↑d + ↑b * ofDigits (↑b) L
                                 -- 🎉 no goals
#align nat.coe_int_of_digits Nat.coe_int_ofDigits

theorem digits_zero_of_eq_zero {b : ℕ} (h : b ≠ 0) :
    ∀ {L : List ℕ} (_ : ofDigits b L = 0), ∀ l ∈ L, l = 0
  | _ :: _, h0, _, List.Mem.head .. => Nat.eq_zero_of_add_eq_zero_right h0
  | _ :: _, h0, _, List.Mem.tail _ hL =>
    digits_zero_of_eq_zero h (mul_right_injective₀ h (Nat.eq_zero_of_add_eq_zero_left h0)) _ hL
#align nat.digits_zero_of_eq_zero Nat.digits_zero_of_eq_zero

theorem digits_ofDigits (b : ℕ) (h : 1 < b) (L : List ℕ) (w₁ : ∀ l ∈ L, l < b)
    (w₂ : ∀ h : L ≠ [], L.getLast h ≠ 0) : digits b (ofDigits b L) = L := by
  induction' L with d L ih
  -- ⊢ digits b (ofDigits b []) = []
  · dsimp [ofDigits]
    -- ⊢ digits b 0 = []
    simp
    -- 🎉 no goals
  · dsimp [ofDigits]
    -- ⊢ digits b (d + b * ofDigits b L) = d :: L
    replace w₂ := w₂ (by simp)
    -- ⊢ digits b (d + b * ofDigits b L) = d :: L
    rw [digits_add b h]
    · rw [ih]
      -- ⊢ ∀ (l : ℕ), l ∈ L → l < b
      · intro l m
        -- ⊢ l < b
        apply w₁
        -- ⊢ l ∈ d :: L
        exact List.mem_cons_of_mem _ m
        -- 🎉 no goals
      · intro h
        -- ⊢ List.getLast L h ≠ 0
        · rw [List.getLast_cons h] at w₂
          -- ⊢ List.getLast L h ≠ 0
          convert w₂
          -- 🎉 no goals
    · exact w₁ d (List.mem_cons_self _ _)
      -- 🎉 no goals
    · by_cases h' : L = []
      -- ⊢ d ≠ 0 ∨ ofDigits b L ≠ 0
      · rcases h' with rfl
        -- ⊢ d ≠ 0 ∨ ofDigits b [] ≠ 0
        left
        -- ⊢ d ≠ 0
        simpa using w₂
        -- 🎉 no goals
      · right
        -- ⊢ ofDigits b L ≠ 0
        contrapose! w₂
        -- ⊢ List.getLast (d :: L) (_ : ¬d :: L = []) = 0
        refine' digits_zero_of_eq_zero h.ne_bot w₂ _ _
        -- ⊢ List.getLast (d :: L) (_ : ¬d :: L = []) ∈ L
        rw [List.getLast_cons h']
        -- ⊢ List.getLast L h' ∈ L
        exact List.getLast_mem h'
        -- 🎉 no goals
#align nat.digits_of_digits Nat.digits_ofDigits

theorem ofDigits_digits (b n : ℕ) : ofDigits b (digits b n) = n := by
  cases' b with b
  -- ⊢ ofDigits zero (digits zero n) = n
  · cases' n with n
    -- ⊢ ofDigits zero (digits zero zero) = zero
    · rfl
      -- 🎉 no goals
    · change ofDigits 0 [n + 1] = n + 1
      -- ⊢ ofDigits 0 [n + 1] = n + 1
      dsimp [ofDigits]
      -- 🎉 no goals
  · cases' b with b
    -- ⊢ ofDigits (succ zero) (digits (succ zero) n) = n
    · induction' n with n ih
      -- ⊢ ofDigits (succ zero) (digits (succ zero) zero) = zero
      · rfl
        -- 🎉 no goals
      · rw[show succ zero = 1 by rfl] at ih ⊢
        -- ⊢ ofDigits 1 (digits 1 (succ n)) = succ n
        simp only [ih, add_comm 1, ofDigits_one_cons, Nat.cast_id, digits_one_succ]
        -- 🎉 no goals
    · apply Nat.strongInductionOn n _
      -- ⊢ ∀ (n : ℕ), (∀ (m : ℕ), m < n → ofDigits (succ (succ b)) (digits (succ (succ  …
      clear n
      -- ⊢ ∀ (n : ℕ), (∀ (m : ℕ), m < n → ofDigits (succ (succ b)) (digits (succ (succ  …
      intro n h
      -- ⊢ ofDigits (succ (succ b)) (digits (succ (succ b)) n) = n
      cases n
      -- ⊢ ofDigits (succ (succ b)) (digits (succ (succ b)) zero) = zero
      · rw [digits_zero]
        -- ⊢ ofDigits (succ (succ b)) [] = zero
        rfl
        -- 🎉 no goals
      · simp only [Nat.succ_eq_add_one, digits_add_two_add_one]
        -- ⊢ ofDigits (b + 1 + 1) ((n✝ + 1) % (b + 2) :: digits (b + 2) ((n✝ + 1) / (b +  …
        dsimp [ofDigits]
        -- ⊢ (n✝ + 1) % (b + 2) + (b + 1 + 1) * ofDigits (b + 1 + 1) (digits (b + 2) ((n✝ …
        rw [h _ (Nat.div_lt_self' _ b)]
        -- ⊢ (n✝ + 1) % (b + 2) + (b + 1 + 1) * ((n✝ + 1) / (b + 2)) = n✝ + 1
        rw [Nat.mod_add_div]
        -- 🎉 no goals
#align nat.of_digits_digits Nat.ofDigits_digits

theorem ofDigits_one (L : List ℕ) : ofDigits 1 L = L.sum := by
  induction' L with _ _ ih
  -- ⊢ ofDigits 1 [] = List.sum []
  · rfl
    -- 🎉 no goals
  · simp [ofDigits, List.sum_cons, ih]
    -- 🎉 no goals
#align nat.of_digits_one Nat.ofDigits_one

/-!
### Properties

This section contains various lemmas of properties relating to `digits` and `ofDigits`.
-/


theorem digits_eq_nil_iff_eq_zero {b n : ℕ} : digits b n = [] ↔ n = 0 := by
  constructor
  -- ⊢ digits b n = [] → n = 0
  · intro h
    -- ⊢ n = 0
    have : ofDigits b (digits b n) = ofDigits b [] := by rw [h]
    -- ⊢ n = 0
    convert this
    -- ⊢ n = ofDigits b (digits b n)
    rw [ofDigits_digits]
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ digits b 0 = []
    simp
    -- 🎉 no goals
#align nat.digits_eq_nil_iff_eq_zero Nat.digits_eq_nil_iff_eq_zero

theorem digits_ne_nil_iff_ne_zero {b n : ℕ} : digits b n ≠ [] ↔ n ≠ 0 :=
  not_congr digits_eq_nil_iff_eq_zero
#align nat.digits_ne_nil_iff_ne_zero Nat.digits_ne_nil_iff_ne_zero

theorem digits_eq_cons_digits_div {b n : ℕ} (h : 1 < b) (w : n ≠ 0) :
    digits b n = (n % b) :: digits b (n / b) := by
  rcases b with (_ | _ | b)
  · rw [digits_zero_succ' w, Nat.mod_zero, Nat.div_zero, Nat.digits_zero_zero]
    -- 🎉 no goals
  · norm_num at h
    -- 🎉 no goals
  rcases n with (_ | n)
  -- ⊢ digits (succ (succ b)) zero = zero % succ (succ b) :: digits (succ (succ b)) …
  · norm_num at w
    -- 🎉 no goals
  · simp only [digits_add_two_add_one, ne_eq]
    -- 🎉 no goals
#align nat.digits_eq_cons_digits_div Nat.digits_eq_cons_digits_div

theorem digits_getLast {b : ℕ} (m : ℕ) (h : 1 < b) (p q) :
    (digits b m).getLast p = (digits b (m / b)).getLast q := by
  by_cases hm : m = 0
  -- ⊢ List.getLast (digits b m) p = List.getLast (digits b (m / b)) q
  · simp [hm]
    -- 🎉 no goals
  simp only [digits_eq_cons_digits_div h hm]
  -- ⊢ List.getLast (m % b :: digits b (m / b)) (_ : m % b :: digits b (m / b) ≠ [] …
  rw [List.getLast_cons]
  -- 🎉 no goals
#align nat.digits_last Nat.digits_getLast

theorem digits.injective (b : ℕ) : Function.Injective b.digits :=
  Function.LeftInverse.injective (ofDigits_digits b)
#align nat.digits.injective Nat.digits.injective

@[simp]
theorem digits_inj_iff {b n m : ℕ} : b.digits n = b.digits m ↔ n = m :=
  (digits.injective b).eq_iff
#align nat.digits_inj_iff Nat.digits_inj_iff

theorem digits_len (b n : ℕ) (hb : 1 < b) (hn : n ≠ 0) : (b.digits n).length = b.log n + 1 := by
  induction' n using Nat.strong_induction_on with n IH
  -- ⊢ List.length (digits b n) = log b n + 1
  rw [digits_eq_cons_digits_div hb hn, List.length]
  -- ⊢ List.length (digits b (n / b)) + 1 = log b n + 1
  by_cases h : n / b = 0
  -- ⊢ List.length (digits b (n / b)) + 1 = log b n + 1
  · have hb0 : b ≠ 0 := (Nat.succ_le_iff.1 hb).ne_bot
    -- ⊢ List.length (digits b (n / b)) + 1 = log b n + 1
    simp [h, log_eq_zero_iff, ← Nat.div_eq_zero_iff hb0.bot_lt]
    -- 🎉 no goals
  · have : n / b < n := div_lt_self (Nat.pos_of_ne_zero hn) hb
    -- ⊢ List.length (digits b (n / b)) + 1 = log b n + 1
    rw [IH _ this h, log_div_base, tsub_add_cancel_of_le]
    -- ⊢ 1 ≤ log b n
    refine' Nat.succ_le_of_lt (log_pos hb _)
    -- ⊢ b ≤ n
    contrapose! h
    -- ⊢ n / b = 0
    exact div_eq_of_lt h
    -- 🎉 no goals
#align nat.digits_len Nat.digits_len

theorem getLast_digit_ne_zero (b : ℕ) {m : ℕ} (hm : m ≠ 0) :
    (digits b m).getLast (digits_ne_nil_iff_ne_zero.mpr hm) ≠ 0 := by
  rcases b with (_ | _ | b)
  · cases m
    -- ⊢ List.getLast (digits zero zero) (_ : digits zero zero ≠ []) ≠ 0
    · cases hm rfl
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
  · cases m
    -- ⊢ List.getLast (digits (succ zero) zero) (_ : digits (succ zero) zero ≠ []) ≠ 0
    · cases hm rfl
      -- 🎉 no goals
    rename ℕ => m
    -- ⊢ List.getLast (digits (succ zero) (succ m)) (_ : digits (succ zero) (succ m)  …
    simp only [digits_one, List.getLast_replicate_succ m 1]
    -- 🎉 no goals
  revert hm
  -- ⊢ ∀ (hm : m ≠ 0), List.getLast (digits (succ (succ b)) m) (_ : digits (succ (s …
  apply Nat.strongInductionOn m
  -- ⊢ ∀ (n : ℕ), (∀ (m : ℕ), m < n → ∀ (hm : m ≠ 0), List.getLast (digits (succ (s …
  intro n IH hn
  -- ⊢ List.getLast (digits (succ (succ b)) n) (_ : digits (succ (succ b)) n ≠ [])  …
  by_cases hnb : n < b + 2
  -- ⊢ List.getLast (digits (succ (succ b)) n) (_ : digits (succ (succ b)) n ≠ [])  …
  · simpa only [digits_of_lt (b + 2) n hn hnb]
    -- 🎉 no goals
  · rw [digits_getLast n (le_add_left 2 b)]
    -- ⊢ List.getLast (digits (b + 2) (n / (b + 2))) ?neg.q✝ ≠ 0
    refine' IH _ (Nat.div_lt_self hn.bot_lt (one_lt_succ_succ b)) _
    -- ⊢ n / succ (succ b) ≠ 0
    · rw [← pos_iff_ne_zero]
      -- ⊢ 0 < n / succ (succ b)
      exact Nat.div_pos (le_of_not_lt hnb) (zero_lt_succ (succ b))
      -- 🎉 no goals
#align nat.last_digit_ne_zero Nat.getLast_digit_ne_zero

/-- The digits in the base b+2 expansion of n are all less than b+2 -/
theorem digits_lt_base' {b m : ℕ} : ∀ {d}, d ∈ digits (b + 2) m → d < b + 2 := by
  apply Nat.strongInductionOn m
  -- ⊢ ∀ (n : ℕ), (∀ (m : ℕ), m < n → ∀ {d : ℕ}, d ∈ digits (b + 2) m → d < b + 2)  …
  intro n IH d hd
  -- ⊢ d < b + 2
  cases' n with n
  -- ⊢ d < b + 2
  · rw [digits_zero] at hd
    -- ⊢ d < b + 2
    cases hd
    -- 🎉 no goals
  -- base b+2 expansion of 0 has no digits
  rw [digits_add_two_add_one] at hd
  -- ⊢ d < b + 2
  cases hd
  -- ⊢ (n + 1) % (b + 2) < b + 2
  · exact n.succ.mod_lt (by simp)
    -- 🎉 no goals
  -- Porting note: Previous code (single line) contained linarith.
  -- . exact IH _ (Nat.div_lt_self (Nat.succ_pos _) (by linarith)) hd
  · apply IH ((n + 1) / (b + 2))
    -- ⊢ (n + 1) / (b + 2) < succ n
    · apply Nat.div_lt_self <;> simp
      -- ⊢ 0 < n + 1
                                -- 🎉 no goals
                                -- 🎉 no goals
    · assumption
      -- 🎉 no goals
#align nat.digits_lt_base' Nat.digits_lt_base'

/-- The digits in the base b expansion of n are all less than b, if b ≥ 2 -/
theorem digits_lt_base {b m d : ℕ} (hb : 1 < b) (hd : d ∈ digits b m) : d < b := by
  rcases b with (_ | _ | b) <;> try simp_all
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- ⊢ d < succ (succ b)
  exact digits_lt_base' hd
  -- 🎉 no goals
#align nat.digits_lt_base Nat.digits_lt_base

/-- an n-digit number in base b + 2 is less than (b + 2)^n -/
theorem ofDigits_lt_base_pow_length' {b : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, x < b + 2) :
    ofDigits (b + 2) l < (b + 2) ^ l.length := by
  induction' l with hd tl IH
  -- ⊢ ofDigits (b + 2) [] < (b + 2) ^ List.length []
  · simp [ofDigits]
    -- 🎉 no goals
  · rw [ofDigits, List.length_cons, pow_succ]
    -- ⊢ ↑hd + (b + 2) * ofDigits (b + 2) tl < (b + 2) ^ List.length tl * (b + 2)
    have : (ofDigits (b + 2) tl + 1) * (b + 2) ≤ (b + 2) ^ tl.length * (b + 2) :=
      mul_le_mul (IH fun x hx => hl _ (List.mem_cons_of_mem _ hx)) (by rfl) (by simp only [zero_le])
        (Nat.zero_le _)
    suffices ↑hd < b + 2 by linarith
    -- ⊢ hd < b + 2
    norm_cast
    -- ⊢ hd < b + 2
    exact hl hd (List.mem_cons_self _ _)
    -- 🎉 no goals
#align nat.of_digits_lt_base_pow_length' Nat.ofDigits_lt_base_pow_length'

/-- an n-digit number in base b is less than b^n if b > 1 -/
theorem ofDigits_lt_base_pow_length {b : ℕ} {l : List ℕ} (hb : 1 < b) (hl : ∀ x ∈ l, x < b) :
    ofDigits b l < b ^ l.length := by
  rcases b with (_ | _ | b) <;> try simp_all
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- ⊢ ofDigits (succ (succ b)) l < succ (succ b) ^ List.length l
  exact ofDigits_lt_base_pow_length' hl
  -- 🎉 no goals
#align nat.of_digits_lt_base_pow_length Nat.ofDigits_lt_base_pow_length

/-- Any number m is less than (b+2)^(number of digits in the base b + 2 representation of m) -/
theorem lt_base_pow_length_digits' {b m : ℕ} : m < (b + 2) ^ (digits (b + 2) m).length := by
  convert @ofDigits_lt_base_pow_length' b (digits (b + 2) m) fun _ => digits_lt_base'
  -- ⊢ m = ofDigits (b + 2) (digits (b + 2) m)
  rw [ofDigits_digits (b + 2) m]
  -- 🎉 no goals
#align nat.lt_base_pow_length_digits' Nat.lt_base_pow_length_digits'

/-- Any number m is less than b^(number of digits in the base b representation of m) -/
theorem lt_base_pow_length_digits {b m : ℕ} (hb : 1 < b) : m < b ^ (digits b m).length := by
  rcases b with (_ | _ | b) <;> try simp_all
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- ⊢ m < succ (succ b) ^ List.length (digits (succ (succ b)) m)
  exact lt_base_pow_length_digits'
  -- 🎉 no goals
#align nat.lt_base_pow_length_digits Nat.lt_base_pow_length_digits

theorem ofDigits_digits_append_digits {b m n : ℕ} :
    ofDigits b (digits b n ++ digits b m) = n + b ^ (digits b n).length * m := by
  rw [ofDigits_append, ofDigits_digits, ofDigits_digits]
  -- 🎉 no goals
#align nat.of_digits_digits_append_digits Nat.ofDigits_digits_append_digits

theorem digits_len_le_digits_len_succ (b n : ℕ) :
    (digits b n).length ≤ (digits b (n + 1)).length := by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  -- ⊢ List.length (digits b 0) ≤ List.length (digits b (0 + 1))
  · simp
    -- 🎉 no goals
  cases' le_or_lt b 1 with hb hb
  -- ⊢ List.length (digits b n) ≤ List.length (digits b (n + 1))
  · interval_cases b <;> simp_arith [digits_zero_succ', hn]
    -- ⊢ List.length (digits 0 n) ≤ List.length (digits 0 (n + 1))
                         -- 🎉 no goals
                         -- 🎉 no goals
  simpa [digits_len, hb, hn] using log_mono_right (le_succ _)
  -- 🎉 no goals
#align nat.digits_len_le_digits_len_succ Nat.digits_len_le_digits_len_succ

theorem le_digits_len_le (b n m : ℕ) (h : n ≤ m) : (digits b n).length ≤ (digits b m).length :=
  monotone_nat_of_le_succ (digits_len_le_digits_len_succ b) h
#align nat.le_digits_len_le Nat.le_digits_len_le

@[mono]
theorem ofDigits_monotone {p q : ℕ} (L : List ℕ) (h : p ≤ q) : ofDigits p L ≤ ofDigits q L := by
  induction' L with _ _ hi
  -- ⊢ ofDigits p [] ≤ ofDigits q []
  · rfl
    -- 🎉 no goals
  · simp only [ofDigits, cast_id, add_le_add_iff_left]
    -- ⊢ p * ofDigits p tail✝ ≤ q * ofDigits q tail✝
    exact Nat.mul_le_mul h hi
    -- 🎉 no goals

theorem sum_le_ofDigits (L : List ℕ) (h: 1 ≤ p) : L.sum ≤ ofDigits p L :=
  (ofDigits_one L).symm ▸ ofDigits_monotone L h

theorem digit_sum_le (p n : ℕ) : List.sum (digits p n) ≤ n := by
  induction' n with n
  -- ⊢ List.sum (digits p zero) ≤ zero
  · exact digits_zero _ ▸ Nat.le_refl (List.sum [])
    -- 🎉 no goals
  · induction' p with p
    -- ⊢ List.sum (digits zero (succ n)) ≤ succ n
    · rw [digits_zero_succ, List.sum_cons, List.sum_nil, add_zero]
      -- 🎉 no goals
    · nth_rw 2 [← ofDigits_digits p.succ n.succ]
      -- ⊢ List.sum (digits (succ p) (succ n)) ≤ ofDigits (succ p) (digits (succ p) (su …
      rw [← ofDigits_one <| digits p.succ n.succ]
      -- ⊢ ofDigits 1 (digits (succ p) (succ n)) ≤ ofDigits (succ p) (digits (succ p) ( …
      exact ofDigits_monotone (digits p.succ n.succ) <| Nat.succ_pos p
      -- 🎉 no goals

theorem pow_length_le_mul_ofDigits {b : ℕ} {l : List ℕ} (hl : l ≠ []) (hl2 : l.getLast hl ≠ 0) :
    (b + 2) ^ l.length ≤ (b + 2) * ofDigits (b + 2) l := by
  rw [← List.dropLast_append_getLast hl]
  -- ⊢ (b + 2) ^ List.length (List.dropLast l ++ [List.getLast l hl]) ≤ (b + 2) * o …
  simp only [List.length_append, List.length, zero_add, List.length_dropLast, ofDigits_append,
    List.length_dropLast, ofDigits_singleton, add_comm (l.length - 1), pow_add, pow_one]
  apply Nat.mul_le_mul_left
  -- ⊢ (b + 2) ^ (List.length l - 1) ≤ ofDigits (b + 2) (List.dropLast l) + (b + 2) …
  refine' le_trans _ (Nat.le_add_left _ _)
  -- ⊢ (b + 2) ^ (List.length l - 1) ≤ (b + 2) ^ (List.length l - 1) * List.getLast …
  have : 0 < l.getLast hl := by rwa [pos_iff_ne_zero]
  -- ⊢ (b + 2) ^ (List.length l - 1) ≤ (b + 2) ^ (List.length l - 1) * List.getLast …
  convert Nat.mul_le_mul_left ((b + 2) ^ (l.length - 1)) this using 1
  -- ⊢ (b + 2) ^ (List.length l - 1) = (b + 2) ^ (List.length l - 1) * succ 0
  rw [Nat.mul_one]
  -- 🎉 no goals
#align nat.pow_length_le_mul_of_digits Nat.pow_length_le_mul_ofDigits

/-- Any non-zero natural number `m` is greater than
(b+2)^((number of digits in the base (b+2) representation of m) - 1)
-/
theorem base_pow_length_digits_le' (b m : ℕ) (hm : m ≠ 0) :
    (b + 2) ^ (digits (b + 2) m).length ≤ (b + 2) * m := by
  have : digits (b + 2) m ≠ [] := digits_ne_nil_iff_ne_zero.mpr hm
  -- ⊢ (b + 2) ^ List.length (digits (b + 2) m) ≤ (b + 2) * m
  convert @pow_length_le_mul_ofDigits b (digits (b+2) m)
    this (getLast_digit_ne_zero _ hm)
  rw [ofDigits_digits]
  -- 🎉 no goals
#align nat.base_pow_length_digits_le' Nat.base_pow_length_digits_le'

/-- Any non-zero natural number `m` is greater than
b^((number of digits in the base b representation of m) - 1)
-/
theorem base_pow_length_digits_le (b m : ℕ) (hb : 1 < b) :
    m ≠ 0 → b ^ (digits b m).length ≤ b * m := by
  rcases b with (_ | _ | b) <;> try simp_all
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- ⊢ ¬m = 0 → succ (succ b) ^ List.length (digits (succ (succ b)) m) ≤ succ (succ …
  exact base_pow_length_digits_le' b m
  -- 🎉 no goals
#align nat.base_pow_length_digits_le Nat.base_pow_length_digits_le

/-- Interpreting as a base `p` number and dividing by `p` is the same as interpreting the tail.
-/
lemma ofDigits_div_eq_ofDigits_tail (hpos : 0 < p) (digits : List ℕ)
    (w₁ : ∀ l ∈ digits, l < p) : ofDigits p digits / p = ofDigits p digits.tail := by
  induction' digits with hd tl
  -- ⊢ ofDigits p [] / p = ofDigits p (List.tail [])
  · simp [ofDigits]
    -- 🎉 no goals
  · refine' Eq.trans (add_mul_div_left hd _ hpos) _
    -- ⊢ hd / p + ofDigits p tl = ofDigits p (List.tail (hd :: tl))
    rw [Nat.div_eq_zero <| w₁ _ <| List.mem_cons_self _ _, zero_add]
    -- ⊢ ofDigits p tl = ofDigits p (List.tail (hd :: tl))
    rfl
    -- 🎉 no goals

/-- Interpreting as a base `p` number and dividing by `p^i` is the same as dropping `i`.
-/
lemma ofDigits_div_pow_eq_ofDigits_drop
    (i : ℕ) (hpos : 0 < p) (digits : List ℕ) (w₁ : ∀ l ∈ digits, l < p) :
    ofDigits p digits / p ^ i = ofDigits p (digits.drop i) := by
  induction' i with i hi
  -- ⊢ ofDigits p digits / p ^ zero = ofDigits p (List.drop zero digits)
  · simp
    -- 🎉 no goals
  · rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hi, ofDigits_div_eq_ofDigits_tail hpos
      (List.drop i digits) <| fun x hx ↦ w₁ x <| List.mem_of_mem_drop hx, ← List.drop_one,
      List.drop_drop, add_comm]

/-- Dividing `n` by `p^i` is like truncating the first `i` digits of `n` in base `p`.
-/
lemma self_div_pow_eq_ofDigits_drop (i n : ℕ) (h : 2 ≤ p):
    n / p ^ i = ofDigits p ((p.digits n).drop i) := by
  convert ofDigits_div_pow_eq_ofDigits_drop i (zero_lt_of_lt h) (p.digits n)
    (fun l hl ↦ digits_lt_base h hl)
  exact (ofDigits_digits p n).symm
  -- 🎉 no goals

open BigOperators Finset

theorem sub_one_mul_sum_div_pow_eq_sub_sum_digits
    (L : List ℕ) {h_nonempty} (h_ne_zero : L.getLast h_nonempty ≠ 0) (h_lt : ∀ l ∈ L, l < p) :
    (p - 1) * ∑ i in range L.length, (ofDigits p L) / p ^ i.succ = (ofDigits p L) - L.sum := by
  obtain h | rfl | h : 1 < p ∨ 1 = p ∨ p < 1 := trichotomous 1 p
  · induction' L with hd tl ih
    -- ⊢ (p - 1) * ∑ i in range (List.length []), ofDigits p [] / p ^ succ i = ofDigi …
    · simp [ofDigits]
      -- 🎉 no goals
    · simp only [List.length_cons, List.sum_cons, self_div_pow_eq_ofDigits_drop _ _ h,
          digits_ofDigits p h (hd :: tl) h_lt (fun _ => h_ne_zero)]
      simp only [ofDigits]
      -- ⊢ (p - 1) * ∑ x in range (succ (List.length tl)), ofDigits p (List.drop (succ  …
      rw [sum_range_succ, Nat.cast_id]
      -- ⊢ (p - 1) * (∑ x in range (List.length tl), ofDigits p (List.drop (succ x) (hd …
      simp only [List.drop, List.drop_length]
      -- ⊢ (p - 1) * (∑ x in range (List.length tl), ofDigits p (List.drop x tl) + ofDi …
      obtain rfl | h' := em <| tl = []
      -- ⊢ (p - 1) * (∑ x in range (List.length []), ofDigits p (List.drop x []) + ofDi …
      · simp [ofDigits]
        -- 🎉 no goals
      · have w₁' := fun l hl ↦ h_lt l <| List.mem_cons_of_mem hd hl
        -- ⊢ (p - 1) * (∑ x in range (List.length tl), ofDigits p (List.drop x tl) + ofDi …
        have w₂' := fun (h : tl ≠ []) ↦ (List.getLast_cons h) ▸ h_ne_zero
        -- ⊢ (p - 1) * (∑ x in range (List.length tl), ofDigits p (List.drop x tl) + ofDi …
        have ih := ih (w₂' h') w₁'
        -- ⊢ (p - 1) * (∑ x in range (List.length tl), ofDigits p (List.drop x tl) + ofDi …
        simp only [self_div_pow_eq_ofDigits_drop _ _ h, digits_ofDigits p h tl w₁' w₂',
          succ_eq_one_add] at ih
        have := @sum_singleton _ _ tl.length (fun x => ofDigits p <| tl.drop x) _
        -- ⊢ (p - 1) * (∑ x in range (List.length tl), ofDigits p (List.drop x tl) + ofDi …
        rw [← Ico_succ_singleton, List.drop_length, ofDigits] at this
        -- ⊢ (p - 1) * (∑ x in range (List.length tl), ofDigits p (List.drop x tl) + ofDi …
        have h₁ : 1 ≤ tl.length :=  List.length_pos.mpr h'
        -- ⊢ (p - 1) * (∑ x in range (List.length tl), ofDigits p (List.drop x tl) + ofDi …
        rw [← sum_range_add_sum_Ico _ <| h₁, ← add_zero (∑ x in Ico _ _, ofDigits p (tl.drop x)),
            ← this, sum_Ico_consecutive _  h₁ <| le_succ tl.length, ← sum_Ico_add _ 0 tl.length 1,
            Ico_zero_eq_range, mul_add, mul_add, ih, range_one, sum_singleton, List.drop, ofDigits,
            mul_zero, add_zero, ← Nat.add_sub_assoc <| sum_le_ofDigits _ <| Nat.le_of_lt h]
        nth_rw 2 [← one_mul <| ofDigits p tl]
        -- ⊢ (p - 1) * ofDigits p tl + 1 * ofDigits p tl - List.sum tl = hd + p * ofDigit …
        rw [← add_mul, one_eq_succ_zero, Nat.sub_add_cancel <| zero_lt_of_lt h,
           Nat.add_sub_add_left]
  · simp [ofDigits_one]
    -- 🎉 no goals
  · simp [lt_one_iff.mp h]
    -- ⊢ 0 = ofDigits 0 L - List.sum L
    cases L
    -- ⊢ 0 = ofDigits 0 [] - List.sum []
    · simp
      -- 🎉 no goals
    · simp [ofDigits]
      -- 🎉 no goals

theorem sub_one_mul_sum_log_div_pow_eq_sub_sum_digits (n : ℕ) :
     (p - 1) * ∑ i in range (log p n).succ, n / p ^ i.succ = n - (p.digits n).sum := by
  obtain h | rfl | h : 1 < p ∨ 1 = p ∨ p < 1 := trichotomous 1 p
  · rcases eq_or_ne n 0 with rfl | hn
    -- ⊢ (p - 1) * ∑ i in range (succ (log p 0)), 0 / p ^ succ i = 0 - List.sum (digi …
    · simp
      -- 🎉 no goals
    · convert sub_one_mul_sum_div_pow_eq_sub_sum_digits (p.digits n) (getLast_digit_ne_zero p hn) <|
          (fun l a ↦ digits_lt_base h a)
      · refine' (digits_len p n h hn).symm
        -- 🎉 no goals
      all_goals exact (ofDigits_digits p n).symm
      -- 🎉 no goals
  · simp
    -- 🎉 no goals
  · simp [lt_one_iff.mp h]
    -- ⊢ 0 = n - List.sum (digits 0 n)
    cases n
    -- ⊢ 0 = zero - List.sum (digits 0 zero)
    all_goals simp
    -- 🎉 no goals

/-! ### Binary -/


theorem digits_two_eq_bits (n : ℕ) : digits 2 n = n.bits.map fun b => cond b 1 0 := by
  induction' n using Nat.binaryRecFromOne with b n h ih
  · simp
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
  rw [bits_append_bit _ _ fun hn => absurd hn h]
  -- ⊢ digits 2 (bit b n) = List.map (fun b => bif b then 1 else 0) (b :: bits n)
  cases b
  -- ⊢ digits 2 (bit false n) = List.map (fun b => bif b then 1 else 0) (false :: b …
  · rw [digits_def' one_lt_two]
    -- ⊢ bit false n % 2 :: digits 2 (bit false n / 2) = List.map (fun b => bif b the …
    · simpa [Nat.bit, Nat.bit0_val n]
      -- 🎉 no goals
    · simpa [pos_iff_ne_zero, bit_eq_zero_iff]
      -- 🎉 no goals
  · simpa [Nat.bit, Nat.bit1_val n, add_comm, digits_add 2 one_lt_two 1 n]
    -- 🎉 no goals
#align nat.digits_two_eq_bits Nat.digits_two_eq_bits

/-! ### Modular Arithmetic -/


-- This is really a theorem about polynomials.
theorem dvd_ofDigits_sub_ofDigits {α : Type*} [CommRing α] {a b k : α} (h : k ∣ a - b)
    (L : List ℕ) : k ∣ ofDigits a L - ofDigits b L := by
  induction' L with d L ih
  -- ⊢ k ∣ ofDigits a [] - ofDigits b []
  · change k ∣ 0 - 0
    -- ⊢ k ∣ 0 - 0
    simp
    -- 🎉 no goals
  · simp only [ofDigits, add_sub_add_left_eq_sub]
    -- ⊢ k ∣ a * ofDigits a L - b * ofDigits b L
    exact dvd_mul_sub_mul h ih
    -- 🎉 no goals
#align nat.dvd_of_digits_sub_of_digits Nat.dvd_ofDigits_sub_ofDigits

theorem ofDigits_modEq' (b b' : ℕ) (k : ℕ) (h : b ≡ b' [MOD k]) (L : List ℕ) :
    ofDigits b L ≡ ofDigits b' L [MOD k] := by
  induction' L with d L ih
  -- ⊢ ofDigits b [] ≡ ofDigits b' [] [MOD k]
  · rfl
    -- 🎉 no goals
  · dsimp [ofDigits]
    -- ⊢ d + b * ofDigits b L ≡ d + b' * ofDigits b' L [MOD k]
    dsimp [Nat.ModEq] at *
    -- ⊢ (d + b * ofDigits b L) % k = (d + b' * ofDigits b' L) % k
    conv_lhs => rw [Nat.add_mod, Nat.mul_mod, h, ih]
    -- ⊢ (d % k + b' % k * (ofDigits b' L % k) % k) % k = (d + b' * ofDigits b' L) % k
    conv_rhs => rw [Nat.add_mod, Nat.mul_mod]
    -- 🎉 no goals
#align nat.of_digits_modeq' Nat.ofDigits_modEq'

theorem ofDigits_modEq (b k : ℕ) (L : List ℕ) : ofDigits b L ≡ ofDigits (b % k) L [MOD k] :=
  ofDigits_modEq' b (b % k) k (b.mod_modEq k).symm L
#align nat.of_digits_modeq Nat.ofDigits_modEq

theorem ofDigits_mod (b k : ℕ) (L : List ℕ) : ofDigits b L % k = ofDigits (b % k) L % k :=
  ofDigits_modEq b k L
#align nat.of_digits_mod Nat.ofDigits_mod

theorem ofDigits_zmodeq' (b b' : ℤ) (k : ℕ) (h : b ≡ b' [ZMOD k]) (L : List ℕ) :
    ofDigits b L ≡ ofDigits b' L [ZMOD k] := by
  induction' L with d L ih
  -- ⊢ ofDigits b [] ≡ ofDigits b' [] [ZMOD ↑k]
  · rfl
    -- 🎉 no goals
  · dsimp [ofDigits]
    -- ⊢ ↑d + b * ofDigits b L ≡ ↑d + b' * ofDigits b' L [ZMOD ↑k]
    dsimp [Int.ModEq] at *
    -- ⊢ (↑d + b * ofDigits b L) % ↑k = (↑d + b' * ofDigits b' L) % ↑k
    conv_lhs => rw [Int.add_emod, Int.mul_emod, h, ih]
    -- ⊢ (↑d % ↑k + b' % ↑k * (ofDigits b' L % ↑k) % ↑k) % ↑k = (↑d + b' * ofDigits b …
    conv_rhs => rw [Int.add_emod, Int.mul_emod]
    -- 🎉 no goals
#align nat.of_digits_zmodeq' Nat.ofDigits_zmodeq'

theorem ofDigits_zmodeq (b : ℤ) (k : ℕ) (L : List ℕ) : ofDigits b L ≡ ofDigits (b % k) L [ZMOD k] :=
  ofDigits_zmodeq' b (b % k) k (b.mod_modEq ↑k).symm L
#align nat.of_digits_zmodeq Nat.ofDigits_zmodeq

theorem ofDigits_zmod (b : ℤ) (k : ℕ) (L : List ℕ) : ofDigits b L % k = ofDigits (b % k) L % k :=
  ofDigits_zmodeq b k L
#align nat.of_digits_zmod Nat.ofDigits_zmod

theorem modEq_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) : n ≡ (digits b' n).sum [MOD b] := by
  rw [← ofDigits_one]
  -- ⊢ n ≡ ofDigits 1 (digits b' n) [MOD b]
  conv =>
    congr
    · skip
    · rw [← ofDigits_digits b' n]
  convert ofDigits_modEq b' b (digits b' n)
  -- ⊢ 1 = b' % b
  exact h.symm
  -- 🎉 no goals
#align nat.modeq_digits_sum Nat.modEq_digits_sum

theorem modEq_three_digits_sum (n : ℕ) : n ≡ (digits 10 n).sum [MOD 3] :=
  modEq_digits_sum 3 10 (by norm_num) n
                            -- 🎉 no goals
#align nat.modeq_three_digits_sum Nat.modEq_three_digits_sum

theorem modEq_nine_digits_sum (n : ℕ) : n ≡ (digits 10 n).sum [MOD 9] :=
  modEq_digits_sum 9 10 (by norm_num) n
                            -- 🎉 no goals
#align nat.modeq_nine_digits_sum Nat.modEq_nine_digits_sum

theorem zmodeq_ofDigits_digits (b b' : ℕ) (c : ℤ) (h : b' ≡ c [ZMOD b]) (n : ℕ) :
    n ≡ ofDigits c (digits b' n) [ZMOD b] := by
  conv =>
    congr
    · skip
    · rw [← ofDigits_digits b' n]
  rw [coe_int_ofDigits]
  -- ⊢ ofDigits (↑b') (digits b' n) ≡ ofDigits c (digits b' n) [ZMOD ↑b]
  apply ofDigits_zmodeq' _ _ _ h
  -- 🎉 no goals
#align nat.zmodeq_of_digits_digits Nat.zmodeq_ofDigits_digits

theorem ofDigits_neg_one :
    ∀ L : List ℕ, ofDigits (-1 : ℤ) L = (L.map fun n : ℕ => (n : ℤ)).alternatingSum
  | [] => rfl
  | [n] => by simp [ofDigits, List.alternatingSum]
              -- 🎉 no goals
  | a :: b :: t => by
    simp only [ofDigits, List.alternatingSum, List.map_cons, ofDigits_neg_one t]
    -- ⊢ ↑a + -1 * (↑b + -1 * List.alternatingSum (List.map (fun n => ↑n) t)) = ↑a +  …
    ring
    -- 🎉 no goals
#align nat.of_digits_neg_one Nat.ofDigits_neg_one

theorem modEq_eleven_digits_sum (n : ℕ) :
    n ≡ ((digits 10 n).map fun n : ℕ => (n : ℤ)).alternatingSum [ZMOD 11] := by
  have t := zmodeq_ofDigits_digits 11 10 (-1 : ℤ) (by unfold Int.ModEq; norm_num) n
  -- ⊢ ↑n ≡ List.alternatingSum (List.map (fun n => ↑n) (digits 10 n)) [ZMOD 11]
  rwa [ofDigits_neg_one] at t
  -- 🎉 no goals
#align nat.modeq_eleven_digits_sum Nat.modEq_eleven_digits_sum

/-! ## Divisibility  -/


theorem dvd_iff_dvd_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) :
    b ∣ n ↔ b ∣ (digits b' n).sum := by
  rw [← ofDigits_one]
  -- ⊢ b ∣ n ↔ b ∣ ofDigits 1 (digits b' n)
  conv_lhs => rw [← ofDigits_digits b' n]
  -- ⊢ b ∣ ofDigits b' (digits b' n) ↔ b ∣ ofDigits 1 (digits b' n)
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, ofDigits_mod, h]
  -- 🎉 no goals
#align nat.dvd_iff_dvd_digits_sum Nat.dvd_iff_dvd_digits_sum

/-- **Divisibility by 3 Rule** -/
theorem three_dvd_iff (n : ℕ) : 3 ∣ n ↔ 3 ∣ (digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 3 10 (by norm_num) n
                                  -- 🎉 no goals
#align nat.three_dvd_iff Nat.three_dvd_iff

theorem nine_dvd_iff (n : ℕ) : 9 ∣ n ↔ 9 ∣ (digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 9 10 (by norm_num) n
                                  -- 🎉 no goals
#align nat.nine_dvd_iff Nat.nine_dvd_iff

theorem dvd_iff_dvd_ofDigits (b b' : ℕ) (c : ℤ) (h : (b : ℤ) ∣ (b' : ℤ) - c) (n : ℕ) :
    b ∣ n ↔ (b : ℤ) ∣ ofDigits c (digits b' n) := by
  rw [← Int.coe_nat_dvd]
  -- ⊢ ↑b ∣ ↑n ↔ ↑b ∣ ofDigits c (digits b' n)
  exact
    dvd_iff_dvd_of_dvd_sub (zmodeq_ofDigits_digits b b' c (Int.modEq_iff_dvd.2 h).symm _).symm.dvd
#align nat.dvd_iff_dvd_of_digits Nat.dvd_iff_dvd_ofDigits

theorem eleven_dvd_iff :
    11 ∣ n ↔ (11 : ℤ) ∣ ((digits 10 n).map fun n : ℕ => (n : ℤ)).alternatingSum := by
  have t := dvd_iff_dvd_ofDigits 11 10 (-1 : ℤ) (by norm_num) n
  -- ⊢ 11 ∣ n ↔ 11 ∣ List.alternatingSum (List.map (fun n => ↑n) (digits 10 n))
  rw [ofDigits_neg_one] at t
  -- ⊢ 11 ∣ n ↔ 11 ∣ List.alternatingSum (List.map (fun n => ↑n) (digits 10 n))
  exact t
  -- 🎉 no goals
#align nat.eleven_dvd_iff Nat.eleven_dvd_iff

theorem eleven_dvd_of_palindrome (p : (digits 10 n).Palindrome) (h : Even (digits 10 n).length) :
    11 ∣ n := by
  let dig := (digits 10 n).map (Coe.coe : ℕ → ℤ)
  -- ⊢ 11 ∣ n
  replace h : Even dig.length := by rwa [List.length_map]
  -- ⊢ 11 ∣ n
  refine' eleven_dvd_iff.2 ⟨0, (_ : dig.alternatingSum = 0)⟩
  -- ⊢ List.alternatingSum dig = 0
  have := dig.alternatingSum_reverse
  -- ⊢ List.alternatingSum dig = 0
  rw [(p.map _).reverse_eq, _root_.pow_succ, h.neg_one_pow, mul_one, neg_one_zsmul] at this
  -- ⊢ List.alternatingSum dig = 0
  exact eq_zero_of_neg_eq this.symm
  -- 🎉 no goals
#align nat.eleven_dvd_of_palindrome Nat.eleven_dvd_of_palindrome

/-! ### `norm_digits` tactic -/


namespace NormDigits

theorem digits_succ (b n m r l) (e : r + b * m = n) (hr : r < b)
    (h : Nat.digits b m = l ∧ 1 < b ∧ 0 < m) : (Nat.digits b n = r :: l) ∧ 1 < b ∧ 0 < n := by
  rcases h with ⟨h, b2, m0⟩
  -- ⊢ digits b n = r :: l ∧ 1 < b ∧ 0 < n
  have b0 : 0 < b := by linarith
  -- ⊢ digits b n = r :: l ∧ 1 < b ∧ 0 < n
  have n0 : 0 < n := by linarith [mul_pos b0 m0]
  -- ⊢ digits b n = r :: l ∧ 1 < b ∧ 0 < n
  refine' ⟨_, b2, n0⟩
  -- ⊢ digits b n = r :: l
  obtain ⟨rfl, rfl⟩ := (Nat.div_mod_unique b0).2 ⟨e, hr⟩
  -- ⊢ digits b n = n % b :: l
  subst h; exact Nat.digits_def' b2 n0
  -- ⊢ digits b n = n % b :: digits b (n / b)
           -- 🎉 no goals
#align nat.norm_digits.digits_succ Nat.NormDigits.digits_succ

theorem digits_one (b n) (n0 : 0 < n) (nb : n < b) : Nat.digits b n = [n] ∧ 1 < b ∧ 0 < n := by
  have b2 : 1 < b :=
    lt_iff_add_one_le.mpr (le_trans (add_le_add_right (lt_iff_add_one_le.mp n0) 1) nb)
  refine' ⟨_, b2, n0⟩
  -- ⊢ digits b n = [n]
  rw [Nat.digits_def' b2 n0, Nat.mod_eq_of_lt nb,
    (Nat.div_eq_zero_iff ((zero_le n).trans_lt nb)).2 nb, Nat.digits_zero]
#align nat.norm_digits.digits_one Nat.NormDigits.digits_one

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
#align nat.norm_digits.eval_aux Nat.NormDigits.eval_aux

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
#align nat.norm_digits.eval Nat.NormDigits.eval
-/

end NormDigits

end Nat
