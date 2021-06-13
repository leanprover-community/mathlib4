/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Shing Tak Lam, Mario Carneiro, Ryan Lahfa
-/
import Mathlib.Logic.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Instances
import Mathlib.Tactic.NormNum

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

-- Naming convention stuff
def digitsAux0 : ℕ -> List ℕ
| 0 => []
| (n + 1) => [n + 1]

def digitsAux1 (n: ℕ): List ℕ := List.repeat 1 n

def digitsAuxF (b: ℕ) (h: 2 ≤ b)
  (n: ℕ) (f: ∀ m, m < n -> List ℕ): List ℕ :=
  match (generalizing := true) n with
  | 0 => []
  | succ m =>
    (succ m) % b :: f ((succ m) / b) (div_lt_self (succ_pos _) h)

partial def unsafeDigitsAux (b: ℕ) (h: 2 ≤ b): ℕ -> List ℕ
| 0 => []
| succ n => (succ n) % b :: unsafeDigitsAux b h ((succ n) / b)

@[implementedBy unsafeDigitsAux]
noncomputable def digitsAux (b: ℕ) (h: 2 ≤ b): ℕ -> List ℕ :=
fun n => WellFounded.fix Nat.ltWf (digitsAuxF b h) n

@[simp] theorem digitsAuxZero (b: ℕ) (h: 2 ≤ b): digitsAux b h 0 = List.nil := rfl

lemma digitsAuxDef (b: ℕ) (h: 2 ≤ b) (w: 0 < n):
  digitsAux b h n = n % b :: digitsAux b h (n / b) := by
  cases n
  { trivial }
  { rfl }


/--
`digits b n` gives the digits, in little-endian order,
of a natural number `n` in a specified base `b`.
In any base, we have `of_digits b L = L.foldr (λ x y, x + b * y) 0`.
* For any `2 ≤ b`, we have `l < b` for any `l ∈ digits b n`,
  and the last digit is not zero.
  This uniquely specifies the behaviour of `digits b`.
* For `b = 1`, we define `digits 1 n = list.repeat 1 n`.
* For `b = 0`, we define `digits 0 n = [n]`, except `digits 0 0 = []`.
Note this differs from the existing `nat.to_digits` in core, which is used for printing numerals.
In particular, `nat.to_digits b 0 = [0]`, while `digits b 0 = []`.
-/
def digits : ℕ → ℕ → List ℕ
| 0 => digitsAux0
| 1 => digitsAux1
| (b + 2) => digitsAux (b + 2) (by admit)

@[simp] lemma digitsZero (b: ℕ) : digits b 0 = List.nil := by
  match b with
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => rfl

@[simp] lemma digitsZeroZero : digits 0 0 = List.nil := rfl
@[simp] lemma digitsZeroSucc (n: ℕ) : digits 0 (n.succ) = [n + 1] := rfl

@[simp] lemma digitsOne (n: ℕ): digits 1 n = List.repeat 1 n := rfl
@[simp] lemma digitsOneSucc (n: ℕ): digits 1 (n + 1) = 1 :: digits 1 n := rfl

@[simp] lemma digitsAddTwoAddOne (b n: ℕ):
  digits (b + 2) (n + 1) = ((n + 1) % (b + 2)) :: digits (b + 2) ((n + 1) / (b + 2)) := rfl

@[simp] lemma digitsOfLt (b x : ℕ) (w₁ : 0 < x) (w₂ : x < b): digits b x = [x] := by
  match b with
  | 0 => trivial
  | 1 => simp; admit
  | (b + 2) => match x with
    | 0 => trivial
    | (n + 1) => rw [digitsAddTwoAddOne, div_eq_of_lt w₂, digitsZero, mod_eq_of_lt w₂]

lemma digitsAdd (b: ℕ) (h: 2 ≤ b) (x y: ℕ) (w: x < b) (w': 0 < x ∨ 0 < y):
  digits b ( x + b * y) = x :: digits b y := by
  match b with
  | 0 => trivial
  | 1 => trivial
  |(b + 2) => match y with
    | 0 => simp; admit -- require normNum for inequalities.
    | (y + 1) => admit

def ofDigits {α: Type} [Semiring α] (b: α) : List ℕ → α
| [] => 0
| h :: t => Numeric.ofNat h + b * ofDigits b t -- should have auto-coercions?

-- @[simp] lemma ofDigitsSingleton {b n: ℕ} : ofDigits b [n] = n := by simp [ofDigits]
@[simp] lemma ofDigitsOneCons {α: Type} [Semiring α] (h: ℕ) (L: List ℕ):
  ofDigits (1: α) (h :: L) = Numeric.ofNat h + ofDigits 1 L := by simp [ofDigits]

lemma ofDigitsAppend {b: ℕ} {l1 l2: List ℕ}:
  ofDigits b (l1 ++ l2) = ofDigits b l1 + Monoid.npow (l1.length) b * ofDigits b l2 := by
  induction l1 with
  | nil => simp [ofDigits, Monoid.npow_zero']
  | cons hd tl hl =>
    simp [ofDigits, hl,
    List.length_cons, Numeric.ofNat, Semiring.mul_add,
    Monoid.npow_succ' (List.length tl),
    Nat.mul_assoc,
    Nat.add_assoc]
end Nat
