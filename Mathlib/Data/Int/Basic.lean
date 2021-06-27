/-
Ported by Deniz Aydin from the lean3 prelude's data/int/basic.lean.
Should be in a "prelude"

Original file license:
  Copyright (c) 2016 Jeremy Avigad. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Jeremy Avigad
-/

import Mathlib.Data.Nat.Basic
open Nat

/- ## Additional notation -/

notation "ℤ" => Int
notation "-[1+ " n "]" => Int.negSucc n

namespace Int

/- ## Edits to the naming conventions -/
def neg_of_nat := @negOfNat
def sub_nat_nat := @subNatNat
def nonneg := @NonNeg
protected def dec_eq := @Int.decEq
def nat_abs := @natAbs
def to_nat := @toNat
def nat_mod := @natMod

protected lemma coe_nat_eq (n : ℕ) : ↑n = ofNat n := rfl

-- TODO: use these to instantiate "has zero" and "has one" classes
-- (which rn seem to be in Mathlib.Algebra.Group.Defs for some reason)
protected def zero : ℤ := ofNat 0
protected def one  : ℤ := ofNat 1

lemma of_nat_zero : ofNat (0 : ℕ) = (0 : ℤ) := rfl

lemma of_nat_one  : ofNat (1 : ℕ) = (1 : ℤ) := rfl

/- ## Definitions of basic functions -/

lemma sub_nat_nat_of_sub_eq_zero {m n : ℕ} (h : n - m = 0) : sub_nat_nat m n = ofNat (m - n) := by
  show (match (n - m) with -- No `unfold` so I do this
  | 0 => ofNat (m-n)
  | succ k => -[1+ k]
  ) = ofNat (m - n)
  rw [h]
  rfl

lemma sub_nat_nat_of_sub_eq_succ {m n k : ℕ} (h : n - m = succ k) : sub_nat_nat m n = -[1+ k] := by
  show (match n - m with
  | 0 => ofNat (m - n)
  | succ k => -[1+ k]) =
  -[1+ k]
  rw [h]

protected lemma neg_zero : -(0:ℤ) = 0 := rfl

lemma of_nat_add (n m : ℕ) : ofNat (n + m) = ofNat n + ofNat m := rfl
lemma of_nat_mul (n m : ℕ) : ofNat (n * m) = ofNat n * ofNat m := rfl
lemma of_nat_succ (n : ℕ) : ofNat (succ n) = ofNat n + 1 := rfl

lemma neg_of_nat_zero : -(ofNat 0) = 0 := rfl
lemma neg_of_nat_of_succ (n : ℕ) : -(ofNat (succ n)) = -[1+ n] := rfl
lemma neg_neg_of_nat_succ (n : ℕ) : -(-[1+ n]) = ofNat (succ n) := rfl

lemma of_nat_eq_coe (n : ℕ) : ofNat n = ↑n := rfl
lemma neg_succ_of_nat_coe (n : ℕ) : -[1+ n] = -↑(n + 1) := rfl

protected lemma coe_nat_add (m n : ℕ) : (↑(m + n) : ℤ) = ↑m + ↑n := rfl
protected lemma coe_nat_mul (m n : ℕ) : (↑(m * n) : ℤ) = ↑m * ↑n := rfl
protected lemma coe_nat_zero : ↑(0 : ℕ) = (0 : ℤ) := rfl
protected lemma coe_nat_one : ↑(1 : ℕ) = (1 : ℤ) := rfl
protected lemma coe_nat_succ (n : ℕ) : (↑(succ n) : ℤ) = (↑n : Int) + 1 := rfl

protected lemma coe_nat_add_out (m n : ℕ) : ↑m + ↑n = (m + n : ℤ) := rfl
protected lemma coe_nat_mul_out (m n : ℕ) : ↑m * ↑n = (↑(m * n) : ℤ) := rfl
protected lemma coe_nat_add_one_out (n : ℕ) : ↑n + (1 : ℤ) = ↑(succ n) := rfl

/- ## These are only for internal use -/

lemma of_nat_add_of_nat (m n : ℕ) :
    ofNat m + ofNat n = ofNat (m + n) := rfl
lemma of_nat_add_neg_succ_of_nat (m n : ℕ) :
    ofNat m + -[1+ n] = sub_nat_nat m (succ n) := rfl
lemma neg_succ_of_nat_add_of_nat (m n : ℕ) :
    -[1+ m] + ofNat n = sub_nat_nat n (succ m) := rfl
lemma neg_succ_of_nat_add_neg_succ_of_nat (m n : ℕ) :
    -[1+ m] + -[1+ n] = -[1+ succ (m + n)] := rfl

lemma of_nat_mul_of_nat (m n : ℕ) :
    ofNat m * ofNat n = ofNat (m * n) := rfl
lemma of_nat_mul_neg_succ_of_nat (m n : ℕ) :
    ofNat m * -[1+ n] = neg_of_nat (m * succ n) := rfl
lemma neg_succ_of_nat_of_nat (m n : ℕ) :
    -[1+ m] * ofNat n = neg_of_nat (succ m * n) := rfl
lemma mul_neg_succ_of_nat_neg_succ_of_nat (m n : ℕ) :
    -[1+ m] * -[1+ n] = ofNat (succ m * succ n) := rfl

attribute [local simp] of_nat_add_of_nat of_nat_mul_of_nat neg_of_nat_zero neg_of_nat_of_succ
  neg_neg_of_nat_succ of_nat_add_neg_succ_of_nat neg_succ_of_nat_add_of_nat
  neg_succ_of_nat_add_neg_succ_of_nat of_nat_mul_neg_succ_of_nat neg_succ_of_nat_of_nat
  mul_neg_succ_of_nat_neg_succ_of_nat

/- ## some basic functions and properties -/

protected lemma coe_nat_inj {m n : ℕ} (h : (↑m : ℤ) = ↑n) : m = n :=
Int.ofNat.inj h

lemma of_nat_eq_of_nat_iff (m n : ℕ) : ofNat m = ofNat n ↔ m = n :=
Iff.intro Int.ofNat.inj (congr_arg _)

protected lemma coe_nat_eq_coe_nat_iff (m n : ℕ) : (↑m : ℤ) = ↑n ↔ m = n :=
of_nat_eq_of_nat_iff m n

lemma neg_succ_of_nat_inj_iff {m n : ℕ} : negSucc m = negSucc n ↔ m = n :=
⟨Int.negSucc.inj, λ H => by simp [H]⟩

lemma neg_succ_of_nat_eq (n : ℕ) : -[1+ n] = -((↑n) + 1) := rfl

/- ## neg -/

protected lemma neg_neg : ∀ a : ℤ, -(-a) = a
| ofNat 0     => rfl
| ofNat (n+1) => rfl
| -[1+ n]     => rfl

protected lemma neg_inj {a b : ℤ} (h : -a = -b) : a = b :=
by rw [← Int.neg_neg a, ← Int.neg_neg b, h]

protected lemma sub_eq_add_neg {a b : ℤ} : a - b = a + -b := rfl

/- ## basic properties of sub_nat_nat -/

lemma sub_nat_nat_elim (m n : ℕ) (P : ℕ → ℕ → ℤ → Prop)
  (hp : ∀i n, P (n + i) n (ofNat i))
  (hn : ∀i m, P m (m + i + 1) (-[1+ i])) :
  P m n (sub_nat_nat m n) :=
by
  have H : ∀k , n - m = k → P m n (@Nat.casesOn (λ _ => ℤ) k (ofNat (m-n)) negSucc) := by
    intros k h
    cases k with
    | zero =>
        simp
        rw [Nat.sub_eq_zero_iff_le] at h
        let i := m - n
        -- so the second m-n doesn't get rewritten, don't know if there's a better way of doing that
        change P m n (ofNat i)
        rw [← Nat.add_sub_cancel_left n m, Nat.add_sub_assoc h]
        apply hp
    | succ k =>
        simp
        have hle : m ≤ n := Nat.le_of_lt (Nat.lt_of_sub_eq_succ h)
        rw [Nat.sub_eq_iff_eq_add hle] at h
        rw [h, Nat.add_comm]
        apply hn
  exact H _ rfl

lemma sub_nat_nat_add_left {m n : ℕ} :
  sub_nat_nat (m + n) m = ofNat n :=
by
  change (match m - (m + n) with
          | 0      => ofNat (m + n - m)
          | succ k => -[1+ k]) = ofNat n
  rw [Nat.sub_eq_zero_of_le (Nat.le_add_right _ _)]
  rw [Nat.add_sub_cancel_left]
  rfl

lemma sub_nat_nat_add_right {m n : ℕ} : sub_nat_nat m (m + n + 1) = negSucc n := by
  change (match m + n + 1 - m with
          | 0      => ofNat (m - (m + n + 1))
          | succ k => -[1+ k]) = negSucc n
  simp
  rw [Nat.add_assoc, Nat.add_one, Nat.add_sub_cancel_left]

lemma sub_nat_nat_add_add (m n k : ℕ) : sub_nat_nat (m + k) (n + k) = sub_nat_nat m n :=
sub_nat_nat_elim m n (λm n i => sub_nat_nat (m + k) (n + k) = i)
  (by
    intros i j
    rw [Nat.add_assoc, Nat.add_comm i k, ← Nat.add_assoc]
    exact sub_nat_nat_add_left
  )
  (by
    intros i j
    rw [Nat.add_assoc j i 1, Nat.add_comm j (i+1), Nat.add_assoc, Nat.add_comm (i+1) (j+k)]
    exact sub_nat_nat_add_right
  )

lemma sub_nat_nat_of_le {m n : ℕ} (h : n ≤ m) : sub_nat_nat m n = ofNat (m - n) :=
sub_nat_nat_of_sub_eq_zero (sub_eq_zero_of_le h)

lemma sub_nat_nat_of_lt {m n : ℕ} (h : m < n) : sub_nat_nat m n = -[1+ pred (n - m)] := by
  rw [sub_nat_nat_of_sub_eq_succ]
  rw [Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)]

/- ## nat_abs -/

lemma nat_abs_of_nat (n : ℕ) : nat_abs ↑n = n := rfl

lemma eq_zero_of_nat_abs_eq_zero : ∀ {a : ℤ}, nat_abs a = 0 → a = 0
| (ofNat _), H => congr_arg ofNat H
| -[1+ _],   H => absurd H (succ_ne_zero _)

lemma nat_abs_pos_of_ne_zero {a : ℤ} (h : a ≠ 0) : 0 < nat_abs a :=
(eq_zero_or_pos _).resolve_left $ mt eq_zero_of_nat_abs_eq_zero h

lemma nat_abs_zero : nat_abs (0 : ℤ) = (0 : ℕ) := rfl

lemma nat_abs_one : nat_abs (1 : ℤ) = (1 : ℕ) := rfl

lemma nat_abs_mul_self : ∀ {a : ℤ}, ↑(nat_abs a * nat_abs a) = a * a
| (ofNat _) => rfl
| -[1+ _]   => rfl

@[simp] lemma nat_abs_neg (a : ℤ) : nat_abs (-a) = nat_abs a := match a with
| (ofNat zero)     => rfl
| (ofNat (succ _)) => rfl
| (negSucc _)      => rfl

lemma nat_abs_eq : ∀ (a : ℤ), a = nat_abs a ∨ a = -↑(nat_abs a)
| (ofNat _) => Or.inl rfl
| -[1+ _]   => Or.inr rfl

lemma eq_coe_or_neg (a : ℤ) : ∃n : ℕ, a = n ∨ a = -↑n := ⟨_, nat_abs_eq a⟩

/- ## sign -/

def sign : ℤ → ℤ
| (n+1:ℕ) => 1
| 0       => 0
| -[1+ n] => -1

@[simp] theorem sign_zero : sign 0 = 0 := rfl
@[simp] theorem sign_one : sign 1 = 1 := rfl
@[simp] theorem sign_neg_one : sign (-1) = -1 := rfl

/- ## Quotient and remainder
There are three main conventions for integer division,
referred here as the E, F, T rounding conventions.
All three pairs satisfy the identity x % y + (x / y) * y = x
unconditionally. -/

-- E-rounding (`div` and `mod` defined in core) satisfy 0 ≤ mod x y < nat_abs y for y ≠ 0

-- F-rounding: This pair satisfies fdiv x y = floor (x / y)
def fdiv : ℤ → ℤ → ℤ
| 0,       _       => 0
| (m : ℕ), (n : ℕ) => ofNat (m / n)
| (m+1:ℕ), -[1+ n] => -[1+ m / succ n]
| -[1+ m], 0       => 0
| -[1+ m], (n+1:ℕ) => -[1+ m / succ n]
| -[1+ m], -[1+ n] => ofNat (succ m / succ n)

def fmod : ℤ → ℤ → ℤ
| 0,       _       => 0
| (m : ℕ), (n : ℕ) => ofNat (m % n)
| (m+1:ℕ), -[1+ n] => sub_nat_nat (m % succ n) n
| -[1+ m], (n : ℕ) => sub_nat_nat n (succ (m % n))
| -[1+ m], -[1+ n] => -ofNat (succ m % succ n)

-- T-rounding: This pair satisfies quot x y = round_to_zero (x / y)
def quot : ℤ → ℤ → ℤ
| (m : ℕ), (n : ℕ) => ofNat (m / n)
| (m : ℕ), -[1+ n] => -ofNat (m / succ n)
| -[1+ m], (n : ℕ) => -ofNat (succ m / n)
| -[1+ m], -[1+ n] => ofNat (succ m / succ n)

def rem : ℤ → ℤ → ℤ
| (m : ℕ), (n : ℕ) => ofNat (m % n)
| (m : ℕ), -[1+ n] => ofNat (m % succ n)
| -[1+ m], (n : ℕ) => -ofNat (succ m % n)
| -[1+ m], -[1+ n] => -ofNat (succ m % succ n)

/- ## gcd -/
def gcd (m n : ℤ) : ℕ := Nat.gcd (nat_abs m) (nat_abs n)

/-
   # ring properties
-/

/- addition -/

protected lemma add_comm : ∀ a b : ℤ, a + b = b + a
| (n : ℕ), (m : ℕ) => by simp [Nat.add_comm]
| (_ : ℕ), -[1+ _] => rfl
| -[1+ _], (_ : ℕ) => rfl
| -[1+ _], -[1+ _] => by simp [Nat.add_comm]

protected lemma add_zero : ∀ a : ℤ, a + 0 = a
| (ofNat n) => rfl
| -[1+ n]   => rfl

protected lemma zero_add (a : ℤ) : 0 + a = a := Int.add_comm a 0 ▸ Int.add_zero a

lemma sub_nat_nat_sub {m n : ℕ} (h : n ≤ m) (k : ℕ) :
sub_nat_nat (m - n) k = sub_nat_nat m (k + n) := by
  rwa [← sub_nat_nat_add_add _ _ n, Nat.sub_add_cancel]


lemma sub_nat_nat_add (m n k : ℕ) : sub_nat_nat (m + n) k = ofNat m + sub_nat_nat n k :=
by
  have h := Nat.lt_or_le n k
  cases h with
  | inl h' =>
    rw [sub_nat_nat_of_lt h']
    simp
    rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h')]
    apply Eq.trans
    rw [← Nat.sub_add_cancel (Nat.le_of_lt h')]
    apply sub_nat_nat_add_add
  | inr h' =>
    rw [sub_nat_nat_of_le (h')]
    have h₂ : k ≤ m + n := Nat.le_trans h' (le_add_left _ _)
    rw [sub_nat_nat_of_le h₂]
    simp
    rw [Nat.add_sub_assoc h']

lemma sub_nat_nat_add_neg_succ_of_nat (m n k : ℕ) :
    sub_nat_nat m n + -[1+ k] = sub_nat_nat m (n + succ k) :=
by
  have h := Nat.lt_or_le m n
  cases h with
  | inr h' =>
    rw [sub_nat_nat_of_le h']
    simp
    rw [sub_nat_nat_sub h', Nat.add_comm]
  | inl h' =>
    have h₂ : m < n + succ k := Nat.lt_of_lt_of_le h' (le_add_right _ _)
    have h₃ : m ≤ n + k := le_of_succ_le_succ h₂
    rw [sub_nat_nat_of_lt h', sub_nat_nat_of_lt h₂]
    simp [Nat.add_comm]
    rw [← add_succ, succ_pred_eq_of_pos (Nat.sub_pos_of_lt h'), add_succ, succ_sub h₃, pred_succ]
    rw [Nat.add_comm n, Nat.add_sub_assoc (Nat.le_of_lt h')]

lemma add_assoc_aux1 (m n : ℕ) :
    ∀ c : ℤ, ofNat m + ofNat n + c = ofNat m + (ofNat n + c)
| (ofNat k) => by simp [Nat.add_assoc]
| -[1+ k]   => by simp [sub_nat_nat_add]

lemma add_assoc_aux2 (m n k : ℕ) :
  -[1+ m] + -[1+ n] + ofNat k = -[1+ m] + (-[1+ n] + ofNat k) :=
by
  simp [add_succ]
  rw [Int.add_comm, sub_nat_nat_add_neg_succ_of_nat]
  simp [add_succ, succ_add, Nat.add_comm]

protected lemma add_assoc : ∀ a b c : ℤ, a + b + c = a + (b + c)
| (ofNat m), (ofNat n), c         => add_assoc_aux1 _ _ _
| (ofNat m), b,         (ofNat k) => by
  rw [Int.add_comm, ← add_assoc_aux1, Int.add_comm k, add_assoc_aux1, Int.add_comm b]
| a,         (ofNat n), (ofNat k) => by
  rw [Int.add_comm, Int.add_comm a, ← add_assoc_aux1, Int.add_comm a, Int.add_comm (ofNat k)]
| -[1+ m],   -[1+ n],   (ofNat k) => add_assoc_aux2 _ _ _
| -[1+ m],   (ofNat n), -[1+ k]   => by
  rw [Int.add_comm, ← add_assoc_aux2, Int.add_comm n, ← add_assoc_aux2, Int.add_comm -[1+ m]]
| (ofNat m), -[1+ n],   -[1+ k]   => by
  rw [Int.add_comm, Int.add_comm (ofNat m), Int.add_comm m, ← add_assoc_aux2, Int.add_comm -[1+ k]]
| -[1+ m],   -[1+ n],   -[1+ k]   => by
  simp [add_succ, Nat.add_comm, Nat.add_left_comm, neg_of_nat_of_succ]

/- ## negation -/

lemma sub_nat_self : ∀ n, sub_nat_nat n n = 0
| 0        => rfl
| (succ m) => by
  rw [sub_nat_nat_of_sub_eq_zero, Nat.sub_self, of_nat_zero]
  rw [Nat.sub_self]

attribute [local simp] sub_nat_self

protected lemma add_left_neg : ∀ a : ℤ, -a + a = 0
| (ofNat 0)        => rfl
| (ofNat (succ m)) => by simp
| -[1+ m]          => by simp

protected lemma add_right_neg (a : ℤ) : a + -a = 0 :=
by rw [Int.add_comm, Int.add_left_neg]

/- ## multiplication -/

protected lemma mul_comm : ∀ a b : ℤ, a * b = b * a
| (ofNat m), (ofNat n) => by simp [Nat.mul_comm]
| (ofNat m), -[1+ n]   => by simp [Nat.mul_comm]
| -[1+ m],   (ofNat n) => by simp [Nat.mul_comm]
| -[1+ m],   -[1+ n]   => by simp [Nat.mul_comm]

lemma of_nat_mul_neg_of_nat (m : ℕ) : ∀ n, ofNat m * neg_of_nat n = neg_of_nat (m * n)
| 0        => rfl
| (succ n) => by simp [neg_of_nat, negOfNat] -- TODO: How to avoid having to simp through renaming definitions to unfold them?

lemma neg_of_nat_mul_of_nat (m n : ℕ) : neg_of_nat m * ofNat n = neg_of_nat (m * n) := by
    rw [Int.mul_comm]
    simp [of_nat_mul_neg_of_nat, Nat.mul_comm]

lemma neg_succ_of_nat_mul_neg_of_nat (m : ℕ) :
  ∀ n, -[1+ m] * neg_of_nat n = ofNat (succ m * n)
| 0        => rfl
| (succ n) => by simp [neg_of_nat, negOfNat] -- TODO: How to avoid having to simp through renaming definitions to unfold them?

lemma neg_of_nat_mul_neg_succ_of_nat (m n : ℕ) :
  neg_of_nat n * -[1+ m] = ofNat (n * succ m) := by
    simp [Int.mul_comm, neg_succ_of_nat_mul_neg_of_nat, Nat.mul_comm]

attribute [local simp] of_nat_mul_neg_of_nat neg_of_nat_mul_of_nat
  neg_succ_of_nat_mul_neg_of_nat neg_of_nat_mul_neg_succ_of_nat

protected lemma mul_assoc : ∀ a b c : ℤ, a * b * c = a * (b * c)
| (ofNat m), (ofNat n), (ofNat k) => by simp [Nat.mul_assoc]
| (ofNat m), (ofNat n), -[1+ k]   => by simp [Nat.mul_assoc]
| (ofNat m), -[1+ n],   (ofNat k) => by simp [Nat.mul_assoc]
| (ofNat m), -[1+ n],   -[1+ k]   => by simp [Nat.mul_assoc]
| -[1+ m],   (ofNat n), (ofNat k) => by simp [Nat.mul_assoc]
| -[1+ m],   (ofNat n), -[1+ k]   => by simp [Nat.mul_assoc]
| -[1+ m],   -[1+ n],   (ofNat k) => by simp [Nat.mul_assoc]
| -[1+ m],   -[1+ n],   -[1+ k]   => by simp [Nat.mul_assoc]

protected lemma mul_zero : ∀ (a : ℤ), a * 0 = 0
| (ofNat m) => rfl
| -[1+ m]   => rfl

protected lemma zero_mul (a : ℤ) : 0 * a = 0 :=
Int.mul_comm a 0 ▸ Int.mul_zero a

lemma neg_of_nat_eq_sub_nat_nat_zero : ∀ n, neg_of_nat n = sub_nat_nat 0 n
| 0        => rfl
| (succ n) => rfl



lemma of_nat_mul_sub_nat_nat (m n k : ℕ) :
  ofNat m * sub_nat_nat n k = sub_nat_nat (m * n) (m * k) :=
by
  cases m with
  | zero =>
    simp [of_nat_zero, Int.zero_mul, Nat.zero_mul]
  | succ m =>
    have h := Nat.lt_or_le n k
    cases h with
    | inl h =>
      have h' : (succ m) * n < (succ m) * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
      rw [sub_nat_nat_of_lt h, sub_nat_nat_of_lt h']
      simp
      rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)]
      rw [← neg_of_nat_of_succ, Nat.mul_sub_left_distrib]
      rw [← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h')]
      rfl
    | inr h =>
      have h' : (succ m) * k ≤ (succ m) * n := Nat.mul_le_mul_left _ h
      rw [sub_nat_nat_of_le h, sub_nat_nat_of_le h']
      simp
      rw [Nat.mul_sub_left_distrib]



lemma neg_of_nat_add (m n : ℕ) : neg_of_nat m + neg_of_nat n = neg_of_nat (m + n) := by
  cases m
  cases n
  simp
  simp [Nat.zero_add]
  rfl
  cases n
  simp
  rfl
  simp [Nat.succ_add]
  rfl

lemma neg_succ_of_nat_mul_sub_nat_nat (m n k : ℕ) :
  -[1+ m] * sub_nat_nat n k = sub_nat_nat (succ m * k) (succ m * n) :=
by
  have h := Nat.lt_or_le n k
  cases h with
  | inl h =>
    have h' : succ m * n < succ m * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
    rw [sub_nat_nat_of_lt h, sub_nat_nat_of_le (Nat.le_of_lt h')]
    simp [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h), Nat.mul_sub_left_distrib]
  | inr h =>
    cases Nat.lt_or_le k n with
    | inl h' =>

      have h₁ : succ m * n > succ m * k := Nat.mul_lt_mul_of_pos_left h' (Nat.succ_pos m)
      rw [sub_nat_nat_of_le h, sub_nat_nat_of_lt h₁]
      simp [Nat.mul_sub_left_distrib, Nat.mul_comm]
      rw [Nat.mul_comm k, Nat.mul_comm n, ← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁),
          ← neg_of_nat_of_succ]
      rfl
    | inr h' =>
      rw [Nat.le_antisymm h h']
      simp
      rfl

attribute [local simp] of_nat_mul_sub_nat_nat neg_of_nat_add neg_succ_of_nat_mul_sub_nat_nat

protected lemma distrib_left : ∀ a b c : ℤ, a * (b + c) = a * b + a * c
| (ofNat m), (ofNat n), (ofNat k) => by simp [Nat.left_distrib]
| (ofNat m), (ofNat n), -[1+ k]   => by simp [neg_of_nat_eq_sub_nat_nat_zero] rw [← sub_nat_nat_add] rfl
| (ofNat m), -[1+ n],   (ofNat k) => by simp [neg_of_nat_eq_sub_nat_nat_zero] rw [Int.add_comm, ← sub_nat_nat_add] rfl
| (ofNat m), -[1+ n],   -[1+ k]   => by simp rw [← Nat.left_distrib, succ_add] rfl
| -[1+ m],   (ofNat n), (ofNat k) => by simp [Nat.mul_comm] rw [← Nat.right_distrib, Nat.mul_comm]
| -[1+ m],   (ofNat n), -[1+ k]   => by simp [neg_of_nat_eq_sub_nat_nat_zero] rw [Int.add_comm, ← sub_nat_nat_add] rfl
| -[1+ m],   -[1+ n],   (ofNat k) => by simp [neg_of_nat_eq_sub_nat_nat_zero] rw [← sub_nat_nat_add] rfl
| -[1+ m],   -[1+ n],   -[1+ k]   => by simp rw [← Nat.left_distrib, succ_add] rfl

protected lemma distrib_right (a b c : ℤ) : (a + b) * c = a * c + b * c := by
  rw [Int.mul_comm, Int.distrib_left]
  simp [Int.mul_comm]

protected lemma zero_ne_one : (0 : ℤ) ≠ 1 := λ h => Int.noConfusion h fun.

lemma of_nat_sub {n m : ℕ} (h : m ≤ n) : ofNat (n - m) = ofNat n - ofNat m := by
  show ofNat (n - m) = ofNat n + neg_of_nat m
  match m, h with
  | 0,      h => rfl
  | succ m, h =>
                show ofNat (n - succ m) = sub_nat_nat n (succ m)
                simp [sub_nat_nat, subNatNat] -- TODO: How to avoid having to simp through rename definitions to unfold them?
                rw [sub_eq_zero_of_le h]
                rfl

protected lemma add_left_comm (a b c : ℤ) : a + (b + c) = b + (a + c) :=
by rw [← Int.add_assoc, Int.add_comm a, Int.add_assoc]

protected lemma add_left_cancel {a b c : ℤ} (h : a + b = a + c) : b = c := by
  have h₁ : -a + (a + b) = -a + (a + c) := by rw [h]
  rwa [← Int.add_assoc, ← Int.add_assoc, Int.add_left_neg, Int.zero_add, Int.zero_add] at h₁

protected lemma neg_add {a b : ℤ} : - (a + b) = -a + -b := by
  have h₁ : - (a + b) = -(a + b) + (a + b) + -a + -b := by
    rw [Int.add_assoc, Int.add_comm (-a), Int.add_assoc, Int.add_assoc, ← Int.add_assoc b]
    rw [Int.add_right_neg, Int.zero_add, Int.add_right_neg, Int.add_zero]
  rwa [Int.add_left_neg, Int.zero_add] at h₁

lemma neg_succ_of_nat_coe' (n : ℕ) : -[1+ n] = -↑n - 1 :=
by rw [Int.sub_eq_add_neg, ← Int.neg_add]; rfl

protected lemma coe_nat_sub {n m : ℕ} : n ≤ m → (↑(m - n) : ℤ) = ↑m - ↑n := of_nat_sub

attribute [local simp] Int.sub_eq_add_neg

protected lemma sub_nat_nat_eq_coe {m n : ℕ} : sub_nat_nat m n = ↑m - ↑n :=
sub_nat_nat_elim m n (λm n i => i = ↑m - ↑n)
  (λi n => by
    simp [Int.coe_nat_add, Int.add_left_comm, Int.add_assoc, Int.add_right_neg]
    rfl)
  (λi n => by
    simp
    rw [Int.coe_nat_add, Int.coe_nat_add, Int.coe_nat_one, Int.neg_succ_of_nat_eq,
         Int.neg_add, Int.neg_add, Int.neg_add, ← Int.add_assoc,
        ← Int.add_assoc, Int.add_right_neg, Int.zero_add])

theorem to_nat_sub (m n : ℕ) : to_nat (m - n) = m - n := rfl

protected lemma one_mul : ∀ (a : ℤ), (1 : ℤ) * a = a
| (ofNat n) => show ofNat (1 * n) = ofNat n by rw [Nat.one_mul]
| -[1+ n]   => show -[1+ (1 * n)] = -[1+ n] by rw [Nat.one_mul]

protected lemma mul_one (a : ℤ) : a * 1 = a :=
by rw [Int.mul_comm, Int.one_mul]

protected lemma neg_eq_neg_one_mul : ∀ a : ℤ, -a = -1 * a
| (ofNat 0)     => rfl
| (ofNat (n+1)) => show _ = -[1+ (1*n)+0] by rw [Nat.one_mul] rfl
| -[1+ n]       => show _ = ofNat _ by rw [Nat.one_mul] rfl

theorem sign_mul_nat_abs : ∀ (a : ℤ), sign a * nat_abs a = a
| (n+1:ℕ) => Int.one_mul _
| 0       => rfl
| -[1+ n] => (Int.neg_eq_neg_one_mul _).symm

end Int
