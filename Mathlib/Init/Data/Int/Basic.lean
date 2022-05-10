/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Deniz Aydin, Floris van Doorn
-/

import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Coe
import Mathlib.Tactic.NormCast.Lemmas
open Nat

namespace Int

notation "ℤ" => Int
notation "-[1+ " n "]" => Int.negSucc n

lemma ofNat_zero : ofNat (0 : ℕ) = (0 : ℤ) := rfl

lemma ofNat_one  : ofNat (1 : ℕ) = (1 : ℤ) := rfl

/- ## Definitions of basic functions -/

lemma subNatNat_of_sub_eq_zero {m n : ℕ} (h : n - m = 0) : subNatNat m n = ofNat (m - n) := by
  show (match (n - m) with -- No `unfold` so I do this
  | 0 => ofNat (m-n)
  | succ k => -[1+ k]
  ) = ofNat (m - n)
  rw [h]

lemma subNatNat_of_sub_eq_succ {m n k : ℕ} (h : n - m = succ k) : subNatNat m n = -[1+ k] := by
  show (match n - m with
  | 0 => ofNat (m - n)
  | succ k => -[1+ k]) =
  -[1+ k]
  rw [h]

protected lemma neg_zero : -(0:ℤ) = 0 := rfl

lemma ofNat_add (n m : ℕ) : ofNat (n + m) = ofNat n + ofNat m := rfl
lemma ofNat_mul (n m : ℕ) : ofNat (n * m) = ofNat n * ofNat m := rfl
lemma ofNat_succ (n : ℕ) : ofNat (succ n) = ofNat n + 1 := rfl

lemma neg_ofNat_zero : -(ofNat 0) = 0 := rfl
lemma neg_ofNat_of_succ (n : ℕ) : -(ofNat (succ n)) = -[1+ n] := rfl
lemma neg_neg_ofNat_succ (n : ℕ) : -(-[1+ n]) = ofNat (succ n) := rfl

lemma negSucc_ofNat_coe (n : ℕ) : -[1+ n] = -↑(n + 1) := rfl

/- ## These are only for internal use -/

lemma ofNat_add_ofNat (m n : ℕ) :
    ofNat m + ofNat n = ofNat (m + n) := rfl
lemma ofNat_add_negSucc_ofNat (m n : ℕ) :
    ofNat m + -[1+ n] = subNatNat m (succ n) := rfl
lemma negSucc_ofNat_add_ofNat (m n : ℕ) :
    -[1+ m] + ofNat n = subNatNat n (succ m) := rfl
lemma negSucc_ofNat_add_negSucc_ofNat (m n : ℕ) :
    -[1+ m] + -[1+ n] = -[1+ succ (m + n)] := rfl

lemma ofNat_mul_ofNat (m n : ℕ) :
    ofNat m * ofNat n = ofNat (m * n) := rfl
lemma ofNat_mul_negSucc_ofNat (m n : ℕ) :
    ofNat m * -[1+ n] = negOfNat (m * succ n) := rfl
lemma negSucc_ofNat_ofNat (m n : ℕ) :
    -[1+ m] * ofNat n = negOfNat (succ m * n) := rfl
lemma mul_negSucc_ofNat_negSucc_ofNat (m n : ℕ) :
    -[1+ m] * -[1+ n] = ofNat (succ m * succ n) := rfl

attribute [local simp] ofNat_add_ofNat ofNat_mul_ofNat neg_ofNat_zero neg_ofNat_of_succ
  neg_neg_ofNat_succ ofNat_add_negSucc_ofNat negSucc_ofNat_add_ofNat
  negSucc_ofNat_add_negSucc_ofNat ofNat_mul_negSucc_ofNat negSucc_ofNat_ofNat
  mul_negSucc_ofNat_negSucc_ofNat

/- ## some basic functions and properties -/

protected lemma coe_nat_inj {m n : ℕ} (h : (↑m : ℤ) = ↑n) : m = n :=
Int.ofNat.inj h

lemma ofNat_eq_ofNat_iff (m n : ℕ) : ofNat m = ofNat n ↔ m = n :=
Iff.intro Int.ofNat.inj (congrArg _)

lemma negSucc_ofNat_inj_iff {m n : ℕ} : negSucc m = negSucc n ↔ m = n :=
⟨Int.negSucc.inj, λ H => by simp [H]⟩

lemma negSucc_ofNat_eq (n : ℕ) : -[1+ n] = -((↑n) + 1) := rfl

/- ## neg -/

protected lemma neg_neg : ∀ a : ℤ, -(-a) = a
| ofNat 0     => rfl
| ofNat (n+1) => rfl
| -[1+ n]     => rfl

protected lemma neg_inj {a b : ℤ} (h : -a = -b) : a = b :=
by rw [← Int.neg_neg a, ← Int.neg_neg b, h]

protected lemma sub_eq_add_neg {a b : ℤ} : a - b = a + -b := rfl

/- ## basic properties of subNatNat -/

lemma subNatNat_elim (m n : ℕ) (P : ℕ → ℕ → ℤ → Prop)
  (hp : ∀i n, P (n + i) n (ofNat i))
  (hn : ∀i m, P m (m + i + 1) (-[1+ i])) :
  P m n (subNatNat m n) :=
by
  have H : ∀ k , n - m = k → P m n (match n - m with | 0 => ofNat (m - n) | succ k => -[1+ k] : ℤ) := by
    intros k h
    cases k with
    | zero =>
        have ⟨k, h⟩ := (Nat.le.dest (Nat.le_of_sub_eq_zero h))
        rw [h.symm, Nat.add_sub_cancel_left, Nat.sub_self_add]
        apply hp
    | succ k =>
        simp
        have hle : m ≤ n := Nat.le_of_lt (Nat.lt_of_sub_eq_succ h)
        rw [Nat.sub_eq_iff_eq_add hle] at h
        rw [h, Nat.add_comm, Nat.add_sub_cancel_left]
        apply hn
  exact H _ rfl

lemma subNatNat_add_left {m n : ℕ} :
  subNatNat (m + n) m = ofNat n :=
by
  change (match m - (m + n) with
          | 0      => ofNat (m + n - m)
          | succ k => -[1+ k]) = ofNat n
  rw [Nat.sub_eq_zero_of_le (Nat.le_add_right _ _)]
  rw [Nat.add_sub_cancel_left]

lemma subNatNat_add_right {m n : ℕ} : subNatNat m (m + n + 1) = negSucc n := by
  change (match m + n + 1 - m with
          | 0      => ofNat (m - (m + n + 1))
          | succ k => -[1+ k]) = negSucc n
  simp
  rw [Nat.add_assoc, Nat.add_one, Nat.add_sub_cancel_left]

lemma subNatNat_add_add (m n k : ℕ) : subNatNat (m + k) (n + k) = subNatNat m n :=
subNatNat_elim m n (λm n i => subNatNat (m + k) (n + k) = i)
  (by
    intros i j
    rw [Nat.add_assoc, Nat.add_comm i k, ← Nat.add_assoc]
    exact subNatNat_add_left
  )
  (by
    intros i j
    rw [Nat.add_assoc j i 1, Nat.add_comm j (i+1), Nat.add_assoc, Nat.add_comm (i+1) (j+k)]
    exact subNatNat_add_right
  )

lemma subNatNat_of_le {m n : ℕ} (h : n ≤ m) : subNatNat m n = ofNat (m - n) :=
subNatNat_of_sub_eq_zero (Nat.sub_eq_zero_of_le h)

lemma subNatNat_of_lt {m n : ℕ} (h : m < n) : subNatNat m n = -[1+ pred (n - m)] := by
  rw [subNatNat_of_sub_eq_succ]
  rw [Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)]

/- ## natAbs -/

lemma natAbs_ofNat (n : ℕ) : natAbs ↑n = n := rfl

lemma eq_zero_ofNatAbs_eq_zero : ∀ {a : ℤ}, natAbs a = 0 → a = 0
| (ofNat _), H => congr_arg ofNat H
| -[1+ _],   H => absurd H (succ_ne_zero _)

lemma natAbs_pos_of_ne_zero {a : ℤ} (h : a ≠ 0) : 0 < natAbs a :=
(eq_zero_or_pos _).resolve_left $ mt eq_zero_ofNatAbs_eq_zero h

lemma natAbs_zero : natAbs (0 : ℤ) = (0 : ℕ) := rfl

lemma natAbs_one : natAbs (1 : ℤ) = (1 : ℕ) := rfl

lemma natAbs_mul_self : ∀ {a : ℤ}, ↑(natAbs a * natAbs a) = a * a
| (ofNat _) => rfl
| -[1+ _]   => rfl

@[simp] lemma natAbs_neg (a : ℤ) : natAbs (-a) = natAbs a := match a with
| (ofNat zero)     => rfl
| (ofNat (succ _)) => rfl
| (negSucc _)      => rfl

lemma natAbs_eq : ∀ (a : ℤ), a = natAbs a ∨ a = -↑(natAbs a)
| (ofNat _) => Or.inl rfl
| -[1+ _]   => Or.inr rfl

lemma eq_x_or_neg (a : ℤ) : ∃n : ℕ, a = n ∨ a = -↑n := ⟨_, natAbs_eq a⟩

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

-- E-rounding (`div` and `mod` defined in core) satisfy 0 ≤ mod x y < natAbs y for y ≠ 0

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
| (m+1:ℕ), -[1+ n] => subNatNat (m % succ n) n
| -[1+ m], (n : ℕ) => subNatNat n (succ (m % n))
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
def gcd (m n : ℤ) : ℕ := Nat.gcd (natAbs m) (natAbs n)

/- # ring properties -/

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

lemma subNatNat_sub {m n : ℕ} (h : n ≤ m) (k : ℕ) :
subNatNat (m - n) k = subNatNat m (k + n) := by
  rwa [← subNatNat_add_add _ _ n, Nat.sub_add_cancel]

lemma subNatNat_add (m n k : ℕ) : subNatNat (m + n) k = ofNat m + subNatNat n k :=
by
  have h := Nat.lt_or_ge n k
  cases h with
  | inl h' =>
    rw [subNatNat_of_lt h']
    simp
    rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h')]
    apply Eq.trans
    rw [← Nat.sub_add_cancel (Nat.le_of_lt h')]
    apply subNatNat_add_add
  | inr h' =>
    rw [subNatNat_of_le (h')]
    have h₂ : k ≤ m + n := Nat.le_trans h' (le_add_left _ _)
    rw [subNatNat_of_le h₂]
    simp
    rw [Nat.add_sub_assoc h']

lemma subNatNat_add_negSucc_ofNat (m n k : ℕ) :
    subNatNat m n + -[1+ k] = subNatNat m (n + succ k) :=
by
  have h := Nat.lt_or_ge m n
  cases h with
  | inr h' =>
    rw [subNatNat_of_le h']
    simp
    rw [subNatNat_sub h', Nat.add_comm]
  | inl h' =>
    have h₂ : m < n + succ k := Nat.lt_of_lt_of_le h' (le_add_right _ _)
    have h₃ : m ≤ n + k := le_of_succ_le_succ h₂
    rw [subNatNat_of_lt h', subNatNat_of_lt h₂]
    simp [Nat.add_comm]
    rw [← add_succ, succ_pred_eq_of_pos (Nat.sub_pos_of_lt h'), add_succ, succ_sub h₃, Nat.pred_succ]
    rw [Nat.add_comm n, Nat.add_sub_assoc (Nat.le_of_lt h')]

lemma add_assoc_aux1 (m n : ℕ) :
    ∀ c : ℤ, ofNat m + ofNat n + c = ofNat m + (ofNat n + c)
| (ofNat k) => by simp [Nat.add_assoc]
| -[1+ k]   => by simp [subNatNat_add]

lemma add_assoc_aux2 (m n k : ℕ) :
  -[1+ m] + -[1+ n] + ofNat k = -[1+ m] + (-[1+ n] + ofNat k) :=
by
  simp [add_succ]
  rw [Int.add_comm, subNatNat_add_negSucc_ofNat]
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
  simp [add_succ, Nat.add_comm, Nat.add_left_comm, neg_ofNat_of_succ]

/- ## negation -/

lemma sub_nat_self : ∀ n, subNatNat n n = 0
| 0        => rfl
| (succ m) => by
  rw [subNatNat_of_sub_eq_zero, Nat.sub_self, ofNat_zero]
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
| a, b => by cases a <;> cases b <;> simp [Nat.mul_comm]

lemma ofNat_mul_negOfNat (m : ℕ) : ∀ n, ofNat m * negOfNat n = negOfNat (m * n)
| 0        => rfl
| (succ n) => rfl

lemma negOfNat_mul_ofNat (m n : ℕ) : negOfNat m * ofNat n = negOfNat (m * n) := by
    rw [Int.mul_comm]
    simp [ofNat_mul_negOfNat, Nat.mul_comm]

lemma negSucc_ofNat_mul_negOfNat (m : ℕ) :
  ∀ n, -[1+ m] * negOfNat n = ofNat (succ m * n)
| 0        => rfl
| (succ n) => rfl

lemma negOfNat_mul_negSucc_ofNat (m n : ℕ) :
  negOfNat n * -[1+ m] = ofNat (n * succ m) := by
    rw [Int.mul_comm, negSucc_ofNat_mul_negOfNat, Nat.mul_comm]

attribute [local simp] ofNat_mul_negOfNat negOfNat_mul_ofNat
  negSucc_ofNat_mul_negOfNat negOfNat_mul_negSucc_ofNat

protected lemma mul_assoc : ∀ a b c : ℤ, a * b * c = a * (b * c)
| a, b, c => by cases a <;> cases b <;> cases c <;> simp [Nat.mul_assoc]

protected lemma mul_zero : ∀ (a : ℤ), a * 0 = 0
| (ofNat m) => rfl
| -[1+ m]   => rfl

protected lemma zero_mul (a : ℤ) : 0 * a = 0 :=
Int.mul_comm a 0 ▸ Int.mul_zero a

lemma negOfNat_eq_subNatNat_zero : ∀ n, negOfNat n = subNatNat 0 n
| 0        => rfl
| (succ n) => rfl

lemma ofNat_mul_subNatNat (m n k : ℕ) :
  ofNat m * subNatNat n k = subNatNat (m * n) (m * k) :=
by
  cases m with
  | zero =>
    simp [ofNat_zero, Int.zero_mul, Nat.zero_mul]
  | succ m =>
    have h := Nat.lt_or_ge n k
    cases h with
    | inl h =>
      have h' : (succ m) * n < (succ m) * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
      rw [subNatNat_of_lt h, subNatNat_of_lt h']
      simp
      rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)]
      rw [← neg_ofNat_of_succ, Nat.mul_sub_left_distrib]
      rw [← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h')]
      rfl
    | inr h =>
      have h' : (succ m) * k ≤ (succ m) * n := Nat.mul_le_mul_left _ h
      rw [subNatNat_of_le h, subNatNat_of_le h']
      simp
      rw [Nat.mul_sub_left_distrib]

lemma negOfNat_add : ∀ m n : ℕ, negOfNat m + negOfNat n = negOfNat (m + n)
| zero,   zero   => by simp
| zero,   succ n => by simp [Nat.zero_add]; rfl
| succ m, zero   => by simp; rfl
| succ m, succ n => by simp [Nat.succ_add]; rfl

lemma negSucc_ofNat_mul_subNatNat (m n k : ℕ) :
  -[1+ m] * subNatNat n k = subNatNat (succ m * k) (succ m * n) :=
by
  have h := Nat.lt_or_ge n k
  cases h with
  | inl h =>
    have h' : succ m * n < succ m * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
    rw [subNatNat_of_lt h, subNatNat_of_le (Nat.le_of_lt h')]
    simp [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h), Nat.mul_sub_left_distrib]
  | inr h =>
    cases Nat.lt_or_ge k n with
    | inl h' =>
      have h₁ : succ m * n > succ m * k := Nat.mul_lt_mul_of_pos_left h' (Nat.succ_pos m)
      rw [subNatNat_of_le h, subNatNat_of_lt h₁, negSucc_ofNat_ofNat,
        Nat.mul_sub_left_distrib, ← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁)]
      rfl
    | inr h' =>
      rw [Nat.le_antisymm h h', sub_nat_self, sub_nat_self, Int.mul_zero]

attribute [local simp] ofNat_mul_subNatNat negOfNat_add negSucc_ofNat_mul_subNatNat

protected lemma distrib_left : ∀ a b c : ℤ, a * (b + c) = a * b + a * c
| (ofNat m), (ofNat n), (ofNat k) => by simp [Nat.left_distrib]
| (ofNat m), (ofNat n), -[1+ k]   => by simp [negOfNat_eq_subNatNat_zero] rw [← subNatNat_add] rfl
| (ofNat m), -[1+ n],   (ofNat k) => by simp [negOfNat_eq_subNatNat_zero] rw [Int.add_comm, ← subNatNat_add] rfl
| (ofNat m), -[1+ n],   -[1+ k]   => by simp rw [← Nat.left_distrib, succ_add] rfl
| -[1+ m],   (ofNat n), (ofNat k) => by simp [Nat.mul_comm] rw [← Nat.right_distrib, Nat.mul_comm]
| -[1+ m],   (ofNat n), -[1+ k]   => by simp [negOfNat_eq_subNatNat_zero] rw [Int.add_comm, ← subNatNat_add] rfl
| -[1+ m],   -[1+ n],   (ofNat k) => by simp [negOfNat_eq_subNatNat_zero] rw [← subNatNat_add] rfl
| -[1+ m],   -[1+ n],   -[1+ k]   => by simp rw [← Nat.left_distrib, succ_add] rfl

protected lemma distrib_right (a b c : ℤ) : (a + b) * c = a * c + b * c :=
by simp [Int.mul_comm, Int.distrib_left]

protected lemma zero_ne_one : (0 : ℤ) ≠ 1 := λ h => Int.noConfusion h fun.

lemma ofNat_sub {n m : ℕ} (h : m ≤ n) : ofNat (n - m) = ofNat n - ofNat m := by
  show ofNat (n - m) = ofNat n + negOfNat m
  match m, h with
  | 0, h =>
    rfl
  | succ m, h =>
    show ofNat (n - succ m) = subNatNat n (succ m)
    simp [subNatNat, subNatNat] -- TODO: How to avoid having to simp through rename definitions to unfold them?
    rw [Nat.sub_eq_zero_of_le h]

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

lemma negSucc_ofNat_coe' (n : ℕ) : -[1+ n] = -↑n - 1 :=
by rw [Int.sub_eq_add_neg, ← Int.neg_add]; rfl

protected lemma subNatNat_eq_coe {m n : ℕ} : subNatNat m n = ↑m - ↑n := by
  refine subNatNat_elim m n (fun m n i => i = ↑m - ↑n) ?p ?n
  case p =>
    intros i n
    rw [Int.ofNat_add, Int.sub_eq_add_neg, Int.add_assoc, Int.add_left_comm,
      Int.add_right_neg, Int.add_zero]
  case n =>
    intros i n
    simp only [negSucc_ofNat_coe, ofNat_add, Int.sub_eq_add_neg, Int.neg_add, ← Int.add_assoc]
    rw [← @Int.sub_eq_add_neg n, ← ofNat_sub, Nat.sub_self, ofNat_zero, Int.zero_add]
    apply Nat.le_refl

theorem toNat_sub (m n : ℕ) : toNat (m - n : ℕ) = m - n := rfl

protected lemma one_mul : ∀ (a : ℤ), (1 : ℤ) * a = a
| (ofNat n) => show ofNat (1 * n) = ofNat n by rw [Nat.one_mul]
| -[1+ n]   => show -[1+ (1 * n)] = -[1+ n] by rw [Nat.one_mul]

protected lemma mul_one (a : ℤ) : a * 1 = a :=
by rw [Int.mul_comm, Int.one_mul]

protected lemma neg_eq_neg_one_mul : ∀ a : ℤ, -a = -1 * a
| (ofNat 0)     => rfl
| (ofNat (n+1)) => show _ = -[1+ (1*n)+0] by rw [Nat.one_mul] rfl
| -[1+ n]       => show _ = ofNat _ by rw [Nat.one_mul] rfl

theorem sign_mul_natAbs : ∀ (a : ℤ), sign a * natAbs a = a
| (n+1:ℕ) => Int.one_mul _
| 0       => rfl
| -[1+ n] => (Int.neg_eq_neg_one_mul _).symm

end Int
