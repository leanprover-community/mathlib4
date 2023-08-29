/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Num.Bitwise
import Mathlib.Data.Int.CharZero
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.PSub
import Mathlib.Data.Nat.Size

#align_import data.num.lemmas from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

/-!
# Properties of the binary representation of integers
-/

/-
Porting note:
`bit0` and `bit1` are deprecated because it is mainly used to represent number literal in Lean3 but
not in Lean4 anymore. However, this file uses them for encoding numbers so this linter is
unnecessary.
-/
set_option linter.deprecated false

-- Porting note: Required for the notation `-[n+1]`.
open Int

attribute [local simp] add_assoc

namespace PosNum

variable {α : Type*}

@[simp, norm_cast]
theorem cast_one [One α] [Add α] : ((1 : PosNum) : α) = 1 :=
  rfl
#align pos_num.cast_one PosNum.cast_one

@[simp]
theorem cast_one' [One α] [Add α] : (PosNum.one : α) = 1 :=
  rfl
#align pos_num.cast_one' PosNum.cast_one'

@[simp, norm_cast]
theorem cast_bit0 [One α] [Add α] (n : PosNum) : (n.bit0 : α) = _root_.bit0 (n : α) :=
  rfl
#align pos_num.cast_bit0 PosNum.cast_bit0

@[simp, norm_cast]
theorem cast_bit1 [One α] [Add α] (n : PosNum) : (n.bit1 : α) = _root_.bit1 (n : α) :=
  rfl
#align pos_num.cast_bit1 PosNum.cast_bit1

@[simp, norm_cast]
theorem cast_to_nat [AddMonoidWithOne α] : ∀ n : PosNum, ((n : ℕ) : α) = n
  | 1 => Nat.cast_one
  | bit0 p => (Nat.cast_bit0 _).trans <| congr_arg _root_.bit0 p.cast_to_nat
  | bit1 p => (Nat.cast_bit1 _).trans <| congr_arg _root_.bit1 p.cast_to_nat
#align pos_num.cast_to_nat PosNum.cast_to_nat

@[norm_cast] -- @[simp] -- Porting note: simp can prove this
theorem to_nat_to_int (n : PosNum) : ((n : ℕ) : ℤ) = n :=
  cast_to_nat _
#align pos_num.to_nat_to_int PosNum.to_nat_to_int

@[simp, norm_cast]
theorem cast_to_int [AddGroupWithOne α] (n : PosNum) : ((n : ℤ) : α) = n := by
  rw [← to_nat_to_int, Int.cast_ofNat, cast_to_nat]
  -- 🎉 no goals
#align pos_num.cast_to_int PosNum.cast_to_int

theorem succ_to_nat : ∀ n, (succ n : ℕ) = n + 1
  | 1 => rfl
  | bit0 p => rfl
  | bit1 p =>
    (congr_arg _root_.bit0 (succ_to_nat p)).trans <|
      show ↑p + 1 + ↑p + 1 = ↑p + ↑p + 1 + 1 by simp [add_left_comm]
                                                -- 🎉 no goals
#align pos_num.succ_to_nat PosNum.succ_to_nat

theorem one_add (n : PosNum) : 1 + n = succ n := by cases n <;> rfl
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
#align pos_num.one_add PosNum.one_add

theorem add_one (n : PosNum) : n + 1 = succ n := by cases n <;> rfl
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
#align pos_num.add_one PosNum.add_one

@[norm_cast]
theorem add_to_nat : ∀ m n, ((m + n : PosNum) : ℕ) = m + n
  | 1, b => by rw [one_add b, succ_to_nat, add_comm]; rfl
               -- ⊢ 1 + ↑b = ↑1 + ↑b
                                                      -- 🎉 no goals
  | a, 1 => by rw [add_one a, succ_to_nat]; rfl
               -- ⊢ ↑a + 1 = ↑a + ↑1
                                            -- 🎉 no goals
  | bit0 a, bit0 b => (congr_arg _root_.bit0 (add_to_nat a b)).trans <| add_add_add_comm _ _ _ _
  | bit0 a, bit1 b =>
    (congr_arg _root_.bit1 (add_to_nat a b)).trans <|
      show (a + b + (a + b) + 1 : ℕ) = a + a + (b + b + 1) by simp [add_left_comm]
                                                              -- 🎉 no goals
  | bit1 a, bit0 b =>
    (congr_arg _root_.bit1 (add_to_nat a b)).trans <|
      show (a + b + (a + b) + 1 : ℕ) = a + a + 1 + (b + b) by simp [add_comm, add_left_comm]
                                                              -- 🎉 no goals
  | bit1 a, bit1 b =>
    show (succ (a + b) + succ (a + b) : ℕ) = a + a + 1 + (b + b + 1) by
      rw [succ_to_nat, add_to_nat a b]; simp [add_left_comm]
      -- ⊢ ↑a + ↑b + 1 + (↑a + ↑b + 1) = ↑a + ↑a + 1 + (↑b + ↑b + 1)
                                        -- 🎉 no goals
#align pos_num.add_to_nat PosNum.add_to_nat

theorem add_succ : ∀ m n : PosNum, m + succ n = succ (m + n)
  | 1, b => by simp [one_add]
               -- 🎉 no goals
  | bit0 a, 1 => congr_arg bit0 (add_one a)
  | bit1 a, 1 => congr_arg bit1 (add_one a)
  | bit0 a, bit0 b => rfl
  | bit0 a, bit1 b => congr_arg bit0 (add_succ a b)
  | bit1 a, bit0 b => rfl
  | bit1 a, bit1 b => congr_arg bit1 (add_succ a b)
#align pos_num.add_succ PosNum.add_succ

theorem bit0_of_bit0 : ∀ n, _root_.bit0 n = bit0 n
  | 1 => rfl
  | bit0 p => congr_arg bit0 (bit0_of_bit0 p)
  | bit1 p => show bit0 (succ (_root_.bit0 p)) = _ by rw [bit0_of_bit0 p]; rfl
                                                      -- ⊢ bit0 (succ (bit0 p)) = bit0 (bit1 p)
                                                                           -- 🎉 no goals
#align pos_num.bit0_of_bit0 PosNum.bit0_of_bit0

theorem bit1_of_bit1 (n : PosNum) : _root_.bit1 n = bit1 n :=
  show _root_.bit0 n + 1 = bit1 n by rw [add_one, bit0_of_bit0]; rfl
                                     -- ⊢ succ (bit0 n) = bit1 n
                                                                 -- 🎉 no goals
#align pos_num.bit1_of_bit1 PosNum.bit1_of_bit1

@[norm_cast]
theorem mul_to_nat (m) : ∀ n, ((m * n : PosNum) : ℕ) = m * n
  | 1 => (mul_one _).symm
  | bit0 p => show (↑(m * p) + ↑(m * p) : ℕ) = ↑m * (p + p) by rw [mul_to_nat m p, left_distrib]
                                                               -- 🎉 no goals
  | bit1 p =>
    (add_to_nat (bit0 (m * p)) m).trans <|
      show (↑(m * p) + ↑(m * p) + ↑m : ℕ) = ↑m * (p + p) + m by rw [mul_to_nat m p, left_distrib]
                                                                -- 🎉 no goals
#align pos_num.mul_to_nat PosNum.mul_to_nat

theorem to_nat_pos : ∀ n : PosNum, 0 < (n : ℕ)
  | 1 => zero_lt_one
  | bit0 p =>
    let h := to_nat_pos p
    add_pos h h
  | bit1 _p => Nat.succ_pos _
#align pos_num.to_nat_pos PosNum.to_nat_pos

theorem cmp_to_nat_lemma {m n : PosNum} : (m : ℕ) < n → (bit1 m : ℕ) < bit0 n :=
  show (m : ℕ) < n → (m + m + 1 + 1 : ℕ) ≤ n + n by
    intro h; rw [Nat.add_right_comm m m 1, add_assoc]; exact add_le_add h h
    -- ⊢ ↑m + ↑m + 1 + 1 ≤ ↑n + ↑n
             -- ⊢ ↑m + 1 + (↑m + 1) ≤ ↑n + ↑n
                                                       -- 🎉 no goals
#align pos_num.cmp_to_nat_lemma PosNum.cmp_to_nat_lemma

theorem cmp_swap (m) : ∀ n, (cmp m n).swap = cmp n m := by
  induction' m with m IH m IH <;> intro n <;> cases' n with n n <;> unfold cmp <;>
                                  -- ⊢ Ordering.swap (cmp one n) = cmp n one
                                  -- ⊢ Ordering.swap (cmp (bit1 m) n) = cmp n (bit1 m)
                                  -- ⊢ Ordering.swap (cmp (bit0 m) n) = cmp n (bit0 m)
                                                                    -- ⊢ Ordering.swap Ordering.eq = Ordering.eq
                                                                    -- ⊢ Ordering.swap Ordering.lt = Ordering.gt
                                                                    -- ⊢ Ordering.swap Ordering.lt = Ordering.gt
                                                                    -- ⊢ Ordering.swap Ordering.gt = Ordering.lt
                                                                    -- ⊢ Ordering.swap (cmp m n) = cmp n m
                                                                    -- ⊢ Ordering.swap (Ordering.casesOn (cmp m n) Ordering.lt Ordering.gt Ordering.g …
                                                                    -- ⊢ Ordering.swap Ordering.gt = Ordering.lt
                                                                    -- ⊢ Ordering.swap (Ordering.casesOn (cmp m n) Ordering.lt Ordering.lt Ordering.g …
                                                                    -- ⊢ Ordering.swap (cmp m n) = cmp n m
    try { rfl } <;> rw [← IH] <;> cases cmp m n <;> rfl
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- ⊢ Ordering.swap (cmp m n) = cmp n m
    -- ⊢ Ordering.swap (Ordering.casesOn (cmp m n) Ordering.lt Ordering.gt Ordering.g …
    -- 🎉 no goals
    -- ⊢ Ordering.swap (Ordering.casesOn (cmp m n) Ordering.lt Ordering.lt Ordering.g …
    -- ⊢ Ordering.swap (cmp m n) = cmp n m
                    -- 🎉 no goals
                    -- ⊢ Ordering.swap (Ordering.casesOn (cmp m n) Ordering.lt Ordering.gt Ordering.g …
                    -- ⊢ Ordering.swap (Ordering.casesOn (cmp m n) Ordering.lt Ordering.lt Ordering.g …
                    -- 🎉 no goals
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
#align pos_num.cmp_swap PosNum.cmp_swap

theorem cmp_to_nat : ∀ m n, (Ordering.casesOn (cmp m n) ((m : ℕ) < n) (m = n) ((n : ℕ) < m) : Prop)
  | 1, 1 => rfl
  | bit0 a, 1 =>
    let h : (1 : ℕ) ≤ a := to_nat_pos a
    add_le_add h h
  | bit1 a, 1 => Nat.succ_lt_succ <| to_nat_pos <| bit0 a
  | 1, bit0 b =>
    let h : (1 : ℕ) ≤ b := to_nat_pos b
    add_le_add h h
  | 1, bit1 b => Nat.succ_lt_succ <| to_nat_pos <| bit0 b
  | bit0 a, bit0 b => by
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    -- ⊢ Ordering.casesOn (cmp (bit0 a) (bit0 b)) (↑(bit0 a) < ↑(bit0 b)) (bit0 a = b …
                            -- ⊢ Ordering.casesOn (cmp a b) (↑a < ↑b) (a = b) (↑b < ↑a) → Ordering.casesOn (c …
                                                           -- ⊢ ↑a < ↑b → _root_.bit0 ↑a < _root_.bit0 ↑b
                                                           -- ⊢ a = b → bit0 a = bit0 b
                                                           -- ⊢ ↑b < ↑a → _root_.bit0 ↑b < _root_.bit0 ↑a
                                                                     -- ⊢ _root_.bit0 ↑a < _root_.bit0 ↑b
                                                                     -- ⊢ bit0 a = bit0 b
                                                                     -- ⊢ _root_.bit0 ↑b < _root_.bit0 ↑a
    · exact add_lt_add this this
      -- 🎉 no goals
    · rw [this]
      -- 🎉 no goals
    · exact add_lt_add this this
      -- 🎉 no goals
  | bit0 a, bit1 b => by
    dsimp [cmp]
    -- ⊢ Ordering.rec (_root_.bit0 ↑a < _root_.bit1 ↑b) (bit0 a = bit1 b) (_root_.bit …
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    -- ⊢ Ordering.rec (_root_.bit0 ↑a < _root_.bit1 ↑b) (bit0 a = bit1 b) (_root_.bit …
                            -- ⊢ Ordering.casesOn (cmp a b) (↑a < ↑b) (a = b) (↑b < ↑a) → Ordering.rec (_root …
                                                           -- ⊢ ↑a < ↑b → _root_.bit0 ↑a < _root_.bit1 ↑b
                                                           -- ⊢ a = b → _root_.bit0 ↑a < _root_.bit1 ↑b
                                                           -- ⊢ ↑b < ↑a → _root_.bit1 ↑b < _root_.bit0 ↑a
                                                                     -- ⊢ _root_.bit0 ↑a < _root_.bit1 ↑b
                                                                     -- ⊢ _root_.bit0 ↑a < _root_.bit1 ↑b
                                                                     -- ⊢ _root_.bit1 ↑b < _root_.bit0 ↑a
    · exact Nat.le_succ_of_le (add_lt_add this this)
      -- 🎉 no goals
    · rw [this]
      -- ⊢ _root_.bit0 ↑b < _root_.bit1 ↑b
      apply Nat.lt_succ_self
      -- 🎉 no goals
    · exact cmp_to_nat_lemma this
      -- 🎉 no goals
  | bit1 a, bit0 b => by
    dsimp [cmp]
    -- ⊢ Ordering.rec (_root_.bit1 ↑a < _root_.bit0 ↑b) (bit1 a = bit0 b) (_root_.bit …
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    -- ⊢ Ordering.rec (_root_.bit1 ↑a < _root_.bit0 ↑b) (bit1 a = bit0 b) (_root_.bit …
                            -- ⊢ Ordering.casesOn (cmp a b) (↑a < ↑b) (a = b) (↑b < ↑a) → Ordering.rec (_root …
                                                           -- ⊢ ↑a < ↑b → _root_.bit1 ↑a < _root_.bit0 ↑b
                                                           -- ⊢ a = b → _root_.bit0 ↑b < _root_.bit1 ↑a
                                                           -- ⊢ ↑b < ↑a → _root_.bit0 ↑b < _root_.bit1 ↑a
                                                                     -- ⊢ _root_.bit1 ↑a < _root_.bit0 ↑b
                                                                     -- ⊢ _root_.bit0 ↑b < _root_.bit1 ↑a
                                                                     -- ⊢ _root_.bit0 ↑b < _root_.bit1 ↑a
    · exact cmp_to_nat_lemma this
      -- 🎉 no goals
    · rw [this]
      -- ⊢ _root_.bit0 ↑b < _root_.bit1 ↑b
      apply Nat.lt_succ_self
      -- 🎉 no goals
    · exact Nat.le_succ_of_le (add_lt_add this this)
      -- 🎉 no goals
  | bit1 a, bit1 b => by
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    -- ⊢ Ordering.casesOn (cmp (bit1 a) (bit1 b)) (↑(bit1 a) < ↑(bit1 b)) (bit1 a = b …
                            -- ⊢ Ordering.casesOn (cmp a b) (↑a < ↑b) (a = b) (↑b < ↑a) → Ordering.casesOn (c …
                                                           -- ⊢ ↑a < ↑b → _root_.bit1 ↑a < _root_.bit1 ↑b
                                                           -- ⊢ a = b → bit1 a = bit1 b
                                                           -- ⊢ ↑b < ↑a → _root_.bit1 ↑b < _root_.bit1 ↑a
                                                                     -- ⊢ _root_.bit1 ↑a < _root_.bit1 ↑b
                                                                     -- ⊢ bit1 a = bit1 b
                                                                     -- ⊢ _root_.bit1 ↑b < _root_.bit1 ↑a
    · exact Nat.succ_lt_succ (add_lt_add this this)
      -- 🎉 no goals
    · rw [this]
      -- 🎉 no goals
    · exact Nat.succ_lt_succ (add_lt_add this this)
      -- 🎉 no goals
#align pos_num.cmp_to_nat PosNum.cmp_to_nat

@[norm_cast]
theorem lt_to_nat {m n : PosNum} : (m : ℕ) < n ↔ m < n :=
  show (m : ℕ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by simp at h; simp [h]
                           -- ⊢ ↑m < ↑n ↔ Ordering.lt = Ordering.lt
                                      -- 🎉 no goals
    | Ordering.eq, h => by simp at h; simp [h, lt_irrefl]
                           -- ⊢ ↑m < ↑n ↔ Ordering.eq = Ordering.lt
                                      -- 🎉 no goals
    | Ordering.gt, h => by simp [not_lt_of_gt h]
                           -- 🎉 no goals
#align pos_num.lt_to_nat PosNum.lt_to_nat

@[norm_cast]
theorem le_to_nat {m n : PosNum} : (m : ℕ) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr lt_to_nat
  -- ⊢ ¬↑n < ↑m ↔ m ≤ n
                 -- 🎉 no goals
#align pos_num.le_to_nat PosNum.le_to_nat

end PosNum

namespace Num

variable {α : Type*}

open PosNum

theorem add_zero (n : Num) : n + 0 = n := by cases n <;> rfl
                                             -- ⊢ zero + 0 = zero
                                                         -- 🎉 no goals
                                                         -- 🎉 no goals
#align num.add_zero Num.add_zero

theorem zero_add (n : Num) : 0 + n = n := by cases n <;> rfl
                                             -- ⊢ 0 + zero = zero
                                                         -- 🎉 no goals
                                                         -- 🎉 no goals
#align num.zero_add Num.zero_add

theorem add_one : ∀ n : Num, n + 1 = succ n
  | 0 => rfl
  | pos p => by cases p <;> rfl
                            -- 🎉 no goals
                            -- 🎉 no goals
                            -- 🎉 no goals
#align num.add_one Num.add_one

theorem add_succ : ∀ m n : Num, m + succ n = succ (m + n)
  | 0, n => by simp [zero_add]
               -- 🎉 no goals
  | pos p, 0 => show pos (p + 1) = succ (pos p + 0) by rw [PosNum.add_one, add_zero]; rfl
                                                       -- ⊢ pos (PosNum.succ p) = succ (pos p)
                                                                                      -- 🎉 no goals
  | pos p, pos q => congr_arg pos (PosNum.add_succ _ _)
#align num.add_succ Num.add_succ

theorem bit0_of_bit0 : ∀ n : Num, bit0 n = n.bit0
  | 0 => rfl
  | pos p => congr_arg pos p.bit0_of_bit0
#align num.bit0_of_bit0 Num.bit0_of_bit0

theorem bit1_of_bit1 : ∀ n : Num, bit1 n = n.bit1
  | 0 => rfl
  | pos p => congr_arg pos p.bit1_of_bit1
#align num.bit1_of_bit1 Num.bit1_of_bit1

@[simp]
theorem ofNat'_zero : Num.ofNat' 0 = 0 := by simp [Num.ofNat']
                                             -- 🎉 no goals
#align num.of_nat'_zero Num.ofNat'_zero

theorem ofNat'_bit (b n) : ofNat' (Nat.bit b n) = cond b Num.bit1 Num.bit0 (ofNat' n) :=
  Nat.binaryRec_eq rfl _ _
#align num.of_nat'_bit Num.ofNat'_bit

@[simp]
theorem ofNat'_one : Num.ofNat' 1 = 1 := by erw [ofNat'_bit true 0, cond, ofNat'_zero]; rfl
                                            -- ⊢ (match (motive := Bool → Num → Num) true with
                                                                                        -- 🎉 no goals
#align num.of_nat'_one Num.ofNat'_one

theorem bit1_succ : ∀ n : Num, n.bit1.succ = n.succ.bit0
  | 0 => rfl
  | pos _n => rfl
#align num.bit1_succ Num.bit1_succ

theorem ofNat'_succ : ∀ {n}, ofNat' (n + 1) = ofNat' n + 1 :=
  @(Nat.binaryRec (by simp) fun b n ih => by
                      -- 🎉 no goals
    cases b
    -- ⊢ ofNat' (Nat.bit false n + 1) = ofNat' (Nat.bit false n) + 1
    · erw [ofNat'_bit true n, ofNat'_bit]
      -- ⊢ cond true Num.bit1 Num.bit0 (ofNat' n) = cond false Num.bit1 Num.bit0 (ofNat …
      simp only [← bit1_of_bit1, ← bit0_of_bit0, cond, _root_.bit1]
      -- 🎉 no goals
    -- Porting note: `cc` was not ported yet so `exact Nat.add_left_comm n 1 1` is used.
    · erw [show n.bit true + 1 = (n + 1).bit false by
        simp [Nat.bit, _root_.bit1, _root_.bit0]; exact Nat.add_left_comm n 1 1,
        ofNat'_bit, ofNat'_bit, ih]
      simp only [cond, add_one, bit1_succ])
      -- 🎉 no goals
#align num.of_nat'_succ Num.ofNat'_succ

@[simp]
theorem add_ofNat' (m n) : Num.ofNat' (m + n) = Num.ofNat' m + Num.ofNat' n := by
  -- Porting note: `simp` fails to unify `ofNat' (n + 1)` with `ofNat' n.succ`
  have : ∀ {n}, ofNat' n.succ = ofNat' n + 1 := ofNat'_succ
  -- ⊢ ofNat' (m + n) = ofNat' m + ofNat' n
  induction n <;> simp [Nat.add_zero, this, add_zero, Nat.add_succ, add_one, add_succ, *]
  -- ⊢ ofNat' (m + Nat.zero) = ofNat' m + ofNat' Nat.zero
                  -- 🎉 no goals
                  -- 🎉 no goals
#align num.add_of_nat' Num.add_ofNat'

@[simp, norm_cast]
theorem cast_zero [Zero α] [One α] [Add α] : ((0 : Num) : α) = 0 :=
  rfl
#align num.cast_zero Num.cast_zero

@[simp]
theorem cast_zero' [Zero α] [One α] [Add α] : (Num.zero : α) = 0 :=
  rfl
#align num.cast_zero' Num.cast_zero'

@[simp, norm_cast]
theorem cast_one [Zero α] [One α] [Add α] : ((1 : Num) : α) = 1 :=
  rfl
#align num.cast_one Num.cast_one

@[simp]
theorem cast_pos [Zero α] [One α] [Add α] (n : PosNum) : (Num.pos n : α) = n :=
  rfl
#align num.cast_pos Num.cast_pos

theorem succ'_to_nat : ∀ n, (succ' n : ℕ) = n + 1
  | 0 => (Nat.zero_add _).symm
  | pos _p => PosNum.succ_to_nat _
#align num.succ'_to_nat Num.succ'_to_nat

theorem succ_to_nat (n) : (succ n : ℕ) = n + 1 :=
  succ'_to_nat n
#align num.succ_to_nat Num.succ_to_nat

@[simp, norm_cast]
theorem cast_to_nat [AddMonoidWithOne α] : ∀ n : Num, ((n : ℕ) : α) = n
  | 0 => Nat.cast_zero
  | pos p => p.cast_to_nat
#align num.cast_to_nat Num.cast_to_nat

@[norm_cast]
theorem add_to_nat : ∀ m n, ((m + n : Num) : ℕ) = m + n
  | 0, 0 => rfl
  | 0, pos _q => (Nat.zero_add _).symm
  | pos _p, 0 => rfl
  | pos _p, pos _q => PosNum.add_to_nat _ _
#align num.add_to_nat Num.add_to_nat

@[norm_cast]
theorem mul_to_nat : ∀ m n, ((m * n : Num) : ℕ) = m * n
  | 0, 0 => rfl
  | 0, pos _q => (zero_mul _).symm
  | pos _p, 0 => rfl
  | pos _p, pos _q => PosNum.mul_to_nat _ _
#align num.mul_to_nat Num.mul_to_nat

theorem cmp_to_nat : ∀ m n, (Ordering.casesOn (cmp m n) ((m : ℕ) < n) (m = n) ((n : ℕ) < m) : Prop)
  | 0, 0 => rfl
  | 0, pos b => to_nat_pos _
  | pos a, 0 => to_nat_pos _
  | pos a, pos b => by
    have := PosNum.cmp_to_nat a b; revert this; dsimp [cmp]; cases PosNum.cmp a b
    -- ⊢ Ordering.casesOn (cmp (pos a) (pos b)) (↑(pos a) < ↑(pos b)) (pos a = pos b) …
                                   -- ⊢ Ordering.casesOn (PosNum.cmp a b) (↑a < ↑b) (a = b) (↑b < ↑a) → Ordering.cas …
                                                -- ⊢ Ordering.rec (↑a < ↑b) (a = b) (↑b < ↑a) (PosNum.cmp a b) → Ordering.rec (↑a …
    exacts [id, congr_arg pos, id]
    -- 🎉 no goals
#align num.cmp_to_nat Num.cmp_to_nat

@[norm_cast]
theorem lt_to_nat {m n : Num} : (m : ℕ) < n ↔ m < n :=
  show (m : ℕ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by simp at h; simp [h]
                           -- ⊢ ↑m < ↑n ↔ Ordering.lt = Ordering.lt
                                      -- 🎉 no goals
    | Ordering.eq, h => by simp at h; simp [h, lt_irrefl]
                           -- ⊢ ↑m < ↑n ↔ Ordering.eq = Ordering.lt
                                      -- 🎉 no goals
    | Ordering.gt, h => by simp [not_lt_of_gt h]
                           -- 🎉 no goals
#align num.lt_to_nat Num.lt_to_nat

@[norm_cast]
theorem le_to_nat {m n : Num} : (m : ℕ) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr lt_to_nat
  -- ⊢ ¬↑n < ↑m ↔ m ≤ n
                 -- 🎉 no goals
#align num.le_to_nat Num.le_to_nat

end Num

namespace PosNum

@[simp]
theorem of_to_nat' : ∀ n : PosNum, Num.ofNat' (n : ℕ) = Num.pos n
  | 1 => by erw [@Num.ofNat'_bit true 0, Num.ofNat'_zero]; rfl
            -- ⊢ cond true Num.bit1 Num.bit0 0 = Num.pos 1
                                                           -- 🎉 no goals
  | bit0 p => by erw [@Num.ofNat'_bit false, of_to_nat' p]; rfl
                 -- ⊢ cond false Num.bit1 Num.bit0 (Num.pos p) = Num.pos (bit0 p)
                                                            -- 🎉 no goals
  | bit1 p => by erw [@Num.ofNat'_bit true, of_to_nat' p]; rfl
                 -- ⊢ cond true Num.bit1 Num.bit0 (Num.pos p) = Num.pos (bit1 p)
                                                           -- 🎉 no goals
#align pos_num.of_to_nat' PosNum.of_to_nat'

end PosNum

namespace Num

@[simp, norm_cast]
theorem of_to_nat' : ∀ n : Num, Num.ofNat' (n : ℕ) = n
  | 0 => ofNat'_zero
  | pos p => p.of_to_nat'
#align num.of_to_nat' Num.of_to_nat'

@[norm_cast]
theorem to_nat_inj {m n : Num} : (m : ℕ) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective of_to_nat' h, congr_arg _⟩
#align num.to_nat_inj Num.to_nat_inj

/-- This tactic tries to turn an (in)equality about `Num`s to one about `Nat`s by rewriting.
```lean
example (n : Num) (m : Num) : n ≤ n + m := by
  transfer_rw
  exact Nat.le_add_right _ _
```
-/
scoped macro (name := transfer_rw) "transfer_rw" : tactic => `(tactic|
    (repeat first | rw [← to_nat_inj] | rw [← lt_to_nat] | rw [← le_to_nat]
     repeat first | rw [add_to_nat] | rw [mul_to_nat] | rw [cast_one] | rw [cast_zero]))

/--
This tactic tries to prove (in)equalities about `Num`s by transferring them to the `Nat` world and
then trying to call `simp`.
```lean
example (n : Num) (m : Num) : n ≤ n + m := by transfer
```
-/
scoped macro (name := transfer) "transfer" : tactic => `(tactic|
    (intros; transfer_rw; try simp))

instance addMonoid : AddMonoid Num where
  add := (· + ·)
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  add_assoc := by transfer
                  -- 🎉 no goals
#align num.add_monoid Num.addMonoid

instance addMonoidWithOne : AddMonoidWithOne Num :=
  { Num.addMonoid with
    natCast := Num.ofNat'
    one := 1
    natCast_zero := ofNat'_zero
    natCast_succ := fun _ => ofNat'_succ }
#align num.add_monoid_with_one Num.addMonoidWithOne

instance commSemiring : CommSemiring Num := by
  refine'
    { Num.addMonoid,
      Num.addMonoidWithOne with
      mul := (· * ·)
      one := 1
      add := (· + ·)
      zero := 0
      npow := @npowRec Num ⟨1⟩ ⟨(· * ·)⟩, .. } <;>
    try { intros; rfl } <;>
    -- ⊢ ∀ (a b : Num), a + b = b + a
    -- ⊢ ∀ (a b c : Num), a * (b + c) = a * b + a * c
    -- ⊢ ∀ (a b c : Num), (a + b) * c = a * c + b * c
    -- ⊢ ∀ (a : Num), 0 * a = 0
    -- ⊢ ∀ (a : Num), a * 0 = 0
    -- ⊢ ∀ (a b c : Num), a * b * c = a * (b * c)
    -- ⊢ ∀ (a : Num), 1 * a = a
    -- ⊢ ∀ (a : Num), a * 1 = a
    -- 🎉 no goals
    -- 🎉 no goals
    -- ⊢ ∀ (a b : Num), a * b = b * a
    transfer <;>
    -- ⊢ ↑a✝ + ↑b✝ = ↑b✝ + ↑a✝
    simp [add_comm, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm]
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
#align num.comm_semiring Num.commSemiring

instance orderedCancelAddCommMonoid : OrderedCancelAddCommMonoid Num :=
  { Num.commSemiring with
    lt := (· < ·)
    lt_iff_le_not_le := by
      intro a b
      -- ⊢ a < b ↔ a ≤ b ∧ ¬b ≤ a
      transfer_rw
      -- ⊢ ↑a < ↑b ↔ ↑a ≤ ↑b ∧ ¬↑b ≤ ↑a
      apply lt_iff_le_not_le
      -- 🎉 no goals
      -- 🎉 no goals
    le := (· ≤ ·)
    le_refl := by
      -- ⊢ a ≤ b → b ≤ c → a ≤ c
      transfer
      -- ⊢ ↑a ≤ ↑b → ↑b ≤ ↑c → ↑a ≤ ↑c
    le_trans := by
      -- 🎉 no goals
      intro a b c
      transfer_rw
      apply le_trans
    le_antisymm := by
      intro a b
      -- ⊢ a ≤ b → b ≤ a → a = b
      transfer_rw
      -- ⊢ ↑a ≤ ↑b → ↑b ≤ ↑a → ↑a = ↑b
      apply le_antisymm
      -- 🎉 no goals
    add_le_add_left := by
      intro a b h c
      -- ⊢ c + a ≤ c + b
      revert h
      -- ⊢ a ≤ b → c + a ≤ c + b
      transfer_rw
      -- ⊢ ↑a ≤ ↑b → ↑c + ↑a ≤ ↑c + ↑b
      exact fun h => add_le_add_left h c
      -- 🎉 no goals
    le_of_add_le_add_left := by
      intro a b c
      -- ⊢ a + b ≤ a + c → b ≤ c
      transfer_rw
      -- ⊢ ↑a + ↑b ≤ ↑a + ↑c → ↑b ≤ ↑c
      apply le_of_add_le_add_left }
      -- 🎉 no goals
#align num.ordered_cancel_add_comm_monoid Num.orderedCancelAddCommMonoid

instance linearOrderedSemiring : LinearOrderedSemiring Num :=
  { Num.commSemiring,
    Num.orderedCancelAddCommMonoid with
    le_total := by
      intro a b
      -- ⊢ a ≤ b ∨ b ≤ a
      transfer_rw
      -- ⊢ ↑a ≤ ↑b ∨ ↑b ≤ ↑a
                      -- 🎉 no goals
      apply le_total
      -- 🎉 no goals
      -- ⊢ a < b → 0 < c → c * a < c * b
    zero_le_one := by decide
      -- ⊢ ↑a < ↑b → 0 < ↑c → ↑c * ↑a < ↑c * ↑b
    mul_lt_mul_of_pos_left := by
      -- 🎉 no goals
      intro a b c
      transfer_rw
      -- ⊢ a < b → 0 < c → a * c < b * c
      apply mul_lt_mul_of_pos_left
      -- ⊢ ↑a < ↑b → 0 < ↑c → ↑a * ↑c < ↑b * ↑c
    mul_lt_mul_of_pos_right := by
      -- 🎉 no goals
                                -- 🎉 no goals
      intro a b c
      transfer_rw
      apply mul_lt_mul_of_pos_right
    decidableLT := Num.decidableLT
    decidableLE := Num.decidableLE
    -- This is relying on an automatically generated instance name,
    -- generated in a `deriving` handler.
    -- See https://github.com/leanprover/lean4/issues/2343
    decidableEq := instDecidableEqNum
    exists_pair_ne := ⟨0, 1, by decide⟩ }
#align num.linear_ordered_semiring Num.linearOrderedSemiring

@[norm_cast] -- @[simp] -- Porting note: simp can prove this
theorem add_of_nat (m n) : ((m + n : ℕ) : Num) = m + n :=
  add_ofNat' _ _
#align num.add_of_nat Num.add_of_nat

@[norm_cast]  -- @[simp] -- Porting note: simp can prove this
theorem to_nat_to_int (n : Num) : ((n : ℕ) : ℤ) = n :=
  cast_to_nat _
#align num.to_nat_to_int Num.to_nat_to_int

@[simp, norm_cast]
theorem cast_to_int {α} [AddGroupWithOne α] (n : Num) : ((n : ℤ) : α) = n := by
  rw [← to_nat_to_int, Int.cast_ofNat, cast_to_nat]
  -- 🎉 no goals
#align num.cast_to_int Num.cast_to_int

theorem to_of_nat : ∀ n : ℕ, ((n : Num) : ℕ) = n
  | 0 => by rw [Nat.cast_zero, cast_zero]
            -- 🎉 no goals
  | n + 1 => by rw [Nat.cast_succ, add_one, succ_to_nat, to_of_nat n]
                -- 🎉 no goals
#align num.to_of_nat Num.to_of_nat

@[simp, norm_cast]
theorem of_nat_cast {α} [AddMonoidWithOne α] (n : ℕ) : ((n : Num) : α) = n := by
  rw [← cast_to_nat, to_of_nat]
  -- 🎉 no goals
#align num.of_nat_cast Num.of_nat_cast

@[norm_cast] -- @[simp] -- Porting note: simp can prove this
theorem of_nat_inj {m n : ℕ} : (m : Num) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective to_of_nat h, congr_arg _⟩
#align num.of_nat_inj Num.of_nat_inj

-- Porting note: The priority should be `high`er than `cast_to_nat`.
@[simp high, norm_cast]
theorem of_to_nat : ∀ n : Num, ((n : ℕ) : Num) = n :=
  of_to_nat'
#align num.of_to_nat Num.of_to_nat

@[norm_cast]
theorem dvd_to_nat (m n : Num) : (m : ℕ) ∣ n ↔ m ∣ n :=
  ⟨fun ⟨k, e⟩ => ⟨k, by rw [← of_to_nat n, e]; simp⟩, fun ⟨k, e⟩ => ⟨k, by simp [e, mul_to_nat]⟩⟩
                        -- ⊢ ↑(↑m * k) = m * ↑k
                                               -- 🎉 no goals
                                                                           -- 🎉 no goals
#align num.dvd_to_nat Num.dvd_to_nat

end Num

namespace PosNum

variable {α : Type*}

open Num

-- Porting note: The priority should be `high`er than `cast_to_nat`.
@[simp high, norm_cast]
theorem of_to_nat : ∀ n : PosNum, ((n : ℕ) : Num) = Num.pos n :=
  of_to_nat'
#align pos_num.of_to_nat PosNum.of_to_nat

@[norm_cast]
theorem to_nat_inj {m n : PosNum} : (m : ℕ) = n ↔ m = n :=
  ⟨fun h => Num.pos.inj <| by rw [← PosNum.of_to_nat, ← PosNum.of_to_nat, h], congr_arg _⟩
                              -- 🎉 no goals
#align pos_num.to_nat_inj PosNum.to_nat_inj

theorem pred'_to_nat : ∀ n, (pred' n : ℕ) = Nat.pred n
  | 1 => rfl
  | bit0 n =>
    have : Nat.succ ↑(pred' n) = ↑n := by
      rw [pred'_to_nat n, Nat.succ_pred_eq_of_pos (to_nat_pos n)]
      -- 🎉 no goals
    match (motive :=
        ∀ k : Num, Nat.succ ↑k = ↑n → ↑(Num.casesOn k 1 bit1 : PosNum) = Nat.pred (_root_.bit0 n))
      pred' n, this with
    | 0, (h : ((1 : Num) : ℕ) = n) => by rw [← to_nat_inj.1 h]; rfl
                                         -- ⊢ ↑(Num.casesOn 0 1 bit1) = Nat.pred (_root_.bit0 ↑1)
                                                                -- 🎉 no goals
    | Num.pos p, (h : Nat.succ ↑p = n) => by rw [← h]; exact (Nat.succ_add p p).symm
                                             -- ⊢ ↑(Num.casesOn (pos p) 1 bit1) = Nat.pred (_root_.bit0 (Nat.succ ↑p))
                                                       -- 🎉 no goals
  | bit1 n => rfl
#align pos_num.pred'_to_nat PosNum.pred'_to_nat

@[simp]
theorem pred'_succ' (n) : pred' (succ' n) = n :=
  Num.to_nat_inj.1 <| by rw [pred'_to_nat, succ'_to_nat, Nat.add_one, Nat.pred_succ]
                         -- 🎉 no goals
#align pos_num.pred'_succ' PosNum.pred'_succ'

@[simp]
theorem succ'_pred' (n) : succ' (pred' n) = n :=
  to_nat_inj.1 <| by
    rw [succ'_to_nat, pred'_to_nat, Nat.add_one, Nat.succ_pred_eq_of_pos (to_nat_pos _)]
    -- 🎉 no goals
#align pos_num.succ'_pred' PosNum.succ'_pred'

instance dvd : Dvd PosNum :=
  ⟨fun m n => pos m ∣ pos n⟩
#align pos_num.has_dvd PosNum.dvd

@[norm_cast]
theorem dvd_to_nat {m n : PosNum} : (m : ℕ) ∣ n ↔ m ∣ n :=
  Num.dvd_to_nat (pos m) (pos n)
#align pos_num.dvd_to_nat PosNum.dvd_to_nat

theorem size_to_nat : ∀ n, (size n : ℕ) = Nat.size n
  | 1 => Nat.size_one.symm
  | bit0 n => by
    rw [size, succ_to_nat, size_to_nat n, cast_bit0, Nat.size_bit0 <| ne_of_gt <| to_nat_pos n]
    -- 🎉 no goals
  | bit1 n => by rw [size, succ_to_nat, size_to_nat n, cast_bit1, Nat.size_bit1]
                 -- 🎉 no goals
#align pos_num.size_to_nat PosNum.size_to_nat

theorem size_eq_natSize : ∀ n, (size n : ℕ) = natSize n
  | 1 => rfl
  | bit0 n => by rw [size, succ_to_nat, natSize, size_eq_natSize n]
                 -- 🎉 no goals
  | bit1 n => by rw [size, succ_to_nat, natSize, size_eq_natSize n]
                 -- 🎉 no goals
#align pos_num.size_eq_nat_size PosNum.size_eq_natSize

theorem natSize_to_nat (n) : natSize n = Nat.size n := by rw [← size_eq_natSize, size_to_nat]
                                                          -- 🎉 no goals
#align pos_num.nat_size_to_nat PosNum.natSize_to_nat

theorem natSize_pos (n) : 0 < natSize n := by cases n <;> apply Nat.succ_pos
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
#align pos_num.nat_size_pos PosNum.natSize_pos

/-- This tactic tries to turn an (in)equality about `PosNum`s to one about `Nat`s by rewriting.
```lean
example (n : PosNum) (m : PosNum) : n ≤ n + m := by
  transfer_rw
  exact Nat.le_add_right _ _
```
-/
scoped macro (name := transfer_rw) "transfer_rw" : tactic => `(tactic|
    (repeat first | rw [← to_nat_inj] | rw [← lt_to_nat] | rw [← le_to_nat]
     repeat first | rw [add_to_nat] | rw [mul_to_nat] | rw [cast_one] | rw [cast_zero]))

/--
This tactic tries to prove (in)equalities about `PosNum`s by transferring them to the `Nat` world
and then trying to call `simp`.
```lean
example (n : PosNum) (m : PosNum) : n ≤ n + m := by transfer
```
-/
scoped macro (name := transfer) "transfer" : tactic => `(tactic|
    (intros; transfer_rw; try simp [add_comm, add_left_comm, mul_comm, mul_left_comm]))

instance addCommSemigroup : AddCommSemigroup PosNum := by
  refine' { add := (· + ·).. } <;> transfer
  -- ⊢ ∀ (a b c : PosNum), a + b + c = a + (b + c)
                                   -- 🎉 no goals
                                   -- 🎉 no goals
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align pos_num.add_comm_semigroup PosNum.addCommSemigroup

instance commMonoid : CommMonoid PosNum := by
  refine'
    { mul := (· * ·)
      one := (1 : PosNum)
      npow := @npowRec PosNum ⟨1⟩ ⟨(· * ·)⟩,.. } <;>
  try { intros; rfl } <;>
  -- ⊢ ∀ (a b c : PosNum), a * b * c = a * (b * c)
  -- ⊢ ∀ (a : PosNum), 1 * a = a
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- ⊢ ∀ (a b : PosNum), a * b = b * a
  transfer
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
#align pos_num.comm_monoid PosNum.commMonoid

instance distrib : Distrib PosNum := by
  refine'
    { add := (· + ·)
      mul := (· * ·).. } <;>
  (transfer
   -- ⊢ ↑a✝ * (↑b✝ + ↑c✝) = ↑a✝ * ↑b✝ + ↑a✝ * ↑c✝
   -- ⊢ ↑a✝ * (↑b✝ + ↑c✝) = ↑a✝ * ↑b✝ + ↑a✝ * ↑c✝
   -- ⊢ ↑c✝ * (↑a✝ + ↑b✝) = ↑a✝ * ↑c✝ + ↑b✝ * ↑c✝
   -- 🎉 no goals
   -- ⊢ ↑c✝ * (↑a✝ + ↑b✝) = ↑a✝ * ↑c✝ + ↑b✝ * ↑c✝
   simp [mul_add, mul_comm])
   -- 🎉 no goals
#align pos_num.distrib PosNum.distrib

instance linearOrder : LinearOrder PosNum where
  lt := (· < ·)
  lt_iff_le_not_le := by
    intro a b
    -- ⊢ a < b ↔ a ≤ b ∧ ¬b ≤ a
    transfer_rw
    -- ⊢ ↑a < ↑b ↔ ↑a ≤ ↑b ∧ ¬↑b ≤ ↑a
    -- ⊢ ↑a < ↑b ↔ ↑a ≤ ↑b ∧ ¬↑b ≤ ↑a
                -- 🎉 no goals
                -- 🎉 no goals
    apply lt_iff_le_not_le
    -- 🎉 no goals
    -- ⊢ a ≤ b → b ≤ c → a ≤ c
  le := (· ≤ ·)
    -- ⊢ ↑a ≤ ↑b → ↑b ≤ ↑c → ↑a ≤ ↑c
    -- ⊢ ↑a ≤ ↑b → ↑b ≤ ↑c → ↑a ≤ ↑c
  le_refl := by transfer
    -- 🎉 no goals
  le_trans := by
    intro a b c
    transfer_rw
    apply le_trans
  le_antisymm := by
    intro a b
    -- ⊢ a ≤ b → b ≤ a → a = b
    transfer_rw
    -- ⊢ ↑a ≤ ↑b → ↑b ≤ ↑a → ↑a = ↑b
    -- ⊢ ↑a ≤ ↑b → ↑b ≤ ↑a → ↑a = ↑b
    apply le_antisymm
    -- 🎉 no goals
  le_total := by
    intro a b
    -- ⊢ a ≤ b ∨ b ≤ a
    transfer_rw
    -- ⊢ ↑a ≤ ↑b ∨ ↑b ≤ ↑a
    -- ⊢ ↑a ≤ ↑b ∨ ↑b ≤ ↑a
    apply le_total
    -- 🎉 no goals
  decidableLT := by infer_instance
                    -- 🎉 no goals
                    -- 🎉 no goals
  decidableLE := by infer_instance
                    -- 🎉 no goals
  decidableEq := by infer_instance
#align pos_num.linear_order PosNum.linearOrder

@[simp]
theorem cast_to_num (n : PosNum) : ↑n = Num.pos n := by rw [← cast_to_nat, ← of_to_nat n]
                                                        -- 🎉 no goals
#align pos_num.cast_to_num PosNum.cast_to_num

@[simp, norm_cast]
theorem bit_to_nat (b n) : (bit b n : ℕ) = Nat.bit b n := by cases b <;> rfl
                                                             -- ⊢ ↑(bit false n) = Nat.bit false ↑n
                                                                         -- 🎉 no goals
                                                                         -- 🎉 no goals
#align pos_num.bit_to_nat PosNum.bit_to_nat

@[simp, norm_cast]
theorem cast_add [AddMonoidWithOne α] (m n) : ((m + n : PosNum) : α) = m + n := by
  rw [← cast_to_nat, add_to_nat, Nat.cast_add, cast_to_nat, cast_to_nat]
  -- 🎉 no goals
#align pos_num.cast_add PosNum.cast_add

@[simp 500, norm_cast]
theorem cast_succ [AddMonoidWithOne α] (n : PosNum) : (succ n : α) = n + 1 := by
  rw [← add_one, cast_add, cast_one]
  -- 🎉 no goals
#align pos_num.cast_succ PosNum.cast_succ

@[simp, norm_cast]
theorem cast_inj [AddMonoidWithOne α] [CharZero α] {m n : PosNum} : (m : α) = n ↔ m = n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_inj, to_nat_inj]
  -- 🎉 no goals
#align pos_num.cast_inj PosNum.cast_inj

@[simp]
theorem one_le_cast [LinearOrderedSemiring α] (n : PosNum) : (1 : α) ≤ n := by
  rw [← cast_to_nat, ← Nat.cast_one, Nat.cast_le (α := α)]; apply to_nat_pos
  -- ⊢ 1 ≤ ↑n
                                                            -- 🎉 no goals
#align pos_num.one_le_cast PosNum.one_le_cast

@[simp]
theorem cast_pos [LinearOrderedSemiring α] (n : PosNum) : 0 < (n : α) :=
  lt_of_lt_of_le zero_lt_one (one_le_cast n)
#align pos_num.cast_pos PosNum.cast_pos

@[simp, norm_cast]
theorem cast_mul [Semiring α] (m n) : ((m * n : PosNum) : α) = m * n := by
  rw [← cast_to_nat, mul_to_nat, Nat.cast_mul, cast_to_nat, cast_to_nat]
  -- 🎉 no goals
#align pos_num.cast_mul PosNum.cast_mul

@[simp]
theorem cmp_eq (m n) : cmp m n = Ordering.eq ↔ m = n := by
  have := cmp_to_nat m n
  -- ⊢ cmp m n = Ordering.eq ↔ m = n
  -- Porting note: `cases` didn't rewrite at `this`, so `revert` & `intro` are required.
  revert this; cases cmp m n <;> intro this <;> simp at this ⊢ <;> try { exact this } <;>
  -- ⊢ Ordering.casesOn (cmp m n) (↑m < ↑n) (m = n) (↑n < ↑m) → (cmp m n = Ordering …
                                 -- ⊢ Ordering.lt = Ordering.eq ↔ m = n
                                 -- ⊢ Ordering.eq = Ordering.eq ↔ m = n
                                 -- ⊢ Ordering.gt = Ordering.eq ↔ m = n
                                                -- ⊢ ¬m = n
                                                -- ⊢ m = n
                                                -- ⊢ ¬m = n
                                                                   -- ⊢ ¬m = n
                                                                   -- 🎉 no goals
                                                                   -- ⊢ ¬m = n
    simp [show m ≠ n from fun e => by rw [e] at this;exact lt_irrefl _ this]
    -- 🎉 no goals
    -- 🎉 no goals
#align pos_num.cmp_eq PosNum.cmp_eq

@[simp, norm_cast]
theorem cast_lt [LinearOrderedSemiring α] {m n : PosNum} : (m : α) < n ↔ m < n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_lt (α := α), lt_to_nat]
  -- 🎉 no goals
#align pos_num.cast_lt PosNum.cast_lt

@[simp, norm_cast]
theorem cast_le [LinearOrderedSemiring α] {m n : PosNum} : (m : α) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr cast_lt
  -- ⊢ ¬↑n < ↑m ↔ m ≤ n
                 -- 🎉 no goals
#align pos_num.cast_le PosNum.cast_le

end PosNum

namespace Num

variable {α : Type*}

open PosNum

theorem bit_to_nat (b n) : (bit b n : ℕ) = Nat.bit b n := by cases b <;> cases n <;> rfl
                                                             -- ⊢ ↑(bit false n) = Nat.bit false ↑n
                                                                         -- ⊢ ↑(bit false zero) = Nat.bit false ↑zero
                                                                         -- ⊢ ↑(bit true zero) = Nat.bit true ↑zero
                                                                                     -- 🎉 no goals
                                                                                     -- 🎉 no goals
                                                                                     -- 🎉 no goals
                                                                                     -- 🎉 no goals
#align num.bit_to_nat Num.bit_to_nat

theorem cast_succ' [AddMonoidWithOne α] (n) : (succ' n : α) = n + 1 := by
  rw [← PosNum.cast_to_nat, succ'_to_nat, Nat.cast_add_one, cast_to_nat]
  -- 🎉 no goals
#align num.cast_succ' Num.cast_succ'

theorem cast_succ [AddMonoidWithOne α] (n) : (succ n : α) = n + 1 :=
  cast_succ' n
#align num.cast_succ Num.cast_succ

@[simp, norm_cast]
theorem cast_add [Semiring α] (m n) : ((m + n : Num) : α) = m + n := by
  rw [← cast_to_nat, add_to_nat, Nat.cast_add, cast_to_nat, cast_to_nat]
  -- 🎉 no goals
#align num.cast_add Num.cast_add

@[simp, norm_cast]
theorem cast_bit0 [Semiring α] (n : Num) : (n.bit0 : α) = _root_.bit0 (n : α) := by
  rw [← bit0_of_bit0, _root_.bit0, cast_add]; rfl
  -- ⊢ ↑n + ↑n = _root_.bit0 ↑n
                                              -- 🎉 no goals
#align num.cast_bit0 Num.cast_bit0

@[simp, norm_cast]
theorem cast_bit1 [Semiring α] (n : Num) : (n.bit1 : α) = _root_.bit1 (n : α) := by
  rw [← bit1_of_bit1, _root_.bit1, bit0_of_bit0, cast_add, cast_bit0]; rfl
  -- ⊢ _root_.bit0 ↑n + ↑1 = _root_.bit1 ↑n
                                                                       -- 🎉 no goals
#align num.cast_bit1 Num.cast_bit1

@[simp, norm_cast]
theorem cast_mul [Semiring α] : ∀ m n, ((m * n : Num) : α) = m * n
  | 0, 0 => (zero_mul _).symm
  | 0, pos _q => (zero_mul _).symm
  | pos _p, 0 => (mul_zero _).symm
  | pos _p, pos _q => PosNum.cast_mul _ _
#align num.cast_mul Num.cast_mul

theorem size_to_nat : ∀ n, (size n : ℕ) = Nat.size n
  | 0 => Nat.size_zero.symm
  | pos p => p.size_to_nat
#align num.size_to_nat Num.size_to_nat

theorem size_eq_natSize : ∀ n, (size n : ℕ) = natSize n
  | 0 => rfl
  | pos p => p.size_eq_natSize
#align num.size_eq_nat_size Num.size_eq_natSize

theorem natSize_to_nat (n) : natSize n = Nat.size n := by rw [← size_eq_natSize, size_to_nat]
                                                          -- 🎉 no goals
#align num.nat_size_to_nat Num.natSize_to_nat

@[simp 999]
theorem ofNat'_eq : ∀ n, Num.ofNat' n = n :=
  Nat.binaryRec (by simp) fun b n IH => by
                    -- 🎉 no goals
    rw [ofNat'] at IH ⊢
    -- ⊢ Nat.binaryRec 0 (fun b x => bif b then Num.bit1 else Num.bit0) (Nat.bit b n) …
    rw [Nat.binaryRec_eq, IH]
    -- ⊢ cond b Num.bit1 Num.bit0 ↑n = ↑(Nat.bit b n)
    -- Porting note: `Nat.cast_bit0` & `Nat.cast_bit1` are not `simp` theorems anymore.
    · cases b <;> simp [Nat.bit, bit0_of_bit0, bit1_of_bit1, Nat.cast_bit0, Nat.cast_bit1]
      -- ⊢ cond false Num.bit1 Num.bit0 ↑n = ↑(Nat.bit false n)
                  -- 🎉 no goals
                  -- 🎉 no goals
    · rfl
      -- 🎉 no goals
#align num.of_nat'_eq Num.ofNat'_eq

theorem zneg_toZNum (n : Num) : -n.toZNum = n.toZNumNeg := by cases n <;> rfl
                                                              -- ⊢ -toZNum zero = toZNumNeg zero
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
#align num.zneg_to_znum Num.zneg_toZNum

theorem zneg_toZNumNeg (n : Num) : -n.toZNumNeg = n.toZNum := by cases n <;> rfl
                                                                 -- ⊢ -toZNumNeg zero = toZNum zero
                                                                             -- 🎉 no goals
                                                                             -- 🎉 no goals
#align num.zneg_to_znum_neg Num.zneg_toZNumNeg

theorem toZNum_inj {m n : Num} : m.toZNum = n.toZNum ↔ m = n :=
  ⟨fun h => by cases m <;> cases n <;> cases h <;> rfl, congr_arg _⟩
               -- ⊢ zero = n
                           -- ⊢ zero = zero
                           -- ⊢ pos a✝ = zero
                                       -- ⊢ zero = zero
                                       -- 🎉 no goals
                                       -- 🎉 no goals
                                       -- ⊢ pos a✝ = pos a✝
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
#align num.to_znum_inj Num.toZNum_inj


@[simp]
theorem cast_toZNum [Zero α] [One α] [Add α] [Neg α] : ∀ n : Num, (n.toZNum : α) = n
  | 0 => rfl
  | Num.pos _p => rfl
#align num.cast_to_znum Num.cast_toZNum

@[simp]
theorem cast_toZNumNeg [AddGroup α] [One α] : ∀ n : Num, (n.toZNumNeg : α) = -n
  | 0 => neg_zero.symm
  | Num.pos _p => rfl
#align num.cast_to_znum_neg Num.cast_toZNumNeg

@[simp]
theorem add_toZNum (m n : Num) : Num.toZNum (m + n) = m.toZNum + n.toZNum := by
  cases m <;> cases n <;> rfl
  -- ⊢ toZNum (zero + n) = toZNum zero + toZNum n
              -- ⊢ toZNum (zero + zero) = toZNum zero + toZNum zero
              -- ⊢ toZNum (pos a✝ + zero) = toZNum (pos a✝) + toZNum zero
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
#align num.add_to_znum Num.add_toZNum

end Num

namespace PosNum

open Num

theorem pred_to_nat {n : PosNum} (h : 1 < n) : (pred n : ℕ) = Nat.pred n := by
  unfold pred
  -- ⊢ ↑(Num.casesOn (pred' n) 1 id) = Nat.pred ↑n
  cases e : pred' n
  -- ⊢ ↑(Num.casesOn zero 1 id) = Nat.pred ↑n
  · have : (1 : ℕ) ≤ Nat.pred n := Nat.pred_le_pred ((@cast_lt ℕ _ _ _).2 h)
    -- ⊢ ↑(Num.casesOn zero 1 id) = Nat.pred ↑n
    rw [← pred'_to_nat, e] at this
    -- ⊢ ↑(Num.casesOn zero 1 id) = Nat.pred ↑n
    exact absurd this (by decide)
    -- 🎉 no goals
  · rw [← pred'_to_nat, e]
    -- ⊢ ↑(Num.casesOn (pos a✝) 1 id) = ↑(pos a✝)
    rfl
    -- 🎉 no goals
#align pos_num.pred_to_nat PosNum.pred_to_nat

theorem sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum := by cases a <;> rfl
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
#align pos_num.sub'_one PosNum.sub'_one

theorem one_sub' (a : PosNum) : sub' 1 a = (pred' a).toZNumNeg := by cases a <;> rfl
                                                                                 -- 🎉 no goals
                                                                                 -- 🎉 no goals
                                                                                 -- 🎉 no goals
#align pos_num.one_sub' PosNum.one_sub'

theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt :=
  Iff.rfl
#align pos_num.lt_iff_cmp PosNum.lt_iff_cmp

theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ Ordering.gt :=
  not_congr <| lt_iff_cmp.trans <| by rw [← cmp_swap]; cases cmp m n <;> exact by decide
                                      -- ⊢ Ordering.swap (cmp m n) = Ordering.lt ↔ cmp m n = Ordering.gt
                                                                         -- 🎉 no goals
                                                                         -- 🎉 no goals
                                                                         -- 🎉 no goals
#align pos_num.le_iff_cmp PosNum.le_iff_cmp

end PosNum

namespace Num

variable {α : Type*}

open PosNum

theorem pred_to_nat : ∀ n : Num, (pred n : ℕ) = Nat.pred n
  | 0 => rfl
  | pos p => by rw [pred, PosNum.pred'_to_nat]; rfl
                -- ⊢ Nat.pred ↑p = Nat.pred ↑(pos p)
                                                -- 🎉 no goals
#align num.pred_to_nat Num.pred_to_nat

theorem ppred_to_nat : ∀ n : Num, (↑) <$> ppred n = Nat.ppred n
  | 0 => rfl
  | pos p => by
    rw [ppred, Option.map_some, Nat.ppred_eq_some.2]
    -- ⊢ Nat.succ ↑(pred' p) = ↑(pos p)
    rw [PosNum.pred'_to_nat, Nat.succ_pred_eq_of_pos (PosNum.to_nat_pos _)]
    -- ⊢ ↑p = ↑(pos p)
    rfl
    -- 🎉 no goals
#align num.ppred_to_nat Num.ppred_to_nat

theorem cmp_swap (m n) : (cmp m n).swap = cmp n m := by
  cases m <;> cases n <;> try { unfold cmp } <;> try { rfl }; apply PosNum.cmp_swap
  -- ⊢ Ordering.swap (cmp zero n) = cmp n zero
              -- ⊢ Ordering.swap (cmp zero zero) = cmp zero zero
              -- ⊢ Ordering.swap (cmp (pos a✝) zero) = cmp zero (pos a✝)
                          -- ⊢ Ordering.swap (cmp zero zero) = cmp zero zero
                          -- ⊢ Ordering.swap (cmp zero (pos a✝)) = cmp (pos a✝) zero
                          -- ⊢ Ordering.swap (cmp (pos a✝) zero) = cmp zero (pos a✝)
                          -- ⊢ Ordering.swap (cmp (pos a✝¹) (pos a✝)) = cmp (pos a✝) (pos a✝¹)
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- ⊢ Ordering.swap (cmp (pos a✝¹) (pos a✝)) = cmp (pos a✝) (pos a✝¹)
                                                              -- 🎉 no goals
#align num.cmp_swap Num.cmp_swap

theorem cmp_eq (m n) : cmp m n = Ordering.eq ↔ m = n := by
  have := cmp_to_nat m n
  -- ⊢ cmp m n = Ordering.eq ↔ m = n
  -- Porting note: `cases` didn't rewrite at `this`, so `revert` & `intro` are required.
  revert this; cases cmp m n <;> intro this <;> simp at this ⊢ <;> try { exact this } <;>
  -- ⊢ Ordering.casesOn (cmp m n) (↑m < ↑n) (m = n) (↑n < ↑m) → (cmp m n = Ordering …
                                 -- ⊢ Ordering.lt = Ordering.eq ↔ m = n
                                 -- ⊢ Ordering.eq = Ordering.eq ↔ m = n
                                 -- ⊢ Ordering.gt = Ordering.eq ↔ m = n
                                                -- ⊢ ¬m = n
                                                -- ⊢ m = n
                                                -- ⊢ ¬m = n
                                                                   -- ⊢ ¬m = n
                                                                   -- 🎉 no goals
                                                                   -- ⊢ ¬m = n
    simp [show m ≠ n from fun e => by rw [e] at this; exact lt_irrefl _ this]
    -- 🎉 no goals
    -- 🎉 no goals
#align num.cmp_eq Num.cmp_eq

@[simp, norm_cast]
theorem cast_lt [LinearOrderedSemiring α] {m n : Num} : (m : α) < n ↔ m < n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_lt (α := α), lt_to_nat]
  -- 🎉 no goals
#align num.cast_lt Num.cast_lt

@[simp, norm_cast]
theorem cast_le [LinearOrderedSemiring α] {m n : Num} : (m : α) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr cast_lt
  -- ⊢ ¬↑n < ↑m ↔ m ≤ n
                 -- 🎉 no goals
#align num.cast_le Num.cast_le

@[simp, norm_cast]
theorem cast_inj [LinearOrderedSemiring α] {m n : Num} : (m : α) = n ↔ m = n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_inj, to_nat_inj]
  -- 🎉 no goals
#align num.cast_inj Num.cast_inj

theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt :=
  Iff.rfl
#align num.lt_iff_cmp Num.lt_iff_cmp

theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ Ordering.gt :=
  not_congr <| lt_iff_cmp.trans <| by rw [← cmp_swap]; cases cmp m n <;> exact by decide
                                      -- ⊢ Ordering.swap (cmp m n) = Ordering.lt ↔ cmp m n = Ordering.gt
                                                                         -- 🎉 no goals
                                                                         -- 🎉 no goals
                                                                         -- 🎉 no goals
#align num.le_iff_cmp Num.le_iff_cmp

theorem bitwise'_to_nat {f : Num → Num → Num} {g : Bool → Bool → Bool} (p : PosNum → PosNum → Num)
    (gff : g false false = false) (f00 : f 0 0 = 0)
    (f0n : ∀ n, f 0 (pos n) = cond (g false true) (pos n) 0)
    (fn0 : ∀ n, f (pos n) 0 = cond (g true false) (pos n) 0)
    (fnn : ∀ m n, f (pos m) (pos n) = p m n) (p11 : p 1 1 = cond (g true true) 1 0)
    (p1b : ∀ b n, p 1 (PosNum.bit b n) = bit (g true b) (cond (g false true) (pos n) 0))
    (pb1 : ∀ a m, p (PosNum.bit a m) 1 = bit (g a true) (cond (g true false) (pos m) 0))
    (pbb : ∀ a b m n, p (PosNum.bit a m) (PosNum.bit b n) = bit (g a b) (p m n)) :
    ∀ m n : Num, (f m n : ℕ) = Nat.bitwise' g m n := by
  -- Porting note: `change .. with ..` is now `simp only [show .. = .. from rfl]`.
  intros m n
  -- ⊢ ↑(f m n) = Nat.bitwise' g ↑m ↑n
  cases' m with m <;> cases' n with n <;>
  -- ⊢ ↑(f zero n) = Nat.bitwise' g ↑zero ↑n
                      -- ⊢ ↑(f zero zero) = Nat.bitwise' g ↑zero ↑zero
                      -- ⊢ ↑(f (pos m) zero) = Nat.bitwise' g ↑(pos m) ↑zero
      try simp only [show zero = 0 from rfl, show ((0 : Num) : ℕ) = 0 from rfl]
      -- ⊢ ↑(f 0 0) = Nat.bitwise' g 0 0
      -- ⊢ ↑(f 0 (pos n)) = Nat.bitwise' g 0 ↑(pos n)
      -- ⊢ ↑(f (pos m) 0) = Nat.bitwise' g (↑(pos m)) 0
      -- ⊢ ↑(f (pos m) (pos n)) = Nat.bitwise' g ↑(pos m) ↑(pos n)
  · rw [f00, Nat.bitwise'_zero]; rfl
    -- ⊢ ↑0 = 0
                                 -- 🎉 no goals
  · unfold Nat.bitwise'
    -- ⊢ ↑(f 0 (pos n)) = Nat.binaryRec (fun n => bif g false true then n else 0) (fu …
    rw [f0n, Nat.binaryRec_zero]
    -- ⊢ ↑(bif g false true then pos n else 0) = bif g false true then ↑(pos n) else 0
    cases g false true <;> rfl
    -- ⊢ ↑(bif false then pos n else 0) = bif false then ↑(pos n) else 0
                           -- 🎉 no goals
                           -- 🎉 no goals
  · unfold Nat.bitwise'
    -- ⊢ ↑(f (pos m) 0) = Nat.binaryRec (fun n => bif g false true then n else 0) (fu …
    generalize h : (pos m : ℕ) = m'
    -- ⊢ ↑(f (pos m) 0) = Nat.binaryRec (fun n => bif g false true then n else 0) (fu …
    revert h
    -- ⊢ ↑(pos m) = m' → ↑(f (pos m) 0) = Nat.binaryRec (fun n => bif g false true th …
    apply Nat.bitCasesOn m' _
    -- ⊢ ∀ (b : Bool) (n : ℕ), ↑(pos m) = Nat.bit b n → ↑(f (pos m) 0) = Nat.binaryRe …
    intro b m' h
    -- ⊢ ↑(f (pos m) 0) = Nat.binaryRec (fun n => bif g false true then n else 0) (fu …
    rw [fn0, Nat.binaryRec_eq, Nat.binaryRec_zero, ← h]
    -- ⊢ ↑(bif g true false then pos m else 0) = bif g true false then ↑(pos m) else 0
    cases g true false <;> rfl
    -- ⊢ ↑(bif false then pos m else 0) = bif false then ↑(pos m) else 0
                           -- 🎉 no goals
                           -- 🎉 no goals
    apply Nat.bitwise'_bit_aux gff
    -- 🎉 no goals
  · rw [fnn]
    -- ⊢ ↑(p m n) = Nat.bitwise' g ↑(pos m) ↑(pos n)
    have : ∀ (b) (n : PosNum), (cond b (↑n) 0 : ℕ) = ↑(cond b (pos n) 0 : Num) := by
      intros b _; cases b <;> rfl
    induction' m with m IH m IH generalizing n <;> cases' n with n n
    any_goals simp only [show one = 1 from rfl, show pos 1 = 1 from rfl,
      show PosNum.bit0 = PosNum.bit false from rfl, show PosNum.bit1 = PosNum.bit true from rfl,
      show ((1 : Num) : ℕ) = Nat.bit true 0 from rfl]
    all_goals
      repeat'
        rw [show ∀ b n, (pos (PosNum.bit b n) : ℕ) = Nat.bit b ↑n by
          intros b _; cases b <;> rfl]
      rw [Nat.bitwise'_bit]
    any_goals assumption
    any_goals rw [Nat.bitwise'_zero, p11]; cases g true true <;> rfl
    any_goals rw [Nat.bitwise'_zero_left, this, ← bit_to_nat, p1b]
    any_goals rw [Nat.bitwise'_zero_right _ gff, this, ← bit_to_nat, pb1]
    all_goals
      rw [← show ∀ n : PosNum, ↑(p m n) = Nat.bitwise' g ↑m ↑n from IH]
      rw [← bit_to_nat, pbb]
#align num.bitwise_to_nat Num.bitwise'_to_nat

@[simp, norm_cast]
theorem lor'_to_nat : ∀ m n, (lor m n : ℕ) = Nat.lor' m n := by
  -- Porting note: A name of an implicit local hypothesis is not available so
  --               `cases_type*` is used.
  apply bitwise'_to_nat fun x y => pos (PosNum.lor x y) <;>
   intros <;> (try cases_type* Bool) <;> rfl
   -- ⊢ (false || false) = false
   -- ⊢ lor 0 0 = 0
   -- ⊢ lor 0 (pos n✝) = bif false || true then pos n✝ else 0
   -- ⊢ lor (pos n✝) 0 = bif true || false then pos n✝ else 0
   -- ⊢ lor (pos m✝) (pos n✝) = pos (PosNum.lor m✝ n✝)
   -- ⊢ pos (PosNum.lor 1 1) = bif true || true then 1 else 0
   -- ⊢ pos (PosNum.lor 1 (PosNum.bit b✝ n✝)) = bit (true || b✝) (bif false || true  …
   -- ⊢ pos (PosNum.lor (PosNum.bit a✝ m✝) 1) = bit (a✝ || true) (bif true || false  …
   -- ⊢ pos (PosNum.lor (PosNum.bit a✝ m✝) (PosNum.bit b✝ n✝)) = bit (a✝ || b✝) (pos …
               -- ⊢ (false || false) = false
               -- ⊢ lor 0 0 = 0
               -- ⊢ lor 0 (pos n✝) = bif false || true then pos n✝ else 0
               -- ⊢ lor (pos n✝) 0 = bif true || false then pos n✝ else 0
               -- ⊢ lor (pos m✝) (pos n✝) = pos (PosNum.lor m✝ n✝)
               -- ⊢ pos (PosNum.lor 1 1) = bif true || true then 1 else 0
               -- ⊢ pos (PosNum.lor 1 (PosNum.bit false n✝)) = bit (true || false) (bif false || …
               -- ⊢ pos (PosNum.lor (PosNum.bit false m✝) 1) = bit (false || true) (bif true ||  …
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
#align num.lor_to_nat Num.lor'_to_nat

@[simp, norm_cast]
theorem land'_to_nat : ∀ m n, (land m n : ℕ) = Nat.land' m n := by
  apply bitwise'_to_nat PosNum.land <;> intros <;> (try cases_type* Bool) <;> rfl
                                        -- ⊢ (false && false) = false
                                        -- ⊢ land 0 0 = 0
                                        -- ⊢ land 0 (pos n✝) = bif false && true then pos n✝ else 0
                                        -- ⊢ land (pos n✝) 0 = bif true && false then pos n✝ else 0
                                        -- ⊢ land (pos m✝) (pos n✝) = PosNum.land m✝ n✝
                                        -- ⊢ PosNum.land 1 1 = bif true && true then 1 else 0
                                        -- ⊢ PosNum.land 1 (PosNum.bit b✝ n✝) = bit (true && b✝) (bif false && true then  …
                                        -- ⊢ PosNum.land (PosNum.bit a✝ m✝) 1 = bit (a✝ && true) (bif true && false then  …
                                        -- ⊢ PosNum.land (PosNum.bit a✝ m✝) (PosNum.bit b✝ n✝) = bit (a✝ && b✝) (PosNum.l …
                                                    -- ⊢ (false && false) = false
                                                    -- ⊢ land 0 0 = 0
                                                    -- ⊢ land 0 (pos n✝) = bif false && true then pos n✝ else 0
                                                    -- ⊢ land (pos n✝) 0 = bif true && false then pos n✝ else 0
                                                    -- ⊢ land (pos m✝) (pos n✝) = PosNum.land m✝ n✝
                                                    -- ⊢ PosNum.land 1 1 = bif true && true then 1 else 0
                                                    -- ⊢ PosNum.land 1 (PosNum.bit false n✝) = bit (true && false) (bif false && true …
                                                    -- ⊢ PosNum.land (PosNum.bit false m✝) 1 = bit (false && true) (bif true && false …
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
#align num.land_to_nat Num.land'_to_nat

@[simp, norm_cast]
theorem ldiff'_to_nat : ∀ m n, (ldiff m n : ℕ) = Nat.ldiff' m n := by
  apply bitwise'_to_nat PosNum.ldiff <;> intros <;> (try cases_type* Bool) <;> rfl
                                         -- ⊢ (false && !false) = false
                                         -- ⊢ ldiff 0 0 = 0
                                         -- ⊢ ldiff 0 (pos n✝) = bif false && !true then pos n✝ else 0
                                         -- ⊢ ldiff (pos n✝) 0 = bif true && !false then pos n✝ else 0
                                         -- ⊢ ldiff (pos m✝) (pos n✝) = PosNum.ldiff m✝ n✝
                                         -- ⊢ PosNum.ldiff 1 1 = bif true && !true then 1 else 0
                                         -- ⊢ PosNum.ldiff 1 (PosNum.bit b✝ n✝) = bit (true && !b✝) (bif false && !true th …
                                         -- ⊢ PosNum.ldiff (PosNum.bit a✝ m✝) 1 = bit (a✝ && !true) (bif true && !false th …
                                         -- ⊢ PosNum.ldiff (PosNum.bit a✝ m✝) (PosNum.bit b✝ n✝) = bit (a✝ && !b✝) (PosNum …
                                                     -- ⊢ (false && !false) = false
                                                     -- ⊢ ldiff 0 0 = 0
                                                     -- ⊢ ldiff 0 (pos n✝) = bif false && !true then pos n✝ else 0
                                                     -- ⊢ ldiff (pos n✝) 0 = bif true && !false then pos n✝ else 0
                                                     -- ⊢ ldiff (pos m✝) (pos n✝) = PosNum.ldiff m✝ n✝
                                                     -- ⊢ PosNum.ldiff 1 1 = bif true && !true then 1 else 0
                                                     -- ⊢ PosNum.ldiff 1 (PosNum.bit false n✝) = bit (true && !false) (bif false && !t …
                                                     -- ⊢ PosNum.ldiff (PosNum.bit false m✝) 1 = bit (false && !true) (bif true && !fa …
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
#align num.ldiff_to_nat Num.ldiff'_to_nat

@[simp, norm_cast]
theorem lxor'_to_nat : ∀ m n, (lxor m n : ℕ) = Nat.lxor' m n := by
  apply bitwise'_to_nat PosNum.lxor <;> intros <;> (try cases_type* Bool) <;> rfl
                                        -- ⊢ xor false false = false
                                        -- ⊢ lxor 0 0 = 0
                                        -- ⊢ lxor 0 (pos n✝) = bif xor false true then pos n✝ else 0
                                        -- ⊢ lxor (pos n✝) 0 = bif xor true false then pos n✝ else 0
                                        -- ⊢ lxor (pos m✝) (pos n✝) = PosNum.lxor m✝ n✝
                                        -- ⊢ PosNum.lxor 1 1 = bif xor true true then 1 else 0
                                        -- ⊢ PosNum.lxor 1 (PosNum.bit b✝ n✝) = bit (xor true b✝) (bif xor false true the …
                                        -- ⊢ PosNum.lxor (PosNum.bit a✝ m✝) 1 = bit (xor a✝ true) (bif xor true false the …
                                        -- ⊢ PosNum.lxor (PosNum.bit a✝ m✝) (PosNum.bit b✝ n✝) = bit (xor a✝ b✝) (PosNum. …
                                                    -- ⊢ xor false false = false
                                                    -- ⊢ lxor 0 0 = 0
                                                    -- ⊢ lxor 0 (pos n✝) = bif xor false true then pos n✝ else 0
                                                    -- ⊢ lxor (pos n✝) 0 = bif xor true false then pos n✝ else 0
                                                    -- ⊢ lxor (pos m✝) (pos n✝) = PosNum.lxor m✝ n✝
                                                    -- ⊢ PosNum.lxor 1 1 = bif xor true true then 1 else 0
                                                    -- ⊢ PosNum.lxor 1 (PosNum.bit false n✝) = bit (xor true false) (bif xor false tr …
                                                    -- ⊢ PosNum.lxor (PosNum.bit false m✝) 1 = bit (xor false true) (bif xor true fal …
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
#align num.lxor_to_nat Num.lxor'_to_nat

@[simp, norm_cast]
theorem shiftl_to_nat (m n) : (shiftl m n : ℕ) = (m : ℕ) <<< (n : ℕ) := by
  cases m <;> dsimp only [shiftl]
  -- ⊢ ↑(shiftl zero n) = ↑zero <<< n
              -- ⊢ ↑0 = ↑zero <<< n
              -- ⊢ ↑(pos (PosNum.shiftl a✝ n)) = ↑(pos a✝) <<< n
  · symm
    -- ⊢ ↑zero <<< n = ↑0
    apply Nat.zero_shiftLeft
    -- 🎉 no goals
  simp only [cast_pos]
  -- ⊢ ↑(PosNum.shiftl a✝ n) = ↑a✝ <<< n
  induction' n with n IH
  -- ⊢ ↑(PosNum.shiftl a✝ Nat.zero) = ↑a✝ <<< Nat.zero
  · rfl
    -- 🎉 no goals
  simp [PosNum.shiftl_succ_eq_bit0_shiftl, Nat.shiftLeft_succ, IH,
        Nat.bit0_val, pow_succ, ← mul_assoc, mul_comm]
#align num.shiftl_to_nat Num.shiftl_to_nat

@[simp, norm_cast]

theorem shiftr_to_nat (m n) : (shiftr m n : ℕ) = (m : ℕ) >>> (n : ℕ)  := by
  cases' m with m <;> dsimp only [shiftr];
  -- ⊢ ↑(shiftr zero n) = ↑zero >>> n
                      -- ⊢ ↑0 = ↑zero >>> n
                      -- ⊢ ↑(PosNum.shiftr m n) = ↑(pos m) >>> n
  · symm
    -- ⊢ ↑zero >>> n = ↑0
    apply Nat.zero_shiftRight
    -- 🎉 no goals
  induction' n with n IH generalizing m
  -- ⊢ ↑(PosNum.shiftr m Nat.zero) = ↑(pos m) >>> Nat.zero
  · cases m <;> rfl
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
  cases' m with m m <;> dsimp only [PosNum.shiftr]
                        -- ⊢ ↑0 = ↑(pos one) >>> Nat.succ n
                        -- ⊢ ↑(PosNum.shiftr m n) = ↑(pos (PosNum.bit1 m)) >>> Nat.succ n
                        -- ⊢ ↑(PosNum.shiftr m n) = ↑(pos (PosNum.bit0 m)) >>> Nat.succ n
  · rw [Nat.shiftRight_eq_div_pow]
    -- ⊢ ↑0 = ↑(pos one) / 2 ^ Nat.succ n
    symm
    -- ⊢ ↑(pos one) / 2 ^ Nat.succ n = ↑0
    apply Nat.div_eq_of_lt
    -- ⊢ ↑(pos one) < 2 ^ Nat.succ n
    simp [@Nat.pow_lt_pow_of_lt_right 2 (by decide) 0 (n + 1) (Nat.succ_pos _)]
    -- 🎉 no goals
  · trans
    apply IH
    -- ⊢ ↑(pos m) >>> n = ↑(pos (PosNum.bit1 m)) >>> Nat.succ n
    change Nat.shiftRight m n = Nat.shiftRight (_root_.bit1 m) (n + 1)
    -- ⊢ Nat.shiftRight (↑m) n = Nat.shiftRight (_root_.bit1 ↑m) (n + 1)
    rw [add_comm n 1, @Nat.shiftRight_eq _ (1 + n), Nat.shiftRight_add]
    -- ⊢ Nat.shiftRight (↑m) n = _root_.bit1 ↑m >>> 1 >>> n
    apply congr_arg fun x => Nat.shiftRight x n
    -- ⊢ ↑m = _root_.bit1 ↑m >>> 1
    simp [Nat.shiftRight_succ, Nat.shiftRight_zero, ← Nat.div2_val]
    -- 🎉 no goals
  · trans
    apply IH
    -- ⊢ ↑(pos m) >>> n = ↑(pos (PosNum.bit0 m)) >>> Nat.succ n
    change Nat.shiftRight m n = Nat.shiftRight (_root_.bit0 m) (n + 1)
    -- ⊢ Nat.shiftRight (↑m) n = Nat.shiftRight (_root_.bit0 ↑m) (n + 1)
    rw [add_comm n 1,  @Nat.shiftRight_eq _ (1 + n), Nat.shiftRight_add]
    -- ⊢ Nat.shiftRight (↑m) n = _root_.bit0 ↑m >>> 1 >>> n
    apply congr_arg fun x => Nat.shiftRight x n
    -- ⊢ ↑m = _root_.bit0 ↑m >>> 1
    simp [Nat.shiftRight_succ, Nat.shiftRight_zero, ← Nat.div2_val]
    -- 🎉 no goals
#align num.shiftr_to_nat Num.shiftr_to_nat

@[simp]
theorem testBit_to_nat (m n) : testBit m n = Nat.testBit m n := by
  -- Porting note: `unfold` → `dsimp only`
  cases m <;> dsimp only [testBit, Nat.testBit]
  -- ⊢ testBit zero n = Nat.testBit (↑zero) n
              -- ⊢ false = Nat.bodd (↑zero >>> n)
              -- ⊢ PosNum.testBit a✝ n = Nat.bodd (↑(pos a✝) >>> n)
  case zero =>
    change false = Nat.bodd (0 >>> n)
    rw [Nat.zero_shiftRight]
    rfl
  case pos m =>
    induction' n with n IH generalizing m <;> cases' m with m m <;> dsimp only [PosNum.testBit]
    · rfl
    · exact (Nat.bodd_bit _ _).symm
    · exact (Nat.bodd_bit _ _).symm
    · change false = Nat.bodd (1 >>> (n + 1))
      rw [add_comm, Nat.shiftRight_add]
      change false = Nat.bodd (0 >>> n)
      rw [Nat.zero_shiftRight]; rfl
    · change PosNum.testBit m n = Nat.bodd ((Nat.bit true m) >>> (n + 1))
      rw [add_comm, Nat.shiftRight_add]
      simp only [Nat.shiftRight_succ, Nat.shiftRight_zero, ← Nat.div2_val, Nat.div2_bit]
      apply IH
    · change PosNum.testBit m n = Nat.bodd ((Nat.bit false m) >>> (n + 1))
      rw [add_comm, Nat.shiftRight_add]
      simp only [Nat.shiftRight_succ, Nat.shiftRight_zero, ← Nat.div2_val, Nat.div2_bit]
      apply IH
#align num.test_bit_to_nat Num.testBit_to_nat

end Num

namespace ZNum

variable {α : Type*}

open PosNum

@[simp, norm_cast]
theorem cast_zero [Zero α] [One α] [Add α] [Neg α] : ((0 : ZNum) : α) = 0 :=
  rfl
#align znum.cast_zero ZNum.cast_zero

@[simp]
theorem cast_zero' [Zero α] [One α] [Add α] [Neg α] : (ZNum.zero : α) = 0 :=
  rfl
#align znum.cast_zero' ZNum.cast_zero'

@[simp, norm_cast]
theorem cast_one [Zero α] [One α] [Add α] [Neg α] : ((1 : ZNum) : α) = 1 :=
  rfl
#align znum.cast_one ZNum.cast_one

@[simp]
theorem cast_pos [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : (pos n : α) = n :=
  rfl
#align znum.cast_pos ZNum.cast_pos

@[simp]
theorem cast_neg [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : (neg n : α) = -n :=
  rfl
#align znum.cast_neg ZNum.cast_neg

@[simp, norm_cast]
theorem cast_zneg [AddGroup α] [One α] : ∀ n, ((-n : ZNum) : α) = -n
  | 0 => neg_zero.symm
  | pos _p => rfl
  | neg _p => (neg_neg _).symm
#align znum.cast_zneg ZNum.cast_zneg

theorem neg_zero : (-0 : ZNum) = 0 :=
  rfl
#align znum.neg_zero ZNum.neg_zero

theorem zneg_pos (n : PosNum) : -pos n = neg n :=
  rfl
#align znum.zneg_pos ZNum.zneg_pos

theorem zneg_neg (n : PosNum) : -neg n = pos n :=
  rfl
#align znum.zneg_neg ZNum.zneg_neg

theorem zneg_zneg (n : ZNum) : - -n = n := by cases n <;> rfl
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
#align znum.zneg_zneg ZNum.zneg_zneg

theorem zneg_bit1 (n : ZNum) : -n.bit1 = (-n).bitm1 := by cases n <;> rfl
                                                                      -- 🎉 no goals
                                                                      -- 🎉 no goals
                                                                      -- 🎉 no goals
#align znum.zneg_bit1 ZNum.zneg_bit1

theorem zneg_bitm1 (n : ZNum) : -n.bitm1 = (-n).bit1 := by cases n <;> rfl
                                                                       -- 🎉 no goals
                                                                       -- 🎉 no goals
                                                                       -- 🎉 no goals
#align znum.zneg_bitm1 ZNum.zneg_bitm1

theorem zneg_succ (n : ZNum) : -n.succ = (-n).pred := by
  cases n <;> try { rfl }; rw [succ, Num.zneg_toZNumNeg]; rfl
              -- 🎉 no goals
              -- 🎉 no goals
              -- ⊢ -succ (neg a✝) = pred (-neg a✝)
                           -- ⊢ Num.toZNum (pred' a✝) = pred (-neg a✝)
                                                          -- 🎉 no goals
#align znum.zneg_succ ZNum.zneg_succ

theorem zneg_pred (n : ZNum) : -n.pred = (-n).succ := by
  rw [← zneg_zneg (succ (-n)), zneg_succ, zneg_zneg]
  -- 🎉 no goals
#align znum.zneg_pred ZNum.zneg_pred

@[simp]
theorem abs_to_nat : ∀ n, (abs n : ℕ) = Int.natAbs n
  | 0 => rfl
  | pos p => congr_arg Int.natAbs p.to_nat_to_int
  | neg p => show Int.natAbs ((p : ℕ) : ℤ) = Int.natAbs (-p) by rw [p.to_nat_to_int, Int.natAbs_neg]
                                                                -- 🎉 no goals
#align znum.abs_to_nat ZNum.abs_to_nat

@[simp]
theorem abs_toZNum : ∀ n : Num, abs n.toZNum = n
  | 0 => rfl
  | Num.pos _p => rfl
#align znum.abs_to_znum ZNum.abs_toZNum

@[simp, norm_cast]
theorem cast_to_int [AddGroupWithOne α] : ∀ n : ZNum, ((n : ℤ) : α) = n
  | 0 => by rw [cast_zero, cast_zero, Int.cast_zero]
            -- 🎉 no goals
  | pos p => by rw [cast_pos, cast_pos, PosNum.cast_to_int]
                -- 🎉 no goals
  | neg p => by rw [cast_neg, cast_neg, Int.cast_neg, PosNum.cast_to_int]
                -- 🎉 no goals
#align znum.cast_to_int ZNum.cast_to_int

theorem bit0_of_bit0 : ∀ n : ZNum, bit0 n = n.bit0
  | 0 => rfl
  | pos a => congr_arg pos a.bit0_of_bit0
  | neg a => congr_arg neg a.bit0_of_bit0
#align znum.bit0_of_bit0 ZNum.bit0_of_bit0

theorem bit1_of_bit1 : ∀ n : ZNum, bit1 n = n.bit1
  | 0 => rfl
  | pos a => congr_arg pos a.bit1_of_bit1
  | neg a => show PosNum.sub' 1 (_root_.bit0 a) = _ by rw [PosNum.one_sub', a.bit0_of_bit0]; rfl
                                                       -- ⊢ Num.toZNumNeg (pred' (PosNum.bit0 a)) = ZNum.bit1 (neg a)
                                                                                             -- 🎉 no goals
#align znum.bit1_of_bit1 ZNum.bit1_of_bit1

@[simp, norm_cast]
theorem cast_bit0 [AddGroupWithOne α] : ∀ n : ZNum, (n.bit0 : α) = bit0 (n : α)
  | 0 => (add_zero _).symm
  | pos p => by rw [ZNum.bit0, cast_pos, cast_pos]; rfl
                -- ⊢ ↑(PosNum.bit0 p) = _root_.bit0 ↑p
                                                    -- 🎉 no goals
  | neg p => by
    rw [ZNum.bit0, cast_neg, cast_neg, PosNum.cast_bit0, _root_.bit0, _root_.bit0, neg_add_rev]
    -- 🎉 no goals
#align znum.cast_bit0 ZNum.cast_bit0

@[simp, norm_cast]
theorem cast_bit1 [AddGroupWithOne α] : ∀ n : ZNum, (n.bit1 : α) = bit1 (n : α)
  | 0 => by simp [ZNum.bit1, _root_.bit1, _root_.bit0]
            -- 🎉 no goals
  | pos p => by rw [ZNum.bit1, cast_pos, cast_pos]; rfl
                -- ⊢ ↑(PosNum.bit1 p) = _root_.bit1 ↑p
                                                    -- 🎉 no goals
  | neg p => by
    rw [ZNum.bit1, cast_neg, cast_neg]
    -- ⊢ -↑(Num.casesOn (pred' p) 1 PosNum.bit1) = _root_.bit1 (-↑p)
    cases' e : pred' p with a <;>
    -- ⊢ -↑(Num.casesOn Num.zero 1 PosNum.bit1) = _root_.bit1 (-↑p)
      have ep : p = _ := (succ'_pred' p).symm.trans (congr_arg Num.succ' e)
      -- ⊢ -↑(Num.casesOn Num.zero 1 PosNum.bit1) = _root_.bit1 (-↑p)
      -- ⊢ -↑(Num.casesOn (Num.pos a) 1 PosNum.bit1) = _root_.bit1 (-↑p)
    · conv at ep => change p = 1
      -- ⊢ -↑(Num.casesOn Num.zero 1 PosNum.bit1) = _root_.bit1 (-↑p)
      subst p
      -- ⊢ -↑(Num.casesOn Num.zero 1 PosNum.bit1) = _root_.bit1 (-↑1)
      simp [_root_.bit1, _root_.bit0]
      -- 🎉 no goals
    -- Porting note: `rw [Num.succ']` yields a `match` pattern.
    · dsimp only [Num.succ'] at ep
      -- ⊢ -↑(Num.casesOn (Num.pos a) 1 PosNum.bit1) = _root_.bit1 (-↑p)
      subst p
      -- ⊢ -↑(Num.casesOn (Num.pos a) 1 PosNum.bit1) = _root_.bit1 (-↑(PosNum.succ a))
      have : (↑(-↑a : ℤ) : α) = -1 + ↑(-↑a + 1 : ℤ) := by simp [add_comm (- ↑a : ℤ) 1]
      -- ⊢ -↑(Num.casesOn (Num.pos a) 1 PosNum.bit1) = _root_.bit1 (-↑(PosNum.succ a))
      simpa [_root_.bit1, _root_.bit0] using this
      -- 🎉 no goals
#align znum.cast_bit1 ZNum.cast_bit1

@[simp]
theorem cast_bitm1 [AddGroupWithOne α] (n : ZNum) : (n.bitm1 : α) = bit0 (n : α) - 1 := by
  conv =>
    lhs
    rw [← zneg_zneg n]
  rw [← zneg_bit1, cast_zneg, cast_bit1]
  -- ⊢ -_root_.bit1 ↑(-n) = _root_.bit0 ↑n - 1
  have : ((-1 + n + n : ℤ) : α) = (n + n + -1 : ℤ) := by simp [add_comm, add_left_comm]
  -- ⊢ -_root_.bit1 ↑(-n) = _root_.bit0 ↑n - 1
  simpa [_root_.bit1, _root_.bit0, sub_eq_add_neg] using this
  -- 🎉 no goals
#align znum.cast_bitm1 ZNum.cast_bitm1

theorem add_zero (n : ZNum) : n + 0 = n := by cases n <;> rfl
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
#align znum.add_zero ZNum.add_zero

theorem zero_add (n : ZNum) : 0 + n = n := by cases n <;> rfl
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
#align znum.zero_add ZNum.zero_add

theorem add_one : ∀ n : ZNum, n + 1 = succ n
  | 0 => rfl
  | pos p => congr_arg pos p.add_one
  | neg p => by cases p <;> rfl
                            -- 🎉 no goals
                            -- 🎉 no goals
                            -- 🎉 no goals
#align znum.add_one ZNum.add_one

end ZNum

namespace PosNum

variable {α : Type*}

theorem cast_to_znum : ∀ n : PosNum, (n : ZNum) = ZNum.pos n
  | 1 => rfl
  | bit0 p => (ZNum.bit0_of_bit0 p).trans <| congr_arg _ (cast_to_znum p)
  | bit1 p => (ZNum.bit1_of_bit1 p).trans <| congr_arg _ (cast_to_znum p)
#align pos_num.cast_to_znum PosNum.cast_to_znum

theorem cast_sub' [AddGroupWithOne α] : ∀ m n : PosNum, (sub' m n : α) = m - n
  | a, 1 => by
    rw [sub'_one, Num.cast_toZNum, ← Num.cast_to_nat, pred'_to_nat, ← Nat.sub_one]
    -- ⊢ ↑(↑a - 1) = ↑a - ↑1
    simp [PosNum.cast_pos]
    -- 🎉 no goals
  | 1, b => by
    rw [one_sub', Num.cast_toZNumNeg, ← neg_sub, neg_inj, ← Num.cast_to_nat, pred'_to_nat,
        ← Nat.sub_one]
    simp [PosNum.cast_pos]
    -- 🎉 no goals
  | bit0 a, bit0 b => by
    rw [sub', ZNum.cast_bit0, cast_sub' a b]
    -- ⊢ _root_.bit0 (↑a - ↑b) = ↑(bit0 a) - ↑(bit0 b)
    have : ((a + -b + (a + -b) : ℤ) : α) = a + a + (-b + -b) := by simp [add_left_comm]
    -- ⊢ _root_.bit0 (↑a - ↑b) = ↑(bit0 a) - ↑(bit0 b)
    simpa [_root_.bit0, sub_eq_add_neg] using this
    -- 🎉 no goals
  | bit0 a, bit1 b => by
    rw [sub', ZNum.cast_bitm1, cast_sub' a b]
    -- ⊢ _root_.bit0 (↑a - ↑b) - 1 = ↑(bit0 a) - ↑(bit1 b)
    have : ((-b + (a + (-b + -1)) : ℤ) : α) = (a + -1 + (-b + -b) : ℤ) := by
      simp [add_comm, add_left_comm]
    simpa [_root_.bit1, _root_.bit0, sub_eq_add_neg] using this
    -- 🎉 no goals
  | bit1 a, bit0 b => by
    rw [sub', ZNum.cast_bit1, cast_sub' a b]
    -- ⊢ _root_.bit1 (↑a - ↑b) = ↑(bit1 a) - ↑(bit0 b)
    have : ((-b + (a + (-b + 1)) : ℤ) : α) = (a + 1 + (-b + -b) : ℤ) := by
      simp [add_comm, add_left_comm]
    simpa [_root_.bit1, _root_.bit0, sub_eq_add_neg] using this
    -- 🎉 no goals
  | bit1 a, bit1 b => by
    rw [sub', ZNum.cast_bit0, cast_sub' a b]
    -- ⊢ _root_.bit0 (↑a - ↑b) = ↑(bit1 a) - ↑(bit1 b)
    have : ((-b + (a + -b) : ℤ) : α) = a + (-b + -b) := by simp [add_left_comm]
    -- ⊢ _root_.bit0 (↑a - ↑b) = ↑(bit1 a) - ↑(bit1 b)
    simpa [_root_.bit1, _root_.bit0, sub_eq_add_neg] using this
    -- 🎉 no goals
#align pos_num.cast_sub' PosNum.cast_sub'

theorem to_nat_eq_succ_pred (n : PosNum) : (n : ℕ) = n.pred' + 1 := by
  rw [← Num.succ'_to_nat, n.succ'_pred']
  -- 🎉 no goals
#align pos_num.to_nat_eq_succ_pred PosNum.to_nat_eq_succ_pred

theorem to_int_eq_succ_pred (n : PosNum) : (n : ℤ) = (n.pred' : ℕ) + 1 := by
  rw [← n.to_nat_to_int, to_nat_eq_succ_pred]; rfl
  -- ⊢ ↑(↑(pred' n) + 1) = ↑↑(pred' n) + 1
                                               -- 🎉 no goals
#align pos_num.to_int_eq_succ_pred PosNum.to_int_eq_succ_pred

end PosNum

namespace Num

variable {α : Type*}

@[simp]
theorem cast_sub' [AddGroupWithOne α] : ∀ m n : Num, (sub' m n : α) = m - n
  | 0, 0 => (sub_zero _).symm
  | pos _a, 0 => (sub_zero _).symm
  | 0, pos _b => (zero_sub _).symm
  | pos _a, pos _b => PosNum.cast_sub' _ _
#align num.cast_sub' Num.cast_sub'

theorem toZNum_succ : ∀ n : Num, n.succ.toZNum = n.toZNum.succ
  | 0 => rfl
  | pos _n => rfl
#align num.to_znum_succ Num.toZNum_succ

theorem toZNumNeg_succ : ∀ n : Num, n.succ.toZNumNeg = n.toZNumNeg.pred
  | 0 => rfl
  | pos _n => rfl
#align num.to_znum_neg_succ Num.toZNumNeg_succ

@[simp]
theorem pred_succ : ∀ n : ZNum, n.pred.succ = n
  | 0 => rfl
  | ZNum.neg p => show toZNumNeg (pos p).succ'.pred' = _ by rw [PosNum.pred'_succ']; rfl
                                                            -- ⊢ toZNumNeg (pos p) = ZNum.neg p
                                                                                     -- 🎉 no goals
  | ZNum.pos p => by rw [ZNum.pred, ← toZNum_succ, Num.succ, PosNum.succ'_pred', toZNum]
                     -- 🎉 no goals
#align num.pred_succ Num.pred_succ

-- Porting note: `erw [ZNum.ofInt', ZNum.ofInt']` yields `match` so
--               `change` & `dsimp` are required.
theorem succ_ofInt' : ∀ n, ZNum.ofInt' (n + 1) = ZNum.ofInt' n + 1
  | (n : ℕ) => by
    change ZNum.ofInt' (n + 1 : ℕ) = ZNum.ofInt' (n : ℕ) + 1
    -- ⊢ ZNum.ofInt' ↑(n + 1) = ZNum.ofInt' ↑n + 1
    dsimp only [ZNum.ofInt', ZNum.ofInt']
    -- ⊢ toZNum (ofNat' (n + 1)) = toZNum (ofNat' n) + 1
    rw [Num.ofNat'_succ, Num.add_one, toZNum_succ, ZNum.add_one]
    -- 🎉 no goals
  | -[0+1] => by
    change ZNum.ofInt' 0 = ZNum.ofInt' (-[0+1]) + 1
    -- ⊢ ZNum.ofInt' 0 = ZNum.ofInt' -[0+1] + 1
    dsimp only [ZNum.ofInt', ZNum.ofInt']
    -- ⊢ toZNum (ofNat' 0) = toZNumNeg (ofNat' (0 + 1)) + 1
    rw [ofNat'_succ, ofNat'_zero]; rfl
    -- ⊢ toZNum 0 = toZNumNeg (0 + 1) + 1
                                   -- 🎉 no goals
  | -[(n + 1)+1] => by
    change ZNum.ofInt' -[n+1] = ZNum.ofInt' -[(n + 1)+1] + 1
    -- ⊢ ZNum.ofInt' -[n+1] = ZNum.ofInt' -[n + 1+1] + 1
    dsimp only [ZNum.ofInt', ZNum.ofInt']
    -- ⊢ toZNumNeg (ofNat' (n + 1)) = toZNumNeg (ofNat' (n + 1 + 1)) + 1
    rw [@Num.ofNat'_succ (n + 1), Num.add_one, toZNumNeg_succ,
      @ofNat'_succ n, Num.add_one, ZNum.add_one, pred_succ]
#align num.succ_of_int' Num.succ_ofInt'

theorem ofInt'_toZNum : ∀ n : ℕ, toZNum n = ZNum.ofInt' n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.cast_succ, Num.add_one, toZNum_succ, ofInt'_toZNum n, Nat.cast_succ, succ_ofInt',
      ZNum.add_one]
#align num.of_int'_to_znum Num.ofInt'_toZNum

theorem mem_ofZNum' : ∀ {m : Num} {n : ZNum}, m ∈ ofZNum' n ↔ n = toZNum m
  | 0, 0 => ⟨fun _ => rfl, fun _ => rfl⟩
  | pos m, 0 => ⟨fun., fun.⟩
  | m, ZNum.pos p =>
    Option.some_inj.trans <| by cases m <;> constructor <;> intro h <;> try cases h <;> rfl
                                -- ⊢ pos p = zero ↔ ZNum.pos p = toZNum zero
                                            -- ⊢ pos p = zero → ZNum.pos p = toZNum zero
                                            -- ⊢ pos p = pos a✝ → ZNum.pos p = toZNum (pos a✝)
                                                            -- ⊢ ZNum.pos p = toZNum zero
                                                            -- ⊢ pos p = zero
                                                            -- ⊢ ZNum.pos p = toZNum (pos a✝)
                                                            -- ⊢ pos p = pos a✝
                                                                        -- 🎉 no goals
                                                                        -- 🎉 no goals
                                                                        -- 🎉 no goals
                                                                        -- 🎉 no goals
  | m, ZNum.neg p => ⟨fun., fun h => by cases m <;> cases h⟩
                                        -- ⊢ zero ∈ ofZNum' (ZNum.neg p)
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
#align num.mem_of_znum' Num.mem_ofZNum'

theorem ofZNum'_toNat : ∀ n : ZNum, (↑) <$> ofZNum' n = Int.toNat' n
  | 0 => rfl
  | ZNum.pos p => show _ = Int.toNat' p by rw [← PosNum.to_nat_to_int p]; rfl
                                           -- ⊢ castNum <$> ofZNum' (ZNum.pos p) = toNat' ↑↑p
                                                                          -- 🎉 no goals
  | ZNum.neg p =>
    (congr_arg fun x => Int.toNat' (-x)) <|
      show ((p.pred' + 1 : ℕ) : ℤ) = p by rw [← succ'_to_nat]; simp
                                          -- ⊢ ↑↑(succ' (PosNum.pred' p)) = ↑p
                                                               -- 🎉 no goals
#align num.of_znum'_to_nat Num.ofZNum'_toNat

@[simp]
theorem ofZNum_toNat : ∀ n : ZNum, (ofZNum n : ℕ) = Int.toNat n
  | 0 => rfl
  | ZNum.pos p => show _ = Int.toNat p by rw [← PosNum.to_nat_to_int p]; rfl
                                          -- ⊢ ↑(ofZNum (ZNum.pos p)) = toNat ↑↑p
                                                                         -- 🎉 no goals
  | ZNum.neg p =>
    (congr_arg fun x => Int.toNat (-x)) <|
      show ((p.pred' + 1 : ℕ) : ℤ) = p by rw [← succ'_to_nat]; simp
                                          -- ⊢ ↑↑(succ' (PosNum.pred' p)) = ↑p
                                                               -- 🎉 no goals
#align num.of_znum_to_nat Num.ofZNum_toNat

@[simp]
theorem cast_ofZNum [AddGroupWithOne α] (n : ZNum) : (ofZNum n : α) = Int.toNat n := by
  rw [← cast_to_nat, ofZNum_toNat]
  -- 🎉 no goals
#align num.cast_of_znum Num.cast_ofZNum

@[simp, norm_cast]
theorem sub_to_nat (m n) : ((m - n : Num) : ℕ) = m - n :=
  show (ofZNum _ : ℕ) = _ by
    rw [ofZNum_toNat, cast_sub', ← to_nat_to_int, ← to_nat_to_int, Int.toNat_sub]
    -- 🎉 no goals
#align num.sub_to_nat Num.sub_to_nat

end Num

namespace ZNum

variable {α : Type*}

@[simp, norm_cast]
theorem cast_add [AddGroupWithOne α] : ∀ m n, ((m + n : ZNum) : α) = m + n
  | 0, a => by cases a <;> exact (_root_.zero_add _).symm
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
  | b, 0 => by cases b <;> exact (_root_.add_zero _).symm
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
  | pos a, pos b => PosNum.cast_add _ _
  | pos a, neg b => by simpa only [sub_eq_add_neg] using PosNum.cast_sub' (α := α) _ _
                       -- 🎉 no goals
  | neg a, pos b =>
    have : (↑b + -↑a : α) = -↑a + ↑b := by
      rw [← PosNum.cast_to_int a, ← PosNum.cast_to_int b, ← Int.cast_neg, ← Int.cast_add (-a)]
      -- ⊢ ↑↑b + ↑(-↑a) = ↑(-↑a + ↑b)
      simp [add_comm]
      -- 🎉 no goals
    (PosNum.cast_sub' _ _).trans <| (sub_eq_add_neg _ _).trans this
  | neg a, neg b =>
    show -(↑(a + b) : α) = -a + -b by
      rw [PosNum.cast_add, neg_eq_iff_eq_neg, neg_add_rev, neg_neg, neg_neg,
          ← PosNum.cast_to_int a, ← PosNum.cast_to_int b, ← Int.cast_add, ← Int.cast_add, add_comm]
#align znum.cast_add ZNum.cast_add

@[simp]
theorem cast_succ [AddGroupWithOne α] (n) : ((succ n : ZNum) : α) = n + 1 := by
  rw [← add_one, cast_add, cast_one]
  -- 🎉 no goals
#align znum.cast_succ ZNum.cast_succ

@[simp, norm_cast]
theorem mul_to_int : ∀ m n, ((m * n : ZNum) : ℤ) = m * n
  | 0, a => by cases a <;> exact (zero_mul _).symm
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
  | b, 0 => by cases b <;> exact (mul_zero _).symm
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
  | pos a, pos b => PosNum.cast_mul a b
  | pos a, neg b => show -↑(a * b) = ↑a * -↑b by rw [PosNum.cast_mul, neg_mul_eq_mul_neg]
                                                 -- 🎉 no goals
  | neg a, pos b => show -↑(a * b) = -↑a * ↑b by rw [PosNum.cast_mul, neg_mul_eq_neg_mul]
                                                 -- 🎉 no goals
  | neg a, neg b => show ↑(a * b) = -↑a * -↑b by rw [PosNum.cast_mul, neg_mul_neg]
                                                 -- 🎉 no goals
#align znum.mul_to_int ZNum.mul_to_int

theorem cast_mul [Ring α] (m n) : ((m * n : ZNum) : α) = m * n := by
  rw [← cast_to_int, mul_to_int, Int.cast_mul, cast_to_int, cast_to_int]
  -- 🎉 no goals
#align znum.cast_mul ZNum.cast_mul

theorem ofInt'_neg : ∀ n : ℤ, ofInt' (-n) = -ofInt' n
  | -[n+1] => show ofInt' (n + 1 : ℕ) = _ by simp only [ofInt', Num.zneg_toZNumNeg]
                                             -- 🎉 no goals
  | 0 => show Num.toZNum (Num.ofNat' 0) = -Num.toZNum (Num.ofNat' 0) by rw [Num.ofNat'_zero]; rfl
                                                                        -- ⊢ Num.toZNum 0 = -Num.toZNum 0
                                                                                              -- 🎉 no goals
  | (n + 1 : ℕ) => show Num.toZNumNeg _ = -Num.toZNum _ by rw [Num.zneg_toZNum]
                                                           -- 🎉 no goals
#align znum.of_int'_neg ZNum.ofInt'_neg

-- Porting note: `erw [ofInt']` yields `match` so `dsimp` is required.
theorem of_to_int' : ∀ n : ZNum, ZNum.ofInt' n = n
  | 0 => by dsimp [ofInt', cast_zero]; erw [Num.ofNat'_zero, Num.toZNum]
            -- ⊢ Num.toZNum (Num.ofNat' 0) = 0
                                       -- 🎉 no goals
  | pos a => by rw [cast_pos, ← PosNum.cast_to_nat, ← Num.ofInt'_toZNum, PosNum.of_to_nat]; rfl
                -- ⊢ Num.toZNum (Num.pos a) = pos a
                                                                                            -- 🎉 no goals
  | neg a => by
    rw [cast_neg, ofInt'_neg, ← PosNum.cast_to_nat, ← Num.ofInt'_toZNum, PosNum.of_to_nat]; rfl
    -- ⊢ -Num.toZNum (Num.pos a) = neg a
                                                                                            -- 🎉 no goals
#align znum.of_to_int' ZNum.of_to_int'

theorem to_int_inj {m n : ZNum} : (m : ℤ) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective of_to_int' h, congr_arg _⟩
#align znum.to_int_inj ZNum.to_int_inj

theorem cmp_to_int : ∀ m n, (Ordering.casesOn (cmp m n) ((m : ℤ) < n) (m = n) ((n : ℤ) < m) : Prop)
  | 0, 0 => rfl
  | pos a, pos b => by
    have := PosNum.cmp_to_nat a b; revert this; dsimp [cmp]
    -- ⊢ Ordering.casesOn (cmp (pos a) (pos b)) (↑(pos a) < ↑(pos b)) (pos a = pos b) …
                                   -- ⊢ Ordering.casesOn (PosNum.cmp a b) (↑a < ↑b) (a = b) (↑b < ↑a) → Ordering.cas …
                                                -- ⊢ Ordering.rec (↑a < ↑b) (a = b) (↑b < ↑a) (PosNum.cmp a b) → Ordering.rec (↑a …
    cases PosNum.cmp a b <;> dsimp <;> [simp; exact congr_arg pos; simp [GT.gt]]
    -- 🎉 no goals
  | neg a, neg b => by
    have := PosNum.cmp_to_nat b a; revert this; dsimp [cmp]
    -- ⊢ Ordering.casesOn (cmp (neg a) (neg b)) (↑(neg a) < ↑(neg b)) (neg a = neg b) …
                                   -- ⊢ Ordering.casesOn (PosNum.cmp b a) (↑b < ↑a) (b = a) (↑a < ↑b) → Ordering.cas …
                                                -- ⊢ Ordering.rec (↑b < ↑a) (b = a) (↑a < ↑b) (PosNum.cmp b a) → Ordering.rec (-↑ …
    cases PosNum.cmp b a <;> dsimp <;> [simp; simp (config := { contextual := true }); simp [GT.gt]]
    -- 🎉 no goals
  | pos a, 0 => PosNum.cast_pos _
  | pos a, neg b => lt_trans (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
  | 0, neg b => neg_lt_zero.2 <| PosNum.cast_pos _
  | neg a, 0 => neg_lt_zero.2 <| PosNum.cast_pos _
  | neg a, pos b => lt_trans (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
  | 0, pos b => PosNum.cast_pos _
#align znum.cmp_to_int ZNum.cmp_to_int

@[norm_cast]
theorem lt_to_int {m n : ZNum} : (m : ℤ) < n ↔ m < n :=
  show (m : ℤ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_int m n with
    | Ordering.lt, h => by simp at h; simp [h]
                           -- ⊢ ↑m < ↑n ↔ Ordering.lt = Ordering.lt
                                      -- 🎉 no goals
    | Ordering.eq, h => by simp at h; simp [h, lt_irrefl]
                           -- ⊢ ↑m < ↑n ↔ Ordering.eq = Ordering.lt
                                      -- 🎉 no goals
    | Ordering.gt, h => by simp [not_lt_of_gt h]
                           -- 🎉 no goals
#align znum.lt_to_int ZNum.lt_to_int

theorem le_to_int {m n : ZNum} : (m : ℤ) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr lt_to_int
  -- ⊢ ¬↑n < ↑m ↔ m ≤ n
                 -- 🎉 no goals
#align znum.le_to_int ZNum.le_to_int

@[simp, norm_cast]
theorem cast_lt [LinearOrderedRing α] {m n : ZNum} : (m : α) < n ↔ m < n := by
  rw [← cast_to_int m, ← cast_to_int n, Int.cast_lt, lt_to_int]
  -- 🎉 no goals
#align znum.cast_lt ZNum.cast_lt

@[simp, norm_cast]
theorem cast_le [LinearOrderedRing α] {m n : ZNum} : (m : α) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr cast_lt
  -- ⊢ ¬↑n < ↑m ↔ m ≤ n
                 -- 🎉 no goals
#align znum.cast_le ZNum.cast_le

@[simp, norm_cast]
theorem cast_inj [LinearOrderedRing α] {m n : ZNum} : (m : α) = n ↔ m = n := by
  rw [← cast_to_int m, ← cast_to_int n, Int.cast_inj (α := α), to_int_inj]
  -- 🎉 no goals
#align znum.cast_inj ZNum.cast_inj

/-- This tactic tries to turn an (in)equality about `ZNum`s to one about `Int`s by rewriting.
```lean
example (n : ZNum) (m : ZNum) : n ≤ n + m * m := by
  transfer_rw
  exact le_add_of_nonneg_right (mul_self_nonneg _)
```
-/
scoped macro (name := transfer_rw) "transfer_rw" : tactic => `(tactic|
    (repeat first | rw [← to_int_inj] | rw [← lt_to_int] | rw [← le_to_int]
     repeat first | rw [cast_add] | rw [mul_to_int] | rw [cast_one] | rw [cast_zero]))

/--
This tactic tries to prove (in)equalities about `ZNum`s by transferring them to the `Int` world and
then trying to call `simp`.
```lean
example (n : ZNum) (m : ZNum) : n ≤ n + m * m := by
  transfer
  exact mul_self_nonneg _
```
-/
scoped macro (name := transfer) "transfer" : tactic => `(tactic|
    (intros; transfer_rw; try simp [add_comm, add_left_comm, mul_comm, mul_left_comm]))

instance linearOrder : LinearOrder ZNum where
  lt := (· < ·)
  lt_iff_le_not_le := by
    intro a b
    -- ⊢ a < b ↔ a ≤ b ∧ ¬b ≤ a
    transfer_rw
    -- ⊢ ↑a < ↑b ↔ ↑a ≤ ↑b ∧ ¬↑b ≤ ↑a
    apply lt_iff_le_not_le
                -- 🎉 no goals
    -- 🎉 no goals
  le := (· ≤ ·)
    -- ⊢ a ≤ b → b ≤ c → a ≤ c
  le_refl := by transfer
    -- ⊢ ↑a ≤ ↑b → ↑b ≤ ↑c → ↑a ≤ ↑c
  le_trans := by
    -- 🎉 no goals
    intro a b c
    transfer_rw
    apply le_trans
  le_antisymm := by
    intro a b
    -- ⊢ a ≤ b → b ≤ a → a = b
    transfer_rw
    -- ⊢ ↑a ≤ ↑b → ↑b ≤ ↑a → ↑a = ↑b
    apply le_antisymm
    -- 🎉 no goals
  le_total := by
    intro a b
    -- ⊢ a ≤ b ∨ b ≤ a
    transfer_rw
    -- ⊢ ↑a ≤ ↑b ∨ ↑b ≤ ↑a
    apply le_total
    -- 🎉 no goals
  -- This is relying on an automatically generated instance name, generated in a `deriving` handler.
  -- See https://github.com/leanprover/lean4/issues/2343
  decidableEq := instDecidableEqZNum
  decidableLE := ZNum.decidableLE
  decidableLT := ZNum.decidableLT
#align znum.linear_order ZNum.linearOrder

instance addCommGroup : AddCommGroup ZNum where
  add := (· + ·)
  add_assoc := by transfer
                  -- 🎉 no goals
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  add_comm := by transfer
                 -- 🎉 no goals
  neg := Neg.neg
                     -- 🎉 no goals
  add_left_neg := by transfer
#align znum.add_comm_group ZNum.addCommGroup

instance addMonoidWithOne : AddMonoidWithOne ZNum :=
  { ZNum.addCommGroup with
    one := 1
    natCast := fun n => ZNum.ofInt' n
    natCast_zero := show (Num.ofNat' 0).toZNum = 0 by rw [Num.ofNat'_zero]; rfl
                                                      -- ⊢ Num.toZNum 0 = 0
                                                                            -- 🎉 no goals
    natCast_succ := fun n =>
      show (Num.ofNat' (n + 1)).toZNum = (Num.ofNat' n).toZNum + 1 by
        rw [Num.ofNat'_succ, Num.add_one, Num.toZNum_succ, ZNum.add_one] }
        -- 🎉 no goals
#align znum.add_monoid_with_one ZNum.addMonoidWithOne

-- Porting note: These theorems should be declared out of the instance, otherwise timeouts.

private theorem mul_comm : ∀ (a b : ZNum), a * b = b * a := by transfer
                                                               -- 🎉 no goals

private theorem add_le_add_left : ∀ (a b : ZNum), a ≤ b → ∀ (c : ZNum), c + a ≤ c + b := by
  intro a b h c
  -- ⊢ c + a ≤ c + b
  revert h
  -- ⊢ a ≤ b → c + a ≤ c + b
  transfer_rw
  -- ⊢ ↑a ≤ ↑b → ↑c + ↑a ≤ ↑c + ↑b
  exact fun h => _root_.add_le_add_left h c
  -- 🎉 no goals

instance linearOrderedCommRing : LinearOrderedCommRing ZNum :=
  { ZNum.linearOrder, ZNum.addCommGroup, ZNum.addMonoidWithOne with
    mul := (· * ·)
    mul_assoc := by transfer
                    -- 🎉 no goals
                   -- 🎉 no goals
    zero_mul := by transfer
                   -- 🎉 no goals
    mul_zero := by transfer
    one := 1
    one_mul := by transfer
      -- ⊢ ↑a✝ * (↑b✝ + ↑c✝) = ↑a✝ * ↑b✝ + ↑a✝ * ↑c✝
                  -- 🎉 no goals
      -- 🎉 no goals
    mul_one := by transfer
                  -- 🎉 no goals
      -- ⊢ ↑c✝ * (↑a✝ + ↑b✝) = ↑a✝ * ↑c✝ + ↑b✝ * ↑c✝
    left_distrib := by
      -- 🎉 no goals
      transfer
      simp [mul_add]
    right_distrib := by
      transfer
      simp [mul_add, _root_.mul_comm]
    mul_comm := mul_comm
    exists_pair_ne := ⟨0, 1, by decide⟩
                                -- 🎉 no goals
    add_le_add_left := add_le_add_left
    mul_pos := fun a b =>
      show 0 < a → 0 < b → 0 < a * b by
        transfer_rw
        -- ⊢ 0 < ↑a → 0 < ↑b → 0 < ↑a * ↑b
        apply mul_pos
                      -- 🎉 no goals
        -- 🎉 no goals
    zero_le_one := by decide }
#align znum.linear_ordered_comm_ring ZNum.linearOrderedCommRing

@[simp, norm_cast]
theorem cast_sub [Ring α] (m n) : ((m - n : ZNum) : α) = m - n := by simp [sub_eq_neg_add]
                                                                     -- 🎉 no goals
#align znum.cast_sub ZNum.cast_sub

@[norm_cast] -- @[simp] -- Porting note: simp can prove this
theorem neg_of_int : ∀ n, ((-n : ℤ) : ZNum) = -n
  | (n + 1 : ℕ) => rfl
  | 0 => by rw [Int.cast_neg, Int.cast_zero]
            -- 🎉 no goals
  | -[n+1] => (zneg_zneg _).symm
#align znum.neg_of_int ZNum.neg_of_int

@[simp]
theorem ofInt'_eq : ∀ n : ℤ, ZNum.ofInt' n = n
  | (n : ℕ) => rfl
  | -[n+1] => by
    show Num.toZNumNeg (n + 1 : ℕ) = -(n + 1 : ℕ)
    -- ⊢ Num.toZNumNeg ↑(n + 1) = -↑(n + 1)
    rw [← neg_inj, neg_neg, Nat.cast_succ, Num.add_one, Num.zneg_toZNumNeg, Num.toZNum_succ,
      Nat.cast_succ, ZNum.add_one]
    rfl
    -- 🎉 no goals
#align znum.of_int'_eq ZNum.ofInt'_eq

@[simp]
theorem of_nat_toZNum (n : ℕ) : Num.toZNum n = n :=
  rfl
#align znum.of_nat_to_znum ZNum.of_nat_toZNum

-- Porting note: The priority should be `high`er than `cast_to_int`.
@[simp high, norm_cast]
theorem of_to_int (n : ZNum) : ((n : ℤ) : ZNum) = n := by rw [← ofInt'_eq, of_to_int']
                                                          -- 🎉 no goals
#align znum.of_to_int ZNum.of_to_int

theorem to_of_int (n : ℤ) : ((n : ZNum) : ℤ) = n :=
  Int.inductionOn' n 0 (by simp) (by simp) (by simp)
                           -- 🎉 no goals
                                     -- 🎉 no goals
                                               -- 🎉 no goals
#align znum.to_of_int ZNum.to_of_int

@[simp]
theorem of_nat_toZNumNeg (n : ℕ) : Num.toZNumNeg n = -n := by rw [← of_nat_toZNum, Num.zneg_toZNum]
                                                              -- 🎉 no goals
#align znum.of_nat_to_znum_neg ZNum.of_nat_toZNumNeg

@[simp, norm_cast]
theorem of_int_cast [AddGroupWithOne α] (n : ℤ) : ((n : ZNum) : α) = n := by
  rw [← cast_to_int, to_of_int]
  -- 🎉 no goals
#align znum.of_int_cast ZNum.of_int_cast

@[simp, norm_cast]
theorem of_nat_cast [AddGroupWithOne α] (n : ℕ) : ((n : ZNum) : α) = n := by
  rw [← Int.cast_ofNat, of_int_cast, Int.cast_ofNat]
  -- 🎉 no goals
#align znum.of_nat_cast ZNum.of_nat_cast

@[simp, norm_cast]
theorem dvd_to_int (m n : ZNum) : (m : ℤ) ∣ n ↔ m ∣ n :=
  ⟨fun ⟨k, e⟩ => ⟨k, by rw [← of_to_int n, e]; simp⟩, fun ⟨k, e⟩ => ⟨k, by simp [e]⟩⟩
                        -- ⊢ ↑(↑m * k) = m * ↑k
                                               -- 🎉 no goals
                                                                           -- 🎉 no goals
#align znum.dvd_to_int ZNum.dvd_to_int

end ZNum

namespace PosNum

theorem divMod_to_nat_aux {n d : PosNum} {q r : Num} (h₁ : (r : ℕ) + d * _root_.bit0 (q : ℕ) = n)
    (h₂ : (r : ℕ) < 2 * d) :
    ((divModAux d q r).2 + d * (divModAux d q r).1 : ℕ) = ↑n ∧ ((divModAux d q r).2 : ℕ) < d := by
  unfold divModAux
  -- ⊢ ↑(match Num.ofZNum' (Num.sub' r (Num.pos d)) with
  have : ∀ {r₂}, Num.ofZNum' (Num.sub' r (Num.pos d)) = some r₂ ↔ (r : ℕ) = r₂ + d := by
    intro r₂
    apply Num.mem_ofZNum'.trans
    rw [← ZNum.to_int_inj, Num.cast_toZNum, Num.cast_sub', sub_eq_iff_eq_add, ← Int.coe_nat_inj']
    simp
  cases' e : Num.ofZNum' (Num.sub' r (Num.pos d)) with r₂ <;> simp [divModAux]
                                                              -- ⊢ ↑r + ↑d * _root_.bit0 ↑q = ↑n ∧ ↑r < ↑d
                                                              -- ⊢ ↑r₂ + ↑d * _root_.bit1 ↑q = ↑n ∧ ↑r₂ < ↑d
  · refine' ⟨h₁, lt_of_not_ge fun h => _⟩
    -- ⊢ False
    cases' Nat.le.dest h with r₂ e'
    -- ⊢ False
    rw [← Num.to_of_nat r₂, add_comm] at e'
    -- ⊢ False
    cases e.symm.trans (this.2 e'.symm)
    -- 🎉 no goals
  · have := this.1 e
    -- ⊢ ↑r₂ + ↑d * _root_.bit1 ↑q = ↑n ∧ ↑r₂ < ↑d
    constructor
    -- ⊢ ↑r₂ + ↑d * _root_.bit1 ↑q = ↑n
    · rwa [_root_.bit1, add_comm _ 1, mul_add, mul_one, ← add_assoc, ← this]
      -- 🎉 no goals
    · rwa [this, two_mul, add_lt_add_iff_right] at h₂
      -- 🎉 no goals
#align pos_num.divmod_to_nat_aux PosNum.divMod_to_nat_aux

theorem divMod_to_nat (d n : PosNum) :
    (n / d : ℕ) = (divMod d n).1 ∧ (n % d : ℕ) = (divMod d n).2 := by
  rw [Nat.div_mod_unique (PosNum.cast_pos _)]
  -- ⊢ ↑(divMod d n).snd + ↑d * ↑(divMod d n).fst = ↑n ∧ ↑(divMod d n).snd < ↑d
  induction' n with n IH n IH
  · exact
      divMod_to_nat_aux (by simp) (Nat.mul_le_mul_left 2 (PosNum.cast_pos d : (0 : ℕ) < d))
  · unfold divMod
    -- ⊢ ↑(match divMod d n with
    -- Porting note: `cases'` didn't rewrite at `this`, so `revert` & `intro` are required.
    revert IH; cases' divMod d n with q r; intro IH
    -- ⊢ ↑(divMod d n).snd + ↑d * ↑(divMod d n).fst = ↑n ∧ ↑(divMod d n).snd < ↑d →
               -- ⊢ ↑(q, r).snd + ↑d * ↑(q, r).fst = ↑n ∧ ↑(q, r).snd < ↑d →
                                           -- ⊢ ↑(match (q, r) with
    simp only [divMod] at IH ⊢
    -- ⊢ ↑(divModAux d q (Num.bit1 r)).snd + ↑d * ↑(divModAux d q (Num.bit1 r)).fst = …
    apply divMod_to_nat_aux <;> simp
    -- ⊢ ↑(Num.bit1 r) + ↑d * _root_.bit0 ↑q = ↑(bit1 n)
                                -- ⊢ _root_.bit1 ↑r + ↑d * _root_.bit0 ↑q = _root_.bit1 ↑n
                                -- ⊢ _root_.bit1 ↑r < 2 * ↑d
    · rw [_root_.bit1, _root_.bit1, add_right_comm, bit0_eq_two_mul (n : ℕ), ← IH.1, mul_add, ←
        bit0_eq_two_mul, mul_left_comm, ← bit0_eq_two_mul]
    · rw [← bit0_eq_two_mul]
      -- ⊢ _root_.bit1 ↑r < _root_.bit0 ↑d
      exact Nat.bit1_lt_bit0 IH.2
      -- 🎉 no goals
  · unfold divMod
    -- ⊢ ↑(match divMod d n with
    -- Porting note: `cases'` didn't rewrite at `this`, so `revert` & `intro` are required.
    revert IH; cases' divMod d n with q r; intro IH
    -- ⊢ ↑(divMod d n).snd + ↑d * ↑(divMod d n).fst = ↑n ∧ ↑(divMod d n).snd < ↑d →
               -- ⊢ ↑(q, r).snd + ↑d * ↑(q, r).fst = ↑n ∧ ↑(q, r).snd < ↑d →
                                           -- ⊢ ↑(match (q, r) with
    simp only [divMod] at IH ⊢
    -- ⊢ ↑(divModAux d q (Num.bit0 r)).snd + ↑d * ↑(divModAux d q (Num.bit0 r)).fst = …
    apply divMod_to_nat_aux <;> simp
    -- ⊢ ↑(Num.bit0 r) + ↑d * _root_.bit0 ↑q = ↑(bit0 n)
                                -- ⊢ _root_.bit0 ↑r + ↑d * _root_.bit0 ↑q = _root_.bit0 ↑n
                                -- ⊢ _root_.bit0 ↑r < 2 * ↑d
    · rw [bit0_eq_two_mul (n : ℕ), ← IH.1, mul_add, ← bit0_eq_two_mul, mul_left_comm, ←
        bit0_eq_two_mul]
    · rw [← bit0_eq_two_mul]
      -- ⊢ _root_.bit0 ↑r < _root_.bit0 ↑d
      exact Nat.bit0_lt IH.2
      -- 🎉 no goals
#align pos_num.divmod_to_nat PosNum.divMod_to_nat

@[simp]
theorem div'_to_nat (n d) : (div' n d : ℕ) = n / d :=
  (divMod_to_nat _ _).1.symm
#align pos_num.div'_to_nat PosNum.div'_to_nat

@[simp]
theorem mod'_to_nat (n d) : (mod' n d : ℕ) = n % d :=
  (divMod_to_nat _ _).2.symm
#align pos_num.mod'_to_nat PosNum.mod'_to_nat

end PosNum

namespace Num

@[simp]
protected theorem div_zero (n : Num) : n / 0 = 0 :=
  show n.div 0 = 0 by
    cases n
    -- ⊢ div zero 0 = 0
    · rfl
      -- 🎉 no goals
    · simp [Num.div]
      -- 🎉 no goals
#align num.div_zero Num.div_zero

@[simp, norm_cast]
theorem div_to_nat : ∀ n d, ((n / d : Num) : ℕ) = n / d
  | 0, 0 => by simp
               -- 🎉 no goals
  | 0, pos d => (Nat.zero_div _).symm
  | pos n, 0 => (Nat.div_zero _).symm
  | pos n, pos d => PosNum.div'_to_nat _ _
#align num.div_to_nat Num.div_to_nat

@[simp]
protected theorem mod_zero (n : Num) : n % 0 = n :=
  show n.mod 0 = n by
    cases n
    -- ⊢ mod zero 0 = zero
    · rfl
      -- 🎉 no goals
    · simp [Num.mod]
      -- 🎉 no goals
#align num.mod_zero Num.mod_zero

@[simp, norm_cast]
theorem mod_to_nat : ∀ n d, ((n % d : Num) : ℕ) = n % d
  | 0, 0 => by simp
               -- 🎉 no goals
  | 0, pos d => (Nat.zero_mod _).symm
  | pos n, 0 => (Nat.mod_zero _).symm
  | pos n, pos d => PosNum.mod'_to_nat _ _
#align num.mod_to_nat Num.mod_to_nat

theorem gcd_to_nat_aux :
    ∀ {n} {a b : Num}, a ≤ b → (a * b).natSize ≤ n → (gcdAux n a b : ℕ) = Nat.gcd a b
  | 0, 0, b, _ab, _h => (Nat.gcd_zero_left _).symm
  | 0, pos a, 0, ab, _h => (not_lt_of_ge ab).elim rfl
  | 0, pos a, pos b, _ab, h => (not_lt_of_le h).elim <| PosNum.natSize_pos _
  | Nat.succ n, 0, b, _ab, _h => (Nat.gcd_zero_left _).symm
  | Nat.succ n, pos a, b, ab, h => by
    simp [gcdAux]
    -- ⊢ ↑(gcdAux n (b % pos a) (pos a)) = Nat.gcd ↑a ↑b
    rw [Nat.gcd_rec, gcd_to_nat_aux, mod_to_nat]
    · rfl
      -- 🎉 no goals
    · rw [← le_to_nat, mod_to_nat]
      -- ⊢ ↑b % ↑(pos a) ≤ ↑(pos a)
      exact le_of_lt (Nat.mod_lt _ (PosNum.cast_pos _))
      -- 🎉 no goals
    rw [natSize_to_nat, mul_to_nat, Nat.size_le] at h ⊢
    -- ⊢ ↑(b % pos a) * ↑(pos a) < 2 ^ n
    rw [mod_to_nat, mul_comm]
    -- ⊢ ↑(pos a) * (↑b % ↑(pos a)) < 2 ^ n
    rw [pow_succ', ← Nat.mod_add_div b (pos a)] at h
    -- ⊢ ↑(pos a) * (↑b % ↑(pos a)) < 2 ^ n
    refine' lt_of_mul_lt_mul_right (lt_of_le_of_lt _ h) (Nat.zero_le 2)
    -- ⊢ ↑(pos a) * (↑b % ↑(pos a)) * 2 ≤ ↑(pos a) * (↑b % ↑(pos a) + ↑(pos a) * (↑b  …
    rw [mul_two, mul_add]
    -- ⊢ ↑(pos a) * (↑b % ↑(pos a)) + ↑(pos a) * (↑b % ↑(pos a)) ≤ ↑(pos a) * (↑b % ↑ …
    refine'
      add_le_add_left
        (Nat.mul_le_mul_left _ (le_trans (le_of_lt (Nat.mod_lt _ (PosNum.cast_pos _))) _)) _
    suffices : 1 ≤ _; simpa using Nat.mul_le_mul_left (pos a) this
    -- ⊢ ↑a ≤ ↑(pos a) * (↑b / ↑(pos a))
                      -- ⊢ 1 ≤ ↑b / ↑a
    rw [Nat.le_div_iff_mul_le a.cast_pos, one_mul]
    -- ⊢ ↑a ≤ ↑b
    exact le_to_nat.2 ab
    -- 🎉 no goals
#align num.gcd_to_nat_aux Num.gcd_to_nat_aux

@[simp]
theorem gcd_to_nat : ∀ a b, (gcd a b : ℕ) = Nat.gcd a b := by
  have : ∀ a b : Num, (a * b).natSize ≤ a.natSize + b.natSize := by
    intros
    simp [natSize_to_nat]
    rw [Nat.size_le, pow_add]
    exact mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _) (Nat.zero_le _) (Nat.zero_le _)
  intros
  -- ⊢ ↑(gcd a✝ b✝) = Nat.gcd ↑a✝ ↑b✝
  unfold gcd
  -- ⊢ ↑(if a✝ ≤ b✝ then gcdAux (natSize a✝ + natSize b✝) a✝ b✝ else gcdAux (natSiz …
  split_ifs with h
  -- ⊢ ↑(gcdAux (natSize a✝ + natSize b✝) a✝ b✝) = Nat.gcd ↑a✝ ↑b✝
  · exact gcd_to_nat_aux h (this _ _)
    -- 🎉 no goals
  · rw [Nat.gcd_comm]
    -- ⊢ ↑(gcdAux (natSize b✝ + natSize a✝) b✝ a✝) = Nat.gcd ↑b✝ ↑a✝
    exact gcd_to_nat_aux (le_of_not_le h) (this _ _)
    -- 🎉 no goals
#align num.gcd_to_nat Num.gcd_to_nat

theorem dvd_iff_mod_eq_zero {m n : Num} : m ∣ n ↔ n % m = 0 := by
  rw [← dvd_to_nat, Nat.dvd_iff_mod_eq_zero, ← to_nat_inj, mod_to_nat]; rfl
  -- ⊢ ↑n % ↑m = 0 ↔ ↑n % ↑m = ↑0
                                                                        -- 🎉 no goals
#align num.dvd_iff_mod_eq_zero Num.dvd_iff_mod_eq_zero

instance decidableDvd : DecidableRel ((· ∣ ·) : Num → Num → Prop)
  | _a, _b => decidable_of_iff' _ dvd_iff_mod_eq_zero
#align num.decidable_dvd Num.decidableDvd

end Num

instance PosNum.decidableDvd : DecidableRel ((· ∣ ·) : PosNum → PosNum → Prop)
  | _a, _b => Num.decidableDvd _ _
#align pos_num.decidable_dvd PosNum.decidableDvd

namespace ZNum

@[simp]
protected theorem div_zero (n : ZNum) : n / 0 = 0 :=
  show n.div 0 = 0 by cases n <;> rfl
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
#align znum.div_zero ZNum.div_zero

@[simp, norm_cast]
theorem div_to_int : ∀ n d, ((n / d : ZNum) : ℤ) = n / d
  | 0, 0 => by simp [Int.ediv_zero]
               -- 🎉 no goals
  | 0, pos d => (Int.zero_ediv _).symm
  | 0, neg d => (Int.zero_ediv _).symm
  | pos n, 0 => (Int.ediv_zero _).symm
  | neg n, 0 => (Int.ediv_zero _).symm
  | pos n, pos d => (Num.cast_toZNum _).trans <| by rw [← Num.to_nat_to_int]; simp
                                                    -- ⊢ ↑↑(PosNum.div' n d) = ↑(pos n) / ↑(pos d)
                                                                              -- 🎉 no goals
  | pos n, neg d => (Num.cast_toZNumNeg _).trans <| by rw [← Num.to_nat_to_int]; simp
                                                       -- ⊢ -↑↑(PosNum.div' n d) = ↑(pos n) / ↑(neg d)
                                                                                 -- 🎉 no goals
  | neg n, pos d =>
    show -_ = -_ / ↑d by
      rw [n.to_int_eq_succ_pred, d.to_int_eq_succ_pred, ← PosNum.to_nat_to_int, Num.succ'_to_nat,
        Num.div_to_nat]
      change -[n.pred' / ↑d+1] = -[n.pred' / (d.pred' + 1)+1]
      -- ⊢ -[↑(PosNum.pred' n) / ↑d+1] = -[↑(PosNum.pred' n) / (↑(PosNum.pred' d) + 1)+1]
      rw [d.to_nat_eq_succ_pred]
      -- 🎉 no goals
  | neg n, neg d =>
    show ↑(PosNum.pred' n / Num.pos d).succ' = -_ / -↑d by
      rw [n.to_int_eq_succ_pred, d.to_int_eq_succ_pred, ← PosNum.to_nat_to_int, Num.succ'_to_nat,
        Num.div_to_nat]
      change (Nat.succ (_ / d) : ℤ) = Nat.succ (n.pred' / (d.pred' + 1))
      -- ⊢ ↑(Nat.succ (↑(PosNum.pred' n) / ↑d)) = ↑(Nat.succ (↑(PosNum.pred' n) / (↑(Po …
      rw [d.to_nat_eq_succ_pred]
      -- 🎉 no goals
#align znum.div_to_int ZNum.div_to_int

@[simp, norm_cast]
theorem mod_to_int : ∀ n d, ((n % d : ZNum) : ℤ) = n % d
  | 0, d => (Int.zero_emod _).symm
  | pos n, d =>
    (Num.cast_toZNum _).trans <| by
      rw [← Num.to_nat_to_int, cast_pos, Num.mod_to_nat, ← PosNum.to_nat_to_int, abs_to_nat]
      -- ⊢ ↑(↑(Num.pos n) % natAbs ↑d) = ↑↑n % ↑d
      rfl
      -- 🎉 no goals
  | neg n, d =>
    (Num.cast_sub' _ _).trans <| by
      rw [← Num.to_nat_to_int, cast_neg, ← Num.to_nat_to_int, Num.succ_to_nat, Num.mod_to_nat,
          abs_to_nat, ← Int.subNatNat_eq_coe, n.to_int_eq_succ_pred]
      rfl
      -- 🎉 no goals
#align znum.mod_to_int ZNum.mod_to_int

@[simp]
theorem gcd_to_nat (a b) : (gcd a b : ℕ) = Int.gcd a b :=
  (Num.gcd_to_nat _ _).trans <| by simp; rfl
                                   -- ⊢ Nat.gcd (natAbs ↑a) (natAbs ↑b) = Int.gcd ↑a ↑b
                                         -- 🎉 no goals
#align znum.gcd_to_nat ZNum.gcd_to_nat

theorem dvd_iff_mod_eq_zero {m n : ZNum} : m ∣ n ↔ n % m = 0 := by
  rw [← dvd_to_int, Int.dvd_iff_emod_eq_zero, ← to_int_inj, mod_to_int]; rfl
  -- ⊢ ↑n % ↑m = 0 ↔ ↑n % ↑m = ↑0
                                                                         -- 🎉 no goals
#align znum.dvd_iff_mod_eq_zero ZNum.dvd_iff_mod_eq_zero

instance decidableDvd : DecidableRel ((· ∣ ·) : ZNum → ZNum → Prop)
  | _a, _b => decidable_of_iff' _ dvd_iff_mod_eq_zero
#align znum.has_dvd.dvd.decidable_rel ZNum.decidableDvd

end ZNum

namespace Int

/-- Cast a `SNum` to the corresponding integer. -/
def ofSnum : SNum → ℤ :=
  SNum.rec' (fun a => cond a (-1) 0) fun a _p IH => cond a (bit1 IH) (bit0 IH)
#align int.of_snum Int.ofSnum

instance snumCoe : Coe SNum ℤ :=
  ⟨ofSnum⟩
#align int.snum_coe Int.snumCoe

end Int

instance SNum.lt : LT SNum :=
  ⟨fun a b => (a : ℤ) < b⟩
#align snum.has_lt SNum.lt

instance SNum.le : LE SNum :=
  ⟨fun a b => (a : ℤ) ≤ b⟩
#align snum.has_le SNum.le
