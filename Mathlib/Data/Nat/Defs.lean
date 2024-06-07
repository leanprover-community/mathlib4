/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.GCongr.Core
import Mathlib.Tactic.PushNeg
import Mathlib.Util.AssertExists

#align_import data.nat.basic from "leanprover-community/mathlib"@"bd835ef554f37ef9b804f0903089211f89cb370b"
#align_import data.nat.sqrt from "leanprover-community/mathlib"@"ba2245edf0c8bb155f1569fd9b9492a9b384cde6"

/-!
# Basic operations on the natural numbers

This file contains:
* some basic lemmas about natural numbers
* extra recursors:
  * `leRecOn`, `le_induction`: recursion and induction principles starting at non-zero numbers
  * `decreasing_induction`: recursion growing downwards
  * `le_rec_on'`, `decreasing_induction'`: versions with slightly weaker assumptions
  * `strong_rec'`: recursion based on strong inequalities
* decidability instances on predicates about the natural numbers

See note [foundational algebra order theory].

## TODO

Split this file into:
* `Data.Nat.Init` (or maybe `Data.Nat.Batteries`?) for lemmas that could go to Batteries
* `Data.Nat.Basic` for the lemmas that require mathlib definitions
-/

library_note "foundational algebra order theory"/--
Batteries has a home-baked development of the algebraic and order theoretic theory of `ℕ` and `ℤ
which, in particular, is not typeclass-mediated. This is useful to set up the algebra and finiteness
libraries in mathlib (naturals and integers show up as indices/offsets in lists, cardinality in
finsets, powers in groups, ...).

Less basic uses of `ℕ` and `ℤ` should however use the typeclass-mediated development.

The relevant files are:
* `Data.Nat.Defs` for the continuation of the home-baked development on `ℕ`
* `Data.Int.Defs` for the continuation of the home-baked development on `ℤ`
* `Algebra.Group.Nat` for the monoid instances on `ℕ`
* `Algebra.Group.Int` for the group instance on `ℤ`
* `Algebra.Ring.Nat` for the semiring instance on `ℕ`
* `Algebra.Ring.Int` for the ring instance on `ℤ`
* `Algebra.Order.Group.Nat` for the ordered monoid instance on `ℕ`
* `Algebra.Order.Group.Int` for the ordered group instance on `ℤ`
* `Algebra.Order.Ring.Nat` for the ordered semiring instance on `ℕ`
* `Algebra.Order.Ring.Int` for the ordered ring instance on `ℤ`
-/

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid

open Function

namespace Nat
variable {a b c d m n k : ℕ} {p q : ℕ → Prop}

-- TODO: Move the `LinearOrder ℕ` instance to `Order.Nat` (#13092).
instance instLinearOrder : LinearOrder ℕ where
  le := Nat.le
  le_refl := @Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  lt := Nat.lt
  lt_iff_le_not_le := @Nat.lt_iff_le_not_le
  decidableLT := inferInstance
  decidableLE := inferInstance
  decidableEq := inferInstance
#align nat.linear_order Nat.instLinearOrder

instance instNontrivial : Nontrivial ℕ := ⟨⟨0, 1, Nat.zero_ne_one⟩⟩

@[simp] theorem default_eq_zero : default = 0 := rfl

attribute [gcongr] Nat.succ_le_succ
attribute [simp] Nat.not_lt_zero Nat.succ_ne_zero Nat.succ_ne_self Nat.zero_ne_one Nat.one_ne_zero
  Nat.min_eq_left Nat.min_eq_right Nat.max_eq_left Nat.max_eq_right
  -- Nat.zero_ne_bit1 Nat.bit1_ne_zero Nat.bit0_ne_one Nat.one_ne_bit0 Nat.bit0_ne_bit1
  -- Nat.bit1_ne_bit0

attribute [simp] Nat.min_eq_left Nat.min_eq_right

/-! ### `succ`, `pred` -/

lemma succ_pos' : 0 < succ n := succ_pos n
#align nat.succ_pos' Nat.succ_pos'

alias succ_inj := succ_inj'
#align nat.succ_inj' Nat.succ_inj

lemma succ_injective : Injective Nat.succ := @succ.inj
#align nat.succ_injective Nat.succ_injective

lemma succ_ne_succ : succ m ≠ succ n ↔ m ≠ n := succ_injective.ne_iff
#align nat.succ_ne_succ Nat.succ_ne_succ

-- Porting note: no longer a simp lemma, as simp can prove this
lemma succ_succ_ne_one (n : ℕ) : n.succ.succ ≠ 1 := by simp
#align nat.succ_succ_ne_one Nat.succ_succ_ne_one

lemma one_lt_succ_succ (n : ℕ) : 1 < n.succ.succ := succ_lt_succ <| succ_pos n
#align nat.one_lt_succ_succ Nat.one_lt_succ_succ

-- Moved to Batteries
#align nat.succ_le_succ_iff Nat.succ_le_succ_iff
#align nat.succ_lt_succ_iff Nat.succ_lt_succ_iff
#align nat.le_pred_of_lt Nat.le_pred_of_lt
#align nat.max_succ_succ Nat.succ_max_succ

alias _root_.LT.lt.nat_succ_le := succ_le_of_lt
#align has_lt.lt.nat_succ_le LT.lt.nat_succ_le

lemma not_succ_lt_self : ¬ succ n < n := Nat.not_lt_of_ge n.le_succ
#align nat.not_succ_lt_self Nat.not_succ_lt_self

#align nat.lt_succ_iff Nat.lt_succ_iff

lemma succ_le_iff : succ m ≤ n ↔ m < n := ⟨lt_of_succ_le, succ_le_of_lt⟩
#align nat.succ_le_iff Nat.succ_le_iff

lemma le_succ_iff : m ≤ n.succ ↔ m ≤ n ∨ m = n.succ := by
  refine ⟨fun hmn ↦ (Nat.lt_or_eq_of_le hmn).imp_left le_of_lt_succ, ?_⟩
  rintro (hmn | rfl)
  · exact le_succ_of_le hmn
  · exact Nat.le_refl _

alias ⟨of_le_succ, _⟩ := le_succ_iff
#align nat.of_le_succ Nat.of_le_succ

#align nat.lt_succ_iff_lt_or_eq Nat.lt_succ_iff_lt_or_eq
#align nat.eq_of_lt_succ_of_not_lt Nat.eq_of_lt_succ_of_not_lt
#align nat.eq_of_le_of_lt_succ Nat.eq_of_le_of_lt_succ

lemma lt_iff_le_pred : ∀ {n}, 0 < n → (m < n ↔ m ≤ n - 1) | _ + 1, _ => Nat.lt_succ_iff
#align nat.lt_iff_le_pred Nat.lt_iff_le_pred

lemma le_of_pred_lt : ∀ {m}, pred m < n → m ≤ n
  | 0 => Nat.le_of_lt
  | _ + 1 => id
#align nat.le_of_pred_lt Nat.le_of_pred_lt

lemma lt_iff_add_one_le : m < n ↔ m + 1 ≤ n := by rw [succ_le_iff]
#align nat.lt_iff_add_one_le Nat.lt_iff_add_one_le

-- Just a restatement of `Nat.lt_succ_iff` using `+1`.
lemma lt_add_one_iff : m < n + 1 ↔ m ≤ n := Nat.lt_succ_iff
#align nat.lt_add_one_iff Nat.lt_add_one_iff

-- A flipped version of `lt_add_one_iff`.
lemma lt_one_add_iff : m < 1 + n ↔ m ≤ n := by simp only [Nat.add_comm, Nat.lt_succ_iff]
#align nat.lt_one_add_iff Nat.lt_one_add_iff

-- This is true reflexively, by the definition of `≤` on ℕ,
-- but it's still useful to have, to convince Lean to change the syntactic type.
lemma add_one_le_iff : m + 1 ≤ n ↔ m < n := Iff.rfl
#align nat.add_one_le_iff Nat.add_one_le_iff

lemma one_add_le_iff : 1 + m ≤ n ↔ m < n := by simp only [Nat.add_comm, add_one_le_iff]
#align nat.one_add_le_iff Nat.one_add_le_iff

lemma one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 := Nat.pos_iff_ne_zero
#align nat.one_le_iff_ne_zero Nat.one_le_iff_ne_zero

lemma one_lt_iff_ne_zero_and_ne_one : ∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by omega
#align nat.one_lt_iff_ne_zero_and_ne_one Nat.one_lt_iff_ne_zero_and_ne_one

lemma le_one_iff_eq_zero_or_eq_one : ∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1 := by simp [le_succ_iff]

@[simp] lemma lt_one_iff : n < 1 ↔ n = 0 := Nat.lt_succ_iff.trans $ by rw [le_zero_eq]
#align nat.lt_one_iff Nat.lt_one_iff

lemma one_le_of_lt (h : a < b) : 1 ≤ b := Nat.lt_of_le_of_lt (Nat.zero_le _) h
#align nat.one_le_of_lt Nat.one_le_of_lt

@[simp] lemma min_eq_zero_iff : min m n = 0 ↔ m = 0 ∨ n = 0 := by omega
@[simp] lemma max_eq_zero_iff : max m n = 0 ↔ m = 0 ∧ n = 0 := by omega
#align nat.min_eq_zero_iff Nat.min_eq_zero_iff
#align nat.max_eq_zero_iff Nat.max_eq_zero_iff

-- Moved to Batteries
#align nat.succ_eq_one_add Nat.succ_eq_one_add
#align nat.one_add Nat.one_add
#align nat.zero_max Nat.zero_max

#align nat.pred_eq_sub_one Nat.pred_eq_sub_one

lemma pred_one_add (n : ℕ) : pred (1 + n) = n := by rw [Nat.add_comm, add_one, Nat.pred_succ]
#align nat.pred_one_add Nat.pred_one_add

lemma pred_eq_self_iff : n.pred = n ↔ n = 0 := by cases n <;> simp [(Nat.succ_ne_self _).symm]
#align nat.pred_eq_self_iff Nat.pred_eq_self_iff

lemma pred_eq_of_eq_succ (H : m = n.succ) : m.pred = n := by simp [H]
#align nat.pred_eq_of_eq_succ Nat.pred_eq_of_eq_succ

@[simp] lemma pred_eq_succ_iff : n - 1 = m + 1 ↔ n = m + 2 := by
  cases n <;> constructor <;> rintro ⟨⟩ <;> rfl
#align nat.pred_eq_succ_iff Nat.pred_eq_succ_iff

-- Porting note: this doesn't work as a simp lemma in Lean 4
lemma and_forall_succ : p 0 ∧ (∀ n, p (n + 1)) ↔ ∀ n, p n :=
  ⟨fun h n ↦ Nat.casesOn n h.1 h.2, fun h ↦ ⟨h _, fun _ ↦ h _⟩⟩
#align nat.and_forall_succ Nat.and_forall_succ

-- Porting note: this doesn't work as a simp lemma in Lean 4
lemma or_exists_succ : p 0 ∨ (∃ n, p (n + 1)) ↔ ∃ n, p n :=
  ⟨fun h ↦ h.elim (fun h0 ↦ ⟨0, h0⟩) fun ⟨n, hn⟩ ↦ ⟨n + 1, hn⟩, by
    rintro ⟨_ | n, hn⟩
    exacts [Or.inl hn, Or.inr ⟨n, hn⟩]⟩
#align nat.or_exists_succ Nat.or_exists_succ

lemma forall_lt_succ : (∀ m < n + 1, p m) ↔ (∀ m < n, p m) ∧ p n := by
  simp only [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq, or_comm, forall_eq_or_imp, and_comm]
#align nat.forall_lt_succ Nat.forall_lt_succ

lemma exists_lt_succ : (∃ m < n + 1, p m) ↔ (∃ m < n, p m) ∨ p n := by
  rw [← not_iff_not]
  push_neg
  exact forall_lt_succ
#align nat.exists_lt_succ Nat.exists_lt_succ

lemma two_lt_of_ne : ∀ {n}, n ≠ 0 → n ≠ 1 → n ≠ 2 → 2 < n
  | 0, h, _, _ => (h rfl).elim
  | 1, _, h, _ => (h rfl).elim
  | 2, _, _, h => (h rfl).elim
  -- Porting note: was `by decide`
  | n + 3, _, _, _ => le_add_left 3 n
#align nat.two_lt_of_ne Nat.two_lt_of_ne

/-! ### `pred` -/

@[simp] lemma add_succ_sub_one (m n : ℕ) : m + succ n - 1 = m + n := rfl
#align nat.add_succ_sub_one Nat.add_succ_sub_one

@[simp]
lemma succ_add_sub_one (n m : ℕ) : succ m + n - 1 = m + n := by rw [succ_add, Nat.add_one_sub_one]
#align nat.succ_add_sub_one Nat.succ_add_sub_one

lemma pred_sub (n m : ℕ) : pred n - m = pred (n - m) := by
  rw [← Nat.sub_one, Nat.sub_sub, one_add, sub_succ]
#align nat.pred_sub Nat.pred_sub

lemma self_add_sub_one : ∀ n, n + (n - 1) = 2 * n - 1
  | 0 => rfl
  | n + 1 => by rw [Nat.two_mul]; exact (add_succ_sub_one (Nat.succ _) _).symm

lemma sub_one_add_self (n : ℕ) : (n - 1) + n = 2 * n - 1 := Nat.add_comm _ n ▸ self_add_sub_one n

lemma self_add_pred (n : ℕ) : n + pred n = (2 * n).pred := self_add_sub_one n
lemma pred_add_self (n : ℕ) : pred n + n = (2 * n).pred := sub_one_add_self n

lemma pred_le_iff : pred m ≤ n ↔ m ≤ succ n :=
  ⟨le_succ_of_pred_le, by cases m; exacts [fun _ ↦ zero_le n, le_of_succ_le_succ]⟩
#align nat.pred_le_iff Nat.pred_le_iff

lemma lt_of_lt_pred (h : m < n - 1) : m < n := by omega
#align nat.lt_of_lt_pred Nat.lt_of_lt_pred

lemma le_add_pred_of_pos (a : ℕ) (hb : b ≠ 0) : a ≤ b + (a - 1) := by omega
#align nat.le_add_pred_of_pos Nat.le_add_pred_of_pos

/-! ### `add` -/

#align nat.add_pos_left Nat.add_pos_left
#align nat.add_pos_right Nat.add_pos_right
#align nat.exists_eq_add_of_le Nat.exists_eq_add_of_le
#align nat.exists_eq_add_of_le' Nat.exists_eq_add_of_le'
#align nat.exists_eq_add_of_lt Nat.exists_eq_add_of_lt

attribute [simp] le_add_left le_add_right Nat.lt_add_left_iff_pos Nat.lt_add_right_iff_pos
  Nat.add_le_add_iff_left Nat.add_le_add_iff_right Nat.add_lt_add_iff_left Nat.add_lt_add_iff_right
  not_lt_zero

-- We want to use these two lemmas earlier than the lemmas simp can prove them with
@[simp, nolint simpNF] protected alias add_left_inj := Nat.add_right_cancel_iff
@[simp, nolint simpNF] protected alias add_right_inj := Nat.add_left_cancel_iff

-- Sometimes a bare `Nat.add` or similar appears as a consequence of unfolding during pattern
-- matching. These lemmas package them back up as typeclass mediated operations.
-- TODO: This is a duplicate of `Nat.add_eq`
@[simp] lemma add_def : Nat.add m n = m + n := rfl
#align nat.add_def Nat.add_def

-- We want to use these two lemmas earlier than the lemmas simp can prove them with
@[simp, nolint simpNF] protected lemma add_eq_left : a + b = a ↔ b = 0 := by omega
@[simp, nolint simpNF] protected lemma add_eq_right : a + b = b ↔ a = 0 := by omega

lemma two_le_iff : ∀ n, 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp
#align nat.two_le_iff Nat.two_le_iff

lemma add_eq_max_iff : m + n = max m n ↔ m = 0 ∨ n = 0 := by omega
lemma add_eq_min_iff : m + n = min m n ↔ m = 0 ∧ n = 0 := by omega
#align nat.add_eq_max_iff Nat.add_eq_max_iff
#align nat.add_eq_min_iff Nat.add_eq_min_iff

-- We want to use this lemma earlier than the lemma simp can prove it with
@[simp, nolint simpNF] protected lemma add_eq_zero : m + n = 0 ↔ m = 0 ∧ n = 0 := by omega

lemma add_pos_iff_pos_or_pos : 0 < m + n ↔ 0 < m ∨ 0 < n := by omega
#align nat.add_pos_iff_pos_or_pos Nat.add_pos_iff_pos_or_pos

lemma add_eq_one_iff : m + n = 1 ↔ m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 := by
  cases n <;> simp [succ_eq_add_one, ← Nat.add_assoc, succ_inj']
#align nat.add_eq_one_iff Nat.add_eq_one_iff

lemma add_eq_two_iff : m + n = 2 ↔ m = 0 ∧ n = 2 ∨ m = 1 ∧ n = 1 ∨ m = 2 ∧ n = 0 := by
  omega
#align nat.add_eq_two_iff Nat.add_eq_two_iff

lemma add_eq_three_iff :
    m + n = 3 ↔ m = 0 ∧ n = 3 ∨ m = 1 ∧ n = 2 ∨ m = 2 ∧ n = 1 ∨ m = 3 ∧ n = 0 := by
  omega
#align nat.add_eq_three_iff Nat.add_eq_three_iff

lemma le_add_one_iff : m ≤ n + 1 ↔ m ≤ n ∨ m = n + 1 := by
  rw [Nat.le_iff_lt_or_eq, lt_add_one_iff]
#align nat.le_add_one_iff Nat.le_add_one_iff

lemma le_and_le_add_one_iff : n ≤ m ∧ m ≤ n + 1 ↔ m = n ∨ m = n + 1 := by
  rw [le_add_one_iff, and_or_left, ← Nat.le_antisymm_iff, eq_comm, and_iff_right_of_imp]
  rintro rfl
  exact n.le_succ
#align nat.le_and_le_add_one_iff Nat.le_and_le_add_one_iff

lemma add_succ_lt_add (hab : a < b) (hcd : c < d) : a + c + 1 < b + d := by
  rw [Nat.add_assoc]; exact Nat.add_lt_add_of_lt_of_le hab (Nat.succ_le_iff.2 hcd)
#align nat.add_succ_lt_add Nat.add_succ_lt_add

theorem le_or_le_of_add_eq_add_pred (h : a + c = b + d - 1) : b ≤ a ∨ d ≤ c := by
  rcases le_or_lt b a with h' | h' <;> [left; right]
  · exact h'
  · replace h' := Nat.add_lt_add_right h' c
    rw [h] at h'
    rcases d.eq_zero_or_pos with hn | hn
    · rw [hn]
      exact zero_le c
    rw [d.add_sub_assoc (Nat.succ_le_of_lt hn), Nat.add_lt_add_iff_left] at h'
    exact Nat.le_of_pred_lt h'
#align nat.le_or_le_of_add_eq_add_pred Nat.le_or_le_of_add_eq_add_pred

/-! ### `sub` -/

attribute [simp] Nat.sub_eq_zero_of_le Nat.sub_le_iff_le_add Nat.add_sub_cancel_left
  Nat.add_sub_cancel_right

/-- A version of `Nat.sub_succ` in the form `_ - 1` instead of `Nat.pred _`. -/
lemma sub_succ' (m n : ℕ) : m - n.succ = m - n - 1 := rfl
#align nat.sub_succ' Nat.sub_succ'

protected lemma sub_eq_of_eq_add' (h : a = b + c) : a - b = c := by rw [h, Nat.add_sub_cancel_left]
protected lemma eq_sub_of_add_eq (h : c + b = a) : c = a - b := (Nat.sub_eq_of_eq_add h.symm).symm
protected lemma eq_sub_of_add_eq' (h : b + c = a) : c = a - b := (Nat.sub_eq_of_eq_add' h.symm).symm

protected lemma lt_sub_iff_add_lt : a < c - b ↔ a + b < c := ⟨add_lt_of_lt_sub, lt_sub_of_add_lt⟩
protected lemma lt_sub_iff_add_lt' : a < c - b ↔ b + a < c := by omega
protected lemma sub_lt_iff_lt_add (hba : b ≤ a) : a - b < c ↔ a < b + c := by omega
protected lemma sub_lt_iff_lt_add' (hba : b ≤ a) : a - b < c ↔ a < c + b := by omega

protected lemma sub_sub_sub_cancel_right (h : c ≤ b) : a - c - (b - c) = a - b := by omega
protected lemma add_sub_sub_cancel (h : c ≤ a) : a + b - (a - c) = b + c := by omega
protected lemma sub_add_sub_cancel (hab : b ≤ a) (hcb : c ≤ b) : a - b + (b - c) = a - c := by omega

lemma lt_pred_iff : a < pred b ↔ succ a < b := Nat.lt_sub_iff_add_lt (b := 1)
#align nat.lt_pred_iff Nat.lt_pred_iff

protected lemma sub_lt_sub_iff_right (h : c ≤ a) : a - c < b - c ↔ a < b := by omega

/-! ### `mul` -/

#align nat.mul_ne_zero Nat.mul_ne_zero
#align nat.mul_eq_zero Nat.mul_eq_zero
#align nat.eq_of_mul_eq_mul_right Nat.eq_of_mul_eq_mul_right
#align nat.le_mul_of_pos_left Nat.le_mul_of_pos_left
#align nat.le_mul_of_pos_right Nat.le_mul_of_pos_right

@[simp] lemma mul_def : Nat.mul m n = m * n := rfl
#align nat.mul_def Nat.mul_def

-- Porting note: removing `simp` attribute
protected lemma zero_eq_mul : 0 = m * n ↔ m = 0 ∨ n = 0 := by rw [eq_comm, Nat.mul_eq_zero]
#align nat.zero_eq_mul Nat.zero_eq_mul

lemma two_mul_ne_two_mul_add_one : 2 * n ≠ 2 * m + 1 :=
  mt (congrArg (· % 2))
    (by rw [Nat.add_comm, add_mul_mod_self_left, mul_mod_right, mod_eq_of_lt] <;> simp)
#align nat.two_mul_ne_two_mul_add_one Nat.two_mul_ne_two_mul_add_one

-- TODO: Replace `Nat.mul_right_cancel_iff` with `Nat.mul_left_inj`
protected lemma mul_left_inj (ha : a ≠ 0) : b * a = c * a ↔ b = c :=
  Nat.mul_right_cancel_iff (Nat.pos_iff_ne_zero.2 ha) _ _

-- TODO: Replace `Nat.mul_left_cancel_iff` with `Nat.mul_right_inj`
protected lemma mul_right_inj (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  Nat.mul_left_cancel_iff (Nat.pos_iff_ne_zero.2 ha) _ _

protected lemma mul_ne_mul_left (ha : a ≠ 0) : b * a ≠ c * a ↔ b ≠ c :=
  not_congr (Nat.mul_left_inj ha)
#align nat.mul_ne_mul_left Nat.mul_ne_mul_left

protected lemma mul_ne_mul_right (ha : a ≠ 0) : a * b ≠ a * c ↔ b ≠ c :=
  not_congr (Nat.mul_right_inj ha)
#align nat.mul_ne_mul_right Nat.mul_ne_mul_right

lemma mul_eq_left (ha : a ≠ 0) : a * b = a ↔ b = 1 := by simpa using Nat.mul_right_inj ha (c := 1)
lemma mul_eq_right (hb : b ≠ 0) : a * b = b ↔ a = 1 := by simpa using Nat.mul_left_inj hb (c := 1)

-- TODO: Deprecate
lemma mul_right_eq_self_iff (ha : 0 < a) : a * b = a ↔ b = 1 := mul_eq_left $ ne_of_gt ha
#align nat.mul_right_eq_self_iff Nat.mul_right_eq_self_iff

lemma mul_left_eq_self_iff (hb : 0 < b) : a * b = b ↔ a = 1 := mul_eq_right $ ne_of_gt hb
#align nat.mul_left_eq_self_iff Nat.mul_left_eq_self_iff

protected lemma le_of_mul_le_mul_right (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b :=
  Nat.le_of_mul_le_mul_left (by simpa [Nat.mul_comm]) hc

set_option push_neg.use_distrib true in
/-- The product of two natural numbers is greater than 1 if and only if
  at least one of them is greater than 1 and both are positive. -/
lemma one_lt_mul_iff : 1 < m * n ↔ 0 < m ∧ 0 < n ∧ (1 < m ∨ 1 < n) := by
  constructor <;> intro h
  · by_contra h'; push_neg at h'; simp [Nat.le_zero] at h'
    obtain rfl | rfl | h' := h'
    · simp at h
    · simp at h
    · exact Nat.not_lt_of_le (Nat.mul_le_mul h'.1 h'.2) h
  · obtain hm | hn := h.2.2
    · exact Nat.mul_lt_mul_of_lt_of_le' hm h.2.1 Nat.zero_lt_one
    · exact Nat.mul_lt_mul_of_le_of_lt h.1 hn h.1

lemma eq_one_of_mul_eq_one_right (H : m * n = 1) : m = 1 := eq_one_of_dvd_one ⟨n, H.symm⟩
#align nat.eq_one_of_mul_eq_one_right Nat.eq_one_of_mul_eq_one_right

lemma eq_one_of_mul_eq_one_left (H : m * n = 1) : n = 1 :=
  eq_one_of_mul_eq_one_right (by rwa [Nat.mul_comm])
#align nat.eq_one_of_mul_eq_one_left Nat.eq_one_of_mul_eq_one_left

@[simp] protected lemma lt_mul_iff_one_lt_left (hb : 0 < b) : b < a * b ↔ 1 < a := by
  simpa using Nat.mul_lt_mul_right (b := 1) hb

@[simp] protected lemma lt_mul_iff_one_lt_right (ha : 0 < a) : a < a * b ↔ 1 < b := by
  simpa using Nat.mul_lt_mul_left (b := 1) ha

lemma eq_zero_of_double_le (h : 2 * n ≤ n) : n = 0 := by omega
#align nat.eq_zero_of_double_le Nat.eq_zero_of_double_le

lemma eq_zero_of_mul_le (hb : 2 ≤ n) (h : n * m ≤ m) : m = 0 :=
  eq_zero_of_double_le <| Nat.le_trans (Nat.mul_le_mul_right _ hb) h
#align nat.eq_zero_of_mul_le Nat.eq_zero_of_mul_le

lemma succ_mul_pos (m : ℕ) (hn : 0 < n) : 0 < succ m * n := Nat.mul_pos m.succ_pos hn
#align nat.succ_mul_pos Nat.succ_mul_pos

lemma mul_self_le_mul_self (h : m ≤ n) : m * m ≤ n * n := Nat.mul_le_mul h h
#align nat.mul_self_le_mul_self Nat.mul_self_le_mul_self

lemma mul_lt_mul'' (hac : a < c) (hbd : b < d) : a * b < c * d :=
  Nat.mul_lt_mul_of_lt_of_le hac (Nat.le_of_lt hbd) $ by omega

lemma mul_self_lt_mul_self (h : m < n) : m * m < n * n := mul_lt_mul'' h h
#align nat.mul_self_lt_mul_self Nat.mul_self_lt_mul_self

lemma mul_self_le_mul_self_iff : m * m ≤ n * n ↔ m ≤ n :=
  ⟨fun h => Nat.le_of_not_lt fun h' => Nat.not_le_of_gt (mul_self_lt_mul_self h') h,
   mul_self_le_mul_self⟩
#align nat.mul_self_le_mul_self_iff Nat.mul_self_le_mul_self_iff

lemma mul_self_lt_mul_self_iff : m * m < n * n ↔ m < n := by
  simp only [← Nat.not_le, mul_self_le_mul_self_iff]
#align nat.mul_self_lt_mul_self_iff Nat.mul_self_lt_mul_self_iff

lemma le_mul_self : ∀ n : ℕ, n ≤ n * n
  | 0 => Nat.le_refl _
  | n + 1 => by simp [Nat.mul_add]
#align nat.le_mul_self Nat.le_mul_self

lemma mul_self_inj : m * m = n * n ↔ m = n := by
  simp [Nat.le_antisymm_iff, mul_self_le_mul_self_iff]
#align nat.mul_self_inj Nat.mul_self_inj

@[simp] lemma lt_mul_self_iff : ∀ {n : ℕ}, n < n * n ↔ 1 < n
  | 0 => by simp
  | n + 1 => Nat.lt_mul_iff_one_lt_left n.succ_pos
#align nat.lt_mul_self_iff Nat.lt_mul_self_iff

lemma add_sub_one_le_mul (ha : a ≠ 0) (hb : b ≠ 0) : a + b - 1 ≤ a * b := by
  cases a
  · cases ha rfl
  · rw [succ_add, Nat.add_one_sub_one, succ_mul]
    exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ $ Nat.pos_iff_ne_zero.2 hb) _
#align nat.add_sub_one_le_mul Nat.add_sub_one_le_mul

protected lemma add_le_mul {a : ℕ} (ha : 2 ≤ a) : ∀ {b : ℕ} (_ : 2 ≤ b), a + b ≤ a * b
  | 2, _ => by omega
  | b + 3, _ => by have := Nat.add_le_mul ha (Nat.le_add_left _ b); rw [mul_succ]; omega

/-! ### `div` -/

#align nat.pow_div Nat.pow_div
#align nat.div_lt_of_lt_mul Nat.div_lt_of_lt_mul
#align nat.div_eq_zero Nat.div_eq_of_lt

attribute [simp] Nat.div_self

lemma div_le_iff_le_mul_add_pred (hb : 0 < b) : a / b ≤ c ↔ a ≤ b * c + (b - 1) := by
  rw [← Nat.lt_succ_iff, div_lt_iff_lt_mul hb, succ_mul, Nat.mul_comm]
  cases hb <;> exact Nat.lt_succ_iff
#align nat.div_le_iff_le_mul_add_pred Nat.div_le_iff_le_mul_add_pred

/-- A version of `Nat.div_lt_self` using successors, rather than additional hypotheses. -/
lemma div_lt_self' (a b : ℕ) : (a + 1) / (b + 2) < a + 1 :=
  Nat.div_lt_self (Nat.succ_pos _) (Nat.succ_lt_succ (Nat.succ_pos _))
#align nat.div_lt_self' Nat.div_lt_self'

lemma le_div_iff_mul_le' (hb : 0 < b) : a ≤ c / b ↔ a * b ≤ c := le_div_iff_mul_le hb
#align nat.le_div_iff_mul_le' Nat.le_div_iff_mul_le'

lemma div_lt_iff_lt_mul' (hb : 0 < b) : a / b < c ↔ a < c * b := by
  simp only [← Nat.not_le, le_div_iff_mul_le' hb]
#align nat.div_lt_iff_lt_mul' Nat.div_lt_iff_lt_mul'

lemma one_le_div_iff (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by rw [le_div_iff_mul_le hb, Nat.one_mul]
#align nat.one_le_div_iff Nat.one_le_div_iff

lemma div_lt_one_iff (hb : 0 < b) : a / b < 1 ↔ a < b := by
  simp only [← Nat.not_le, one_le_div_iff hb]
#align nat.div_lt_one_iff Nat.div_lt_one_iff

@[gcongr]
protected lemma div_le_div_right (h : a ≤ b) : a / c ≤ b / c :=
  (c.eq_zero_or_pos.elim fun hc ↦ by simp [hc]) fun hc ↦
    (le_div_iff_mul_le' hc).2 <| Nat.le_trans (Nat.div_mul_le_self _ _) h
#align nat.div_le_div_right Nat.div_le_div_right

lemma lt_of_div_lt_div (h : a / c < b / c) : a < b :=
  Nat.lt_of_not_le fun hab ↦ Nat.not_le_of_lt h $ Nat.div_le_div_right hab
#align nat.lt_of_div_lt_div Nat.lt_of_div_lt_div

protected lemma div_pos (hba : b ≤ a) (hb : 0 < b) : 0 < a / b :=
  Nat.pos_of_ne_zero fun h ↦ Nat.lt_irrefl a $
    calc
      a = a % b := by simpa [h] using (mod_add_div a b).symm
      _ < b := mod_lt a hb
      _ ≤ a := hba
#align nat.div_pos Nat.div_pos

lemma lt_mul_of_div_lt (h : a / c < b) (hc : 0 < c) : a < b * c :=
  Nat.lt_of_not_ge <| Nat.not_le_of_gt h ∘ (Nat.le_div_iff_mul_le hc).2
#align nat.lt_mul_of_div_lt Nat.lt_mul_of_div_lt

lemma mul_div_le_mul_div_assoc (a b c : ℕ) : a * (b / c) ≤ a * b / c :=
  if hc0 : c = 0 then by simp [hc0] else
    (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hc0)).2
      (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _))
#align nat.mul_div_le_mul_div_assoc Nat.mul_div_le_mul_div_assoc

#align nat.eq_mul_of_div_eq_right Nat.eq_mul_of_div_eq_right
#align nat.div_eq_iff_eq_mul_right Nat.div_eq_iff_eq_mul_right
#align nat.div_eq_iff_eq_mul_left Nat.div_eq_iff_eq_mul_left

protected lemma eq_mul_of_div_eq_left (H1 : b ∣ a) (H2 : a / b = c) : a = c * b := by
  rw [Nat.mul_comm, Nat.eq_mul_of_div_eq_right H1 H2]
#align nat.eq_mul_of_div_eq_left Nat.eq_mul_of_div_eq_left

protected lemma mul_div_cancel_left' (Hd : a ∣ b) : a * (b / a) = b := by
  rw [Nat.mul_comm, Nat.div_mul_cancel Hd]
#align nat.mul_div_cancel_left' Nat.mul_div_cancel_left'

#align nat.mul_div_mul_left Nat.mul_div_mul_left
#align nat.mul_div_mul_right Nat.mul_div_mul_right

lemma lt_div_mul_add (hb : 0 < b) : a < a / b * b + b := by
  rw [← Nat.succ_mul, ← Nat.div_lt_iff_lt_mul hb]; exact Nat.lt_succ_self _
#align nat.lt_div_mul_add Nat.lt_div_mul_add

@[simp]
protected lemma div_left_inj (hda : d ∣ a) (hdb : d ∣ b) : a / d = b / d ↔ a = b := by
  refine ⟨fun h ↦ ?_, congrArg fun b ↦ b / d⟩
  rw [← Nat.mul_div_cancel' hda, ← Nat.mul_div_cancel' hdb, h]
#align nat.div_left_inj Nat.div_left_inj

lemma div_mul_div_comm : b ∣ a → d ∣ c → (a / b) * (c / d) = (a * c) / (b * d) := by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩
  obtain rfl | hb := b.eq_zero_or_pos
  · simp
  obtain rfl | hd := d.eq_zero_or_pos
  · simp
  rw [Nat.mul_div_cancel_left _ hb, Nat.mul_div_cancel_left _ hd, Nat.mul_assoc b,
    Nat.mul_left_comm x, ← Nat.mul_assoc b, Nat.mul_div_cancel_left _ (Nat.mul_pos hb hd)]
#align nat.div_mul_div_comm Nat.div_mul_div_comm

lemma eq_zero_of_le_div (hn : 2 ≤ n) (h : m ≤ m / n) : m = 0 :=
  eq_zero_of_mul_le hn <| by
    rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le' (Nat.lt_of_lt_of_le (by decide) hn)).1 h
#align nat.eq_zero_of_le_div Nat.eq_zero_of_le_div

lemma div_mul_div_le_div (a b c : ℕ) : a / c * b / a ≤ b / c := by
  obtain rfl | ha := Nat.eq_zero_or_pos a
  · simp
  · calc
      a / c * b / a ≤ b * a / c / a :=
        Nat.div_le_div_right (by rw [Nat.mul_comm]; exact mul_div_le_mul_div_assoc _ _ _)
      _ = b / c := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm b, Nat.mul_comm c,
          Nat.mul_div_mul_left _ _ ha]
#align nat.div_mul_div_le_div Nat.div_mul_div_le_div

lemma eq_zero_of_le_half (h : n ≤ n / 2) : n = 0 := eq_zero_of_le_div (Nat.le_refl _) h
#align nat.eq_zero_of_le_half Nat.eq_zero_of_le_half

lemma le_half_of_half_lt_sub (h : a / 2 < a - b) : b ≤ a / 2 := by
  rw [Nat.le_div_iff_mul_le Nat.two_pos]
  rw [Nat.div_lt_iff_lt_mul Nat.two_pos, Nat.mul_sub_right_distrib, Nat.lt_sub_iff_add_lt,
    Nat.mul_two a] at h
  exact Nat.le_of_lt (Nat.lt_of_add_lt_add_left h)
#align nat.le_half_of_half_lt_sub Nat.le_half_of_half_lt_sub

lemma half_le_of_sub_le_half (h : a - b ≤ a / 2) : a / 2 ≤ b := by
  rw [Nat.le_div_iff_mul_le Nat.two_pos, Nat.mul_sub_right_distrib, Nat.sub_le_iff_le_add,
    Nat.mul_two, Nat.add_le_add_iff_left] at h
  rw [← Nat.mul_div_left b Nat.two_pos]
  exact Nat.div_le_div_right h
#align nat.half_le_of_sub_le_half Nat.half_le_of_sub_le_half

protected lemma div_le_of_le_mul' (h : m ≤ k * n) : m / k ≤ n := by
  obtain rfl | hk := k.eq_zero_or_pos
  · simp
  · refine Nat.le_of_mul_le_mul_left ?_ hk
    calc
      k * (m / k) ≤ m % k + k * (m / k) := Nat.le_add_left _ _
      _ = m := mod_add_div _ _
      _ ≤ k * n := h
#align nat.div_le_of_le_mul' Nat.div_le_of_le_mul'

protected lemma div_le_self' (m n : ℕ) : m / n ≤ m := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  · refine Nat.div_le_of_le_mul' ?_
    calc
      m = 1 * m := by rw [Nat.one_mul]
      _ ≤ n * m := Nat.mul_le_mul_right _ hn
#align nat.div_le_self' Nat.div_le_self'

lemma two_mul_odd_div_two (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 := by
  conv => rhs; rw [← Nat.mod_add_div n 2, hn, Nat.add_sub_cancel_left]
#align nat.two_mul_odd_div_two Nat.two_mul_odd_div_two

@[gcongr]
lemma div_le_div_left (hcb : c ≤ b) (hc : 0 < c) : a / b ≤ a / c :=
  (Nat.le_div_iff_mul_le hc).2 <| Nat.le_trans (Nat.mul_le_mul_left _ hcb) (div_mul_le_self _ _)
#align nat.div_le_div_left Nat.div_le_div_left

lemma div_eq_self : m / n = m ↔ m = 0 ∨ n = 1 := by
  constructor
  · intro
    match n with
    | 0 => simp_all
    | 1 => right; rfl
    | n+2 =>
      left
      have : m / (n + 2) ≤ m / 2 := div_le_div_left (by simp) (by decide)
      refine eq_zero_of_le_half ?_
      simp_all
  · rintro (rfl | rfl) <;> simp
#align nat.div_eq_self Nat.div_eq_self

lemma div_eq_sub_mod_div : m / n = (m - m % n) / n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · rw [Nat.div_zero, Nat.div_zero]
  · have : m - m % n = n * (m / n) := by
      rw [Nat.sub_eq_iff_eq_add (Nat.mod_le _ _), Nat.add_comm, mod_add_div]
    rw [this, mul_div_right _ hn]
#align nat.div_eq_sub_mod_div Nat.div_eq_sub_mod_div

protected lemma eq_div_of_mul_eq_left (hc : c ≠ 0) (h : a * c = b) : a = b / c := by
  rw [← h, Nat.mul_div_cancel _ (Nat.pos_iff_ne_zero.2 hc)]

protected lemma eq_div_of_mul_eq_right (hc : c ≠ 0) (h : c * a = b) : a = b / c := by
  rw [← h, Nat.mul_div_cancel_left _ (Nat.pos_iff_ne_zero.2 hc)]

protected lemma mul_le_of_le_div (k x y : ℕ) (h : x ≤ y / k) : x * k ≤ y := by
  if hk : k = 0 then
    rw [hk, Nat.mul_zero]; exact zero_le _
  else
    rwa [← le_div_iff_mul_le (Nat.pos_iff_ne_zero.2 hk)]

protected lemma div_mul_div_le (a b c d : ℕ) :
    (a / b) * (c / d) ≤ (a * c) / (b * d) := by
  if hb : b = 0 then simp [hb] else
  if hd : d = 0 then simp [hd] else
  have hbd : b * d ≠ 0 := Nat.mul_ne_zero hb hd
  rw [le_div_iff_mul_le (Nat.pos_of_ne_zero hbd)]
  transitivity ((a / b) * b) * ((c / d) * d)
  · apply Nat.le_of_eq; simp only [Nat.mul_assoc, Nat.mul_left_comm]
  · apply Nat.mul_le_mul <;> apply div_mul_le_self

/-!
### `pow`

#### TODO

* Rename `Nat.pow_le_pow_of_le_left` to `Nat.pow_le_pow_left`, protect it, remove the alias
* Rename `Nat.pow_le_pow_of_le_right` to `Nat.pow_le_pow_right`, protect it, remove the alias
-/

#align nat.pow_le_pow_of_le_left Nat.pow_le_pow_left
#align nat.pow_le_pow_of_le_right Nat.pow_le_pow_right
#align nat.pow_le_iff_lt_right Nat.pow_le_pow_iff_right
#align nat.pow_lt_iff_lt_right Nat.pow_lt_pow_iff_right
#align nat.pow_lt_pow_succ Nat.pow_lt_pow_succ

protected lemma pow_lt_pow_left (h : a < b) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < b ^ n
  | 1, _ => by simpa
  | n + 2, _ => Nat.mul_lt_mul_of_lt_of_le (Nat.pow_lt_pow_left h n.succ_ne_zero) (Nat.le_of_lt h)
    (zero_lt_of_lt h)
#align nat.pow_lt_pow_of_lt_left Nat.pow_lt_pow_left

protected lemma pow_lt_pow_right (ha : 1 < a) (h : m < n) : a ^ m < a ^ n :=
  (Nat.pow_lt_pow_iff_right ha).2 h

protected lemma pow_le_pow_iff_left {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ b ^ n ↔ a ≤ b where
  mp := by simpa only [← Nat.not_le, Decidable.not_imp_not] using (Nat.pow_lt_pow_left · hn)
  mpr h := Nat.pow_le_pow_left h _
#align nat.pow_le_iff_le_left Nat.pow_le_pow_iff_left

protected lemma pow_lt_pow_iff_left (hn : n ≠ 0) : a ^ n < b ^ n ↔ a < b := by
  simp only [← Nat.not_le, Nat.pow_le_pow_iff_left hn]
#align nat.pow_lt_iff_lt_left Nat.pow_lt_pow_iff_left

@[deprecated (since := "2023-12-23")] alias pow_lt_pow_of_lt_left := Nat.pow_lt_pow_left
@[deprecated (since := "2023-12-23")] alias pow_le_iff_le_left := Nat.pow_le_pow_iff_left

lemma pow_left_injective (hn : n ≠ 0) : Injective (fun a : ℕ ↦ a ^ n) := by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_left hn]
#align nat.pow_left_injective Nat.pow_left_injective

protected lemma pow_right_injective (ha : 2 ≤ a) : Injective (a ^ ·) :=by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_right ha]
#align nat.pow_right_injective Nat.pow_right_injective

-- We want to use this lemma earlier than the lemma simp can prove it with
@[simp, nolint simpNF] protected lemma pow_eq_zero {a : ℕ} : ∀ {n : ℕ}, a ^ n = 0 ↔ a = 0 ∧ n ≠ 0
  | 0 => by simp
  | n + 1 => by rw [Nat.pow_succ, mul_eq_zero, Nat.pow_eq_zero]; omega

lemma le_self_pow (hn : n ≠ 0) : ∀ a : ℕ, a ≤ a ^ n
  | 0 => zero_le _
  | a + 1 => by simpa using Nat.pow_le_pow_right a.succ_pos (Nat.one_le_iff_ne_zero.2 hn)
#align nat.le_self_pow Nat.le_self_pow

lemma lt_pow_self (ha : 1 < a) : ∀ n : ℕ, n < a ^ n
  | 0 => by simp
  | n + 1 =>
    calc
      n + 1 < a ^ n + 1 := Nat.add_lt_add_right (lt_pow_self ha _) _
      _ ≤ a ^ (n + 1) := Nat.pow_lt_pow_succ ha
#align nat.lt_pow_self Nat.lt_pow_self

lemma lt_two_pow (n : ℕ) : n < 2 ^ n := lt_pow_self (by decide) n
#align nat.lt_two_pow Nat.lt_two_pow

lemma one_le_pow (n m : ℕ) (h : 0 < m) : 1 ≤ m ^ n := by simpa using Nat.pow_le_pow_of_le_left h n
#align nat.one_le_pow Nat.one_le_pow

lemma one_le_pow' (n m : ℕ) : 1 ≤ (m + 1) ^ n := one_le_pow n (m + 1) (succ_pos m)
#align nat.one_le_pow' Nat.one_le_pow'

#align nat.one_le_two_pow Nat.one_le_two_pow

lemma one_lt_pow (hn : n ≠ 0) (ha : 1 < a) : 1 < a ^ n := by simpa using Nat.pow_lt_pow_left ha hn
#align nat.one_lt_pow Nat.one_lt_pow

lemma two_pow_succ (n : ℕ) : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by simp [Nat.pow_succ, Nat.mul_two]

lemma one_lt_pow' (n m : ℕ) : 1 < (m + 2) ^ (n + 1) :=
  one_lt_pow n.succ_ne_zero (Nat.lt_of_sub_eq_succ rfl)
#align nat.one_lt_pow' Nat.one_lt_pow'

@[simp] lemma one_lt_pow_iff {n : ℕ} (hn : n ≠ 0) : ∀ {a}, 1 < a ^ n ↔ 1 < a
 | 0 => by simp [Nat.zero_pow (Nat.pos_of_ne_zero hn)]
 | 1 => by simp
 | a + 2 => by simp [one_lt_pow hn]
  -- one_lt_pow_iff_of_nonneg (zero_le _) h
#align nat.one_lt_pow_iff Nat.one_lt_pow_iff

#align nat.one_lt_two_pow Nat.one_lt_two_pow

lemma one_lt_two_pow' (n : ℕ) : 1 < 2 ^ (n + 1) := one_lt_pow n.succ_ne_zero (by decide)
#align nat.one_lt_two_pow' Nat.one_lt_two_pow'

lemma mul_lt_mul_pow_succ (ha : 0 < a) (hb : 1 < b) : n * b < a * b ^ (n + 1) := by
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_lt_mul_right (Nat.lt_trans Nat.zero_lt_one hb)]
  exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ ha)
    ((Nat.mul_lt_mul_left ha).2 $ Nat.lt_pow_self hb _)
#align nat.mul_lt_mul_pow_succ Nat.mul_lt_mul_pow_succ

lemma sq_sub_sq (a b : ℕ) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  simpa [Nat.pow_succ] using Nat.mul_self_sub_mul_self_eq a b
#align nat.sq_sub_sq Nat.sq_sub_sq

alias pow_two_sub_pow_two := sq_sub_sq
#align nat.pow_two_sub_pow_two Nat.pow_two_sub_pow_two

protected lemma div_pow (h : a ∣ b) : (b / a) ^ c = b ^ c / a ^ c := by
  obtain rfl | hc := c.eq_zero_or_pos
  · simp
  obtain rfl | ha := a.eq_zero_or_pos
  · simp [Nat.zero_pow hc]
  refine (Nat.div_eq_of_eq_mul_right (pos_pow_of_pos c ha) ?_).symm
  rw [← Nat.mul_pow, Nat.mul_div_cancel_left' h]

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

-- Porting note: The type ascriptions of these two lemmas need to be changed,
-- as mathport wrote a lambda that wasn't there in mathlib3, that prevents `simp` applying them.

@[simp]
lemma rec_zero {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) : Nat.rec h0 h 0 = h0 := rfl
#align nat.rec_zero Nat.rec_zero

lemma rec_add_one {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) (n : ℕ) :
    Nat.rec h0 h (n + 1) = h n (Nat.rec h0 h n) := rfl
#align nat.rec_add_one Nat.rec_add_one

@[simp] lemma rec_one {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) :
    Nat.rec (motive := C) h0 h 1 = h 0 h0 := rfl

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k ≥ n`,
there is a map from `C n` to each `C m`, `n ≤ m`. -/
@[elab_as_elim]
def leRecOn' {C : ℕ → Sort*} : ∀ {m}, n ≤ m → (∀ ⦃k⦄, n ≤ k → C k → C (k + 1)) → C n → C m
  | 0, H, _, x => Eq.recOn (Nat.eq_zero_of_le_zero H) x
  | m + 1, H, next, x => (le_succ_iff.1 H).by_cases (fun h : n ≤ m ↦ next h <| leRecOn' h next x)
      fun h : n = m + 1 ↦ Eq.recOn h x
#align nat.le_rec_on' Nat.leRecOn'

/-- Recursion starting at a non-zero number: given a map `C k → C (k + 1)` for each `k`,
there is a map from `C n` to each `C m`, `n ≤ m`. For a version where the assumption is only made
when `k ≥ n`, see `Nat.leRecOn'`. -/
@[elab_as_elim]
def leRecOn {C : ℕ → Sort*} {n : ℕ} : ∀ {m}, n ≤ m → (∀ {k}, C k → C (k + 1)) → C n → C m
  | 0, H, _, x => Eq.recOn (Nat.eq_zero_of_le_zero H) x
  | m + 1, H, next, x => (le_succ_iff.1 H).by_cases (fun h : n ≤ m ↦ next <| leRecOn h next x)
      fun h : n = m + 1 ↦ Eq.recOn h x
#align nat.le_rec_on Nat.leRecOn

lemma leRecOn_self {C : ℕ → Sort*} {n} {next : ∀ {k}, C k → C (k + 1)} (x : C n) :
    (leRecOn n.le_refl next x : C n) = x := by cases n <;> simp [leRecOn, Or.by_cases, dif_neg]
#align nat.le_rec_on_self Nat.leRecOn_self

lemma leRecOn_succ {C : ℕ → Sort*} {n m} (h1 : n ≤ m) {h2 : n ≤ m + 1} {next} (x : C n) :
    (leRecOn h2 next x : C (m + 1)) = next (leRecOn h1 next x : C m) := by
  conv =>
    lhs
    rw [leRecOn, Or.by_cases, dif_pos h1]
#align nat.le_rec_on_succ Nat.leRecOn_succ

lemma leRecOn_succ' {C : ℕ → Sort*} {n} {h : n ≤ n + 1} {next : ∀ {k}, C k → C (k + 1)} (x : C n) :
    (leRecOn h next x : C (n + 1)) = next x := by rw [leRecOn_succ (le_refl n), leRecOn_self]
#align nat.le_rec_on_succ' Nat.leRecOn_succ'

lemma leRecOn_trans {C : ℕ → Sort*} {n m k} (hnm : n ≤ m) (hmk : m ≤ k) {next} (x : C n) :
    (leRecOn (Nat.le_trans hnm hmk) (@next) x : C k) =
      leRecOn hmk (@next) (leRecOn hnm (@next) x) := by
  induction hmk with
  | refl => rw [leRecOn_self]
  | step hmk ih => rw [leRecOn_succ (Nat.le_trans hnm hmk), ih, leRecOn_succ]
#align nat.le_rec_on_trans Nat.leRecOn_trans

lemma leRecOn_succ_left {C : ℕ → Sort*} {n m} (h1 : n ≤ m) (h2 : n + 1 ≤ m)
    {next : ∀ {k}, C k → C (k + 1)} (x : C n) :
    (leRecOn h2 next (next x) : C m) = (leRecOn h1 next x : C m) := by
  rw [Subsingleton.elim h1 (Nat.le_trans (le_succ n) h2), leRecOn_trans (le_succ n) h2,
    leRecOn_succ']
#align nat.le_rec_on_succ_left Nat.leRecOn_succ_left

lemma leRecOn_injective {C : ℕ → Sort*} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Injective (@next n)) : Injective (@leRecOn C n m hnm next) := by
  induction hnm with
  | refl =>
    intro x y H
    rwa [leRecOn_self, leRecOn_self] at H
  | step hnm ih =>
    intro x y H
    rw [leRecOn_succ hnm, leRecOn_succ hnm] at H
    exact ih (Hnext _ H)
#align nat.le_rec_on_injective Nat.leRecOn_injective

lemma leRecOn_surjective {C : ℕ → Sort*} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Surjective (@next n)) : Surjective (@leRecOn C n m hnm next) := by
  induction hnm with
  | refl =>
    intro x
    refine ⟨x, ?_⟩
    rw [leRecOn_self]
  | step hnm ih =>
    intro x
    obtain ⟨w, rfl⟩ := Hnext _ x
    obtain ⟨x, rfl⟩ := ih w
    refine ⟨x, ?_⟩
    rw [leRecOn_succ]
#align nat.le_rec_on_surjective Nat.leRecOn_surjective

/-- Recursion principle based on `<`. -/
@[elab_as_elim]
protected def strongRec' {p : ℕ → Sort*} (H : ∀ n, (∀ m, m < n → p m) → p n) : ∀ n : ℕ, p n
  | n => H n fun m _ ↦ Nat.strongRec' H m
#align nat.strong_rec' Nat.strongRec'

/-- Recursion principle based on `<` applied to some natural number. -/
@[elab_as_elim]
def strongRecOn' {P : ℕ → Sort*} (n : ℕ) (h : ∀ n, (∀ m, m < n → P m) → P n) : P n :=
  Nat.strongRec' h n
#align nat.strong_rec_on' Nat.strongRecOn'

lemma strongRecOn'_beta {P : ℕ → Sort*} {h} :
    (strongRecOn' n h : P n) = h n fun m _ ↦ (strongRecOn' m h : P m) := by
  simp only [strongRecOn']; rw [Nat.strongRec']
#align nat.strong_rec_on_beta' Nat.strongRecOn'_beta

/-- Induction principle starting at a non-zero number. For maps to a `Sort*` see `leRecOn`.
To use in an induction proof, the syntax is `induction n, hn using Nat.le_induction` (or the same
for `induction'`). -/
@[elab_as_elim]
lemma le_induction {m : ℕ} {P : ∀ n, m ≤ n → Prop} (base : P m m.le_refl)
    (succ : ∀ n hmn, P n hmn → P (n + 1) (le_succ_of_le hmn)) : ∀ n hmn, P n hmn := fun n hmn ↦ by
  apply Nat.le.rec
  · exact base
  · intros n hn
    apply succ n hn
#align nat.le_induction Nat.le_induction

/-- Decreasing induction: if `P (k+1)` implies `P k`, then `P n` implies `P m` for all `m ≤ n`.
Also works for functions to `Sort*`. For m version assuming only the assumption for `k < n`, see
`decreasing_induction'`. -/
@[elab_as_elim]
def decreasingInduction {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n) (mn : m ≤ n) (hP : P n) : P m :=
  leRecOn mn (fun {k} ih hsk ↦ ih <| h k hsk) (fun h ↦ h) hP
#align nat.decreasing_induction Nat.decreasingInduction

@[simp]
lemma decreasingInduction_self {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n) (nn : n ≤ n)
    (hP : P n) :
    (decreasingInduction h nn hP : P n) = hP := by
  dsimp only [decreasingInduction]
  rw [leRecOn_self]
#align nat.decreasing_induction_self Nat.decreasingInduction_self

lemma decreasingInduction_succ {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n) (mn : m ≤ n)
    (msn : m ≤ n + 1) (hP : P (n + 1)) :
    (decreasingInduction h msn hP : P m) = decreasingInduction h mn (h n hP) := by
  dsimp only [decreasingInduction]; rw [leRecOn_succ]
#align nat.decreasing_induction_succ Nat.decreasingInduction_succ

@[simp]
lemma decreasingInduction_succ' {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n) {m : ℕ}
    (msm : m ≤ m + 1) (hP : P (m + 1)) : decreasingInduction h msm hP = h m hP := by
  dsimp only [decreasingInduction]; rw [leRecOn_succ']
#align nat.decreasing_induction_succ' Nat.decreasingInduction_succ'

lemma decreasingInduction_trans {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n)
    (hmn : m ≤ n) (hnk : n ≤ k) (hP : P k) :
    (decreasingInduction h (Nat.le_trans hmn hnk) hP : P m) =
    decreasingInduction h hmn (decreasingInduction h hnk hP) := by
  induction hnk with
  | refl => rw [decreasingInduction_self]
  | step hnk ih =>
      rw [decreasingInduction_succ h (Nat.le_trans hmn hnk), ih, decreasingInduction_succ]
#align nat.decreasing_induction_trans Nat.decreasingInduction_trans

lemma decreasingInduction_succ_left {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n)
    (smn : m + 1 ≤ n) (mn : m ≤ n) (hP : P n) :
    decreasingInduction h mn hP = h m (decreasingInduction h smn hP) := by
  rw [Subsingleton.elim mn (Nat.le_trans (le_succ m) smn), decreasingInduction_trans,
    decreasingInduction_succ']
  apply Nat.le_succ
#align nat.decreasing_induction_succ_left Nat.decreasingInduction_succ_left

/-- Given `P : ℕ → ℕ → Sort*`, if for all `m n : ℕ` we can extend `P` from the rectangle
strictly below `(m, n)` to `P m n`, then we have `P n m` for all `n m : ℕ`.
Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
@[elab_as_elim]
def strongSubRecursion {P : ℕ → ℕ → Sort*} (H : ∀ m n, (∀ x y, x < m → y < n → P x y) → P m n) :
    ∀ n m : ℕ, P n m
  | n, m => H n m fun x y _ _ ↦ strongSubRecursion H x y
#align nat.strong_sub_recursion Nat.strongSubRecursion

/-- Given `P : ℕ → ℕ → Sort*`, if we have `P m 0` and `P 0 n` for all `m n : ℕ`, and for any
`m n : ℕ` we can extend `P` from `(m, n + 1)` and `(m + 1, n)` to `(m + 1, n + 1)` then we have
`P m n` for all `m n : ℕ`.

Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
@[elab_as_elim]
def pincerRecursion {P : ℕ → ℕ → Sort*} (Ha0 : ∀ m : ℕ, P m 0) (H0b : ∀ n : ℕ, P 0 n)
    (H : ∀ x y : ℕ, P x y.succ → P x.succ y → P x.succ y.succ) : ∀ n m : ℕ, P n m
  | m, 0 => Ha0 m
  | 0, n => H0b n
  | Nat.succ m, Nat.succ n => H _ _ (pincerRecursion Ha0 H0b H _ _) (pincerRecursion Ha0 H0b H _ _)
#align nat.pincer_recursion Nat.pincerRecursion

/-- Decreasing induction: if `P (k+1)` implies `P k` for all `m ≤ k < n`, then `P n` implies `P m`.
Also works for functions to `Sort*`. Weakens the assumptions of `decreasing_induction`. -/
@[elab_as_elim]
def decreasingInduction' {P : ℕ → Sort*} (h : ∀ k < n, m ≤ k → P (k + 1) → P k)
    (mn : m ≤ n) (hP : P n) : P m := by
  revert h hP
  refine leRecOn' mn ?_ ?_
  · intro n mn ih h hP
    apply ih
    · exact fun k hk ↦ h k (Nat.lt.step hk)
    · exact h n (lt_succ_self n) mn hP
  · intro _ hP
    exact hP
#align nat.decreasing_induction' Nat.decreasingInduction'

/-- Given a predicate on two naturals `P : ℕ → ℕ → Prop`, `P a b` is true for all `a < b` if
`P (a + 1) (a + 1)` is true for all `a`, `P 0 (b + 1)` is true for all `b` and for all
`a < b`, `P (a + 1) b` is true and `P a (b + 1)` is true implies `P (a + 1) (b + 1)` is true. -/
@[elab_as_elim]
theorem diag_induction (P : ℕ → ℕ → Prop) (ha : ∀ a, P (a + 1) (a + 1)) (hb : ∀ b, P 0 (b + 1))
    (hd : ∀ a b, a < b → P (a + 1) b → P a (b + 1) → P (a + 1) (b + 1)) : ∀ a b, a < b → P a b
  | 0, b + 1, _ => hb _
  | a + 1, b + 1, h => by
    apply hd _ _ (Nat.add_lt_add_iff_right.1 h)
    · have this : a + 1 = b ∨ a + 1 < b := by omega
      have wf : (a + 1) + b < (a + 1) + (b + 1) := by simp
      rcases this with (rfl | h)
      · exact ha _
      apply diag_induction P ha hb hd (a + 1) b h
    have _ : a + (b + 1) < (a + 1) + (b + 1) := by simp
    apply diag_induction P ha hb hd a (b + 1)
    apply Nat.lt_of_le_of_lt (Nat.le_succ _) h
  termination_by a b _c => a + b
  decreasing_by all_goals assumption
#align nat.diag_induction Nat.diag_induction

/-- A subset of `ℕ` containing `k : ℕ` and closed under `Nat.succ` contains every `n ≥ k`. -/
lemma set_induction_bounded {S : Set ℕ} (hk : k ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S)
    (hnk : k ≤ n) : n ∈ S :=
  @leRecOn (fun n => n ∈ S) k n hnk @h_ind hk
#align nat.set_induction_bounded Nat.set_induction_bounded

/-- A subset of `ℕ` containing zero and closed under `Nat.succ` contains all of `ℕ`. -/
lemma set_induction {S : Set ℕ} (hb : 0 ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S) (n : ℕ) :
    n ∈ S :=
  set_induction_bounded hb h_ind (zero_le n)
#align nat.set_induction Nat.set_induction

/-! ### `mod`, `dvd` -/

#align nat.pow_dvd_of_le_of_pow_dvd Nat.pow_dvd_of_le_of_pow_dvd
#align nat.dvd_of_pow_dvd Nat.dvd_of_pow_dvd
#align nat.mod_pow_succ Nat.mod_pow_succ
#align nat.pow_dvd_pow_iff_pow_le_pow Nat.pow_dvd_pow_iff_pow_le_pow
#align nat.pow_dvd_pow_iff_le_right Nat.pow_dvd_pow_iff_le_right
#align nat.pow_dvd_pow_iff_le_right' Nat.pow_dvd_pow_iff_le_right'
#align nat.mod_mul_right_div_self Nat.mod_mul_right_div_self
#align nat.mod_mul_left_div_self Nat.mod_mul_left_div_self
#align nat.mod_div_self Nat.mod_div_self

attribute [simp] Nat.dvd_zero

@[simp] lemma mod_two_ne_one : ¬n % 2 = 1 ↔ n % 2 = 0 := by
  cases' mod_two_eq_zero_or_one n with h h <;> simp [h]
#align nat.mod_two_ne_one Nat.mod_two_ne_one

@[simp] lemma mod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by
  cases' mod_two_eq_zero_or_one n with h h <;> simp [h]
#align nat.mod_two_ne_zero Nat.mod_two_ne_zero

@[deprecated mod_mul_right_div_self (since := "2024-05-29")]
lemma div_mod_eq_mod_mul_div (a b c : ℕ) : a / b % c = a % (b * c) / b :=
  (mod_mul_right_div_self a b c).symm
#align nat.div_mod_eq_mod_mul_div Nat.div_mod_eq_mod_mul_div

protected lemma lt_div_iff_mul_lt (hdn : d ∣ n) (a : ℕ) : a < n / d ↔ d * a < n := by
  obtain rfl | hd := d.eq_zero_or_pos
  · simp [Nat.zero_dvd.1 hdn]
  · rw [← Nat.mul_lt_mul_left hd, ← Nat.eq_mul_of_div_eq_right hdn rfl]
#align nat.lt_div_iff_mul_lt Nat.lt_div_iff_mul_lt

lemma mul_div_eq_iff_dvd {n d : ℕ} : d * (n / d) = n ↔ d ∣ n :=
  calc
    d * (n / d) = n ↔ d * (n / d) = d * (n / d) + (n % d) := by rw [div_add_mod]
    _ ↔ d ∣ n := by rw [eq_comm, Nat.add_eq_left, dvd_iff_mod_eq_zero]

lemma mul_div_lt_iff_not_dvd : d * (n / d) < n ↔ ¬ d ∣ n := by
  simp [Nat.lt_iff_le_and_ne, mul_div_eq_iff_dvd, mul_div_le]

lemma div_eq_iff_eq_of_dvd_dvd (hn : n ≠ 0) (ha : a ∣ n) (hb : b ∣ n) : n / a = n / b ↔ a = b := by
  constructor <;> intro h
  · rw [← Nat.mul_right_inj hn]
    apply Nat.eq_mul_of_div_eq_left (Nat.dvd_trans hb (Nat.dvd_mul_right _ _))
    rw [eq_comm, Nat.mul_comm, Nat.mul_div_assoc _ hb]
    exact Nat.eq_mul_of_div_eq_right ha h
  · rw [h]
#align nat.div_eq_iff_eq_of_dvd_dvd Nat.div_eq_iff_eq_of_dvd_dvd

protected lemma div_eq_zero_iff (hb : 0 < b) : a / b = 0 ↔ a < b where
  mp h := by rw [← mod_add_div a b, h, Nat.mul_zero, Nat.add_zero]; exact mod_lt _ hb
  mpr h := by rw [← Nat.mul_right_inj (Nat.ne_of_gt hb), ← Nat.add_left_cancel_iff, mod_add_div,
      mod_eq_of_lt h, Nat.mul_zero, Nat.add_zero]
#align nat.div_eq_zero_iff Nat.div_eq_zero_iff

protected lemma div_ne_zero_iff (hb : b ≠ 0) : a / b ≠ 0 ↔ b ≤ a := by
  rw [ne_eq, Nat.div_eq_zero_iff (Nat.pos_of_ne_zero hb), not_lt]

protected lemma div_pos_iff (hb : b ≠ 0) : 0 < a / b ↔ b ≤ a := by
  rw [Nat.pos_iff_ne_zero, Nat.div_ne_zero_iff hb]

@[deprecated div_mul_div_comm (since := "2024-05-29")]
lemma mul_div_mul_comm_of_dvd_dvd (hba : b ∣ a) (hdc : d ∣ c) :
    a * c / (b * d) = a / b * (c / d) :=
  (div_mul_div_comm hba hdc).symm
#align nat.mul_div_mul_comm_of_dvd_dvd Nat.mul_div_mul_comm_of_dvd_dvd

@[simp] lemma mul_mod_mod (a b c : ℕ) : (a * (b % c)) % c = a * b % c := by
  rw [mul_mod, mod_mod, ← mul_mod]

@[simp] lemma mod_mul_mod (a b c : ℕ) : (a % c * b) % c = a * b % c := by
  rw [mul_mod, mod_mod, ← mul_mod]

lemma pow_mod (a b n : ℕ) : a ^ b % n = (a % n) ^ b % n := by
  induction b with
  | zero => rfl
  | succ b ih => simp [Nat.pow_succ, Nat.mul_mod, ih]
#align nat.pow_mod Nat.pow_mod

lemma not_pos_pow_dvd : ∀ {a n : ℕ} (_ : 1 < a) (_ : 1 < n), ¬ a ^ n ∣ a
  | succ a, succ n, hp, hk, h =>
    have : succ a * succ a ^ n ∣ succ a * 1 := by simpa [pow_succ'] using h
    have : succ a ^ n ∣ 1 := Nat.dvd_of_mul_dvd_mul_left (succ_pos _) this
    have he : succ a ^ n = 1 := eq_one_of_dvd_one this
    have : n < succ a ^ n := lt_pow_self hp n
    have : n < 1 := by rwa [he] at this
    have : n = 0 := Nat.eq_zero_of_le_zero <| le_of_lt_succ this
    have : 1 < 1 := by rwa [this] at hk
    absurd this (by decide)
#align nat.not_pos_pow_dvd Nat.not_pos_pow_dvd

lemma lt_of_pow_dvd_right (hb : b ≠ 0) (ha : 2 ≤ a) (h : a ^ n ∣ b) : n < b := by
  rw [← Nat.pow_lt_pow_iff_right (succ_le_iff.1 ha)]
  exact Nat.lt_of_le_of_lt (le_of_dvd (Nat.pos_iff_ne_zero.2 hb) h) (lt_pow_self ha _)
#align nat.lt_of_pow_dvd_right Nat.lt_of_pow_dvd_right

lemma div_dvd_of_dvd (h : n ∣ m) : m / n ∣ m := ⟨n, (Nat.div_mul_cancel h).symm⟩
#align nat.div_dvd_of_dvd Nat.div_dvd_of_dvd

protected lemma div_div_self (h : n ∣ m) (hm : m ≠ 0) : m / (m / n) = n := by
  rcases h with ⟨_, rfl⟩
  rw [Nat.mul_ne_zero_iff] at hm
  rw [mul_div_right _ (Nat.pos_of_ne_zero hm.1), mul_div_left _ (Nat.pos_of_ne_zero hm.2)]
#align nat.div_div_self Nat.div_div_self

lemma not_dvd_of_pos_of_lt (h1 : 0 < n) (h2 : n < m) : ¬m ∣ n := by
  rintro ⟨k, rfl⟩
  rcases Nat.eq_zero_or_pos k with (rfl | hk)
  · exact Nat.lt_irrefl 0 h1
  · exact Nat.not_lt.2 (Nat.le_mul_of_pos_right _ hk) h2
#align nat.not_dvd_of_pos_of_lt Nat.not_dvd_of_pos_of_lt

lemma mod_eq_iff_lt (hn : n ≠ 0) : m % n = m ↔ m < n :=
  ⟨fun h ↦ by rw [← h]; exact mod_lt _ $ Nat.pos_iff_ne_zero.2 hn, mod_eq_of_lt⟩
#align nat.mod_eq_iff_lt Nat.mod_eq_iff_lt

@[simp]
lemma mod_succ_eq_iff_lt : m % n.succ = m ↔ m < n.succ :=
  mod_eq_iff_lt (succ_ne_zero _)
#align nat.mod_succ_eq_iff_lt Nat.mod_succ_eq_iff_lt

@[simp] lemma mod_succ (n : ℕ) : n % n.succ = n := mod_eq_of_lt n.lt_succ_self

-- Porting note `Nat.div_add_mod` is now in core.

lemma mod_add_div' (a b : ℕ) : a % b + a / b * b = a := by rw [Nat.mul_comm]; exact mod_add_div _ _
#align nat.mod_add_div' Nat.mod_add_div'

lemma div_add_mod' (a b : ℕ) : a / b * b + a % b = a := by rw [Nat.mul_comm]; exact div_add_mod _ _
#align nat.div_add_mod' Nat.div_add_mod'

/-- See also `Nat.divModEquiv` for a similar statement as an `Equiv`. -/
protected lemma div_mod_unique (h : 0 < b) :
    a / b = d ∧ a % b = c ↔ c + b * d = a ∧ c < b :=
  ⟨fun ⟨e₁, e₂⟩ ↦ e₁ ▸ e₂ ▸ ⟨mod_add_div _ _, mod_lt _ h⟩, fun ⟨h₁, h₂⟩ ↦ h₁ ▸ by
    rw [add_mul_div_left _ _ h, add_mul_mod_self_left]; simp [div_eq_of_lt, mod_eq_of_lt, h₂]⟩
#align nat.div_mod_unique Nat.div_mod_unique

/-- If `m` and `n` are equal mod `k`, `m - n` is zero mod `k`. -/
lemma sub_mod_eq_zero_of_mod_eq (h : m % k = n % k) : (m - n) % k = 0 := by
  rw [← Nat.mod_add_div m k, ← Nat.mod_add_div n k, ← h, ← Nat.sub_sub,
    Nat.add_sub_cancel_left, ← Nat.mul_sub_left_distrib k, Nat.mul_mod_right]
#align nat.sub_mod_eq_zero_of_mod_eq Nat.sub_mod_eq_zero_of_mod_eq

@[simp] lemma one_mod (n : ℕ) : 1 % (n + 2) = 1 :=
  Nat.mod_eq_of_lt (Nat.add_lt_add_right n.succ_pos 1)
#align nat.one_mod Nat.one_mod

lemma one_mod_of_ne_one : ∀ {n : ℕ}, n ≠ 1 → 1 % n = 1
  | 0, _ | (n + 2), _ => by simp

lemma dvd_sub_mod (k : ℕ) : n ∣ k - k % n :=
  ⟨k / n, Nat.sub_eq_of_eq_add (Nat.div_add_mod k n).symm⟩
#align nat.dvd_sub_mod Nat.dvd_sub_mod

lemma add_mod_eq_ite :
    (m + n) % k = if k ≤ m % k + n % k then m % k + n % k - k else m % k + n % k := by
  cases k
  · simp
  rw [Nat.add_mod]
  split_ifs with h
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt]
    exact (Nat.sub_lt_iff_lt_add h).mpr (Nat.add_lt_add (m.mod_lt (zero_lt_succ _))
      (n.mod_lt (zero_lt_succ _)))
  · exact Nat.mod_eq_of_lt (Nat.lt_of_not_ge h)
#align nat.add_mod_eq_ite Nat.add_mod_eq_ite

/-- `m` is not divisible by `n` if it is between `n * k` and `n * (k + 1)` for some `k`. -/
theorem not_dvd_of_between_consec_multiples (h1 : n * k < m) (h2 : m < n * (k + 1)) : ¬n ∣ m := by
  rintro ⟨d, rfl⟩
  have := Nat.lt_of_mul_lt_mul_left h1
  have := Nat.lt_of_mul_lt_mul_left h2
  omega
#align nat.not_dvd_of_between_consec_multiples Nat.not_dvd_of_between_consec_multiples

-- TODO: Replace `Nat.dvd_add_iff_left`
protected lemma dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b := (Nat.dvd_add_iff_left h).symm
#align nat.dvd_add_left Nat.dvd_add_left

protected lemma dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c := (Nat.dvd_add_iff_right h).symm
#align nat.dvd_add_right Nat.dvd_add_right

/-- special case of `mul_dvd_mul_iff_left` for `ℕ`.
Duplicated here to keep simple imports for this file. -/
protected lemma mul_dvd_mul_iff_left (ha : 0 < a) : a * b ∣ a * c ↔ b ∣ c :=
  exists_congr fun d ↦ by rw [Nat.mul_assoc, Nat.mul_right_inj $ ne_of_gt ha]
#align nat.mul_dvd_mul_iff_left Nat.mul_dvd_mul_iff_left

/-- special case of `mul_dvd_mul_iff_right` for `ℕ`.
Duplicated here to keep simple imports for this file. -/
protected lemma mul_dvd_mul_iff_right (hc : 0 < c) : a * c ∣ b * c ↔ a ∣ b :=
  exists_congr fun d ↦ by rw [Nat.mul_right_comm, Nat.mul_left_inj $ ne_of_gt hc]
#align nat.mul_dvd_mul_iff_right Nat.mul_dvd_mul_iff_right

#align nat.dvd_one Nat.dvd_one
#align nat.mod_mod_of_dvd Nat.mod_mod_of_dvd

-- Moved to Batteries
#align nat.mod_mod Nat.mod_mod
#align nat.mod_add_mod Nat.mod_add_mod
#align nat.add_mod_mod Nat.add_mod_mod
#align nat.add_mod Nat.add_mod

lemma add_mod_eq_add_mod_right (c : ℕ) (H : a % d = b % d) : (a + c) % d = (b + c) % d := by
  rw [← mod_add_mod, ← mod_add_mod b, H]
#align nat.add_mod_eq_add_mod_right Nat.add_mod_eq_add_mod_right

lemma add_mod_eq_add_mod_left (c : ℕ) (H : a % d = b % d) : (c + a) % d = (c + b) % d := by
  rw [Nat.add_comm, add_mod_eq_add_mod_right _ H, Nat.add_comm]
#align nat.add_mod_eq_add_mod_left Nat.add_mod_eq_add_mod_left

-- Moved to Batteries
#align nat.mul_mod Nat.mul_mod

lemma mul_dvd_of_dvd_div (hcb : c ∣ b) (h : a ∣ b / c) : c * a ∣ b :=
  have ⟨d, hd⟩ := h
  ⟨d, by simpa [Nat.mul_comm, Nat.mul_left_comm] using Nat.eq_mul_of_div_eq_left hcb hd⟩
#align nat.mul_dvd_of_dvd_div Nat.mul_dvd_of_dvd_div

lemma eq_of_dvd_of_div_eq_one (hab : a ∣ b) (h : b / a = 1) : a = b := by
  rw [← Nat.div_mul_cancel hab, h, Nat.one_mul]
#align nat.eq_of_dvd_of_div_eq_one Nat.eq_of_dvd_of_div_eq_one

lemma eq_zero_of_dvd_of_div_eq_zero (hab : a ∣ b) (h : b / a = 0) : b = 0 := by
  rw [← Nat.div_mul_cancel hab, h, Nat.zero_mul]
#align nat.eq_zero_of_dvd_of_div_eq_zero Nat.eq_zero_of_dvd_of_div_eq_zero

@[gcongr]
protected theorem div_le_div {a b c d : ℕ} (h1 : a ≤ b) (h2 : d ≤ c) (h3 : d ≠ 0) : a / c ≤ b / d :=
  calc a / c ≤ b / c := Nat.div_le_div_right h1
    _ ≤ b / d := Nat.div_le_div_left h2 (Nat.pos_of_ne_zero h3)

-- Moved to Batteries
#align nat.mul_div_le Nat.mul_div_le

lemma lt_mul_div_succ (a : ℕ) (hb : 0 < b) : a < b * (a / b + 1) := by
  rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul' hb]
  exact lt_succ_self _
#align nat.lt_mul_div_succ Nat.lt_mul_div_succ

-- TODO: Batteries claimed this name but flipped the order of multiplication
lemma mul_add_mod' (a b c : ℕ) : (a * b + c) % b = c % b := by rw [Nat.mul_comm, Nat.mul_add_mod]
#align nat.mul_add_mod Nat.mul_add_mod'

lemma mul_add_mod_of_lt (h : c < b) : (a * b + c) % b = c := by
  rw [Nat.mul_add_mod', Nat.mod_eq_of_lt h]
#align nat.mul_add_mod_of_lt Nat.mul_add_mod_of_lt

set_option linter.deprecated false in
@[simp]
protected theorem not_two_dvd_bit1 (n : ℕ) : ¬2 ∣ bit1 n := by
  rw [bit1, Nat.dvd_add_right, Nat.dvd_one]
  -- Porting note: was `cc`
  · decide
  · rw [bit0, ← Nat.two_mul]
    exact Nat.dvd_mul_right _ _
#align nat.not_two_dvd_bit1 Nat.not_two_dvd_bit1

/-- A natural number `m` divides the sum `m + n` if and only if `m` divides `n`.-/
@[simp] protected lemma dvd_add_self_left : m ∣ m + n ↔ m ∣ n := Nat.dvd_add_right (Nat.dvd_refl m)
#align nat.dvd_add_self_left Nat.dvd_add_self_left

/-- A natural number `m` divides the sum `n + m` if and only if `m` divides `n`.-/
@[simp] protected lemma dvd_add_self_right : m ∣ n + m ↔ m ∣ n := Nat.dvd_add_left (Nat.dvd_refl m)
#align nat.dvd_add_self_right Nat.dvd_add_self_right

-- TODO: update `Nat.dvd_sub` in core
lemma dvd_sub' (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n := by
  rcases le_total n m with H | H
  · exact dvd_sub H h₁ h₂
  · rw [Nat.sub_eq_zero_iff_le.mpr H]
    exact Nat.dvd_zero k
#align nat.dvd_sub' Nat.dvd_sub'

lemma succ_div : ∀ a b : ℕ, (a + 1) / b = a / b + if b ∣ a + 1 then 1 else 0
  | a, 0 => by simp
  | 0, 1 => by simp
  | 0, b + 2 => by
    have hb2 : b + 2 > 1 := by simp
    simp [ne_of_gt hb2, div_eq_of_lt hb2]
  | a + 1, b + 1 => by
    rw [Nat.div_eq]
    conv_rhs => rw [Nat.div_eq]
    by_cases hb_eq_a : b = a + 1
    · simp [hb_eq_a, Nat.le_refl, Nat.not_succ_le_self, Nat.dvd_refl]
    by_cases hb_le_a1 : b ≤ a + 1
    · have hb_le_a : b ≤ a := le_of_lt_succ (lt_of_le_of_ne hb_le_a1 hb_eq_a)
      have h₁ : 0 < b + 1 ∧ b + 1 ≤ a + 1 + 1 := ⟨succ_pos _, Nat.add_le_add_iff_right.2 hb_le_a1⟩
      have h₂ : 0 < b + 1 ∧ b + 1 ≤ a + 1 := ⟨succ_pos _, Nat.add_le_add_iff_right.2 hb_le_a⟩
      have dvd_iff : b + 1 ∣ a - b + 1 ↔ b + 1 ∣ a + 1 + 1 := by
        rw [Nat.dvd_add_iff_left (Nat.dvd_refl (b + 1)), ← Nat.add_sub_add_right a 1 b,
          Nat.add_comm (_ - _), Nat.add_assoc, Nat.sub_add_cancel (succ_le_succ hb_le_a),
          Nat.add_comm 1]
      have wf : a - b < a + 1 := lt_succ_of_le (Nat.sub_le _ _)
      rw [if_pos h₁, if_pos h₂, Nat.add_sub_add_right, Nat.add_sub_add_right, Nat.add_comm a,
        Nat.add_sub_assoc hb_le_a, Nat.add_comm 1,
        have := wf
        succ_div (a - b)]
      simp [dvd_iff, succ_eq_add_one, Nat.add_comm 1, Nat.add_assoc]
    · have hba : ¬b ≤ a := not_le_of_gt (lt_trans (lt_succ_self a) (lt_of_not_ge hb_le_a1))
      have hb_dvd_a : ¬b + 1 ∣ a + 2 := fun h =>
        hb_le_a1 (le_of_succ_le_succ (le_of_dvd (succ_pos _) h))
      simp [hba, hb_le_a1, hb_dvd_a]
#align nat.succ_div Nat.succ_div

lemma succ_div_of_dvd (hba : b ∣ a + 1) : (a + 1) / b = a / b + 1 := by rw [succ_div, if_pos hba]
#align nat.succ_div_of_dvd Nat.succ_div_of_dvd

lemma succ_div_of_not_dvd (hba : ¬b ∣ a + 1) : (a + 1) / b = a / b := by
  rw [succ_div, if_neg hba, Nat.add_zero]
#align nat.succ_div_of_not_dvd Nat.succ_div_of_not_dvd

lemma dvd_iff_div_mul_eq (n d : ℕ) : d ∣ n ↔ n / d * d = n :=
  ⟨fun h => Nat.div_mul_cancel h, fun h => by rw [← h]; exact Nat.dvd_mul_left _ _⟩
#align nat.dvd_iff_div_mul_eq Nat.dvd_iff_div_mul_eq

lemma dvd_iff_le_div_mul (n d : ℕ) : d ∣ n ↔ n ≤ n / d * d :=
  ((dvd_iff_div_mul_eq _ _).trans le_antisymm_iff).trans (and_iff_right (div_mul_le_self n d))
#align nat.dvd_iff_le_div_mul Nat.dvd_iff_le_div_mul

lemma dvd_iff_dvd_dvd (n d : ℕ) : d ∣ n ↔ ∀ k : ℕ, k ∣ d → k ∣ n :=
  ⟨fun h _ hkd => Nat.dvd_trans hkd h, fun h => h _ (Nat.dvd_refl _)⟩
#align nat.dvd_iff_dvd_dvd Nat.dvd_iff_dvd_dvd

lemma dvd_div_of_mul_dvd (h : a * b ∣ c) : b ∣ c / a :=
  if ha : a = 0 then by simp [ha]
  else
    have ha : 0 < a := Nat.pos_of_ne_zero ha
    have h1 : ∃ d, c = a * b * d := h
    let ⟨d, hd⟩ := h1
    have h2 : c / a = b * d := Nat.div_eq_of_eq_mul_right ha (by simpa [Nat.mul_assoc] using hd)
    show ∃ d, c / a = b * d from ⟨d, h2⟩
#align nat.dvd_div_of_mul_dvd Nat.dvd_div_of_mul_dvd

@[simp] lemma dvd_div_iff (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b :=
  ⟨fun h => mul_dvd_of_dvd_div hbc h, fun h => dvd_div_of_mul_dvd h⟩
#align nat.dvd_div_iff Nat.dvd_div_iff

lemma dvd_mul_of_div_dvd (h : b ∣ a) (hdiv : a / b ∣ c) : a ∣ b * c := by
  obtain ⟨e, rfl⟩ := hdiv
  rw [← Nat.mul_assoc, Nat.mul_comm _ (a / b), Nat.div_mul_cancel h]
  exact Nat.dvd_mul_right a e

@[simp] lemma div_dvd_iff_dvd_mul (h : b ∣ a) (hb : b ≠ 0) : a / b ∣ c ↔ a ∣ b * c :=
  exists_congr <| fun d => by
  have := Nat.dvd_trans (Nat.dvd_mul_left _ d) (Nat.mul_dvd_mul_left d h)
  rw [eq_comm, Nat.mul_comm, ← Nat.mul_div_assoc d h,
    Nat.div_eq_iff_eq_mul_right (Nat.pos_of_ne_zero hb) this, Nat.mul_comm, eq_comm]

@[simp] lemma div_div_div_eq_div (dvd : b ∣ a) (dvd2 : a ∣ c) : c / (a / b) / b = c / a :=
  match a, b, c with
  | 0, _, _ => by simp
  | a + 1, 0, _ => by simp at dvd
  | a + 1, c + 1, _ => by
    have a_split : a + 1 ≠ 0 := succ_ne_zero a
    have c_split : c + 1 ≠ 0 := succ_ne_zero c
    rcases dvd2 with ⟨k, rfl⟩
    rcases dvd with ⟨k2, pr⟩
    have k2_nonzero : k2 ≠ 0 := fun k2_zero => by simp [k2_zero] at pr
    rw [Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero a_split), pr,
      Nat.mul_div_cancel_left k2 (Nat.pos_of_ne_zero c_split), Nat.mul_comm ((c + 1) * k2) k, ←
      Nat.mul_assoc k (c + 1) k2, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero k2_nonzero),
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero c_split)]
#align nat.div_div_div_eq_div Nat.div_div_div_eq_div

/-- If a small natural number is divisible by a larger natural number,
the small number is zero. -/
lemma eq_zero_of_dvd_of_lt (w : a ∣ b) (h : b < a) : b = 0 :=
  Nat.eq_zero_of_dvd_of_div_eq_zero w ((Nat.div_eq_zero_iff (lt_of_le_of_lt (zero_le b) h)).mpr h)
#align nat.eq_zero_of_dvd_of_lt Nat.eq_zero_of_dvd_of_lt

lemma le_of_lt_add_of_dvd (h : a < b + n) : n ∣ a → n ∣ b → a ≤ b := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  rw [← mul_succ] at h
  exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.1 <| Nat.lt_of_mul_lt_mul_left h)
#align nat.le_of_lt_add_of_dvd Nat.le_of_lt_add_of_dvd

/-- `n` is not divisible by `a` iff it is between `a * k` and `a * (k + 1)` for some `k`. -/
lemma not_dvd_iff_between_consec_multiples (n : ℕ) {a : ℕ} (ha : 0 < a) :
    (∃ k : ℕ, a * k < n ∧ n < a * (k + 1)) ↔ ¬a ∣ n := by
  refine
    ⟨fun ⟨k, hk1, hk2⟩ => not_dvd_of_between_consec_multiples hk1 hk2, fun han =>
      ⟨n / a, ⟨lt_of_le_of_ne (mul_div_le n a) ?_, lt_mul_div_succ _ ha⟩⟩⟩
  exact mt (⟨n / a, Eq.symm ·⟩) han
#align nat.not_dvd_iff_between_consec_multiples Nat.not_dvd_iff_between_consec_multiples

/-- Two natural numbers are equal if and only if they have the same multiples. -/
lemma dvd_right_iff_eq : (∀ a : ℕ, m ∣ a ↔ n ∣ a) ↔ m = n :=
  ⟨fun h => Nat.dvd_antisymm ((h _).mpr (Nat.dvd_refl _)) ((h _).mp (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩
#align nat.dvd_right_iff_eq Nat.dvd_right_iff_eq

/-- Two natural numbers are equal if and only if they have the same divisors. -/
lemma dvd_left_iff_eq : (∀ a : ℕ, a ∣ m ↔ a ∣ n) ↔ m = n :=
  ⟨fun h => Nat.dvd_antisymm ((h _).mp (Nat.dvd_refl _)) ((h _).mpr (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩
#align nat.dvd_left_iff_eq Nat.dvd_left_iff_eq

/-- `dvd` is injective in the left argument -/
lemma dvd_left_injective : Function.Injective ((· ∣ ·) : ℕ → ℕ → Prop) := fun _ _ h =>
  dvd_right_iff_eq.mp fun a => iff_of_eq (congr_fun h a)
#align nat.dvd_left_injective Nat.dvd_left_injective

lemma div_lt_div_of_lt_of_dvd {a b d : ℕ} (hdb : d ∣ b) (h : a < b) : a / d < b / d := by
  rw [Nat.lt_div_iff_mul_lt hdb]
  exact lt_of_le_of_lt (mul_div_le a d) h
#align nat.div_lt_div_of_lt_of_dvd Nat.div_lt_div_of_lt_of_dvd

/-!
### `sqrt`

See [Wikipedia, *Methods of computing square roots*]
(https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)).
-/

private lemma iter_fp_bound (n k : ℕ) :
    let iter_next (n guess : ℕ) := (guess + n / guess) / 2;
    sqrt.iter n k ≤ iter_next n (sqrt.iter n k) := by
  intro iter_next
  unfold sqrt.iter
  if h : (k + n / k) / 2 < k then
    simpa [if_pos h] using iter_fp_bound _ _
  else
    simpa [if_neg h] using Nat.le_of_not_lt h

private lemma AM_GM : {a b : ℕ} → (4 * a * b ≤ (a + b) * (a + b))
  | 0, _ => by rw [Nat.mul_zero, Nat.zero_mul]; exact zero_le _
  | _, 0 => by rw [Nat.mul_zero]; exact zero_le _
  | a + 1, b + 1 => by
    simpa only [Nat.mul_add, Nat.add_mul, show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, Nat.one_mul,
      Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_le_add_iff_left]
      using Nat.add_le_add_right (@AM_GM a b) 4

-- These two lemmas seem like they belong to `Batteries.Data.Nat.Basic`.

lemma sqrt.iter_sq_le (n guess : ℕ) : sqrt.iter n guess * sqrt.iter n guess ≤ n := by
  unfold sqrt.iter
  let next := (guess + n / guess) / 2
  if h : next < guess then
    simpa only [dif_pos h] using sqrt.iter_sq_le n next
  else
    simp only [dif_neg h]
    apply Nat.mul_le_of_le_div
    apply Nat.le_of_add_le_add_left (a := guess)
    rw [← Nat.mul_two, ← le_div_iff_mul_le]
    · exact Nat.le_of_not_lt h
    · exact Nat.zero_lt_two

lemma sqrt.lt_iter_succ_sq (n guess : ℕ) (hn : n < (guess + 1) * (guess + 1)) :
    n < (sqrt.iter n guess + 1) * (sqrt.iter n guess + 1) := by
  unfold sqrt.iter
  -- m was `next`
  let m := (guess + n / guess) / 2
  dsimp
  split_ifs with h
  · suffices n < (m + 1) * (m + 1) by
      simpa only [dif_pos h] using sqrt.lt_iter_succ_sq n m this
    refine Nat.lt_of_mul_lt_mul_left ?_ (a := 4 * (guess * guess))
    apply Nat.lt_of_le_of_lt AM_GM
    rw [show (4 : ℕ) = 2 * 2 from rfl]
    rw [Nat.mul_mul_mul_comm 2, Nat.mul_mul_mul_comm (2 * guess)]
    refine Nat.mul_self_lt_mul_self (?_ : _ < _ * succ (_ / 2))
    rw [← add_div_right _ (by decide), Nat.mul_comm 2, Nat.mul_assoc,
      show guess + n / guess + 2 = (guess + n / guess + 1) + 1 from rfl]
    have aux_lemma {a : ℕ} : a ≤ 2 * ((a + 1) / 2) := by omega
    refine lt_of_lt_of_le ?_ (Nat.mul_le_mul_left _ aux_lemma)
    rw [Nat.add_assoc, Nat.mul_add]
    exact Nat.add_lt_add_left (lt_mul_div_succ _ (lt_of_le_of_lt (Nat.zero_le m) h)) _
  · simpa only [dif_neg h] using hn

#align nat.sqrt Nat.sqrt
-- Porting note: the implementation of `Nat.sqrt` in `Batteries` no longer needs `sqrt_aux`.
#noalign nat.sqrt_aux_dec
#noalign nat.sqrt_aux
#noalign nat.sqrt_aux_0
#noalign nat.sqrt_aux_1
#noalign nat.sqrt_aux_2
private def IsSqrt (n q : ℕ) : Prop :=
  q * q ≤ n ∧ n < (q + 1) * (q + 1)
-- Porting note: as the definition of square root has changed,
-- the proof of `sqrt_isSqrt` is attempted from scratch.
/-
Sketch of proof:
Up to rounding, in terms of the definition of `sqrt.iter`,

* By AM-GM inequality, `next² ≥ n` giving one of the bounds.
* When we terminated, we have `guess ≥ next` from which we deduce the other bound `n ≥ next²`.

To turn this into a lean proof we need to manipulate, use properties of natural number division etc.
-/
private lemma sqrt_isSqrt (n : ℕ) : IsSqrt n (sqrt n) := by
  match n with
  | 0 => simp [IsSqrt, sqrt]
  | 1 => simp [IsSqrt, sqrt]
  | n + 2 =>
    have h : ¬ (n + 2) ≤ 1 := by simp
    simp only [IsSqrt, sqrt, h, ite_false]
    refine ⟨sqrt.iter_sq_le _ _, sqrt.lt_iter_succ_sq _ _ ?_⟩
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, ← Nat.add_assoc]
    rw [lt_add_one_iff, Nat.add_assoc, ← Nat.mul_two]
    refine le_trans (Nat.le_of_eq (div_add_mod' (n + 2) 2).symm) ?_
    rw [Nat.add_comm, Nat.add_le_add_iff_right, add_mod_right]
    simp only [Nat.zero_lt_two, add_div_right, succ_mul_succ]
    refine le_trans (b := 1) ?_ ?_
    · exact (lt_succ.1 <| mod_lt n Nat.zero_lt_two)
    · exact Nat.le_add_left _ _

lemma sqrt_le (n : ℕ) : sqrt n * sqrt n ≤ n := (sqrt_isSqrt n).left
#align nat.sqrt_le Nat.sqrt_le

lemma sqrt_le' (n : ℕ) : sqrt n ^ 2 ≤ n := by simpa [Nat.pow_two] using sqrt_le n
#align nat.sqrt_le' Nat.sqrt_le'

lemma lt_succ_sqrt (n : ℕ) : n < succ (sqrt n) * succ (sqrt n) := (sqrt_isSqrt n).right
#align nat.lt_succ_sqrt Nat.lt_succ_sqrt

lemma lt_succ_sqrt' (n : ℕ) : n < succ (sqrt n) ^ 2 := by simpa [Nat.pow_two] using lt_succ_sqrt n
#align nat.lt_succ_sqrt' Nat.lt_succ_sqrt'

lemma sqrt_le_add (n : ℕ) : n ≤ sqrt n * sqrt n + sqrt n + sqrt n := by
  rw [← succ_mul]; exact le_of_lt_succ (lt_succ_sqrt n)
#align nat.sqrt_le_add Nat.sqrt_le_add

lemma le_sqrt : m ≤ sqrt n ↔ m * m ≤ n :=
  ⟨fun h ↦ le_trans (mul_self_le_mul_self h) (sqrt_le n),
    fun h ↦ le_of_lt_succ <| Nat.mul_self_lt_mul_self_iff.1 <| lt_of_le_of_lt h (lt_succ_sqrt n)⟩
#align nat.le_sqrt Nat.le_sqrt

lemma le_sqrt' : m ≤ sqrt n ↔ m ^ 2 ≤ n := by simpa only [Nat.pow_two] using le_sqrt
#align nat.le_sqrt' Nat.le_sqrt'

lemma sqrt_lt : sqrt m < n ↔ m < n * n := by simp only [← not_le, le_sqrt]
#align nat.sqrt_lt Nat.sqrt_lt

lemma sqrt_lt' : sqrt m < n ↔ m < n ^ 2 := by simp only [← not_le, le_sqrt']
#align nat.sqrt_lt' Nat.sqrt_lt'

lemma sqrt_le_self (n : ℕ) : sqrt n ≤ n := le_trans (le_mul_self _) (sqrt_le n)
#align nat.sqrt_le_self Nat.sqrt_le_self

lemma sqrt_le_sqrt (h : m ≤ n) : sqrt m ≤ sqrt n := le_sqrt.2 (le_trans (sqrt_le _) h)
#align nat.sqrt_le_sqrt Nat.sqrt_le_sqrt

@[simp] lemma sqrt_zero : sqrt 0 = 0 := rfl
#align nat.sqrt_zero Nat.sqrt_zero

@[simp] lemma sqrt_one : sqrt 1 = 1 := rfl
#align nat.sqrt_one Nat.sqrt_one

lemma sqrt_eq_zero : sqrt n = 0 ↔ n = 0 :=
  ⟨fun h ↦
      Nat.eq_zero_of_le_zero <| le_of_lt_succ <| (@sqrt_lt n 1).1 <| by rw [h]; decide,
    by rintro rfl; simp⟩
#align nat.sqrt_eq_zero Nat.sqrt_eq_zero

lemma eq_sqrt : a = sqrt n ↔ a * a ≤ n ∧ n < (a + 1) * (a + 1) :=
  ⟨fun e ↦ e.symm ▸ sqrt_isSqrt n,
   fun ⟨h₁, h₂⟩ ↦ le_antisymm (le_sqrt.2 h₁) (le_of_lt_succ <| sqrt_lt.2 h₂)⟩
#align nat.eq_sqrt Nat.eq_sqrt

lemma eq_sqrt' : a = sqrt n ↔ a ^ 2 ≤ n ∧ n < (a + 1) ^ 2 := by
  simpa only [Nat.pow_two] using eq_sqrt
#align nat.eq_sqrt' Nat.eq_sqrt'

lemma le_three_of_sqrt_eq_one (h : sqrt n = 1) : n ≤ 3 :=
  le_of_lt_succ <| (@sqrt_lt n 2).1 <| by rw [h]; decide
#align nat.le_three_of_sqrt_eq_one Nat.le_three_of_sqrt_eq_one

lemma sqrt_lt_self (h : 1 < n) : sqrt n < n :=
  sqrt_lt.2 <| by have := Nat.mul_lt_mul_of_pos_left h (lt_of_succ_lt h); rwa [Nat.mul_one] at this
#align nat.sqrt_lt_self Nat.sqrt_lt_self

lemma sqrt_pos : 0 < sqrt n ↔ 0 < n :=
  le_sqrt
#align nat.sqrt_pos Nat.sqrt_pos

lemma sqrt_add_eq (n : ℕ) (h : a ≤ n + n) : sqrt (n * n + a) = n :=
  le_antisymm
    (le_of_lt_succ <|
      sqrt_lt.2 <| by
        rw [succ_mul, mul_succ, add_succ, Nat.add_assoc];
          exact lt_succ_of_le (Nat.add_le_add_left h _))
    (le_sqrt.2 <| Nat.le_add_right _ _)
#align nat.sqrt_add_eq Nat.sqrt_add_eq

lemma sqrt_add_eq' (n : ℕ) (h : a ≤ n + n) : sqrt (n ^ 2 + a) = n := by
  simpa [Nat.pow_two] using sqrt_add_eq n h
#align nat.sqrt_add_eq' Nat.sqrt_add_eq'

lemma sqrt_eq (n : ℕ) : sqrt (n * n) = n := sqrt_add_eq n (zero_le _)
#align nat.sqrt_eq Nat.sqrt_eq

lemma sqrt_eq' (n : ℕ) : sqrt (n ^ 2) = n := sqrt_add_eq' n (zero_le _)
#align nat.sqrt_eq' Nat.sqrt_eq'

lemma sqrt_succ_le_succ_sqrt (n : ℕ) : sqrt n.succ ≤ n.sqrt.succ :=
  le_of_lt_succ <| sqrt_lt.2 <| lt_succ_of_le <|
  succ_le_succ <| le_trans (sqrt_le_add n) <| Nat.add_le_add_right
    (by refine add_le_add (Nat.mul_le_mul_right _ ?_) ?_ <;> exact Nat.le_add_right _ 2) _
#align nat.sqrt_succ_le_succ_sqrt Nat.sqrt_succ_le_succ_sqrt

lemma exists_mul_self (x : ℕ) : (∃ n, n * n = x) ↔ sqrt x * sqrt x = x :=
  ⟨fun ⟨n, hn⟩ ↦ by rw [← hn, sqrt_eq], fun h ↦ ⟨sqrt x, h⟩⟩
#align nat.exists_mul_self Nat.exists_mul_self

lemma exists_mul_self' (x : ℕ) : (∃ n, n ^ 2 = x) ↔ sqrt x ^ 2 = x := by
  simpa only [Nat.pow_two] using exists_mul_self x
#align nat.exists_mul_self' Nat.exists_mul_self'

lemma sqrt_mul_sqrt_lt_succ (n : ℕ) : sqrt n * sqrt n < n + 1 :=
  Nat.lt_succ_iff.mpr (sqrt_le _)
#align nat.sqrt_mul_sqrt_lt_succ Nat.sqrt_mul_sqrt_lt_succ

lemma sqrt_mul_sqrt_lt_succ' (n : ℕ) : sqrt n ^ 2 < n + 1 :=
  Nat.lt_succ_iff.mpr (sqrt_le' _)
#align nat.sqrt_mul_sqrt_lt_succ' Nat.sqrt_mul_sqrt_lt_succ'

lemma succ_le_succ_sqrt (n : ℕ) : n + 1 ≤ (sqrt n + 1) * (sqrt n + 1) :=
  le_of_pred_lt (lt_succ_sqrt _)
#align nat.succ_le_succ_sqrt Nat.succ_le_succ_sqrt

lemma succ_le_succ_sqrt' (n : ℕ) : n + 1 ≤ (sqrt n + 1) ^ 2 :=
  le_of_pred_lt (lt_succ_sqrt' _)
#align nat.succ_le_succ_sqrt' Nat.succ_le_succ_sqrt'

/-- There are no perfect squares strictly between m² and (m+1)² -/
lemma not_exists_sq (hl : m * m < n) (hr : n < (m + 1) * (m + 1)) : ¬∃ t, t * t = n := by
  rintro ⟨t, rfl⟩
  have h1 : m < t := Nat.mul_self_lt_mul_self_iff.1 hl
  have h2 : t < m + 1 := Nat.mul_self_lt_mul_self_iff.1 hr
  exact (not_lt_of_ge <| le_of_lt_succ h2) h1
#align nat.not_exists_sq Nat.not_exists_sq

lemma not_exists_sq' : m ^ 2 < n → n < (m + 1) ^ 2 → ¬∃ t, t ^ 2 = n := by
  simpa only [Nat.pow_two] using not_exists_sq
#align nat.not_exists_sq' Nat.not_exists_sq'

/-! ### `find` -/

section Find
variable [DecidablePred p] [DecidablePred q]

lemma find_eq_iff (h : ∃ n : ℕ, p n) : Nat.find h = m ↔ p m ∧ ∀ n < m, ¬ p n := by
  constructor
  · rintro rfl
    exact ⟨Nat.find_spec h, fun _ ↦ Nat.find_min h⟩
  · rintro ⟨hm, hlt⟩
    exact le_antisymm (Nat.find_min' h hm) (not_lt.1 <| imp_not_comm.1 (hlt _) <| Nat.find_spec h)
#align nat.find_eq_iff Nat.find_eq_iff

@[simp] lemma find_lt_iff (h : ∃ n : ℕ, p n) (n : ℕ) : Nat.find h < n ↔ ∃ m < n, p m :=
  ⟨fun h2 ↦ ⟨Nat.find h, h2, Nat.find_spec h⟩,
    fun ⟨_, hmn, hm⟩ ↦ Nat.lt_of_le_of_lt (Nat.find_min' h hm) hmn⟩
#align nat.find_lt_iff Nat.find_lt_iff

@[simp] lemma find_le_iff (h : ∃ n : ℕ, p n) (n : ℕ) : Nat.find h ≤ n ↔ ∃ m ≤ n, p m := by
  simp only [exists_prop, ← Nat.lt_succ_iff, find_lt_iff]
#align nat.find_le_iff Nat.find_le_iff

@[simp] lemma le_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n ≤ Nat.find h ↔ ∀ m < n, ¬ p m := by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]
#align nat.le_find_iff Nat.le_find_iff

@[simp] lemma lt_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n < Nat.find h ↔ ∀ m ≤ n, ¬ p m := by
  simp only [← succ_le_iff, le_find_iff, succ_le_succ_iff]
#align nat.lt_find_iff Nat.lt_find_iff

@[simp] lemma find_eq_zero (h : ∃ n : ℕ, p n) : Nat.find h = 0 ↔ p 0 := by simp [find_eq_iff]
#align nat.find_eq_zero Nat.find_eq_zero

lemma find_mono (h : ∀ n, q n → p n) {hp : ∃ n, p n} {hq : ∃ n, q n} : Nat.find hp ≤ Nat.find hq :=
  Nat.find_min' _ (h _ (Nat.find_spec hq))
#align nat.find_mono Nat.find_mono

lemma find_le {h : ∃ n, p n} (hn : p n) : Nat.find h ≤ n :=
  (Nat.find_le_iff _ _).2 ⟨n, le_refl _, hn⟩
#align nat.find_le Nat.find_le

lemma find_comp_succ (h₁ : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h0 : ¬ p 0) :
    Nat.find h₁ = Nat.find h₂ + 1 := by
  refine (find_eq_iff _).2 ⟨Nat.find_spec h₂, fun n hn ↦ ?_⟩
  cases n
  exacts [h0, @Nat.find_min (fun n ↦ p (n + 1)) _ h₂ _ (succ_lt_succ_iff.1 hn)]
#align nat.find_comp_succ Nat.find_comp_succ

-- Porting note (#10618): removing `simp` attribute as `simp` can prove it
lemma find_pos (h : ∃ n : ℕ, p n) : 0 < Nat.find h ↔ ¬p 0 :=
  Nat.pos_iff_ne_zero.trans (Nat.find_eq_zero _).not
#align nat.find_pos Nat.find_pos

lemma find_add {hₘ : ∃ m, p (m + n)} {hₙ : ∃ n, p n} (hn : n ≤ Nat.find hₙ) :
    Nat.find hₘ + n = Nat.find hₙ := by
  refine le_antisymm ((le_find_iff _ _).2 fun m hm hpm => Nat.not_le.2 hm ?_) ?_
  · have hnm : n ≤ m := le_trans hn (find_le hpm)
    refine Nat.add_le_of_le_sub hnm (find_le ?_)
    rwa [Nat.sub_add_cancel hnm]
  · rw [← Nat.sub_le_iff_le_add]
    refine (le_find_iff _ _).2 fun m hm hpm => Nat.not_le.2 hm ?_
    rw [Nat.sub_le_iff_le_add]
    exact find_le hpm
#align nat.find_add Nat.find_add

end Find

/-! ### `Nat.findGreatest` -/

section FindGreatest

/-- `Nat.findGreatest P n` is the largest `i ≤ bound` such that `P i` holds, or `0` if no such `i`
exists -/
def findGreatest (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ
  | 0 => 0
  | n + 1 => if P (n + 1) then n + 1 else Nat.findGreatest P n
#align nat.find_greatest Nat.findGreatest

variable {P Q : ℕ → Prop} [DecidablePred P] {n : ℕ}

@[simp] lemma findGreatest_zero : Nat.findGreatest P 0 = 0 := rfl
#align nat.find_greatest_zero Nat.findGreatest_zero

lemma findGreatest_succ (n : ℕ) :
    Nat.findGreatest P (n + 1) = if P (n + 1) then n + 1 else Nat.findGreatest P n := rfl
#align nat.find_greatest_succ Nat.findGreatest_succ

@[simp] lemma findGreatest_eq : ∀ {n}, P n → Nat.findGreatest P n = n
  | 0, _ => rfl
  | n + 1, h => by simp [Nat.findGreatest, h]
#align nat.find_greatest_eq Nat.findGreatest_eq

@[simp]
lemma findGreatest_of_not (h : ¬ P (n + 1)) : findGreatest P (n + 1) = findGreatest P n := by
  simp [Nat.findGreatest, h]
#align nat.find_greatest_of_not Nat.findGreatest_of_not

lemma findGreatest_eq_iff :
    Nat.findGreatest P k = m ↔ m ≤ k ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n⦄, m < n → n ≤ k → ¬P n := by
  induction' k with k ihk generalizing m
  · rw [eq_comm, Iff.comm]
    simp only [zero_eq, Nat.le_zero, ne_eq, findGreatest_zero, and_iff_left_iff_imp]
    rintro rfl
    exact ⟨fun h ↦ (h rfl).elim, fun n hlt heq ↦ by omega⟩
  · by_cases hk : P (k + 1)
    · rw [findGreatest_eq hk]
      constructor
      · rintro rfl
        exact ⟨le_refl _, fun _ ↦ hk, fun n hlt hle ↦ by omega⟩
      · rintro ⟨hle, h0, hm⟩
        rcases Decidable.eq_or_lt_of_le hle with (rfl | hlt)
        exacts [rfl, (hm hlt (le_refl _) hk).elim]
    · rw [findGreatest_of_not hk, ihk]
      constructor
      · rintro ⟨hle, hP, hm⟩
        refine ⟨le_trans hle k.le_succ, hP, fun n hlt hle ↦ ?_⟩
        rcases Decidable.eq_or_lt_of_le hle with (rfl | hlt')
        exacts [hk, hm hlt <| Nat.lt_succ_iff.1 hlt']
      · rintro ⟨hle, hP, hm⟩
        refine ⟨Nat.lt_succ_iff.1 (lt_of_le_of_ne hle ?_), hP,
          fun n hlt hle ↦ hm hlt (le_trans hle k.le_succ)⟩
        rintro rfl
        exact hk (hP k.succ_ne_zero)
#align nat.find_greatest_eq_iff Nat.findGreatest_eq_iff

lemma findGreatest_eq_zero_iff : Nat.findGreatest P k = 0 ↔ ∀ ⦃n⦄, 0 < n → n ≤ k → ¬P n := by
  simp [findGreatest_eq_iff]
#align nat.find_greatest_eq_zero_iff Nat.findGreatest_eq_zero_iff

@[simp] lemma findGreatest_pos : 0 < Nat.findGreatest P k ↔ ∃ n, 0 < n ∧ n ≤ k ∧ P n := by
  rw [Nat.pos_iff_ne_zero, Ne, findGreatest_eq_zero_iff]; push_neg; rfl

lemma findGreatest_spec (hmb : m ≤ n) (hm : P m) : P (Nat.findGreatest P n) := by
  by_cases h : Nat.findGreatest P n = 0
  · cases m
    · rwa [h]
    exact ((findGreatest_eq_zero_iff.1 h) (zero_lt_succ _) hmb hm).elim
  · exact (findGreatest_eq_iff.1 rfl).2.1 h
#align nat.find_greatest_spec Nat.findGreatest_spec

lemma findGreatest_le (n : ℕ) : Nat.findGreatest P n ≤ n :=
  (findGreatest_eq_iff.1 rfl).1
#align nat.find_greatest_le Nat.findGreatest_le

lemma le_findGreatest (hmb : m ≤ n) (hm : P m) : m ≤ Nat.findGreatest P n :=
  le_of_not_lt fun hlt => (findGreatest_eq_iff.1 rfl).2.2 hlt hmb hm
#align nat.le_find_greatest Nat.le_findGreatest

lemma findGreatest_mono_right (P : ℕ → Prop) [DecidablePred P] {m n} (hmn : m ≤ n) :
    Nat.findGreatest P m ≤ Nat.findGreatest P n := by
  induction' hmn with k hmk ih
  · simp
  rw [findGreatest_succ]
  split_ifs
  · exact le_trans ih $ le_trans (findGreatest_le _) (le_succ _)
  · exact ih
#align nat.find_greatest_mono_right Nat.findGreatest_mono_right

lemma findGreatest_mono_left [DecidablePred Q] (hPQ : ∀ n, P n → Q n) (n : ℕ) :
    Nat.findGreatest P n ≤ Nat.findGreatest Q n := by
  induction' n with n hn
  · rfl
  by_cases h : P (n + 1)
  · rw [findGreatest_eq h, findGreatest_eq (hPQ _ h)]
  · rw [findGreatest_of_not h]
    exact le_trans hn (Nat.findGreatest_mono_right _ <| le_succ _)
#align nat.find_greatest_mono_left Nat.findGreatest_mono_left

lemma findGreatest_mono [DecidablePred Q] (hPQ : ∀ n, P n → Q n) (hmn : m ≤ n) :
    Nat.findGreatest P m ≤ Nat.findGreatest Q n :=
  le_trans (Nat.findGreatest_mono_right _ hmn) (findGreatest_mono_left hPQ _)
#align nat.find_greatest_mono Nat.findGreatest_mono

theorem findGreatest_is_greatest (hk : Nat.findGreatest P n < k) (hkb : k ≤ n) : ¬P k :=
  (findGreatest_eq_iff.1 rfl).2.2 hk hkb
#align nat.find_greatest_is_greatest Nat.findGreatest_is_greatest

theorem findGreatest_of_ne_zero (h : Nat.findGreatest P n = m) (h0 : m ≠ 0) : P m :=
  (findGreatest_eq_iff.1 h).2.1 h0
#align nat.find_greatest_of_ne_zero Nat.findGreatest_of_ne_zero

end FindGreatest

/-! ### Decidability of predicates -/

#align nat.decidable_ball_lt Nat.decidableBallLT
#align nat.decidable_forall_fin Nat.decidableForallFin
#align nat.decidable_ball_le Nat.decidableBallLE
#align nat.decidable_exists_lt Nat.decidableExistsLT
#align nat.decidable_exists_le Nat.decidableExistsLE

instance decidableLoHi (lo hi : ℕ) (P : ℕ → Prop) [H : DecidablePred P] :
    Decidable (∀ x, lo ≤ x → x < hi → P x) :=
  decidable_of_iff (∀ x < hi - lo, P (lo + x)) $ by
    refine ⟨fun al x hl hh ↦ ?_,
      fun al x h ↦ al _ (Nat.le_add_right _ _) (Nat.lt_sub_iff_add_lt'.1 h)⟩
    have := al (x - lo) ((Nat.sub_lt_sub_iff_right hl).2 hh)
    rwa [Nat.add_sub_cancel' hl] at this
#align nat.decidable_lo_hi Nat.decidableLoHi

instance decidableLoHiLe (lo hi : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Decidable (∀ x, lo ≤ x → x ≤ hi → P x) :=
  decidable_of_iff (∀ x, lo ≤ x → x < hi + 1 → P x) <|
    forall₂_congr fun _ _ ↦ imp_congr Nat.lt_succ_iff Iff.rfl
#align nat.decidable_lo_hi_le Nat.decidableLoHiLe

end Nat
