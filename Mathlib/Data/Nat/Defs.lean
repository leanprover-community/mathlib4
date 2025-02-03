/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.GCongr.CoreAttrs
import Mathlib.Tactic.PushNeg
import Mathlib.Util.AssertExists

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
variable {a b c d m n k : ℕ} {p : ℕ → Prop}

-- TODO: Move the `LinearOrder ℕ` instance to `Order.Nat` (https://github.com/leanprover-community/mathlib4/pull/13092).
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

-- Shortcut instances
instance : Preorder ℕ := inferInstance
instance : PartialOrder ℕ := inferInstance
instance : Min ℕ := inferInstance
instance : Max ℕ := inferInstance
instance : Ord ℕ := inferInstance

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

alias succ_inj := succ_inj'

lemma succ_injective : Injective Nat.succ := @succ.inj

lemma succ_ne_succ : succ m ≠ succ n ↔ m ≠ n := succ_injective.ne_iff

lemma succ_succ_ne_one (n : ℕ) : n.succ.succ ≠ 1 := by simp

lemma one_lt_succ_succ (n : ℕ) : 1 < n.succ.succ := succ_lt_succ <| succ_pos n

-- Moved to Batteries

alias _root_.LT.lt.nat_succ_le := succ_le_of_lt

lemma not_succ_lt_self : ¬ succ n < n := Nat.not_lt_of_ge n.le_succ

lemma succ_le_iff : succ m ≤ n ↔ m < n := ⟨lt_of_succ_le, succ_le_of_lt⟩

lemma le_succ_iff : m ≤ n.succ ↔ m ≤ n ∨ m = n.succ := by
  refine ⟨fun hmn ↦ (Nat.lt_or_eq_of_le hmn).imp_left le_of_lt_succ, ?_⟩
  rintro (hmn | rfl)
  · exact le_succ_of_le hmn
  · exact Nat.le_refl _

alias ⟨of_le_succ, _⟩ := le_succ_iff

lemma lt_iff_le_pred : ∀ {n}, 0 < n → (m < n ↔ m ≤ n - 1) | _ + 1, _ => Nat.lt_succ_iff

lemma le_of_pred_lt : ∀ {m}, pred m < n → m ≤ n
  | 0 => Nat.le_of_lt
  | _ + 1 => id

lemma lt_iff_add_one_le : m < n ↔ m + 1 ≤ n := by rw [succ_le_iff]

-- A flipped version of `lt_add_one_iff`.
lemma lt_one_add_iff : m < 1 + n ↔ m ≤ n := by simp only [Nat.add_comm, Nat.lt_succ_iff]

lemma one_add_le_iff : 1 + m ≤ n ↔ m < n := by simp only [Nat.add_comm, add_one_le_iff]

lemma one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 := Nat.pos_iff_ne_zero

lemma one_lt_iff_ne_zero_and_ne_one : ∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by omega

lemma le_one_iff_eq_zero_or_eq_one : ∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1 := by simp [le_succ_iff]

lemma one_le_of_lt (h : a < b) : 1 ≤ b := Nat.lt_of_le_of_lt (Nat.zero_le _) h

protected lemma min_left_comm (a b c : ℕ) : min a (min b c) = min b (min a c) := by
  rw [← Nat.min_assoc, ← Nat.min_assoc, b.min_comm]

protected lemma max_left_comm (a b c : ℕ) : max a (max b c) = max b (max a c) := by
  rw [← Nat.max_assoc, ← Nat.max_assoc, b.max_comm]

protected lemma min_right_comm (a b c : ℕ) : min (min a b) c = min (min a c) b := by
  rw [Nat.min_assoc, Nat.min_assoc, b.min_comm]

protected lemma max_right_comm (a b c : ℕ) : max (max a b) c = max (max a c) b := by
  rw [Nat.max_assoc, Nat.max_assoc, b.max_comm]

@[simp] lemma min_eq_zero_iff : min m n = 0 ↔ m = 0 ∨ n = 0 := by omega
@[simp] lemma max_eq_zero_iff : max m n = 0 ↔ m = 0 ∧ n = 0 := by omega

-- Moved to Batteries

lemma pred_one_add (n : ℕ) : pred (1 + n) = n := by rw [Nat.add_comm, add_one, Nat.pred_succ]

lemma pred_eq_self_iff : n.pred = n ↔ n = 0 := by cases n <;> simp [(Nat.succ_ne_self _).symm]

lemma pred_eq_of_eq_succ (H : m = n.succ) : m.pred = n := by simp [H]

@[simp] lemma pred_eq_succ_iff : n - 1 = m + 1 ↔ n = m + 2 := by
  cases n <;> constructor <;> rintro ⟨⟩ <;> rfl

lemma forall_lt_succ : (∀ m < n + 1, p m) ↔ (∀ m < n, p m) ∧ p n := by
  simp only [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq, or_comm, forall_eq_or_imp, and_comm]

lemma exists_lt_succ : (∃ m < n + 1, p m) ↔ (∃ m < n, p m) ∨ p n := by
  rw [← not_iff_not]
  push_neg
  exact forall_lt_succ

lemma two_lt_of_ne : ∀ {n}, n ≠ 0 → n ≠ 1 → n ≠ 2 → 2 < n
  | 0, h, _, _ => (h rfl).elim
  | 1, _, h, _ => (h rfl).elim
  | 2, _, _, h => (h rfl).elim
  -- Porting note: was `by decide`
  | n + 3, _, _, _ => le_add_left 3 n

/-! ### `pred` -/

@[simp] lemma add_succ_sub_one (m n : ℕ) : m + succ n - 1 = m + n := rfl

@[simp]
lemma succ_add_sub_one (n m : ℕ) : succ m + n - 1 = m + n := by rw [succ_add, Nat.add_one_sub_one]

lemma pred_sub (n m : ℕ) : pred n - m = pred (n - m) := by
  rw [← Nat.sub_one, Nat.sub_sub, one_add, sub_succ]

lemma self_add_sub_one : ∀ n, n + (n - 1) = 2 * n - 1
  | 0 => rfl
  | n + 1 => by rw [Nat.two_mul]; exact (add_succ_sub_one (Nat.succ _) _).symm

lemma sub_one_add_self (n : ℕ) : (n - 1) + n = 2 * n - 1 := Nat.add_comm _ n ▸ self_add_sub_one n

lemma self_add_pred (n : ℕ) : n + pred n = (2 * n).pred := self_add_sub_one n
lemma pred_add_self (n : ℕ) : pred n + n = (2 * n).pred := sub_one_add_self n

lemma pred_le_iff : pred m ≤ n ↔ m ≤ succ n :=
  ⟨le_succ_of_pred_le, by cases m; exacts [fun _ ↦ zero_le n, le_of_succ_le_succ]⟩

lemma lt_of_lt_pred (h : m < n - 1) : m < n := by omega

lemma le_add_pred_of_pos (a : ℕ) (hb : b ≠ 0) : a ≤ b + (a - 1) := by omega

/-! ### `add` -/

attribute [simp] le_add_left le_add_right Nat.lt_add_left_iff_pos Nat.lt_add_right_iff_pos
  Nat.add_le_add_iff_left Nat.add_le_add_iff_right Nat.add_lt_add_iff_left Nat.add_lt_add_iff_right
  not_lt_zero

-- We want to use these two lemmas earlier than the lemmas simp can prove them with
@[simp, nolint simpNF] protected alias add_left_inj := Nat.add_right_cancel_iff
@[simp, nolint simpNF] protected alias add_right_inj := Nat.add_left_cancel_iff
@[simp, nolint simpNF] protected lemma add_eq_left : a + b = a ↔ b = 0 := by omega
@[simp, nolint simpNF] protected lemma add_eq_right : a + b = b ↔ a = 0 := by omega

lemma two_le_iff : ∀ n, 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp

lemma add_eq_max_iff : m + n = max m n ↔ m = 0 ∨ n = 0 := by omega
lemma add_eq_min_iff : m + n = min m n ↔ m = 0 ∧ n = 0 := by omega

-- We want to use this lemma earlier than the lemma simp can prove it with
@[simp, nolint simpNF] protected lemma add_eq_zero : m + n = 0 ↔ m = 0 ∧ n = 0 := by omega

lemma add_pos_iff_pos_or_pos : 0 < m + n ↔ 0 < m ∨ 0 < n := by omega

lemma add_eq_one_iff : m + n = 1 ↔ m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 := by omega

lemma add_eq_two_iff : m + n = 2 ↔ m = 0 ∧ n = 2 ∨ m = 1 ∧ n = 1 ∨ m = 2 ∧ n = 0 := by
  omega

lemma add_eq_three_iff :
    m + n = 3 ↔ m = 0 ∧ n = 3 ∨ m = 1 ∧ n = 2 ∨ m = 2 ∧ n = 1 ∨ m = 3 ∧ n = 0 := by
  omega

lemma le_add_one_iff : m ≤ n + 1 ↔ m ≤ n ∨ m = n + 1 := by omega

lemma le_and_le_add_one_iff : n ≤ m ∧ m ≤ n + 1 ↔ m = n ∨ m = n + 1 := by omega

lemma add_succ_lt_add (hab : a < b) (hcd : c < d) : a + c + 1 < b + d := by omega

theorem le_or_le_of_add_eq_add_pred (h : a + c = b + d - 1) : b ≤ a ∨ d ≤ c := by omega

/-! ### `sub` -/

attribute [simp] Nat.sub_eq_zero_of_le Nat.sub_le_iff_le_add Nat.add_sub_cancel_left
  Nat.add_sub_cancel_right

/-- A version of `Nat.sub_succ` in the form `_ - 1` instead of `Nat.pred _`. -/
lemma sub_succ' (m n : ℕ) : m - n.succ = m - n - 1 := rfl

protected lemma sub_eq_of_eq_add' (h : a = b + c) : a - b = c := by omega
protected lemma eq_sub_of_add_eq (h : c + b = a) : c = a - b := by omega
protected lemma eq_sub_of_add_eq' (h : b + c = a) : c = a - b := by omega

protected lemma lt_sub_iff_add_lt : a < c - b ↔ a + b < c := ⟨add_lt_of_lt_sub, lt_sub_of_add_lt⟩
protected lemma lt_sub_iff_add_lt' : a < c - b ↔ b + a < c := by omega
protected lemma sub_lt_iff_lt_add (hba : b ≤ a) : a - b < c ↔ a < b + c := by omega
protected lemma sub_lt_iff_lt_add' (hba : b ≤ a) : a - b < c ↔ a < c + b := by omega

protected lemma sub_sub_sub_cancel_right (h : c ≤ b) : a - c - (b - c) = a - b := by omega
protected lemma add_sub_sub_cancel (h : c ≤ a) : a + b - (a - c) = b + c := by omega
protected lemma sub_add_sub_cancel (hab : b ≤ a) (hcb : c ≤ b) : a - b + (b - c) = a - c := by omega

lemma lt_pred_iff : a < pred b ↔ succ a < b := Nat.lt_sub_iff_add_lt (b := 1)

protected lemma sub_lt_sub_iff_right (h : c ≤ a) : a - c < b - c ↔ a < b := by omega

/-! ### `mul` -/

@[simp] lemma mul_def : Nat.mul m n = m * n := rfl

-- Porting note: removing `simp` attribute
protected lemma zero_eq_mul : 0 = m * n ↔ m = 0 ∨ n = 0 := by rw [eq_comm, Nat.mul_eq_zero]

lemma two_mul_ne_two_mul_add_one : 2 * n ≠ 2 * m + 1 :=
  mt (congrArg (· % 2))
    (by rw [Nat.add_comm, add_mul_mod_self_left, mul_mod_right, mod_eq_of_lt] <;> simp)

-- TODO: Replace `Nat.mul_right_cancel_iff` with `Nat.mul_left_inj`
protected lemma mul_left_inj (ha : a ≠ 0) : b * a = c * a ↔ b = c :=
  Nat.mul_right_cancel_iff (Nat.pos_iff_ne_zero.2 ha)

-- TODO: Replace `Nat.mul_left_cancel_iff` with `Nat.mul_right_inj`
protected lemma mul_right_inj (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  Nat.mul_left_cancel_iff (Nat.pos_iff_ne_zero.2 ha)

protected lemma mul_ne_mul_left (ha : a ≠ 0) : b * a ≠ c * a ↔ b ≠ c :=
  not_congr (Nat.mul_left_inj ha)

protected lemma mul_ne_mul_right (ha : a ≠ 0) : a * b ≠ a * c ↔ b ≠ c :=
  not_congr (Nat.mul_right_inj ha)

lemma mul_eq_left (ha : a ≠ 0) : a * b = a ↔ b = 1 := by simpa using Nat.mul_right_inj ha (c := 1)
lemma mul_eq_right (hb : b ≠ 0) : a * b = b ↔ a = 1 := by simpa using Nat.mul_left_inj hb (c := 1)

-- TODO: Deprecate
lemma mul_right_eq_self_iff (ha : 0 < a) : a * b = a ↔ b = 1 := mul_eq_left <| ne_of_gt ha

lemma mul_left_eq_self_iff (hb : 0 < b) : a * b = b ↔ a = 1 := mul_eq_right <| ne_of_gt hb

protected lemma le_of_mul_le_mul_right (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b :=
  Nat.le_of_mul_le_mul_left (by simpa [Nat.mul_comm]) hc

protected alias mul_sub := Nat.mul_sub_left_distrib
protected alias sub_mul := Nat.mul_sub_right_distrib

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

lemma eq_one_of_mul_eq_one_left (H : m * n = 1) : n = 1 :=
  eq_one_of_mul_eq_one_right (n := m) (by rwa [Nat.mul_comm])

@[simp] protected lemma lt_mul_iff_one_lt_left (hb : 0 < b) : b < a * b ↔ 1 < a := by
  simpa using Nat.mul_lt_mul_right (b := 1) hb

@[simp] protected lemma lt_mul_iff_one_lt_right (ha : 0 < a) : a < a * b ↔ 1 < b := by
  simpa using Nat.mul_lt_mul_left (b := 1) ha

lemma eq_zero_of_double_le (h : 2 * n ≤ n) : n = 0 := by omega

lemma eq_zero_of_mul_le (hb : 2 ≤ n) (h : n * m ≤ m) : m = 0 :=
  eq_zero_of_double_le <| Nat.le_trans (Nat.mul_le_mul_right _ hb) h

lemma succ_mul_pos (m : ℕ) (hn : 0 < n) : 0 < succ m * n := Nat.mul_pos m.succ_pos hn

lemma mul_self_le_mul_self (h : m ≤ n) : m * m ≤ n * n := Nat.mul_le_mul h h

lemma mul_lt_mul'' (hac : a < c) (hbd : b < d) : a * b < c * d :=
  Nat.mul_lt_mul_of_lt_of_le hac (Nat.le_of_lt hbd) <| by omega

lemma mul_self_lt_mul_self (h : m < n) : m * m < n * n := mul_lt_mul'' h h

lemma mul_self_le_mul_self_iff : m * m ≤ n * n ↔ m ≤ n :=
  ⟨fun h => Nat.le_of_not_lt fun h' => Nat.not_le_of_gt (mul_self_lt_mul_self h') h,
   mul_self_le_mul_self⟩

lemma mul_self_lt_mul_self_iff : m * m < n * n ↔ m < n := by
  simp only [← Nat.not_le, mul_self_le_mul_self_iff]

lemma le_mul_self : ∀ n : ℕ, n ≤ n * n
  | 0 => Nat.le_refl _
  | n + 1 => by simp [Nat.mul_add]

lemma mul_self_inj : m * m = n * n ↔ m = n := by
  simp [Nat.le_antisymm_iff, mul_self_le_mul_self_iff]

@[simp] lemma lt_mul_self_iff : ∀ {n : ℕ}, n < n * n ↔ 1 < n
  | 0 => by simp
  | n + 1 => Nat.lt_mul_iff_one_lt_left n.succ_pos

lemma add_sub_one_le_mul (ha : a ≠ 0) (hb : b ≠ 0) : a + b - 1 ≤ a * b := by
  cases a
  · cases ha rfl
  · rw [succ_add, Nat.add_one_sub_one, succ_mul]
    exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ <| Nat.pos_iff_ne_zero.2 hb) _

protected lemma add_le_mul {a : ℕ} (ha : 2 ≤ a) : ∀ {b : ℕ} (_ : 2 ≤ b), a + b ≤ a * b
  | 2, _ => by omega
  | b + 3, _ => by have := Nat.add_le_mul ha (Nat.le_add_left _ b); rw [mul_succ]; omega

/-! ### `div` -/

lemma le_div_two_iff_mul_two_le {n m : ℕ} : m ≤ n / 2 ↔ (m : ℤ) * 2 ≤ n := by
  rw [Nat.le_div_iff_mul_le Nat.zero_lt_two, ← Int.ofNat_le, Int.ofNat_mul]; rfl

attribute [simp] Nat.div_self

lemma div_le_iff_le_mul_add_pred (hb : 0 < b) : a / b ≤ c ↔ a ≤ b * c + (b - 1) := by
  rw [← Nat.lt_succ_iff, div_lt_iff_lt_mul hb, succ_mul, Nat.mul_comm]
  cases hb <;> exact Nat.lt_succ_iff

/-- A version of `Nat.div_lt_self` using successors, rather than additional hypotheses. -/
lemma div_lt_self' (a b : ℕ) : (a + 1) / (b + 2) < a + 1 :=
  Nat.div_lt_self (Nat.succ_pos _) (Nat.succ_lt_succ (Nat.succ_pos _))

@[deprecated le_div_iff_mul_le (since := "2024-11-06")]
lemma le_div_iff_mul_le' (hb : 0 < b) : a ≤ c / b ↔ a * b ≤ c := le_div_iff_mul_le hb

@[deprecated div_lt_iff_lt_mul (since := "2024-11-06")]
lemma div_lt_iff_lt_mul' (hb : 0 < b) : a / b < c ↔ a < c * b := div_lt_iff_lt_mul hb

lemma one_le_div_iff (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by rw [le_div_iff_mul_le hb, Nat.one_mul]

lemma div_lt_one_iff (hb : 0 < b) : a / b < 1 ↔ a < b := by
  simp only [← Nat.not_le, one_le_div_iff hb]

@[gcongr]
protected lemma div_le_div_right (h : a ≤ b) : a / c ≤ b / c :=
  (c.eq_zero_or_pos.elim fun hc ↦ by simp [hc]) fun hc ↦
    (le_div_iff_mul_le hc).2 <| Nat.le_trans (Nat.div_mul_le_self _ _) h

lemma lt_of_div_lt_div (h : a / c < b / c) : a < b :=
  Nat.lt_of_not_le fun hab ↦ Nat.not_le_of_lt h <| Nat.div_le_div_right hab

@[simp] protected lemma div_eq_zero_iff : a / b = 0 ↔ b = 0 ∨ a < b where
  mp h := by
    rw [← mod_add_div a b, h, Nat.mul_zero, Nat.add_zero, or_iff_not_imp_left]
    exact mod_lt _ ∘ Nat.pos_iff_ne_zero.2
  mpr := by
    obtain rfl | hb := eq_or_ne b 0
    · simp
    simp only [hb, false_or]
    rw [← Nat.mul_right_inj hb, ← Nat.add_left_cancel_iff, mod_add_div]
    simp +contextual [mod_eq_of_lt]

protected lemma div_ne_zero_iff : a / b ≠ 0 ↔ b ≠ 0 ∧ b ≤ a := by simp

@[simp] protected lemma div_pos_iff : 0 < a / b ↔ 0 < b ∧ b ≤ a := by
  simp [Nat.pos_iff_ne_zero]

protected lemma div_pos (hba : b ≤ a) (hb : 0 < b) : 0 < a / b := Nat.div_pos_iff.2 ⟨hb, hba⟩

lemma lt_mul_of_div_lt (h : a / c < b) (hc : 0 < c) : a < b * c :=
  Nat.lt_of_not_ge <| Nat.not_le_of_gt h ∘ (Nat.le_div_iff_mul_le hc).2

lemma mul_div_le_mul_div_assoc (a b c : ℕ) : a * (b / c) ≤ a * b / c :=
  if hc0 : c = 0 then by simp [hc0] else
    (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hc0)).2
      (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _))

protected lemma eq_mul_of_div_eq_left (H1 : b ∣ a) (H2 : a / b = c) : a = c * b := by
  rw [Nat.mul_comm, Nat.eq_mul_of_div_eq_right H1 H2]

protected lemma mul_div_cancel_left' (Hd : a ∣ b) : a * (b / a) = b := by
  rw [Nat.mul_comm, Nat.div_mul_cancel Hd]

lemma lt_div_mul_add (hb : 0 < b) : a < a / b * b + b := by
  rw [← Nat.succ_mul, ← Nat.div_lt_iff_lt_mul hb]; exact Nat.lt_succ_self _

@[simp]
protected lemma div_left_inj (hda : d ∣ a) (hdb : d ∣ b) : a / d = b / d ↔ a = b := by
  refine ⟨fun h ↦ ?_, congrArg fun b ↦ b / d⟩
  rw [← Nat.mul_div_cancel' hda, ← Nat.mul_div_cancel' hdb, h]

lemma div_mul_div_comm : b ∣ a → d ∣ c → (a / b) * (c / d) = (a * c) / (b * d) := by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩
  obtain rfl | hb := b.eq_zero_or_pos
  · simp
  obtain rfl | hd := d.eq_zero_or_pos
  · simp
  rw [Nat.mul_div_cancel_left _ hb, Nat.mul_div_cancel_left _ hd, Nat.mul_assoc b,
    Nat.mul_left_comm x, ← Nat.mul_assoc b, Nat.mul_div_cancel_left _ (Nat.mul_pos hb hd)]

protected lemma mul_div_mul_comm (hba : b ∣ a) (hdc : d ∣ c) : a * c / (b * d) = a / b * (c / d) :=
  (div_mul_div_comm hba hdc).symm

lemma eq_zero_of_le_div (hn : 2 ≤ n) (h : m ≤ m / n) : m = 0 :=
  eq_zero_of_mul_le hn <| by
    rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le (Nat.lt_of_lt_of_le (by decide) hn)).1 h

lemma div_mul_div_le_div (a b c : ℕ) : a / c * b / a ≤ b / c := by
  obtain rfl | ha := Nat.eq_zero_or_pos a
  · simp
  · calc
      a / c * b / a ≤ b * a / c / a :=
        Nat.div_le_div_right (by rw [Nat.mul_comm]; exact mul_div_le_mul_div_assoc _ _ _)
      _ = b / c := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm b, Nat.mul_comm c,
          Nat.mul_div_mul_left _ _ ha]

lemma eq_zero_of_le_half (h : n ≤ n / 2) : n = 0 := eq_zero_of_le_div (Nat.le_refl _) h

lemma le_half_of_half_lt_sub (h : a / 2 < a - b) : b ≤ a / 2 := by
  omega

lemma half_le_of_sub_le_half (h : a - b ≤ a / 2) : a / 2 ≤ b := by
  omega

protected lemma div_le_of_le_mul' (h : m ≤ k * n) : m / k ≤ n := by
  obtain rfl | hk := k.eq_zero_or_pos
  · simp
  · refine Nat.le_of_mul_le_mul_left ?_ hk
    calc
      k * (m / k) ≤ m % k + k * (m / k) := Nat.le_add_left _ _
      _ = m := mod_add_div _ _
      _ ≤ k * n := h

protected lemma div_le_div_of_mul_le_mul (hd : d ≠ 0) (hdc : d ∣ c) (h : a * d ≤ c * b) :
    a / b ≤ c / d :=
  Nat.div_le_of_le_mul' <| by
    rwa [← Nat.mul_div_assoc _ hdc, Nat.le_div_iff_mul_le (Nat.pos_iff_ne_zero.2 hd), b.mul_comm]

protected lemma div_le_self' (m n : ℕ) : m / n ≤ m := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  · refine Nat.div_le_of_le_mul' ?_
    calc
      m = 1 * m := by rw [Nat.one_mul]
      _ ≤ n * m := Nat.mul_le_mul_right _ hn

lemma two_mul_odd_div_two (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 := by
  conv => rhs; rw [← Nat.mod_add_div n 2, hn, Nat.add_sub_cancel_left]

@[gcongr]
lemma div_le_div_left (hcb : c ≤ b) (hc : 0 < c) : a / b ≤ a / c :=
  (Nat.le_div_iff_mul_le hc).2 <| Nat.le_trans (Nat.mul_le_mul_left _ hcb) (div_mul_le_self _ _)

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

lemma div_eq_sub_mod_div : m / n = (m - m % n) / n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · rw [Nat.div_zero, Nat.div_zero]
  · have : m - m % n = n * (m / n) := by
      rw [Nat.sub_eq_iff_eq_add (Nat.mod_le _ _), Nat.add_comm, mod_add_div]
    rw [this, mul_div_right _ hn]

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

protected lemma pow_lt_pow_left (h : a < b) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < b ^ n
  | 1, _ => by simpa
  | n + 2, _ => Nat.mul_lt_mul_of_lt_of_le (Nat.pow_lt_pow_left h n.succ_ne_zero) (Nat.le_of_lt h)
    (zero_lt_of_lt h)

protected lemma pow_lt_pow_right (ha : 1 < a) (h : m < n) : a ^ m < a ^ n :=
  (Nat.pow_lt_pow_iff_right ha).2 h

protected lemma pow_le_pow_iff_left {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ b ^ n ↔ a ≤ b where
  mp := by simpa only [← Nat.not_le, Decidable.not_imp_not] using (Nat.pow_lt_pow_left · hn)
  mpr h := Nat.pow_le_pow_left h _

protected lemma pow_lt_pow_iff_left (hn : n ≠ 0) : a ^ n < b ^ n ↔ a < b := by
  simp only [← Nat.not_le, Nat.pow_le_pow_iff_left hn]

lemma pow_left_injective (hn : n ≠ 0) : Injective (fun a : ℕ ↦ a ^ n) := by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_left hn]

protected lemma pow_right_injective (ha : 2 ≤ a) : Injective (a ^ ·) := by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_right ha]

-- We want to use this lemma earlier than the lemma simp can prove it with
@[simp, nolint simpNF] protected lemma pow_eq_zero {a : ℕ} : ∀ {n : ℕ}, a ^ n = 0 ↔ a = 0 ∧ n ≠ 0
  | 0 => by simp
  | n + 1 => by rw [Nat.pow_succ, mul_eq_zero, Nat.pow_eq_zero]; omega

/-- For `a > 1`, `a ^ b = a` iff `b = 1`. -/
lemma pow_eq_self_iff {a b : ℕ} (ha : 1 < a) : a ^ b = a ↔ b = 1 :=
  (Nat.pow_right_injective ha).eq_iff' a.pow_one

lemma le_self_pow (hn : n ≠ 0) : ∀ a : ℕ, a ≤ a ^ n
  | 0 => zero_le _
  | a + 1 => by simpa using Nat.pow_le_pow_right a.succ_pos (Nat.one_le_iff_ne_zero.2 hn)

lemma one_le_pow (n m : ℕ) (h : 0 < m) : 1 ≤ m ^ n := by simpa using Nat.pow_le_pow_of_le_left h n

lemma one_le_pow' (n m : ℕ) : 1 ≤ (m + 1) ^ n := one_le_pow n (m + 1) (succ_pos m)

lemma one_lt_pow (hn : n ≠ 0) (ha : 1 < a) : 1 < a ^ n := by simpa using Nat.pow_lt_pow_left ha hn

lemma two_pow_succ (n : ℕ) : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by simp [Nat.pow_succ, Nat.mul_two]

lemma one_lt_pow' (n m : ℕ) : 1 < (m + 2) ^ (n + 1) :=
  one_lt_pow n.succ_ne_zero (Nat.lt_of_sub_eq_succ rfl)

@[simp] lemma one_lt_pow_iff {n : ℕ} (hn : n ≠ 0) : ∀ {a}, 1 < a ^ n ↔ 1 < a
 | 0 => by simp [Nat.zero_pow (Nat.pos_of_ne_zero hn)]
 | 1 => by simp
 | a + 2 => by simp [one_lt_pow hn]

lemma one_lt_two_pow' (n : ℕ) : 1 < 2 ^ (n + 1) := one_lt_pow n.succ_ne_zero (by decide)

lemma mul_lt_mul_pow_succ (ha : 0 < a) (hb : 1 < b) : n * b < a * b ^ (n + 1) := by
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_lt_mul_right (Nat.lt_trans Nat.zero_lt_one hb)]
  exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ ha)
    ((Nat.mul_lt_mul_left ha).2 <| Nat.lt_pow_self hb)

lemma sq_sub_sq (a b : ℕ) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  simpa [Nat.pow_succ] using Nat.mul_self_sub_mul_self_eq a b

alias pow_two_sub_pow_two := sq_sub_sq

protected lemma div_pow (h : a ∣ b) : (b / a) ^ c = b ^ c / a ^ c := by
  obtain rfl | hc := c.eq_zero_or_pos
  · simp
  obtain rfl | ha := a.eq_zero_or_pos
  · simp [Nat.zero_pow hc]
  refine (Nat.div_eq_of_eq_mul_right (pos_pow_of_pos c ha) ?_).symm
  rw [← Nat.mul_pow, Nat.mul_div_cancel_left' h]

protected lemma pow_pos_iff : 0 < a ^ n ↔ 0 < a ∨ n = 0 := by
  simp [Nat.pos_iff_ne_zero, imp_iff_not_or]

lemma pow_self_pos : 0 < n ^ n := by simp [Nat.pow_pos_iff, n.eq_zero_or_pos.symm]

lemma pow_self_mul_pow_self_le : m ^ m * n ^ n ≤ (m + n) ^ (m + n) := by
  rw [Nat.pow_add]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (le_add_right ..) _)
    (Nat.pow_le_pow_left (le_add_left ..) _)

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

-- Porting note: The type ascriptions of these two lemmas need to be changed,
-- as mathport wrote a lambda that wasn't there in mathlib3, that prevents `simp` applying them.

@[simp]
lemma rec_zero {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) : Nat.rec h0 h 0 = h0 := rfl

lemma rec_add_one {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) (n : ℕ) :
    Nat.rec h0 h (n + 1) = h n (Nat.rec h0 h n) := rfl

@[simp] lemma rec_one {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) :
    Nat.rec (motive := C) h0 h 1 = h 0 h0 := rfl

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k ≥ n`,
there is a map from `C n` to each `C m`, `n ≤ m`.

This is a version of `Nat.le.rec` that works for `Sort u`.
Similarly to `Nat.le.rec`, it can be used as
```
induction hle using Nat.leRec with
| refl => sorry
| le_succ_of_le hle ih => sorry
```
-/
@[elab_as_elim]
def leRec {n} {motive : (m : ℕ) → n ≤ m → Sort*}
    (refl : motive n le_rfl)
    (le_succ_of_le : ∀ ⦃k⦄ (h : n ≤ k), motive k h → motive (k + 1) (le_succ_of_le h)) :
    ∀ {m} (h : n ≤ m), motive m h
  | 0, H => Nat.eq_zero_of_le_zero H ▸ refl
  | m + 1, H =>
    (le_succ_iff.1 H).by_cases
      (fun h : n ≤ m ↦ le_succ_of_le h <| leRec refl le_succ_of_le h)
      (fun h : n = m + 1 ↦ h ▸ refl)

-- This verifies the signatures of the recursor matches the builtin one, as promised in the
-- above.
theorem leRec_eq_leRec : @Nat.leRec.{0} = @Nat.le.rec := rfl

@[simp]
lemma leRec_self {n} {motive : (m : ℕ) → n ≤ m → Sort*}
    (refl : motive n le_rfl)
    (le_succ_of_le : ∀ ⦃k⦄ (h : n ≤ k), motive k h → motive (k + 1) (le_succ_of_le h)) :
    (leRec (motive := motive) refl le_succ_of_le le_rfl : motive n le_rfl) = refl := by
  cases n <;> simp [leRec, Or.by_cases, dif_neg]

@[simp]
lemma leRec_succ {n} {motive : (m : ℕ) → n ≤ m → Sort*}
    (refl : motive n le_rfl)
    (le_succ_of_le : ∀ ⦃k⦄ (h : n ≤ k), motive k h → motive (k + 1) (le_succ_of_le h))
    (h1 : n ≤ m) {h2 : n ≤ m + 1} :
    (leRec (motive := motive) refl le_succ_of_le h2) =
      le_succ_of_le h1 (leRec (motive := motive) refl le_succ_of_le h1) := by
  conv =>
    lhs
    rw [leRec, Or.by_cases, dif_pos h1]

lemma leRec_succ' {n} {motive : (m : ℕ) → n ≤ m → Sort*} (refl le_succ_of_le) :
    (leRec (motive := motive) refl le_succ_of_le (le_succ _)) = le_succ_of_le _ refl := by
  rw [leRec_succ, leRec_self]

lemma leRec_trans {n m k} {motive : (m : ℕ) → n ≤ m → Sort*} (refl le_succ_of_le)
    (hnm : n ≤ m) (hmk : m ≤ k) :
    leRec (motive := motive) refl le_succ_of_le (Nat.le_trans hnm hmk) =
      leRec
        (leRec refl (fun _ h => le_succ_of_le h) hnm)
        (fun _ h => le_succ_of_le <| Nat.le_trans hnm h) hmk := by
  induction hmk with
  | refl => rw [leRec_self]
  | step hmk ih => rw [leRec_succ _ _ (Nat.le_trans hnm hmk), ih, leRec_succ]

lemma leRec_succ_left {motive : (m : ℕ) → n ≤ m → Sort*}
    (refl le_succ_of_le) {m} (h1 : n ≤ m) (h2 : n + 1 ≤ m) :
    -- the `@` is needed for this to elaborate, even though we only provide explicit arguments!
    @leRec _ _ (le_succ_of_le le_rfl refl) (fun _ h ih => le_succ_of_le (le_of_succ_le h) ih) _ h2 =
      leRec (motive := motive) refl le_succ_of_le h1 := by
  rw [leRec_trans _ _ (le_succ n) h2, leRec_succ']

/-- Recursion starting at a non-zero number: given a map `C k → C (k + 1)` for each `k`,
there is a map from `C n` to each `C m`, `n ≤ m`. For a version where the assumption is only made
when `k ≥ n`, see `Nat.leRec`. -/
@[elab_as_elim]
def leRecOn {C : ℕ → Sort*} {n : ℕ} : ∀ {m}, n ≤ m → (∀ {k}, C k → C (k + 1)) → C n → C m :=
  fun h of_succ self => Nat.leRec self (fun _ _ => @of_succ _) h

lemma leRecOn_self {C : ℕ → Sort*} {n} {next : ∀ {k}, C k → C (k + 1)} (x : C n) :
    (leRecOn n.le_refl next x : C n) = x :=
  leRec_self _ _

lemma leRecOn_succ {C : ℕ → Sort*} {n m} (h1 : n ≤ m) {h2 : n ≤ m + 1} {next} (x : C n) :
    (leRecOn h2 next x : C (m + 1)) = next (leRecOn h1 next x : C m) :=
  leRec_succ _ _ _

lemma leRecOn_succ' {C : ℕ → Sort*} {n} {h : n ≤ n + 1} {next : ∀ {k}, C k → C (k + 1)} (x : C n) :
    (leRecOn h next x : C (n + 1)) = next x :=
  leRec_succ' _ _

lemma leRecOn_trans {C : ℕ → Sort*} {n m k} (hnm : n ≤ m) (hmk : m ≤ k) {next} (x : C n) :
    (leRecOn (Nat.le_trans hnm hmk) (@next) x : C k) =
      leRecOn hmk (@next) (leRecOn hnm (@next) x) :=
  leRec_trans _ _ _ _

lemma leRecOn_succ_left {C : ℕ → Sort*} {n m}
    {next : ∀ {k}, C k → C (k + 1)} (x : C n) (h1 : n ≤ m) (h2 : n + 1 ≤ m) :
    (leRecOn h2 next (next x) : C m) = (leRecOn h1 next x : C m) :=
  leRec_succ_left (motive := fun n _ => C n) _ (fun _ _ => @next _) _ _

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

/-- Recursion principle based on `<`. -/
@[elab_as_elim]
protected def strongRec' {p : ℕ → Sort*} (H : ∀ n, (∀ m, m < n → p m) → p n) : ∀ n : ℕ, p n
  | n => H n fun m _ ↦ Nat.strongRec' H m

/-- Recursion principle based on `<` applied to some natural number. -/
@[elab_as_elim]
def strongRecOn' {P : ℕ → Sort*} (n : ℕ) (h : ∀ n, (∀ m, m < n → P m) → P n) : P n :=
  Nat.strongRec' h n

lemma strongRecOn'_beta {P : ℕ → Sort*} {h} :
    (strongRecOn' n h : P n) = h n fun m _ ↦ (strongRecOn' m h : P m) := by
  simp only [strongRecOn']; rw [Nat.strongRec']

/-- Induction principle starting at a non-zero number.
To use in an induction proof, the syntax is `induction n, hn using Nat.le_induction` (or the same
for `induction'`).

This is an alias of `Nat.leRec`, specialized to `Prop`. -/
@[elab_as_elim]
lemma le_induction {m : ℕ} {P : ∀ n, m ≤ n → Prop} (base : P m m.le_refl)
    (succ : ∀ n hmn, P n hmn → P (n + 1) (le_succ_of_le hmn)) : ∀ n hmn, P n hmn :=
  @Nat.leRec (motive := P) _ base succ

/-- Induction principle deriving the next case from the two previous ones. -/
def twoStepInduction {P : ℕ → Sort*} (zero : P 0) (one : P 1)
    (more : ∀ n, P n → P (n + 1) → P (n + 2)) : ∀ a, P a
  | 0 => zero
  | 1 => one
  | _ + 2 => more _ (twoStepInduction zero one more _) (twoStepInduction zero one more _)

@[elab_as_elim]
protected theorem strong_induction_on {p : ℕ → Prop} (n : ℕ)
    (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
  Nat.strongRecOn n h

protected theorem case_strong_induction_on {p : ℕ → Prop} (a : ℕ) (hz : p 0)
    (hi : ∀ n, (∀ m, m ≤ n → p m) → p (n + 1)) : p a :=
  Nat.caseStrongRecOn a hz hi

/-- Decreasing induction: if `P (k+1)` implies `P k` for all `k < n`, then `P n` implies `P m` for
all `m ≤ n`.
Also works for functions to `Sort*`.

For a version also assuming `m ≤ k`, see `Nat.decreasingInduction'`. -/
@[elab_as_elim]
def decreasingInduction {n} {motive : (m : ℕ) → m ≤ n → Sort*}
    (of_succ : ∀ k (h : k < n), motive (k + 1) h → motive k (le_of_succ_le h))
    (self : motive n le_rfl) {m} (mn : m ≤ n) : motive m mn := by
  induction mn using leRec with
  | refl => exact self
  | @le_succ_of_le k _ ih =>
    apply ih (fun i hi => of_succ i (le_succ_of_le hi)) (of_succ k (lt_succ_self _) self)

@[simp]
lemma decreasingInduction_self {n} {motive : (m : ℕ) → m ≤ n → Sort*} (of_succ self) :
    (decreasingInduction (motive := motive) of_succ self le_rfl) = self := by
  dsimp only [decreasingInduction]
  rw [leRec_self]

lemma decreasingInduction_succ {n} {motive : (m : ℕ) → m ≤ n + 1 → Sort*} (of_succ self)
    (mn : m ≤ n) (msn : m ≤ n + 1) :
    (decreasingInduction (motive := motive) of_succ self msn : motive m msn) =
      decreasingInduction (motive := fun m h => motive m (le_succ_of_le h))
        (fun _ _ => of_succ _ _) (of_succ _ _ self) mn := by
  dsimp only [decreasingInduction]; rw [leRec_succ]

@[simp]
lemma decreasingInduction_succ' {n} {motive : (m : ℕ) → m ≤ n + 1 → Sort*} (of_succ self) :
    decreasingInduction (motive := motive) of_succ self n.le_succ = of_succ _ _ self := by
  dsimp only [decreasingInduction]; rw [leRec_succ']

lemma decreasingInduction_trans {motive : (m : ℕ) → m ≤ k → Sort*} (hmn : m ≤ n) (hnk : n ≤ k)
    (of_succ self) :
    (decreasingInduction (motive := motive) of_succ self (Nat.le_trans hmn hnk) : motive m _) =
    decreasingInduction (fun _ _ => of_succ _ _) (decreasingInduction of_succ self hnk) hmn := by
  induction hnk with
  | refl => rw [decreasingInduction_self]
  | step hnk ih =>
      rw [decreasingInduction_succ _ _ (Nat.le_trans hmn hnk), ih, decreasingInduction_succ]

lemma decreasingInduction_succ_left  {motive : (m : ℕ) → m ≤ n → Sort*} (of_succ self)
    (smn : m + 1 ≤ n) (mn : m ≤ n) :
    decreasingInduction (motive := motive) of_succ self mn =
      of_succ m smn (decreasingInduction of_succ self smn) := by
  rw [Subsingleton.elim mn (Nat.le_trans (le_succ m) smn), decreasingInduction_trans,
    decreasingInduction_succ']

/-- Given `P : ℕ → ℕ → Sort*`, if for all `m n : ℕ` we can extend `P` from the rectangle
strictly below `(m, n)` to `P m n`, then we have `P n m` for all `n m : ℕ`.
Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
@[elab_as_elim]
def strongSubRecursion {P : ℕ → ℕ → Sort*} (H : ∀ m n, (∀ x y, x < m → y < n → P x y) → P m n) :
    ∀ n m : ℕ, P n m
  | n, m => H n m fun x y _ _ ↦ strongSubRecursion H x y

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
  | Nat.succ _, Nat.succ _ => H _ _ (pincerRecursion Ha0 H0b H _ _) (pincerRecursion Ha0 H0b H _ _)

/-- Decreasing induction: if `P (k+1)` implies `P k` for all `m ≤ k < n`, then `P n` implies `P m`.
Also works for functions to `Sort*`.

Weakens the assumptions of `Nat.decreasingInduction`. -/
@[elab_as_elim]
def decreasingInduction' {P : ℕ → Sort*} (h : ∀ k < n, m ≤ k → P (k + 1) → P k)
    (mn : m ≤ n) (hP : P n) : P m := by
  induction mn using decreasingInduction with
  | self => exact hP
  | of_succ k hk ih =>
    exact h _ (lt_of_succ_le hk) le_rfl (ih fun k' hk' h'' => h k' hk' <| le_of_succ_le h'')

/-- Given a predicate on two naturals `P : ℕ → ℕ → Prop`, `P a b` is true for all `a < b` if
`P (a + 1) (a + 1)` is true for all `a`, `P 0 (b + 1)` is true for all `b` and for all
`a < b`, `P (a + 1) b` is true and `P a (b + 1)` is true implies `P (a + 1) (b + 1)` is true. -/
@[elab_as_elim]
theorem diag_induction (P : ℕ → ℕ → Prop) (ha : ∀ a, P (a + 1) (a + 1)) (hb : ∀ b, P 0 (b + 1))
    (hd : ∀ a b, a < b → P (a + 1) b → P a (b + 1) → P (a + 1) (b + 1)) : ∀ a b, a < b → P a b
  | 0, _ + 1, _ => hb _
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

/-- A subset of `ℕ` containing `k : ℕ` and closed under `Nat.succ` contains every `n ≥ k`. -/
lemma set_induction_bounded {S : Set ℕ} (hk : k ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S)
    (hnk : k ≤ n) : n ∈ S :=
  @leRecOn (fun n => n ∈ S) k n hnk @h_ind hk

/-- A subset of `ℕ` containing zero and closed under `Nat.succ` contains all of `ℕ`. -/
lemma set_induction {S : Set ℕ} (hb : 0 ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S) (n : ℕ) :
    n ∈ S :=
  set_induction_bounded hb h_ind (zero_le n)

/-! ### `mod`, `dvd` -/

attribute [simp] Nat.dvd_zero

@[simp] lemma mod_two_not_eq_one : ¬n % 2 = 1 ↔ n % 2 = 0 := by
  cases mod_two_eq_zero_or_one n <;> simp [*]

@[simp] lemma mod_two_not_eq_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by
  cases mod_two_eq_zero_or_one n <;> simp [*]

lemma mod_two_ne_one : n % 2 ≠ 1 ↔ n % 2 = 0 := mod_two_not_eq_one
lemma mod_two_ne_zero : n % 2 ≠ 0 ↔ n % 2 = 1 := mod_two_not_eq_zero

/-- Variant of `Nat.lt_div_iff_mul_lt` that assumes `d ∣ n`. -/
protected lemma lt_div_iff_mul_lt' (hdn : d ∣ n) (a : ℕ) : a < n / d ↔ d * a < n := by
  obtain rfl | hd := d.eq_zero_or_pos
  · simp [Nat.zero_dvd.1 hdn]
  · rw [← Nat.mul_lt_mul_left hd, ← Nat.eq_mul_of_div_eq_right hdn rfl]

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

lemma le_iff_ne_zero_of_dvd (ha : a ≠ 0) (hab : a ∣ b) : a ≤ b ↔ b ≠ 0 where
  mp := by rw [← Nat.pos_iff_ne_zero] at ha ⊢; exact Nat.lt_of_lt_of_le ha
  mpr hb := Nat.le_of_dvd (Nat.pos_iff_ne_zero.2 hb) hab

lemma div_ne_zero_iff_of_dvd (hba : b ∣ a) : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [Nat.div_ne_zero_iff, Nat.le_iff_ne_zero_of_dvd, *]

@[simp] lemma mul_mod_mod (a b c : ℕ) : (a * (b % c)) % c = a * b % c := by
  rw [mul_mod, mod_mod, ← mul_mod]

lemma pow_mod (a b n : ℕ) : a ^ b % n = (a % n) ^ b % n := by
  induction b with
  | zero => rfl
  | succ b ih => simp [Nat.pow_succ, Nat.mul_mod, ih]

lemma not_pos_pow_dvd : ∀ {a n : ℕ} (_ : 1 < a) (_ : 1 < n), ¬ a ^ n ∣ a
  | succ a, succ n, hp, hk, h =>
    have : succ a * succ a ^ n ∣ succ a * 1 := by simpa [pow_succ'] using h
    have : succ a ^ n ∣ 1 := Nat.dvd_of_mul_dvd_mul_left (succ_pos _) this
    have he : succ a ^ n = 1 := eq_one_of_dvd_one this
    have : n < succ a ^ n := n.lt_pow_self hp
    have : n < 1 := by rwa [he] at this
    have : n = 0 := Nat.eq_zero_of_le_zero <| le_of_lt_succ this
    have : 1 < 1 := by rwa [this] at hk
    absurd this (by decide)

lemma lt_of_pow_dvd_right (hb : b ≠ 0) (ha : 2 ≤ a) (h : a ^ n ∣ b) : n < b := by
  rw [← Nat.pow_lt_pow_iff_right (succ_le_iff.1 ha)]
  exact Nat.lt_of_le_of_lt (le_of_dvd (Nat.pos_iff_ne_zero.2 hb) h) (Nat.lt_pow_self ha)

lemma div_dvd_of_dvd (h : n ∣ m) : m / n ∣ m := ⟨n, (Nat.div_mul_cancel h).symm⟩

protected lemma div_div_self (h : n ∣ m) (hm : m ≠ 0) : m / (m / n) = n := by
  rcases h with ⟨_, rfl⟩
  rw [Nat.mul_ne_zero_iff] at hm
  rw [mul_div_right _ (Nat.pos_of_ne_zero hm.1), mul_div_left _ (Nat.pos_of_ne_zero hm.2)]

lemma not_dvd_of_pos_of_lt (h1 : 0 < n) (h2 : n < m) : ¬m ∣ n := by
  rintro ⟨k, rfl⟩
  rcases Nat.eq_zero_or_pos k with (rfl | hk)
  · exact Nat.lt_irrefl 0 h1
  · exact Nat.not_lt.2 (Nat.le_mul_of_pos_right _ hk) h2

lemma eq_of_dvd_of_lt_two_mul (ha : a ≠ 0) (hdvd : b ∣ a) (hlt : a < 2 * b) : a = b := by
  obtain ⟨_ | _ | c, rfl⟩ := hdvd
  · simp at ha
  · exact Nat.mul_one _
  · rw [Nat.mul_comm] at hlt
    cases Nat.not_le_of_lt hlt (Nat.mul_le_mul_right _ (by omega))

lemma mod_eq_iff_lt (hn : n ≠ 0) : m % n = m ↔ m < n :=
  ⟨fun h ↦ by rw [← h]; exact mod_lt _ <| Nat.pos_iff_ne_zero.2 hn, mod_eq_of_lt⟩

@[simp]
lemma mod_succ_eq_iff_lt : m % n.succ = m ↔ m < n.succ :=
  mod_eq_iff_lt (succ_ne_zero _)

@[simp] lemma mod_succ (n : ℕ) : n % n.succ = n := mod_eq_of_lt n.lt_succ_self

-- Porting note `Nat.div_add_mod` is now in core.

lemma mod_add_div' (a b : ℕ) : a % b + a / b * b = a := by rw [Nat.mul_comm]; exact mod_add_div _ _

lemma div_add_mod' (a b : ℕ) : a / b * b + a % b = a := by rw [Nat.mul_comm]; exact div_add_mod _ _

/-- See also `Nat.divModEquiv` for a similar statement as an `Equiv`. -/
protected lemma div_mod_unique (h : 0 < b) :
    a / b = d ∧ a % b = c ↔ c + b * d = a ∧ c < b :=
  ⟨fun ⟨e₁, e₂⟩ ↦ e₁ ▸ e₂ ▸ ⟨mod_add_div _ _, mod_lt _ h⟩, fun ⟨h₁, h₂⟩ ↦ h₁ ▸ by
    rw [add_mul_div_left _ _ h, add_mul_mod_self_left]; simp [div_eq_of_lt, mod_eq_of_lt, h₂]⟩

/-- If `m` and `n` are equal mod `k`, `m - n` is zero mod `k`. -/
lemma sub_mod_eq_zero_of_mod_eq (h : m % k = n % k) : (m - n) % k = 0 := by
  rw [← Nat.mod_add_div m k, ← Nat.mod_add_div n k, ← h, ← Nat.sub_sub,
    Nat.add_sub_cancel_left, ← k.mul_sub, Nat.mul_mod_right]

@[simp] lemma one_mod (n : ℕ) : 1 % (n + 2) = 1 :=
  Nat.mod_eq_of_lt (Nat.add_lt_add_right n.succ_pos 1)

lemma one_mod_eq_one : ∀ {n : ℕ}, 1 % n = 1 ↔ n ≠ 1
  | 0 | 1 | n + 2 => by simp

@[deprecated "No deprecation message was provided." (since := "2024-08-28")]
lemma one_mod_of_ne_one  : ∀ {n : ℕ}, n ≠ 1 → 1 % n = 1 := one_mod_eq_one.mpr

lemma dvd_sub_mod (k : ℕ) : n ∣ k - k % n :=
  ⟨k / n, Nat.sub_eq_of_eq_add (Nat.div_add_mod k n).symm⟩

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

/-- `m` is not divisible by `n` if it is between `n * k` and `n * (k + 1)` for some `k`. -/
theorem not_dvd_of_between_consec_multiples (h1 : n * k < m) (h2 : m < n * (k + 1)) : ¬n ∣ m := by
  rintro ⟨d, rfl⟩
  have := Nat.lt_of_mul_lt_mul_left h1
  have := Nat.lt_of_mul_lt_mul_left h2
  omega

-- TODO: Replace `Nat.dvd_add_iff_left`
protected lemma dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b := (Nat.dvd_add_iff_left h).symm

protected lemma dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c := (Nat.dvd_add_iff_right h).symm

/-- special case of `mul_dvd_mul_iff_left` for `ℕ`.
Duplicated here to keep simple imports for this file. -/
protected lemma mul_dvd_mul_iff_left (ha : 0 < a) : a * b ∣ a * c ↔ b ∣ c :=
  exists_congr fun d ↦ by rw [Nat.mul_assoc, Nat.mul_right_inj <| ne_of_gt ha]

/-- special case of `mul_dvd_mul_iff_right` for `ℕ`.
Duplicated here to keep simple imports for this file. -/
protected lemma mul_dvd_mul_iff_right (hc : 0 < c) : a * c ∣ b * c ↔ a ∣ b :=
  exists_congr fun d ↦ by rw [Nat.mul_right_comm, Nat.mul_left_inj <| ne_of_gt hc]

-- Moved to Batteries

lemma add_mod_eq_add_mod_right (c : ℕ) (H : a % d = b % d) : (a + c) % d = (b + c) % d := by
  rw [← mod_add_mod, ← mod_add_mod b, H]

lemma add_mod_eq_add_mod_left (c : ℕ) (H : a % d = b % d) : (c + a) % d = (c + b) % d := by
  rw [Nat.add_comm, add_mod_eq_add_mod_right _ H, Nat.add_comm]

-- Moved to Batteries

lemma mul_dvd_of_dvd_div (hcb : c ∣ b) (h : a ∣ b / c) : c * a ∣ b :=
  have ⟨d, hd⟩ := h
  ⟨d, by simpa [Nat.mul_comm, Nat.mul_left_comm] using Nat.eq_mul_of_div_eq_left hcb hd⟩

lemma eq_of_dvd_of_div_eq_one (hab : a ∣ b) (h : b / a = 1) : a = b := by
  rw [← Nat.div_mul_cancel hab, h, Nat.one_mul]

lemma eq_zero_of_dvd_of_div_eq_zero (hab : a ∣ b) (h : b / a = 0) : b = 0 := by
  rw [← Nat.div_mul_cancel hab, h, Nat.zero_mul]

@[gcongr]
protected theorem div_le_div {a b c d : ℕ} (h1 : a ≤ b) (h2 : d ≤ c) (h3 : d ≠ 0) : a / c ≤ b / d :=
  calc a / c ≤ b / c := Nat.div_le_div_right h1
    _ ≤ b / d := Nat.div_le_div_left h2 (Nat.pos_of_ne_zero h3)

-- Moved to Batteries

lemma lt_mul_div_succ (a : ℕ) (hb : 0 < b) : a < b * (a / b + 1) := by
  rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul hb]
  exact lt_succ_self _

-- TODO: Batteries claimed this name but flipped the order of multiplication
lemma mul_add_mod' (a b c : ℕ) : (a * b + c) % b = c % b := by rw [Nat.mul_comm, Nat.mul_add_mod]

lemma mul_add_mod_of_lt (h : c < b) : (a * b + c) % b = c := by
  rw [Nat.mul_add_mod', Nat.mod_eq_of_lt h]

@[simp]
protected theorem not_two_dvd_bit1 (n : ℕ) : ¬2 ∣ 2 * n + 1 := by
  omega

/-- A natural number `m` divides the sum `m + n` if and only if `m` divides `n`.-/
@[simp] protected lemma dvd_add_self_left : m ∣ m + n ↔ m ∣ n := Nat.dvd_add_right (Nat.dvd_refl m)

/-- A natural number `m` divides the sum `n + m` if and only if `m` divides `n`.-/
@[simp] protected lemma dvd_add_self_right : m ∣ n + m ↔ m ∣ n := Nat.dvd_add_left (Nat.dvd_refl m)

-- TODO: update `Nat.dvd_sub` in core
lemma dvd_sub' (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n := by
  rcases le_total n m with H | H
  · exact dvd_sub H h₁ h₂
  · rw [Nat.sub_eq_zero_iff_le.mpr H]
    exact Nat.dvd_zero k

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
      simp [dvd_iff, Nat.add_comm 1, Nat.add_assoc]
    · have hba : ¬b ≤ a := not_le_of_gt (lt_trans (lt_succ_self a) (lt_of_not_ge hb_le_a1))
      have hb_dvd_a : ¬b + 1 ∣ a + 2 := fun h =>
        hb_le_a1 (le_of_succ_le_succ (le_of_dvd (succ_pos _) h))
      simp [hba, hb_le_a1, hb_dvd_a]

lemma succ_div_of_dvd (hba : b ∣ a + 1) : (a + 1) / b = a / b + 1 := by rw [succ_div, if_pos hba]

lemma succ_div_of_not_dvd (hba : ¬b ∣ a + 1) : (a + 1) / b = a / b := by
  rw [succ_div, if_neg hba, Nat.add_zero]

lemma dvd_iff_div_mul_eq (n d : ℕ) : d ∣ n ↔ n / d * d = n :=
  ⟨fun h => Nat.div_mul_cancel h, fun h => by rw [← h]; exact Nat.dvd_mul_left _ _⟩

lemma dvd_iff_le_div_mul (n d : ℕ) : d ∣ n ↔ n ≤ n / d * d :=
  ((dvd_iff_div_mul_eq _ _).trans le_antisymm_iff).trans (and_iff_right (div_mul_le_self n d))

lemma dvd_iff_dvd_dvd (n d : ℕ) : d ∣ n ↔ ∀ k : ℕ, k ∣ d → k ∣ n :=
  ⟨fun h _ hkd => Nat.dvd_trans hkd h, fun h => h _ (Nat.dvd_refl _)⟩

lemma dvd_div_of_mul_dvd (h : a * b ∣ c) : b ∣ c / a :=
  if ha : a = 0 then by simp [ha]
  else
    have ha : 0 < a := Nat.pos_of_ne_zero ha
    have h1 : ∃ d, c = a * b * d := h
    let ⟨d, hd⟩ := h1
    have h2 : c / a = b * d := Nat.div_eq_of_eq_mul_right ha (by simpa [Nat.mul_assoc] using hd)
    show ∃ d, c / a = b * d from ⟨d, h2⟩

@[simp] lemma dvd_div_iff_mul_dvd (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b :=
  ⟨fun h => mul_dvd_of_dvd_div hbc h, fun h => dvd_div_of_mul_dvd h⟩

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

/-- If a small natural number is divisible by a larger natural number,
the small number is zero. -/
lemma eq_zero_of_dvd_of_lt (w : a ∣ b) (h : b < a) : b = 0 :=
  Nat.eq_zero_of_dvd_of_div_eq_zero w (by simp [h])

lemma le_of_lt_add_of_dvd (h : a < b + n) : n ∣ a → n ∣ b → a ≤ b := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  rw [← mul_succ] at h
  exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.1 <| Nat.lt_of_mul_lt_mul_left h)

/-- `n` is not divisible by `a` iff it is between `a * k` and `a * (k + 1)` for some `k`. -/
lemma not_dvd_iff_between_consec_multiples (n : ℕ) {a : ℕ} (ha : 0 < a) :
    (∃ k : ℕ, a * k < n ∧ n < a * (k + 1)) ↔ ¬a ∣ n := by
  refine
    ⟨fun ⟨k, hk1, hk2⟩ => not_dvd_of_between_consec_multiples hk1 hk2, fun han =>
      ⟨n / a, ⟨lt_of_le_of_ne (mul_div_le n a) ?_, lt_mul_div_succ _ ha⟩⟩⟩
  exact mt (⟨n / a, Eq.symm ·⟩) han

/-- Two natural numbers are equal if and only if they have the same multiples. -/
lemma dvd_right_iff_eq : (∀ a : ℕ, m ∣ a ↔ n ∣ a) ↔ m = n :=
  ⟨fun h => Nat.dvd_antisymm ((h _).mpr (Nat.dvd_refl _)) ((h _).mp (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩

/-- Two natural numbers are equal if and only if they have the same divisors. -/
lemma dvd_left_iff_eq : (∀ a : ℕ, a ∣ m ↔ a ∣ n) ↔ m = n :=
  ⟨fun h => Nat.dvd_antisymm ((h _).mp (Nat.dvd_refl _)) ((h _).mpr (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩

/-- `dvd` is injective in the left argument -/
lemma dvd_left_injective : Function.Injective ((· ∣ ·) : ℕ → ℕ → Prop) := fun _ _ h =>
  dvd_right_iff_eq.mp fun a => iff_of_eq (congr_fun h a)

lemma div_lt_div_of_lt_of_dvd {a b d : ℕ} (hdb : d ∣ b) (h : a < b) : a / d < b / d := by
  rw [Nat.lt_div_iff_mul_lt' hdb]
  exact lt_of_le_of_lt (mul_div_le a d) h

/-! ### Decidability of predicates -/

instance decidableLoHi (lo hi : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Decidable (∀ x, lo ≤ x → x < hi → P x) :=
  decidable_of_iff (∀ x < hi - lo, P (lo + x)) <| by
    refine ⟨fun al x hl hh ↦ ?_,
      fun al x h ↦ al _ (Nat.le_add_right _ _) (Nat.lt_sub_iff_add_lt'.1 h)⟩
    have := al (x - lo) ((Nat.sub_lt_sub_iff_right hl).2 hh)
    rwa [Nat.add_sub_cancel' hl] at this

instance decidableLoHiLe (lo hi : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Decidable (∀ x, lo ≤ x → x ≤ hi → P x) :=
  decidable_of_iff (∀ x, lo ≤ x → x < hi + 1 → P x) <|
    forall₂_congr fun _ _ ↦ imp_congr Nat.lt_succ_iff Iff.rfl

end Nat
