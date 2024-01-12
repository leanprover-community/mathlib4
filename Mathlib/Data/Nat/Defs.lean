/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Use

#align_import data.nat.basic from "leanprover-community/mathlib"@"bd835ef554f37ef9b804f0903089211f89cb370b"

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

Many theorems that used to live in this file have been moved to `Data.Nat.Order`, so that
this file requires fewer imports. For each section here there is a corresponding section in
that file with additional results. It may be possible to move some of these results here,
by tweaking their proofs.
-/

open Function

namespace Nat
variable {a b c d m n k : ℕ} {p q : ℕ → Prop}

instance nontrivial : Nontrivial ℕ := ⟨⟨0, 1, Nat.zero_ne_one⟩⟩

attribute [simp] Nat.not_lt_zero Nat.succ_ne_zero Nat.succ_ne_self Nat.zero_ne_one Nat.one_ne_zero
  -- Nat.zero_ne_bit1 Nat.bit1_ne_zero Nat.bit0_ne_one Nat.one_ne_bit0 Nat.bit0_ne_bit1
  -- Nat.bit1_ne_bit0

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

@[simp] lemma one_lt_succ_succ (n : ℕ) : 1 < n.succ.succ := succ_lt_succ <| succ_pos n
#align nat.one_lt_succ_succ Nat.one_lt_succ_succ

-- Moved to Std
#align nat.succ_le_succ_iff Nat.succ_le_succ_iff
#align nat.succ_lt_succ_iff Nat.succ_lt_succ_iff
#align nat.le_pred_of_lt Nat.le_pred_of_lt
#align nat.max_succ_succ Nat.succ_max_succ

alias _root_.LT.lt.nat_succ_le := succ_le_of_lt
#align has_lt.lt.nat_succ_le LT.lt.nat_succ_le

lemma not_succ_lt_self : ¬ succ n < n := not_lt_of_ge n.le_succ
#align nat.not_succ_lt_self Nat.not_succ_lt_self

lemma lt_succ_iff : m < succ n ↔ m ≤ n := ⟨le_of_lt_succ, lt_succ_of_le⟩
#align nat.lt_succ_iff Nat.lt_succ_iff

lemma succ_le_iff : succ m ≤ n ↔ m < n := ⟨lt_of_succ_le, succ_le_of_lt⟩
#align nat.succ_le_iff Nat.succ_le_iff

lemma le_succ_iff : m ≤ n.succ ↔ m ≤ n ∨ m = n.succ := by
  refine ⟨fun hmn ↦ (lt_or_eq_of_le hmn).imp_left le_of_lt_succ, ?_⟩
  rintro (hmn | rfl)
  · exact le_succ_of_le hmn
  · rfl

alias ⟨of_le_succ, _⟩ := le_succ_iff
#align nat.of_le_succ Nat.of_le_succ

lemma lt_succ_iff_lt_or_eq : m < n.succ ↔ m < n ∨ m = n := lt_succ_iff.trans Nat.le_iff_lt_or_eq
#align nat.lt_succ_iff_lt_or_eq Nat.lt_succ_iff_lt_or_eq

lemma eq_of_lt_succ_of_not_lt (hmn : m < n + 1) (h : ¬ m < n) : m = n := by omega
#align nat.eq_of_lt_succ_of_not_lt Nat.eq_of_lt_succ_of_not_lt

lemma eq_of_le_of_lt_succ (h₁ : n ≤ m) (h₂ : m < n + 1) : m = n :=
  Nat.le_antisymm (le_of_succ_le_succ h₂) h₁
#align nat.eq_of_le_of_lt_succ Nat.eq_of_le_of_lt_succ

lemma lt_iff_le_pred : ∀ {n}, 0 < n → (m < n ↔ m ≤ n - 1) | _ + 1, _ => lt_succ_iff
#align nat.lt_iff_le_pred Nat.lt_iff_le_pred

lemma le_of_pred_lt : ∀ {m}, pred m < n → m ≤ n
  | 0 => le_of_lt
  | _ + 1 => id
#align nat.le_of_pred_lt Nat.le_of_pred_lt

lemma lt_iff_add_one_le : m < n ↔ m + 1 ≤ n := by rw [succ_le_iff]
#align nat.lt_iff_add_one_le Nat.lt_iff_add_one_le

-- Just a restatement of `Nat.lt_succ_iff` using `+1`.
lemma lt_add_one_iff : m < n + 1 ↔ m ≤ n := lt_succ_iff
#align nat.lt_add_one_iff Nat.lt_add_one_iff

-- A flipped version of `lt_add_one_iff`.
lemma lt_one_add_iff : m < 1 + n ↔ m ≤ n := by simp only [Nat.add_comm, lt_succ_iff]
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
  | n + 2 => by simp
#align nat.one_lt_iff_ne_zero_and_ne_one Nat.one_lt_iff_ne_zero_and_ne_one

lemma le_one_iff_eq_zero_or_eq_one : ∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1 := by simp [le_succ_iff]

-- Moved to Std
#align nat.succ_eq_one_add Nat.succ_eq_one_add
#align nat.one_add Nat.one_add

lemma pred_eq_sub_one (n : ℕ) : pred n = n - 1 := rfl
#align nat.pred_eq_sub_one Nat.pred_eq_sub_one

/-- This ensures that `simp` succeeds on `pred (n + 1) = n`. -/
@[simp]
lemma pred_one_add (n : ℕ) : pred (1 + n) = n := by rw [Nat.add_comm, add_one, Nat.pred_succ]
#align nat.pred_one_add Nat.pred_one_add

lemma pred_eq_self_iff : n.pred = n ↔ n = 0 := by cases n <;> simp [(Nat.succ_ne_self _).symm]
#align nat.pred_eq_self_iff Nat.pred_eq_self_iff

lemma pred_eq_of_eq_succ (H : m = n.succ) : m.pred = n := by simp [H]
#align nat.pred_eq_of_eq_succ Nat.pred_eq_of_eq_succ

@[simp] lemma pred_eq_succ_iff : pred n = succ m ↔ n = m + 2 := by
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
  simp only [lt_succ_iff, Nat.le_iff_lt_or_eq, or_comm, forall_eq_or_imp, and_comm]
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
  | n + 3, _, _, _ => by omega
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

/-! ### `add` -/

-- Sometimes a bare `Nat.add` or similar appears as a consequence of unfolding during pattern
-- matching. These lemmas package them back up as typeclass mediated operations.
@[simp] lemma add_def : Nat.add m n = m + n := rfl
#align nat.add_def Nat.add_def

lemma exists_eq_add_of_le (h : m ≤ n) : ∃ k : ℕ, n = m + k := ⟨n - m, (add_sub_of_le h).symm⟩
#align nat.exists_eq_add_of_le Nat.exists_eq_add_of_le

lemma exists_eq_add_of_le' (h : m ≤ n) : ∃ k : ℕ, n = k + m := ⟨n - m, (Nat.sub_add_cancel h).symm⟩
#align nat.exists_eq_add_of_le' Nat.exists_eq_add_of_le'

lemma exists_eq_add_of_lt (h : m < n) : ∃ k : ℕ, n = m + k + 1 :=
  ⟨n - (m + 1), by rw [Nat.add_right_comm, add_sub_of_le h]⟩
#align nat.exists_eq_add_of_lt Nat.exists_eq_add_of_lt

/-! ### `mul` -/

@[simp] lemma mul_def : Nat.mul m n = m * n := rfl
#align nat.mul_def Nat.mul_def

-- Moved to core
#align nat.eq_of_mul_eq_mul_right Nat.eq_of_mul_eq_mul_right

lemma two_mul_ne_two_mul_add_one : 2 * n ≠ 2 * m + 1 := by omega
#align nat.two_mul_ne_two_mul_add_one Nat.two_mul_ne_two_mul_add_one

-- TODO: Replace `Nat.mul_right_cancel_iff` with `Nat.mul_left_inj`
protected lemma mul_left_inj (ha : a ≠ 0) : b * a = c * a ↔ b = c :=
  Nat.mul_right_cancel_iff (Nat.pos_iff_ne_zero.2 ha) _ _

-- TODO: Replace `Nat.mul_left_cancel_iff` with `Nat.mul_right_inj`
protected lemma mul_right_inj (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  Nat.mul_left_cancel_iff (Nat.pos_iff_ne_zero.2 ha) _ _

protected lemma mul_ne_mul_left (ha : a ≠ 0) : b * a ≠ c * a ↔ b ≠ c := (Nat.mul_left_inj ha).not
#align nat.mul_ne_mul_left Nat.mul_ne_mul_left

protected lemma mul_ne_mul_right (ha : a ≠ 0) : a * b ≠ a * c ↔ b ≠ c := (Nat.mul_right_inj ha).not
#align nat.mul_ne_mul_right Nat.mul_ne_mul_right

lemma mul_eq_left (ha : a ≠ 0) : a * b = a ↔ b = 1 := by simpa using Nat.mul_right_inj ha (c := 1)
lemma mul_eq_right (hb : b ≠ 0) : a * b = b ↔ a = 1 := by simpa using Nat.mul_left_inj hb (c := 1)

-- TODO: Deprecate
lemma mul_right_eq_self_iff (ha : 0 < a) : a * b = a ↔ b = 1 := mul_eq_left $ ne_of_gt ha
#align nat.mul_right_eq_self_iff Nat.mul_right_eq_self_iff

lemma mul_left_eq_self_iff (hb : 0 < b) : a * b = b ↔ a = 1 := mul_eq_right $ ne_of_gt hb
#align nat.mul_left_eq_self_iff Nat.mul_left_eq_self_iff

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

/-! ### `div` -/

attribute [simp] Nat.div_self

lemma div_le_iff_le_mul_add_pred (hb : 0 < b) : a / b ≤ c ↔ a ≤ b * c + (b - 1) := by
  rw [← lt_succ_iff, div_lt_iff_lt_mul hb, succ_mul, Nat.mul_comm]; cases hb <;> exact lt_succ_iff
#align nat.div_le_iff_le_mul_add_pred Nat.div_le_iff_le_mul_add_pred

/-- A version of `Nat.div_lt_self` using successors, rather than additional hypotheses. -/
lemma div_lt_self' (a b : ℕ) : (a + 1) / (b + 2) < a + 1 :=
  Nat.div_lt_self (Nat.succ_pos _) (Nat.succ_lt_succ (Nat.succ_pos _))
#align nat.div_lt_self' Nat.div_lt_self'

lemma le_div_iff_mul_le' (hb : 0 < b) : a ≤ c / b ↔ a * b ≤ c := le_div_iff_mul_le hb
#align nat.le_div_iff_mul_le' Nat.le_div_iff_mul_le'

lemma div_lt_iff_lt_mul' (hb : 0 < b) : a / b < c ↔ a < c * b := by
  simp only [← not_le, le_div_iff_mul_le' hb]
#align nat.div_lt_iff_lt_mul' Nat.div_lt_iff_lt_mul'

lemma one_le_div_iff (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by rw [le_div_iff_mul_le hb, Nat.one_mul]
#align nat.one_le_div_iff Nat.one_le_div_iff

lemma div_lt_one_iff (hb : 0 < b) : a / b < 1 ↔ a < b := by simp only [← not_le, one_le_div_iff hb]
#align nat.div_lt_one_iff Nat.div_lt_one_iff

protected lemma div_le_div_right (h : a ≤ b) : a / c ≤ b / c :=
  (c.eq_zero_or_pos.elim fun hc ↦ by simp [hc]) fun hc ↦
    (le_div_iff_mul_le' hc).2 <| le_trans (Nat.div_mul_le_self _ _) h
#align nat.div_le_div_right Nat.div_le_div_right

lemma lt_of_div_lt_div (h : a / c < b / c) : a < b :=
  Nat.lt_of_not_le fun hab ↦ Nat.not_le_of_lt h $ Nat.div_le_div_right hab
#align nat.lt_of_div_lt_div Nat.lt_of_div_lt_div

protected lemma div_pos (hba : b ≤ a) (hb : 0 < b) : 0 < a / b :=
  Nat.pos_of_ne_zero fun h ↦ lt_irrefl a $
    calc
      a = a % b := by simpa [h] using (mod_add_div a b).symm
      _ < b := mod_lt a hb
      _ ≤ a := hba
#align nat.div_pos Nat.div_pos

lemma lt_mul_of_div_lt (h : a / c < b) (hc : 0 < c) : a < b * c :=
  lt_of_not_ge <| not_le_of_gt h ∘ (Nat.le_div_iff_mul_le hc).2
#align nat.lt_mul_of_div_lt Nat.lt_mul_of_div_lt

lemma mul_div_le_mul_div_assoc (a b c : ℕ) : a * (b / c) ≤ a * b / c :=
  if hc0 : c = 0 then by simp [hc0] else
    (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hc0)).2
      (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _))
#align nat.mul_div_le_mul_div_assoc Nat.mul_div_le_mul_div_assoc

protected lemma eq_mul_of_div_eq_right (H1 : b ∣ a) (H2 : a / b = c) : a = b * c := by
  rw [← H2, Nat.mul_div_cancel' H1]
#align nat.eq_mul_of_div_eq_right Nat.eq_mul_of_div_eq_right

protected lemma div_eq_iff_eq_mul_right (H : 0 < b) (H' : b ∣ a) : a / b = c ↔ a = b * c :=
  ⟨Nat.eq_mul_of_div_eq_right H', Nat.div_eq_of_eq_mul_right H⟩
#align nat.div_eq_iff_eq_mul_right Nat.div_eq_iff_eq_mul_right

protected lemma div_eq_iff_eq_mul_left (H : 0 < b) (H' : b ∣ a) : a / b = c ↔ a = c * b := by
  rw [Nat.mul_comm]; exact Nat.div_eq_iff_eq_mul_right H H'
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
  refine ⟨fun h ↦ ?_, congr_arg fun b ↦ b / d⟩
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

@[simp] lemma rec_add_one {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) (n : ℕ) :
    Nat.rec h0 h (n + 1) = h n (Nat.rec h0 h n) := rfl
#align nat.rec_add_one Nat.rec_add_one

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
    (leRecOn (le_trans hnm hmk) (@next) x : C k) = leRecOn hmk (@next) (leRecOn hnm (@next) x) := by
  induction' hmk with k hmk ih
  · rw [leRecOn_self]
  · rw [leRecOn_succ (le_trans hnm hmk), ih, leRecOn_succ]
#align nat.le_rec_on_trans Nat.leRecOn_trans

lemma leRecOn_succ_left {C : ℕ → Sort*} {n m} (h1 : n ≤ m) (h2 : n + 1 ≤ m)
    {next : ∀ {k}, C k → C (k + 1)} (x : C n) :
    (leRecOn h2 next (next x) : C m) = (leRecOn h1 next x : C m) := by
  rw [Subsingleton.elim h1 (le_trans (le_succ n) h2), leRecOn_trans (le_succ n) h2, leRecOn_succ']
#align nat.le_rec_on_succ_left Nat.leRecOn_succ_left

lemma leRecOn_injective {C : ℕ → Sort*} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Injective (@next n)) : Injective (@leRecOn C n m hnm next) := by
  induction' hnm with m hnm ih
  · intro x y H
    rwa [leRecOn_self, leRecOn_self] at H
  intro x y H
  rw [leRecOn_succ hnm, leRecOn_succ hnm] at H
  exact ih (Hnext _ H)
#align nat.le_rec_on_injective Nat.leRecOn_injective

lemma leRecOn_surjective {C : ℕ → Sort*} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Surjective (@next n)) : Surjective (@leRecOn C n m hnm next) := by
  induction' hnm with m hnm ih
  · intro x
    use x
    rw [leRecOn_self]
  intro x
  obtain ⟨w, rfl⟩ := Hnext _ x
  obtain ⟨x, rfl⟩ := ih w
  use x
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
    (decreasingInduction h (le_trans hmn hnk) hP : P m) =
    decreasingInduction h hmn (decreasingInduction h hnk hP) := by
  induction' hnk with k hnk ih
  · rw [decreasingInduction_self]
  · rw [decreasingInduction_succ h (le_trans hmn hnk), ih, decreasingInduction_succ]
#align nat.decreasing_induction_trans Nat.decreasingInduction_trans

lemma decreasingInduction_succ_left {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n)
    (smn : m + 1 ≤ n) (mn : m ≤ n) (hP : P n) :
    decreasingInduction h mn hP = h m (decreasingInduction h smn hP) := by
  rw [Subsingleton.elim mn (le_trans (le_succ m) smn), decreasingInduction_trans,
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
termination_by pincerRecursion Ha0 Hab H n m => n + m
#align nat.pincer_recursion Nat.pincerRecursion

/-- Decreasing induction: if `P (k+1)` implies `P k` for all `m ≤ k < n`, then `P n` implies `P m`.
Also works for functions to `Sort*`. Weakens the assumptions of `decreasing_induction`. -/
@[elab_as_elim]
def decreasingInduction' {P : ℕ → Sort*} {m n : ℕ} (h : ∀ k < n, m ≤ k → P (k + 1) → P k)
    (mn : m ≤ n) (hP : P n) : P m := by
  revert h hP
  refine' leRecOn' mn _ _
  · intro n mn ih h hP
    apply ih
    · exact fun k hk ↦ h k (Nat.lt.step hk)
    · exact h n (lt_succ_self n) mn hP
  · intro _ hP
    exact hP
#align nat.decreasing_induction' Nat.decreasingInduction'

/-! ### `mod`, `dvd` -/

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

-- TODO: Replace `Nat.dvd_add_iff_left`
protected lemma dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b := (Nat.dvd_add_iff_left h).symm
#align nat.dvd_add_left Nat.dvd_add_left

protected lemma dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c := (Nat.dvd_add_iff_right h).symm
#align nat.dvd_add_right Nat.dvd_add_right

protected lemma mul_dvd_mul_iff_left (ha : 0 < a) : a * b ∣ a * c ↔ b ∣ c :=
  exists_congr fun d ↦ by rw [Nat.mul_assoc, Nat.mul_right_inj $ ne_of_gt ha]
#align nat.mul_dvd_mul_iff_left Nat.mul_dvd_mul_iff_left

protected lemma mul_dvd_mul_iff_right (hc : 0 < c) : a * c ∣ b * c ↔ a ∣ b :=
  exists_congr fun d ↦ by rw [Nat.mul_right_comm, Nat.mul_left_inj $ ne_of_gt hc]
#align nat.mul_dvd_mul_iff_right Nat.mul_dvd_mul_iff_right

#align nat.dvd_one Nat.dvd_one

@[simp] lemma mod_mod_of_dvd (a : ℕ) (h : c ∣ b) : a % b % c = a % c := by
  conv_rhs => rw [← mod_add_div a b]
  obtain ⟨x, rfl⟩ := h
  rw [Nat.mul_assoc, add_mul_mod_self_left]
#align nat.mod_mod_of_dvd Nat.mod_mod_of_dvd

-- Moved to Std
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

-- Moved to Std
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

lemma div_le_div_left (hcb : c ≤ b) (hc : 0 < c) : a / b ≤ a / c :=
  (Nat.le_div_iff_mul_le hc).2 <| le_trans (Nat.mul_le_mul_left _ hcb) (div_mul_le_self _ _)
#align nat.div_le_div_left Nat.div_le_div_left

-- Moved to Std
#align nat.mul_div_le Nat.mul_div_le

lemma lt_mul_div_succ (a : ℕ) (hb : 0 < b) : a < b * (a / b + 1) := by
  rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul' hb]
  exact lt_succ_self _
#align nat.lt_mul_div_succ Nat.lt_mul_div_succ

-- TODO: Std4 claimed this name but flipped the order of multiplication
lemma mul_add_mod' (a b c : ℕ) : (a * b + c) % b = c % b := by rw [Nat.mul_comm, Nat.mul_add_mod]
#align nat.mul_add_mod Nat.mul_add_mod'

lemma mul_add_mod_of_lt (h : c < b) : (a * b + c) % b = c := by
  rw [Nat.mul_add_mod', Nat.mod_eq_of_lt h]
#align nat.mul_add_mod_of_lt Nat.mul_add_mod_of_lt

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
  simp only [exists_prop, ← lt_succ_iff, find_lt_iff]
#align nat.find_le_iff Nat.find_le_iff

@[simp] lemma le_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n ≤ Nat.find h ↔ ∀ m < n, ¬ p m := by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]
#align nat.le_find_iff Nat.le_find_iff

@[simp] lemma lt_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n < Nat.find h ↔ ∀ m ≤ n, ¬ p m := by
  simp only [← succ_le_iff, le_find_iff, succ_le_succ_iff]
#align nat.lt_find_iff Nat.lt_find_iff

@[simp] lemma find_eq_zero (h : ∃ n : ℕ, p n) : Nat.find h = 0 ↔ p 0 := by simp [find_eq_iff]
#align nat.find_eq_zero Nat.find_eq_zero

lemma find_mono (h : ∀ n, q n → p n) {hp : ∃ n, p n} {hq : ∃ n, q n} :  Nat.find hp ≤ Nat.find hq :=
  Nat.find_min' _ (h _ (Nat.find_spec hq))
#align nat.find_mono Nat.find_mono

lemma find_le {h : ∃ n, p n} (hn : p n) : Nat.find h ≤ n :=
  (Nat.find_le_iff _ _).2 ⟨n, le_refl _, hn⟩
#align nat.find_le Nat.find_le

lemma find_comp_succ (h₁ : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h0 : ¬ p 0) :
    Nat.find h₁ = Nat.find h₂ + 1 := by
  refine' (find_eq_iff _).2 ⟨Nat.find_spec h₂, fun n hn ↦ _⟩
  cases' n with n
  exacts [h0, @Nat.find_min (fun n ↦ p (n + 1)) _ h₂ _ (succ_lt_succ_iff.1 hn)]
#align nat.find_comp_succ Nat.find_comp_succ

end Find

/-! ### `find_greatest` -/

section FindGreatest

/-- `find_greatest P n` is the largest `i ≤ bound` such that `P i` holds, or `0` if no such `i`
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

end FindGreatest

/-! ### Decidability of predicates -/

-- To work around lean4#2552, we use `match` instead of `if/casesOn` with decidable instances.
instance decidableBallLT :
  ∀ (n : Nat) (P : ∀ k, k < n → Prop) [∀ n h, Decidable (P n h)], Decidable (∀ n h, P n h)
| 0, _, _ => isTrue fun _ ↦ (by cases ·)
| n + 1, P, H =>
  match decidableBallLT n (P · <| lt_succ_of_lt ·) with
  | isFalse h => isFalse (h fun _ _ ↦ · _ _)
  | isTrue h =>
    match H n Nat.le.refl with
    | isFalse p => isFalse (p <| · _ _)
    | isTrue p => isTrue fun _ h' ↦ (lt_succ_iff_lt_or_eq.1 h').elim (h _) fun hn ↦ hn ▸ p
#align nat.decidable_ball_lt Nat.decidableBallLT

-- To verify we don't have a regression on the speed, we put a difficult example.
-- any regression should take a huge amount of heartbeats -- we are currently at 187621.
-- For reference, the instance using `casesOn` took 44544 for 4; this one takes 1299 for 4.
example : ∀ m, m < 25 → ∀ n, n < 25 → ∀ c, c < 25 → m ^ 2 + n ^ 2 + c ^ 2 ≠ 7 := by decide

instance decidableForallFin (P : Fin n → Prop) [DecidablePred P] : Decidable (∀ i, P i) :=
  decidable_of_iff (∀ k h, P ⟨k, h⟩) ⟨fun m ⟨k, h⟩ ↦ m k h, fun m k h ↦ m ⟨k, h⟩⟩
#align nat.decidable_forall_fin Nat.decidableForallFin

instance decidableBallLe (n : ℕ) (P : ∀ k ≤ n, Prop) [∀ n h, Decidable (P n h)] :
    Decidable (∀ n h, P n h) :=
  decidable_of_iff (∀ (k) (h : k < succ n), P k (le_of_lt_succ h))
    ⟨fun m k h ↦ m k (lt_succ_of_le h), fun m k _ ↦ m k _⟩
#align nat.decidable_ball_le Nat.decidableBallLe

instance decidableExistsLT [h : DecidablePred p] : DecidablePred fun n ↦ ∃ m : ℕ, m < n ∧ p m
  | 0 => isFalse (by simp)
  | n + 1 =>
    @decidable_of_decidable_of_iff _ _ (@instDecidableOr _ _ (decidableExistsLT n) (h n))
      (by simp only [lt_succ_iff_lt_or_eq, or_and_right, exists_or, exists_eq_left])
#align nat.decidable_exists_lt Nat.decidableExistsLT

instance decidableExistsLe [DecidablePred p] : DecidablePred fun n ↦ ∃ m : ℕ, m ≤ n ∧ p m :=
  fun n ↦ decidable_of_iff (∃ m, m < n + 1 ∧ p m)
    (exists_congr fun _ ↦ and_congr_left' lt_succ_iff)
#align nat.decidable_exists_le Nat.decidableExistsLe

end Nat
