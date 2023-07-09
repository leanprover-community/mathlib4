/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

! This file was ported from Lean 3 source module init.data.nat.lemmas
! leanprover-community/lean commit 38b59111b2b4e6c572582b27e8937e92fc70ac02
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Std.Data.Nat.Lemmas
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Div
import Mathlib.Init.Algebra.Functions

universe u

namespace Nat

/-! addition -/

#align nat.add_comm Nat.add_comm

#align nat.add_assoc Nat.add_assoc

#align nat.add_left_comm Nat.add_left_comm

#align nat.add_left_cancel Nat.add_left_cancel

#align nat.add_right_cancel Nat.add_right_cancel

#align nat.succ_ne_zero Nat.succ_ne_zero

#align nat.succ_ne_self Nat.succ_ne_self

#align nat.one_ne_zero Nat.one_ne_zero

#align nat.zero_ne_one Nat.zero_ne_one

#align nat.eq_zero_of_add_eq_zero_right Nat.eq_zero_of_add_eq_zero_right

#align nat.eq_zero_of_add_eq_zero_left Nat.eq_zero_of_add_eq_zero_left

#align nat.add_right_comm Nat.add_right_comm

#align nat.eq_zero_of_add_eq_zero Nat.eq_zero_of_add_eq_zero

/-! multiplication -/

#align nat.mul_zero Nat.mul_zero

#align nat.mul_succ Nat.mul_succ

#align nat.zero_mul Nat.zero_mul

#align nat.succ_mul Nat.succ_mul

#align nat.right_distrib Nat.right_distrib

#align nat.left_distrib Nat.left_distrib

#align nat.mul_comm Nat.mul_comm

#align nat.mul_assoc Nat.mul_assoc

#align nat.mul_one Nat.mul_one

#align nat.one_mul Nat.one_mul

#align nat.succ_add_eq_succ_add Nat.succ_add_eq_succ_add

theorem eq_zero_of_mul_eq_zero : ∀ {n m : ℕ}, n * m = 0 → n = 0 ∨ m = 0
  | 0, m => fun _ => Or.inl rfl
  | succ n, m => by
    rw [succ_mul]; intro h
    exact Or.inr (Nat.eq_zero_of_add_eq_zero_left h)
#align nat.eq_zero_of_mul_eq_zero Nat.eq_zero_of_mul_eq_zero

/-! properties of inequality -/

#align nat.le_of_eq Nat.le_of_eq

#align nat.le_succ_of_le Nat.le_succ_of_le

#align nat.le_of_succ_le Nat.le_of_succ_le

#align nat.le_of_lt Nat.le_of_lt

#align nat.lt.step Nat.lt.step

#align nat.eq_zero_or_pos Nat.eq_zero_or_pos

#align nat.pos_of_ne_zero Nat.pos_of_ne_zero

#align nat.lt_trans Nat.lt_trans

#align nat.lt_of_le_of_lt Nat.lt_of_le_of_lt

#align nat.lt.base Nat.lt.base

#align nat.lt_succ_self Nat.lt_succ_self

#align nat.le_antisymm Nat.le_antisymm

#align nat.lt_or_ge Nat.lt_or_ge

#align nat.le_total Nat.le_total

protected theorem lt_of_le_and_ne {m n : ℕ} (h1 : m ≤ n) : m ≠ n → m < n :=
  Or.resolve_right (Or.symm (Nat.eq_or_lt_of_le h1))
#align nat.lt_of_le_and_ne Nat.lt_of_le_and_ne

#align nat.lt_iff_le_not_le Nat.lt_iff_le_not_le

instance : LinearOrder ℕ where
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

#align nat.eq_zero_of_le_zero Nat.eq_zero_of_le_zero

#align nat.succ_lt_succ Nat.succ_lt_succ

#align nat.lt_of_succ_lt Nat.lt_of_succ_lt

#align nat.lt_of_succ_lt_succ Nat.lt_of_succ_lt_succ

#align nat.pred_lt_pred Nat.pred_lt_pred

#align nat.lt_of_succ_le Nat.lt_of_succ_le

#align nat.succ_le_of_lt Nat.succ_le_of_lt

#align nat.le_add_right Nat.le_add_right

#align nat.le_add_left Nat.le_add_left

#align nat.le.dest Nat.le.dest

#align nat.le.intro Nat.le.intro

#align nat.add_le_add_left Nat.add_le_add_left

#align nat.add_le_add_right Nat.add_le_add_right

#align nat.le_of_add_le_add_left Nat.le_of_add_le_add_left

#align nat.le_of_add_le_add_right Nat.le_of_add_le_add_rightₓ

protected theorem add_le_add_iff_right {k n m : ℕ} : n + k ≤ m + k ↔ n ≤ m :=
  ⟨Nat.le_of_add_le_add_right, fun h => Nat.add_le_add_right h _⟩
#align nat.add_le_add_iff_right Nat.add_le_add_iff_right

#align nat.lt_of_add_lt_add_left Nat.lt_of_add_lt_add_left

#align nat.lt_of_add_lt_add_right Nat.lt_of_add_lt_add_right

#align nat.add_lt_add_left Nat.add_lt_add_left

#align nat.add_lt_add_right Nat.add_lt_add_right

#align nat.lt_add_of_pos_right Nat.lt_add_of_pos_right

#align nat.lt_add_of_pos_left Nat.lt_add_of_pos_left

#align nat.add_lt_add Nat.add_lt_add

#align nat.add_le_add Nat.add_le_add

#align nat.zero_lt_one Nat.zero_lt_one

#align nat.mul_le_mul_left Nat.mul_le_mul_left

#align nat.mul_le_mul_right Nat.mul_le_mul_right

#align nat.mul_lt_mul_of_pos_left Nat.mul_lt_mul_of_pos_left

#align nat.mul_lt_mul_of_pos_right Nat.mul_lt_mul_of_pos_right

#align nat.le_of_mul_le_mul_left Nat.le_of_mul_le_mul_left

#align nat.le_of_lt_succ Nat.le_of_lt_succ

#align nat.eq_of_mul_eq_mul_left Nat.eq_of_mul_eq_mul_left

#align nat.mul_pos Nat.mul_pos

#align nat.le_succ_of_pred_le Nat.le_succ_of_pred_le

#align nat.le_lt_antisymm Nat.le_lt_antisymm

#align nat.lt_le_antisymm Nat.lt_le_antisymm

#align nat.lt_asymm Nat.lt_asymm

protected def ltGeByCases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : b ≤ a → C) : C :=
  Decidable.byCases h₁ fun h => h₂ (Or.elim (Nat.lt_or_ge a b) (fun a => absurd a h) fun a => a)
#align nat.lt_ge_by_cases Nat.ltGeByCases

protected def ltByCases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : a = b → C) (h₃ : b < a → C) :
    C :=
  Nat.ltGeByCases h₁ fun h₁ => Nat.ltGeByCases h₃ fun h => h₂ (Nat.le_antisymm h h₁)
#align nat.lt_by_cases Nat.ltByCases

#align nat.lt_trichotomy Nat.lt_trichotomy

#align nat.eq_or_lt_of_not_lt Nat.eq_or_lt_of_not_lt

#align nat.lt_succ_of_lt Nat.lt_succ_of_lt

#align nat.one_pos Nat.one_pos

#align nat.mul_le_mul_of_nonneg_left Nat.mul_le_mul_of_nonneg_left

#align nat.mul_le_mul_of_nonneg_right Nat.mul_le_mul_of_nonneg_right

#align nat.mul_lt_mul Nat.mul_lt_mulₓ

#align nat.mul_lt_mul' Nat.mul_lt_mul'ₓ

-- TODO: there are four variations, depending on which variables we assume to be nonneg
#align nat.mul_le_mul Nat.mul_le_mul

/-! bit0/bit1 properties -/
section bit
set_option linter.deprecated false

protected theorem bit1_eq_succ_bit0 (n : ℕ) : bit1 n = succ (bit0 n) :=
  rfl
#align nat.bit1_eq_succ_bit0 Nat.bit1_eq_succ_bit0

protected theorem bit1_succ_eq (n : ℕ) : bit1 (succ n) = succ (succ (bit1 n)) :=
  Eq.trans (Nat.bit1_eq_succ_bit0 (succ n)) (congr_arg succ (Nat.bit0_succ_eq n))
#align nat.bit1_succ_eq Nat.bit1_succ_eq

protected theorem bit1_ne_one : ∀ {n : ℕ}, n ≠ 0 → bit1 n ≠ 1
  | 0, h, h1 => absurd rfl h
  | n + 1, h, h1 => Nat.noConfusion h1 fun h2 => absurd h2 (succ_ne_zero _)
#align nat.bit1_ne_one Nat.bit1_ne_one

protected theorem bit0_ne_one : ∀ n : ℕ, bit0 n ≠ 1
  | 0, h => absurd h (Ne.symm Nat.one_ne_zero)
  | n + 1, h =>
    have h1 : succ (succ (n + n)) = 1 := succ_add n n ▸ h
    Nat.noConfusion h1 fun h2 => absurd h2 (succ_ne_zero (n + n))
#align nat.bit0_ne_one Nat.bit0_ne_one

#align nat.add_self_ne_one Nat.add_self_ne_one

protected theorem bit1_ne_bit0 : ∀ n m : ℕ, bit1 n ≠ bit0 m
  | 0, m, h => absurd h (Ne.symm (Nat.add_self_ne_one m))
  | n + 1, 0, h =>
    have h1 : succ (bit0 (succ n)) = 0 := h
    absurd h1 (Nat.succ_ne_zero _)
  | n + 1, m + 1, h =>
    have h1 : succ (succ (bit1 n)) = succ (succ (bit0 m)) :=
      Nat.bit0_succ_eq m ▸ Nat.bit1_succ_eq n ▸ h
    have h2 : bit1 n = bit0 m := Nat.noConfusion h1 fun h2' => Nat.noConfusion h2' fun h2'' => h2''
    absurd h2 (Nat.bit1_ne_bit0 n m)
#align nat.bit1_ne_bit0 Nat.bit1_ne_bit0

protected theorem bit0_ne_bit1 : ∀ n m : ℕ, bit0 n ≠ bit1 m := fun n m : Nat =>
  Ne.symm (Nat.bit1_ne_bit0 m n)
#align nat.bit0_ne_bit1 Nat.bit0_ne_bit1

protected theorem bit0_inj : ∀ {n m : ℕ}, bit0 n = bit0 m → n = m
  | 0, 0, h => rfl
  | 0, m + 1, h => by contradiction
  | n + 1, 0, h => by contradiction
  | n + 1, m + 1, h =>
    by
    have : succ (succ (n + n)) = succ (succ (m + m)) :=
      by
      unfold bit0 at h ; simp [add_one, add_succ, succ_add] at h
      have aux : n + n = m + m := h; rw [aux]
    have : n + n = m + m := by repeat injection this with this
    have : n = m := Nat.bit0_inj this
    rw [this]
#align nat.bit0_inj Nat.bit0_inj

protected theorem bit1_inj : ∀ {n m : ℕ}, bit1 n = bit1 m → n = m := @fun n m h =>
  have : succ (bit0 n) = succ (bit0 m) := by simp [Nat.bit1_eq_succ_bit0] at h ; rw [h]
  have : bit0 n = bit0 m := by injection this
  Nat.bit0_inj this
#align nat.bit1_inj Nat.bit1_inj

protected theorem bit0_ne {n m : ℕ} : n ≠ m → bit0 n ≠ bit0 m := fun h₁ h₂ =>
  absurd (Nat.bit0_inj h₂) h₁
#align nat.bit0_ne Nat.bit0_ne

protected theorem bit1_ne {n m : ℕ} : n ≠ m → bit1 n ≠ bit1 m := fun h₁ h₂ =>
  absurd (Nat.bit1_inj h₂) h₁
#align nat.bit1_ne Nat.bit1_ne

protected theorem zero_ne_bit0 {n : ℕ} : n ≠ 0 → 0 ≠ bit0 n := fun h => Ne.symm (Nat.bit0_ne_zero h)
#align nat.zero_ne_bit0 Nat.zero_ne_bit0

protected theorem zero_ne_bit1 (n : ℕ) : 0 ≠ bit1 n :=
  Ne.symm (Nat.bit1_ne_zero n)
#align nat.zero_ne_bit1 Nat.zero_ne_bit1

protected theorem one_ne_bit0 (n : ℕ) : 1 ≠ bit0 n :=
  Ne.symm (Nat.bit0_ne_one n)
#align nat.one_ne_bit0 Nat.one_ne_bit0

protected theorem one_ne_bit1 {n : ℕ} : n ≠ 0 → 1 ≠ bit1 n := fun h => Ne.symm (Nat.bit1_ne_one h)
#align nat.one_ne_bit1 Nat.one_ne_bit1

protected theorem one_lt_bit1 : ∀ {n : Nat}, n ≠ 0 → 1 < bit1 n
  | 0, h => by contradiction
  | succ n, h => by
    rw [Nat.bit1_succ_eq]
    apply succ_lt_succ
    apply zero_lt_succ
#align nat.one_lt_bit1 Nat.one_lt_bit1

protected theorem one_lt_bit0 : ∀ {n : Nat}, n ≠ 0 → 1 < bit0 n
  | 0, h => by contradiction
  | succ n, h => by
    rw [Nat.bit0_succ_eq]
    apply succ_lt_succ
    apply zero_lt_succ
#align nat.one_lt_bit0 Nat.one_lt_bit0

protected theorem bit0_lt {n m : Nat} (h : n < m) : bit0 n < bit0 m :=
  Nat.add_lt_add h h
#align nat.bit0_lt Nat.bit0_lt

protected theorem bit1_lt {n m : Nat} (h : n < m) : bit1 n < bit1 m :=
  succ_lt_succ (Nat.add_lt_add h h)
#align nat.bit1_lt Nat.bit1_lt

protected theorem bit0_lt_bit1 {n m : Nat} (h : n ≤ m) : bit0 n < bit1 m :=
  lt_succ_of_le (Nat.add_le_add h h)
#align nat.bit0_lt_bit1 Nat.bit0_lt_bit1

protected theorem bit1_lt_bit0 : ∀ {n m : Nat}, n < m → bit1 n < bit0 m
  | n, 0, h => absurd h n.not_lt_zero
  | n, succ m, h =>
    have : n ≤ m := le_of_lt_succ h
    have : succ (n + n) ≤ succ (m + m) := succ_le_succ (Nat.add_le_add this this)
    have : succ (n + n) ≤ succ m + m := by rw [succ_add]; assumption
    show succ (n + n) < succ (succ m + m) from lt_succ_of_le this
#align nat.bit1_lt_bit0 Nat.bit1_lt_bit0

protected theorem one_le_bit1 (n : ℕ) : 1 ≤ bit1 n :=
  show 1 ≤ succ (bit0 n) from succ_le_succ (bit0 n).zero_le
#align nat.one_le_bit1 Nat.one_le_bit1

protected theorem one_le_bit0 : ∀ n : ℕ, n ≠ 0 → 1 ≤ bit0 n
  | 0, h => absurd rfl h
  | n + 1, h =>
    suffices 1 ≤ succ (succ (bit0 n)) from Eq.symm (Nat.bit0_succ_eq n) ▸ this
    succ_le_succ (bit0 n).succ.zero_le
#align nat.one_le_bit0 Nat.one_le_bit0

end bit

/-! successor and predecessor -/

#align nat.pred_zero Nat.pred_zero

#align nat.pred_succ Nat.pred_succ

#align nat.add_one_ne_zero Nat.add_one_ne_zero

#align nat.eq_zero_or_eq_succ_pred Nat.eq_zero_or_eq_succ_pred

#align nat.exists_eq_succ_of_ne_zero Nat.exists_eq_succ_of_ne_zero

def discriminate {B : Sort u} {n : ℕ} (H1 : n = 0 → B) (H2 : ∀ m, n = succ m → B) : B := by
  induction' h : n
  · exact H1 h
  · exact H2 _ h
#align nat.discriminate Nat.discriminate

theorem one_succ_zero : 1 = succ 0 :=
  rfl
#align nat.one_succ_zero Nat.one_succ_zero

#align nat.pred_inj Nat.pred_inj

/-! subtraction

Many lemmas are proven more generally in mathlib `algebra/order/sub` -/

#align nat.zero_sub Nat.zero_sub

#align nat.sub_lt_succ Nat.sub_lt_succ

#align nat.sub_zero Nat.sub_zero

#align nat.sub_succ Nat.sub_succ

#align nat.succ_sub_succ Nat.succ_sub_succ

#align nat.sub_self Nat.sub_self

#align nat.add_sub_add_right Nat.add_sub_add_right

#align nat.add_sub_add_left Nat.add_sub_add_left

#align nat.add_sub_cancel Nat.add_sub_cancel

#align nat.add_sub_cancel_left Nat.add_sub_cancel_left

#align nat.sub_sub Nat.sub_sub

#align nat.le_of_le_of_sub_le_sub_right Nat.le_of_le_of_sub_le_sub_right

protected theorem sub_le_sub_iff_right {n m k : ℕ} (h : k ≤ m) : n - k ≤ m - k ↔ n ≤ m :=
  ⟨Nat.le_of_le_of_sub_le_sub_right h, fun h => Nat.sub_le_sub_right h k⟩
#align nat.sub_le_sub_iff_right Nat.sub_le_sub_iff_right

#align nat.sub_self_add Nat.sub_self_add

protected theorem le_sub_iff_right {x y k : ℕ} (h : k ≤ y) : x ≤ y - k ↔ x + k ≤ y := by
  rw [← Nat.add_sub_cancel x k, Nat.sub_le_sub_iff_right h, Nat.add_sub_cancel]
#align nat.le_sub_iff_right Nat.le_sub_iff_right

#align nat.sub_lt_of_pos_le Nat.sub_lt_of_pos_le

#align nat.sub_one Nat.sub_one

#align nat.succ_sub_one Nat.succ_sub_one

#align nat.succ_pred_eq_of_pos Nat.succ_pred_eq_of_pos

#align nat.sub_eq_zero_of_le Nat.sub_eq_zero_of_le

#align nat.le_of_sub_eq_zero Nat.le_of_sub_eq_zero

#align nat.sub_eq_zero_iff_le Nat.sub_eq_zero_iff_le

#align nat.add_sub_of_le Nat.add_sub_of_le

#align nat.sub_add_cancel Nat.sub_add_cancel

#align nat.add_sub_assoc Nat.add_sub_assoc

#align nat.sub_eq_iff_eq_add Nat.sub_eq_iff_eq_add

#align nat.lt_of_sub_eq_succ Nat.lt_of_sub_eq_succ

#align nat.sub_le_sub_left Nat.sub_le_sub_left

#align nat.succ_sub_sub_succ Nat.succ_sub_sub_succ

protected theorem sub.right_comm (m n k : ℕ) : m - n - k = m - k - n := by
  rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]
#align nat.sub.right_comm Nat.sub.right_comm

#align nat.succ_sub Nat.succ_sub

#align nat.sub_pos_of_lt Nat.sub_pos_of_lt

#align nat.sub_sub_self Nat.sub_sub_self

#align nat.sub_add_comm Nat.sub_add_comm

#align nat.sub_one_sub_lt Nat.sub_one_sub_ltₓ

#align nat.mul_pred_left Nat.mul_pred_left

#align nat.mul_pred_right Nat.mul_pred_right

#align nat.mul_sub_right_distrib Nat.mul_sub_right_distrib

#align nat.mul_sub_left_distrib Nat.mul_sub_left_distrib

#align nat.mul_self_sub_mul_self_eq Nat.mul_self_sub_mul_self_eq

#align nat.succ_mul_succ_eq Nat.succ_mul_succ_eq

/-! min -/


protected theorem zero_min (a : ℕ) : min 0 a = 0 :=
  min_eq_left a.zero_le
#align nat.zero_min Nat.zero_min

protected theorem min_zero (a : ℕ) : min a 0 = 0 :=
  min_eq_right a.zero_le
#align nat.min_zero Nat.min_zero

-- Distribute succ over min
theorem min_succ_succ (x y : ℕ) : min (succ x) (succ y) = succ (min x y) :=
  have f : x ≤ y → min (succ x) (succ y) = succ (min x y) := fun p =>
    calc
      min (succ x) (succ y) = succ x := if_pos (succ_le_succ p)
      _ = succ (min x y) := congr_arg succ (Eq.symm (if_pos p))
  have g : ¬x ≤ y → min (succ x) (succ y) = succ (min x y) := fun p =>
    calc
      min (succ x) (succ y) = succ y := if_neg fun eq => p (pred_le_pred Eq)
      _ = succ (min x y) := congr_arg succ (Eq.symm (if_neg p))
  Decidable.byCases f g
#align nat.min_succ_succ Nat.min_succ_succ

theorem sub_eq_sub_min (n m : ℕ) : n - m = n - min n m :=
  if h : n ≥ m then by rw [min_eq_right h]
  else by rw [Nat.sub_eq_zero_of_le (le_of_not_ge h), min_eq_left (le_of_not_ge h), Nat.sub_self]
#align nat.sub_eq_sub_min Nat.sub_eq_sub_min

@[simp]
protected theorem sub_add_min_cancel (n m : ℕ) : n - m + min n m = n := by
  rw [sub_eq_sub_min, Nat.sub_add_cancel (min_le_left n m)]
#align nat.sub_add_min_cancel Nat.sub_add_min_cancel

/-! induction principles -/


def twoStepInduction {P : ℕ → Sort u} (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : ∀ a : ℕ, P a
  | 0 => H1
  | 1 => H2
  | succ (succ n) => H3 _ (two_step_induction _) (two_step_induction _)
#align nat.two_step_induction Nat.twoStepInduction

def subInduction {P : ℕ → ℕ → Sort u} (H1 : ∀ m, P 0 m) (H2 : ∀ n, P (succ n) 0)
    (H3 : ∀ n m, P n m → P (succ n) (succ m)) : ∀ n m : ℕ, P n m
  | 0, m => H1 _
  | succ n, 0 => H2 _
  | succ n, succ m => H3 _ _ (sub_induction n m)
#align nat.sub_induction Nat.subInduction

protected def strongRecOn {p : Nat → Sort u} (n : Nat) (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
  by
  suffices ∀ n m, m < n → p m from this (succ n) n (lt_succ_self _)
  intro n; induction' n with n ih
  · intro m h₁; exact absurd h₁ m.not_lt_zero
  · intro m h₁
    apply Or.by_cases (Decidable.lt_or_eq_of_le (le_of_lt_succ h₁))
    · intros; apply ih; assumption
    · intros; subst m; apply h _ ih
#align nat.strong_rec_on Nat.strongRecOn

protected theorem strong_induction_on {p : Nat → Prop} (n : Nat)
    (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
  Nat.strongRecOn n h
#align nat.strong_induction_on Nat.strong_induction_on

protected theorem case_strong_induction_on {p : Nat → Prop} (a : Nat) (hz : p 0)
    (hi : ∀ n, (∀ m, m ≤ n → p m) → p (succ n)) : p a :=
  Nat.strong_induction_on a fun n =>
    match n with
    | 0 => fun _ => hz
    | n + 1 => fun h₁ => hi n fun m h₂ => h₁ _ (lt_succ_of_le h₂)
#align nat.case_strong_induction_on Nat.case_strong_induction_on

/-! mod -/


private theorem mod_core_congr {x y f1 f2} (h1 : x ≤ f1) (h2 : x ≤ f2) :
    Nat.modCore y f1 x = Nat.modCore y f2 x :=
  by
  cases y; · cases f1 <;> cases f2 <;> rfl
  induction' f1 with f1 ih generalizing x f2; · cases h1; cases f2 <;> rfl
  cases x; · cases f1 <;> cases f2 <;> rfl
  cases f2; · cases h2
  refine' if_congr Iff.rfl _ rfl
  simp only [succ_sub_succ]
  exact
    ih (le_trans (Nat.sub_le _ _) (le_of_succ_le_succ h1))
      (le_trans (Nat.sub_le _ _) (le_of_succ_le_succ h2))

theorem mod_eq (x y : Nat) : x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x :=
  by
  cases x; · cases y <;> rfl
  cases y; · rfl
  refine' if_congr Iff.rfl (mod_core_congr _ _) rfl <;> simp [Nat.sub_le]
#align nat.mod_def Nat.mod_eq

@[simp]
theorem mod_zero (a : Nat) : a % 0 = a := by
  rw [mod_def]
  have h : ¬(0 < 0 ∧ 0 ≤ a)
  simp [lt_irrefl]
  simp [if_neg, h]
#align nat.mod_zero Nat.mod_zero

theorem mod_eq_of_lt {a b : Nat} (h : a < b) : a % b = a :=
  by
  rw [mod_def]
  have h' : ¬(0 < b ∧ b ≤ a)
  simp [not_le_of_gt h]
  simp [if_neg, h']
#align nat.mod_eq_of_lt Nat.mod_eq_of_lt

@[simp]
theorem zero_mod (b : Nat) : 0 % b = 0 := by
  rw [mod_def]
  have h : ¬(0 < b ∧ b ≤ 0) := by intro hn; cases' hn with l r;
    exact absurd (lt_of_lt_of_le l r) (lt_irrefl 0)
  simp [if_neg, h]
#align nat.zero_mod Nat.zero_mod

theorem mod_eq_sub_mod {a b : Nat} (h : b ≤ a) : a % b = (a - b) % b :=
  Or.elim b.eq_zero_or_pos (fun b0 => by rw [b0, Nat.sub_zero]) fun h₂ => by
    rw [mod_def, if_pos (And.intro h₂ h)]
#align nat.mod_eq_sub_mod Nat.mod_eq_sub_mod

theorem mod_lt (x : Nat) {y : Nat} (h : 0 < y) : x % y < y :=
  by
  induction' x using Nat.case_strong_induction_on with x ih
  · rw [zero_mod]; assumption
  · by_cases h₁ : succ x < y
    · rwa [mod_eq_of_lt h₁]
    · have h₁ : succ x % y = (succ x - y) % y := mod_eq_sub_mod (not_lt.1 h₁)
      have : succ x - y ≤ x := le_of_lt_succ (Nat.sub_lt (succ_pos x) h)
      have h₂ : (succ x - y) % y < y := ih _ this
      rwa [← h₁] at h₂
#align nat.mod_lt Nat.mod_lt

@[simp]
theorem mod_self (n : Nat) : n % n = 0 := by rw [mod_eq_sub_mod (le_refl _), Nat.sub_self, zero_mod]
#align nat.mod_self Nat.mod_self

@[simp]
theorem mod_one (n : ℕ) : n % 1 = 0 :=
  have : n % 1 < 1 := (mod_lt n) (succ_pos 0)
  Nat.eq_zero_of_le_zero (le_of_lt_succ this)
#align nat.mod_one Nat.mod_one

theorem mod_two_eq_zero_or_one (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 :=
  match n % 2, @Nat.mod_lt n 2 (by decide) with
  | 0, _ => Or.inl rfl
  | 1, _ => Or.inr rfl
  | k + 2, h => absurd h (by decide)
#align nat.mod_two_eq_zero_or_one Nat.mod_two_eq_zero_or_one

theorem mod_le (x y : ℕ) : x % y ≤ x :=
  Or.elim (lt_or_le x y) (fun xlty => by rw [mod_eq_of_lt xlty] <;> rfl) fun ylex =>
    Or.elim y.eq_zero_or_pos (fun y0 => by rw [y0, mod_zero] <;> rfl) fun ypos =>
      le_trans (le_of_lt (mod_lt _ ypos)) ylex
#align nat.mod_le Nat.mod_le

@[simp]
theorem add_mod_right (x z : ℕ) : (x + z) % z = x % z := by
  rw [mod_eq_sub_mod (Nat.le_add_left _ _), Nat.add_sub_cancel]
#align nat.add_mod_right Nat.add_mod_right

@[simp]
theorem add_mod_left (x z : ℕ) : (x + z) % x = z % x := by rw [Nat.add_comm, add_mod_right]
#align nat.add_mod_left Nat.add_mod_left

@[simp]
theorem add_mul_mod_self_left (x y z : ℕ) : (x + y * z) % y = x % y := by induction' z with z ih;
  rw [Nat.mul_zero, Nat.add_zero]; rw [mul_succ, ← Nat.add_assoc, add_mod_right, ih]
#align nat.add_mul_mod_self_left Nat.add_mul_mod_self_left

@[simp]
theorem add_mul_mod_self_right (x y z : ℕ) : (x + y * z) % z = x % z := by
  rw [Nat.mul_comm, add_mul_mod_self_left]
#align nat.add_mul_mod_self_right Nat.add_mul_mod_self_right

@[simp]
theorem mul_mod_right (m n : ℕ) : m * n % m = 0 := by
  rw [← Nat.zero_add (m * n), add_mul_mod_self_left, zero_mod]
#align nat.mul_mod_right Nat.mul_mod_right

@[simp]
theorem mul_mod_left (m n : ℕ) : m * n % n = 0 := by rw [Nat.mul_comm, mul_mod_right]
#align nat.mul_mod_left Nat.mul_mod_left

theorem mul_mod_mul_left (z x y : ℕ) : z * x % (z * y) = z * (x % y) :=
  if y0 : y = 0 then by rw [y0, Nat.mul_zero, mod_zero, mod_zero]
  else
    if z0 : z = 0 then by rw [z0, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, mod_zero]
    else
      x.strong_induction_on fun n IH =>
        have y0 : y > 0 := Nat.pos_of_ne_zero y0
        have z0 : z > 0 := Nat.pos_of_ne_zero z0
        Or.elim (le_or_lt y n)
          (fun yn => by
            rw [mod_eq_sub_mod yn, mod_eq_sub_mod (Nat.mul_le_mul_left z yn), ←
                Nat.mul_sub_left_distrib] <;>
              exact IH _ (Nat.sub_lt (lt_of_lt_of_le y0 yn) y0))
          fun yn => by rw [mod_eq_of_lt yn, mod_eq_of_lt (Nat.mul_lt_mul_of_pos_left yn z0)]
#align nat.mul_mod_mul_left Nat.mul_mod_mul_left

theorem mul_mod_mul_right (z x y : ℕ) : x * z % (y * z) = x % y * z := by
  rw [Nat.mul_comm x z, Nat.mul_comm y z, Nat.mul_comm (x % y) z] <;> apply mul_mod_mul_left
#align nat.mul_mod_mul_right Nat.mul_mod_mul_right

theorem cond_decide_mod_two (x : ℕ) [d : Decidable (x % 2 = 1)] :
    cond (@decide (x % 2 = 1) d) 1 0 = x % 2 :=
  by
  by_cases h : x % 2 = 1
  · simp! [*]
  · cases mod_two_eq_zero_or_one x <;> simp! [*, Nat.zero_ne_one] <;> contradiction
#align nat.cond_to_bool_mod_two Nat.cond_decide_mod_two

theorem sub_mul_mod (x k n : ℕ) (h₁ : n * k ≤ x) : (x - n * k) % n = x % n :=
  by
  induction' k with k
  · rw [Nat.mul_zero, Nat.sub_zero]
  · have h₂ : n * k ≤ x := by
      rw [mul_succ] at h₁
      apply Nat.le_trans _ h₁
      apply Nat.le_add_right _ n
    have h₄ : x - n * k ≥ n := by
      apply @Nat.le_of_add_le_add_right (n * k)
      rw [Nat.sub_add_cancel h₂]
      simp [mul_succ, Nat.add_comm] at h₁ ; simp [h₁]
    rw [mul_succ, ← Nat.sub_sub, ← mod_eq_sub_mod h₄, k_ih h₂]
#align nat.sub_mul_mod Nat.sub_mul_mod

/-! div -/


private theorem div_core_congr {x y f1 f2} (h1 : x ≤ f1) (h2 : x ≤ f2) :
    Nat.divCore y f1 x = Nat.divCore y f2 x :=
  by
  cases y; · cases f1 <;> cases f2 <;> rfl
  induction' f1 with f1 ih generalizing x f2; · cases h1; cases f2 <;> rfl
  cases x; · cases f1 <;> cases f2 <;> rfl
  cases f2; · cases h2
  refine' if_congr Iff.rfl _ rfl
  simp only [succ_sub_succ]
  refine' congr_arg (· + 1) _
  exact
    ih (le_trans (Nat.sub_le _ _) (le_of_succ_le_succ h1))
      (le_trans (Nat.sub_le _ _) (le_of_succ_le_succ h2))

theorem div_eq (x y : Nat) : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
  by
  cases x; · cases y <;> rfl
  cases y; · rfl
  refine' if_congr Iff.rfl (congr_arg (· + 1) _) rfl
  refine' div_core_congr _ _ <;> simp [Nat.sub_le]
#align nat.div_def Nat.div_eq

theorem mod_add_div (m k : ℕ) : m % k + k * (m / k) = m :=
  by
  apply Nat.strong_induction_on m
  clear m
  intro m IH
  cases' Decidable.em (0 < k ∧ k ≤ m) with h h'
  -- 0 < k ∧ k ≤ m
  · have h' : m - k < m := by
      apply Nat.sub_lt _ h.left
      apply lt_of_lt_of_le h.left h.right
    rw [div_def, mod_def, if_pos h, if_pos h]
    simp [Nat.left_distrib, IH _ h', Nat.add_comm, Nat.add_left_comm]
    rw [Nat.add_comm, ← Nat.add_sub_assoc h.right, Nat.mul_one, Nat.add_sub_cancel_left]
  -- ¬ (0 < k ∧ k ≤ m)
  · rw [div_def, mod_def, if_neg h', if_neg h', Nat.mul_zero, Nat.add_zero]
#align nat.mod_add_div Nat.mod_add_div

@[simp]
protected theorem div_one (n : ℕ) : n / 1 = n :=
  by
  have : n % 1 + 1 * (n / 1) = n := mod_add_div _ _
  rwa [mod_one, Nat.zero_add, Nat.one_mul] at this
#align nat.div_one Nat.div_one

@[simp]
protected theorem div_zero (n : ℕ) : n / 0 = 0 := by rw [div_def]; simp [lt_irrefl]
#align nat.div_zero Nat.div_zero

@[simp]
protected theorem zero_div (b : ℕ) : 0 / b = 0 :=
  Eq.trans (div_eq 0 b) <| if_neg (And.ndrec not_le_of_gt)
#align nat.zero_div Nat.zero_div

protected theorem div_le_of_le_mul {m n : ℕ} : ∀ {k}, m ≤ k * n → m / k ≤ n
  | 0, h => by simp [Nat.div_zero, n.zero_le]
  | succ k, h =>
    suffices succ k * (m / succ k) ≤ succ k * n from Nat.le_of_mul_le_mul_left this (zero_lt_succ _)
    calc
      succ k * (m / succ k) ≤ m % succ k + succ k * (m / succ k) := Nat.le_add_left _ _
      _ = m := by rw [mod_add_div]
      _ ≤ succ k * n := h
#align nat.div_le_of_le_mul Nat.div_le_of_le_mul

protected theorem div_le_self : ∀ m n : ℕ, m / n ≤ m
  | m, 0 => by simp [Nat.div_zero, m.zero_le]
  | m, succ n =>
    have : m ≤ succ n * m :=
      calc
        m = 1 * m := by rw [Nat.one_mul]
        _ ≤ succ n * m := m.mul_le_mul_right (succ_le_succ n.zero_le)
    Nat.div_le_of_le_mul this
#align nat.div_le_self Nat.div_le_self

theorem div_eq_sub_div {a b : Nat} (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = (a - b) / b + 1 :=
  by
  rw [div_def a, if_pos]
  constructor <;> assumption
#align nat.div_eq_sub_div Nat.div_eq_sub_divₓ

theorem div_eq_of_lt {a b : ℕ} (h₀ : a < b) : a / b = 0 :=
  by
  rw [div_def a, if_neg]
  intro h₁
  apply not_le_of_gt h₀ h₁.right
#align nat.div_eq_of_lt Nat.div_eq_of_lt

-- this is a Galois connection
--   f x ≤ y ↔ x ≤ g y
-- with
--   f x = x * k
--   g y = y / k
theorem le_div_iff_mul_le {x y k : ℕ} (Hk : 0 < k) : x ≤ y / k ↔ x * k ≤ y :=
  by
  -- Hk is needed because, despite div being made total, y / 0 := 0
  --     x * 0 ≤ y ↔ x ≤ y / 0
  --   ↔ 0 ≤ y ↔ x ≤ 0
  --   ↔ true ↔ x = 0
  --   ↔ x = 0
  revert x
  apply Nat.strong_induction_on y _
  clear y
  intro y IH x
  cases' lt_or_le y k with h h
  -- base case: y < k
  · rw [div_eq_of_lt h]
    cases' x with x
    · simp [Nat.zero_mul, y.zero_le]
    · simp [succ_mul, not_succ_le_zero, Nat.add_comm]
      apply lt_of_lt_of_le h
      apply Nat.le_add_right
  -- step: k ≤ y
  · rw [div_eq_sub_div Hk h]
    cases' x with x
    · simp [Nat.zero_mul, Nat.zero_le]
    ·
      rw [← add_one, Nat.add_le_add_iff_right, IH (y - k) (Nat.sub_lt_of_pos_le _ _ Hk h), add_one,
        succ_mul, Nat.le_sub_iff_right h]
#align nat.le_div_iff_mul_le Nat.le_div_iff_mul_le

theorem div_lt_iff_lt_mul {x y k : ℕ} (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  rw [← not_le, not_congr (le_div_iff_mul_le Hk), not_le]
#align nat.div_lt_iff_lt_mul Nat.div_lt_iff_lt_mul

theorem sub_mul_div (x n p : ℕ) (h₁ : n * p ≤ x) : (x - n * p) / n = x / n - p :=
  by
  cases' Nat.eq_zero_or_pos n with h₀ h₀
  · rw [h₀, Nat.div_zero, Nat.div_zero, Nat.zero_sub]
  · induction' p with p
    · rw [Nat.mul_zero, Nat.sub_zero, Nat.sub_zero]
    · have h₂ : n * p ≤ x := by
        trans
        · apply Nat.mul_le_mul_left; apply le_succ
        · apply h₁
      have h₃ : x - n * p ≥ n := by
        apply Nat.le_of_add_le_add_right
        rw [Nat.sub_add_cancel h₂, Nat.add_comm]
        rw [mul_succ] at h₁
        apply h₁
      rw [sub_succ, ← p_ih h₂]
      rw [@div_eq_sub_div (x - n * p) _ h₀ h₃]
      simp [add_one, pred_succ, mul_succ, Nat.sub_sub]
#align nat.sub_mul_div Nat.sub_mul_div

theorem div_mul_le_self : ∀ m n : ℕ, m / n * n ≤ m
  | m, 0 => by simp [m.zero_le, Nat.zero_mul]
  | m, succ n => (le_div_iff_mul_le <| Nat.succ_pos _).1 (le_refl _)
#align nat.div_mul_le_self Nat.div_mul_le_self

@[simp]
theorem add_div_right (x : ℕ) {z : ℕ} (H : 0 < z) : (x + z) / z = succ (x / z) := by
  rw [div_eq_sub_div H (Nat.le_add_left _ _), Nat.add_sub_cancel]
#align nat.add_div_right Nat.add_div_right

@[simp]
theorem add_div_left (x : ℕ) {z : ℕ} (H : 0 < z) : (z + x) / z = succ (x / z) := by
  rw [Nat.add_comm, add_div_right x H]
#align nat.add_div_left Nat.add_div_left

@[simp]
theorem mul_div_right (n : ℕ) {m : ℕ} (H : 0 < m) : m * n / m = n := by
  induction n <;> simp [*, mul_succ, Nat.mul_zero]
#align nat.mul_div_right Nat.mul_div_right

@[simp]
theorem mul_div_left (m : ℕ) {n : ℕ} (H : 0 < n) : m * n / n = m := by
  rw [Nat.mul_comm, mul_div_right _ H]
#align nat.mul_div_left Nat.mul_div_left

protected theorem div_self {n : ℕ} (H : 0 < n) : n / n = 1 :=
  by
  let t := add_div_right 0 H
  rwa [Nat.zero_add, Nat.zero_div] at t
#align nat.div_self Nat.div_self

theorem add_mul_div_left (x z : ℕ) {y : ℕ} (H : 0 < y) : (x + y * z) / y = x / y + z :=
  by
  induction' z with z ih
  · rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  · rw [mul_succ, ← Nat.add_assoc, add_div_right _ H, ih]; rfl
#align nat.add_mul_div_left Nat.add_mul_div_left

theorem add_mul_div_right (x y : ℕ) {z : ℕ} (H : 0 < z) : (x + y * z) / z = x / z + y := by
  rw [Nat.mul_comm, add_mul_div_left _ _ H]
#align nat.add_mul_div_right Nat.add_mul_div_right

protected theorem mul_div_cancel (m : ℕ) {n : ℕ} (H : 0 < n) : m * n / n = m :=
  by
  let t := add_mul_div_right 0 m H
  rwa [Nat.zero_add, Nat.zero_div, Nat.zero_add] at t
#align nat.mul_div_cancel Nat.mul_div_cancel

protected theorem mul_div_cancel_left (m : ℕ) {n : ℕ} (H : 0 < n) : n * m / n = m := by
  rw [Nat.mul_comm, Nat.mul_div_cancel _ H]
#align nat.mul_div_cancel_left Nat.mul_div_cancel_left

protected theorem div_eq_of_eq_mul_left {m n k : ℕ} (H1 : 0 < n) (H2 : m = k * n) : m / n = k := by
  rw [H2, Nat.mul_div_cancel _ H1]
#align nat.div_eq_of_eq_mul_left Nat.div_eq_of_eq_mul_leftₓ

protected theorem div_eq_of_eq_mul_right {m n k : ℕ} (H1 : 0 < n) (H2 : m = n * k) : m / n = k := by
  rw [H2, Nat.mul_div_cancel_left _ H1]
#align nat.div_eq_of_eq_mul_right Nat.div_eq_of_eq_mul_rightₓ

protected theorem div_eq_of_lt_le {m n k : ℕ} (lo : k * n ≤ m) (hi : m < succ k * n) : m / n = k :=
  have npos : 0 < n :=
    n.eq_zero_or_pos.resolve_left fun hn => by
      rw [hn, Nat.mul_zero] at hi lo  <;> exact absurd lo (not_le_of_gt hi)
  le_antisymm (le_of_lt_succ <| (Nat.div_lt_iff_lt_mul npos).2 hi)
    ((Nat.le_div_iff_mul_le npos).2 lo)
#align nat.div_eq_of_lt_le Nat.div_eq_of_lt_leₓ

theorem mul_sub_div (x n p : ℕ) (h₁ : x < n * p) : (n * p - succ x) / n = p - succ (x / n) :=
  by
  have npos : 0 < n :=
    n.eq_zero_or_pos.resolve_left fun n0 => by
      rw [n0, Nat.zero_mul] at h₁  <;> exact Nat.not_lt_zero _ h₁
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
    apply Nat.sub_le_sub_left
    exact (div_lt_iff_lt_mul npos).1 (lt_succ_self _)
  · change succ (pred (n * p - x)) ≤ succ (pred (p - x / n)) * n
    rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁), succ_pred_eq_of_pos (Nat.sub_pos_of_lt _)]
    · rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
      apply Nat.sub_le_sub_left; apply div_mul_le_self
    · apply (div_lt_iff_lt_mul npos).2; rwa [Nat.mul_comm]
#align nat.mul_sub_div Nat.mul_sub_div

protected theorem div_div_eq_div_mul (m n k : ℕ) : m / n / k = m / (n * k) :=
  by
  cases' k.eq_zero_or_pos with k0 kpos; · rw [k0, Nat.mul_zero, Nat.div_zero, Nat.div_zero]
  cases' n.eq_zero_or_pos with n0 npos; · rw [n0, Nat.zero_mul, Nat.div_zero, Nat.zero_div]
  apply le_antisymm
  · apply (le_div_iff_mul_le <| Nat.mul_pos npos kpos).2
    rw [Nat.mul_comm n k, ← Nat.mul_assoc]
    apply (le_div_iff_mul_le npos).1
    apply (le_div_iff_mul_le kpos).1
    rfl
  · apply (le_div_iff_mul_le kpos).2
    apply (le_div_iff_mul_le npos).2
    rw [Nat.mul_assoc, Nat.mul_comm n k]
    apply (le_div_iff_mul_le (Nat.mul_pos kpos npos)).1
    rfl
#align nat.div_div_eq_div_mul Nat.div_div_eq_div_mul

protected theorem mul_div_mul {m : ℕ} (n k : ℕ) (H : 0 < m) : m * n / (m * k) = n / k := by
  rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ H]
#align nat.mul_div_mul Nat.mul_div_mul

theorem div_lt_self {n m : Nat} : 0 < n → 1 < m → n / m < n :=
  by
  intro h₁ h₂
  have := Nat.mul_lt_mul h₂ (le_refl _) h₁
  rw [Nat.one_mul, Nat.mul_comm] at this
  exact (Nat.div_lt_iff_lt_mul <| lt_trans (by comp_val) h₂).2 this
#align nat.div_lt_self Nat.div_lt_self

/-! dvd -/


protected theorem dvd_mul_right (a b : ℕ) : a ∣ a * b :=
  ⟨b, rfl⟩
#align nat.dvd_mul_right Nat.dvd_mul_right

protected theorem dvd_trans {a b c : ℕ} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
  match h₁, h₂ with
  | ⟨d, (h₃ : b = a * d)⟩, ⟨e, (h₄ : c = b * e)⟩ =>
    ⟨d * e, show c = a * (d * e) by simp [h₃, h₄, Nat.mul_assoc]⟩
#align nat.dvd_trans Nat.dvd_trans

protected theorem eq_zero_of_zero_dvd {a : ℕ} (h : 0 ∣ a) : a = 0 :=
  Exists.elim h fun c => fun H' : a = 0 * c => Eq.trans H' (Nat.zero_mul c)
#align nat.eq_zero_of_zero_dvd Nat.eq_zero_of_zero_dvd

protected theorem dvd_add {a b c : ℕ} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  Exists.elim h₁ fun d hd => Exists.elim h₂ fun e he => ⟨d + e, by simp [Nat.left_distrib, hd, he]⟩
#align nat.dvd_add Nat.dvd_add

protected theorem dvd_add_iff_right {k m n : ℕ} (h : k ∣ m) : k ∣ n ↔ k ∣ m + n :=
  ⟨Nat.dvd_add h,
    Exists.elim h fun d hd =>
      match m, hd with
      | _, rfl => fun h₂ =>
        Exists.elim h₂ fun e he =>
          ⟨e - d, by rw [Nat.mul_sub_left_distrib, ← he, Nat.add_sub_cancel_left]⟩⟩
#align nat.dvd_add_iff_right Nat.dvd_add_iff_right

protected theorem dvd_add_iff_left {k m n : ℕ} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n := by
  rw [Nat.add_comm] <;> exact Nat.dvd_add_iff_right h
#align nat.dvd_add_iff_left Nat.dvd_add_iff_left

theorem dvd_sub {k m n : ℕ} (H : n ≤ m) (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n :=
  (Nat.dvd_add_iff_left h₂).2 <| by rw [Nat.sub_add_cancel H] <;> exact h₁
#align nat.dvd_sub Nat.dvd_sub

theorem dvd_mod_iff {k m n : ℕ} (h : k ∣ n) : k ∣ m % n ↔ k ∣ m :=
  by
  let t := @Nat.dvd_add_iff_left _ (m % n) _ (Nat.dvd_trans h (Nat.dvd_mul_right n (m / n)))
  rwa [mod_add_div] at t
#align nat.dvd_mod_iff Nat.dvd_mod_iff

theorem le_of_dvd {m n : ℕ} (h : 0 < n) : m ∣ n → m ≤ n := fun ⟨k, e⟩ =>
  by
  revert h; rw [e]; refine' k.cases_on _ _
  exact fun hn => absurd hn (lt_irrefl _)
  exact fun k _ => by
    let t := m.mul_le_mul_left (succ_pos k)
    rwa [Nat.mul_one] at t
#align nat.le_of_dvd Nat.le_of_dvd

theorem dvd_antisymm : ∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
  | m, 0, h₁, h₂ => Nat.eq_zero_of_zero_dvd h₂
  | 0, n, h₁, h₂ => (Nat.eq_zero_of_zero_dvd h₁).symm
  | succ m, succ n, h₁, h₂ => le_antisymm (le_of_dvd (succ_pos _) h₁) (le_of_dvd (succ_pos _) h₂)
#align nat.dvd_antisymm Nat.dvd_antisymm

theorem pos_of_dvd_of_pos {m n : ℕ} (H1 : m ∣ n) (H2 : 0 < n) : 0 < m :=
  Nat.pos_of_ne_zero fun m0 => by
    rw [m0] at H1  <;> rw [Nat.eq_zero_of_zero_dvd H1] at H2  <;> exact lt_irrefl _ H2
#align nat.pos_of_dvd_of_pos Nat.pos_of_dvd_of_pos

theorem eq_one_of_dvd_one {n : ℕ} (H : n ∣ 1) : n = 1 :=
  le_antisymm (le_of_dvd (by decide) H) (pos_of_dvd_of_pos H (by decide))
#align nat.eq_one_of_dvd_one Nat.eq_one_of_dvd_one

theorem dvd_of_mod_eq_zero {m n : ℕ} (H : n % m = 0) : m ∣ n :=
  ⟨n / m, by have t := (mod_add_div n m).symm; rwa [H, Nat.zero_add] at t ⟩
#align nat.dvd_of_mod_eq_zero Nat.dvd_of_mod_eq_zero

theorem mod_eq_zero_of_dvd {m n : ℕ} (H : m ∣ n) : n % m = 0 :=
  Exists.elim H fun z H1 => by rw [H1, mul_mod_right]
#align nat.mod_eq_zero_of_dvd Nat.mod_eq_zero_of_dvd

theorem dvd_iff_mod_eq_zero {m n : ℕ} : m ∣ n ↔ n % m = 0 :=
  ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩
#align nat.dvd_iff_mod_eq_zero Nat.dvd_iff_mod_eq_zero

instance decidableDvd : @DecidableRel ℕ (· ∣ ·) := fun m n =>
  decidable_of_decidable_of_iff (by infer_instance) dvd_iff_mod_eq_zero.symm
#align nat.decidable_dvd Nat.decidableDvd

protected theorem mul_div_cancel' {m n : ℕ} (H : n ∣ m) : n * (m / n) = m :=
  by
  let t := mod_add_div m n
  rwa [mod_eq_zero_of_dvd H, Nat.zero_add] at t
#align nat.mul_div_cancel' Nat.mul_div_cancel'ₓ

protected theorem div_mul_cancel {m n : ℕ} (H : n ∣ m) : m / n * n = m := by
  rw [Nat.mul_comm, Nat.mul_div_cancel' H]
#align nat.div_mul_cancel Nat.div_mul_cancelₓ

protected theorem mul_div_assoc (m : ℕ) {n k : ℕ} (H : k ∣ n) : m * n / k = m * (n / k) :=
  Or.elim k.eq_zero_or_pos (fun h => by rw [h, Nat.div_zero, Nat.div_zero, Nat.mul_zero]) fun h =>
    by
    have : m * n / k = m * (n / k * k) / k := by rw [Nat.div_mul_cancel H]
    rw [this, ← Nat.mul_assoc, Nat.mul_div_cancel _ h]
#align nat.mul_div_assoc Nat.mul_div_assocₓ

theorem dvd_of_mul_dvd_mul_left {m n k : ℕ} (kpos : 0 < k) (H : k * m ∣ k * n) : m ∣ n :=
  Exists.elim H fun l H1 => by
    rw [Nat.mul_assoc] at H1  <;> exact ⟨_, Nat.eq_of_mul_eq_mul_left kpos H1⟩
#align nat.dvd_of_mul_dvd_mul_left Nat.dvd_of_mul_dvd_mul_leftₓ

theorem dvd_of_mul_dvd_mul_right {m n k : ℕ} (kpos : 0 < k) (H : m * k ∣ n * k) : m ∣ n := by
  rw [Nat.mul_comm m k, Nat.mul_comm n k] at H  <;> exact dvd_of_mul_dvd_mul_left kpos H
#align nat.dvd_of_mul_dvd_mul_right Nat.dvd_of_mul_dvd_mul_rightₓ

/-! iterate -/


def iterate {α : Sort u} (op : α → α) : ℕ → α → α
  | 0, a => a
  | succ k, a => iterate k (op a)
#align nat.iterate Nat.iterate

notation f "^[" n "]" => iterate f n

/-! find -/


section Find

parameter {p : ℕ → Prop}

private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, ¬p k

parameter [DecidablePred p] (H : ∃ n, p n)

private def wf_lbp : WellFounded lbp :=
  ⟨let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc lbp k from fun a => this _ _ (Nat.le_add_left _ _)
    fun m =>
    Nat.recOn m
      (fun k kn =>
        ⟨_, fun y r =>
          match y, r with
          | _, ⟨rfl, a⟩ => absurd pn (a _ kn)⟩)
      fun m IH k kn =>
      ⟨_, fun y r =>
        match y, r with
        | _, ⟨rfl, a⟩ => IH _ (by rw [Nat.add_right_comm] <;> exact kn)⟩⟩

protected def findX : { n // p n ∧ ∀ m < n, ¬p m } :=
  @WellFounded.fix _ (fun k => (∀ n < k, ¬p n) → { n // p n ∧ ∀ m < n, ¬p m }) lbp wf_lbp
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : ∀ n ≤ m, ¬p n := fun n h =>
          Or.elim (Decidable.lt_or_eq_of_le h) (al n) fun e => by rw [e] <;> exact pm
        IH _ ⟨rfl, this⟩ fun n h => this n <| Nat.le_of_succ_le_succ h)
    0 fun n h => absurd h (Nat.not_lt_zero _)
#align nat.find_x Nat.findX

/-- If `p` is a (decidable) predicate on `ℕ` and `hp : ∃ (n : ℕ), p n` is a proof that
there exists some natural number satisfying `p`, then `nat.find hp` is the
smallest natural number satisfying `p`. Note that `nat.find` is protected,
meaning that you can't just write `find`, even if the `nat` namespace is open.

The API for `nat.find` is:

* `nat.find_spec` is the proof that `nat.find hp` satisfies `p`.
* `nat.find_min` is the proof that if `m < nat.find hp` then `m` does not satisfy `p`.
* `nat.find_min'` is the proof that if `m` does satisfy `p` then `nat.find hp ≤ m`.
-/
protected def find : ℕ :=
  Nat.findX.1
#align nat.find Nat.find

protected theorem find_spec : p Nat.find :=
  Nat.findX.2.left
#align nat.find_spec Nat.find_spec

protected theorem find_min : ∀ {m : ℕ}, m < Nat.find → ¬p m :=
  Nat.findX.2.right
#align nat.find_min Nat.find_min

protected theorem find_min' {m : ℕ} (h : p m) : Nat.find ≤ m :=
  le_of_not_lt fun l => find_min l h
#align nat.find_min' Nat.find_min'

end Find

end Nat
