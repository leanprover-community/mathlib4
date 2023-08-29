/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Std.Data.Nat.Lemmas
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Div
import Mathlib.Init.Algebra.Functions

#align_import init.data.nat.lemmas from "leanprover-community/lean"@"38b59111b2b4e6c572582b27e8937e92fc70ac02"

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
    -- ⊢ n * m + m = 0 → succ n = 0 ∨ m = 0
                   -- ⊢ succ n = 0 ∨ m = 0
    exact Or.inr (Nat.eq_zero_of_add_eq_zero_left h)
    -- 🎉 no goals
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

instance linearOrder : LinearOrder ℕ where
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
#align nat.linear_order Nat.linearOrder

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
  | 0, h, _h1 => absurd rfl h
  | _n + 1, _h, h1 => Nat.noConfusion h1 fun h2 => absurd h2 (succ_ne_zero _)
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
  | 0, 0, _h => rfl
  | 0, m + 1, h => by contradiction
                      -- 🎉 no goals
  | n + 1, 0, h => by contradiction
                      -- 🎉 no goals
  | n + 1, m + 1, h => by
    have : succ (succ (n + n)) = succ (succ (m + m)) := by
      unfold bit0 at h; simp [add_one, add_succ, succ_add] at h
      have aux : n + n = m + m := h; rw [aux]
    have : n + n = m + m := by repeat injection this with this
    -- ⊢ n + 1 = m + 1
    have : n = m := Nat.bit0_inj this
    -- ⊢ n + 1 = m + 1
    rw [this]
    -- 🎉 no goals
#align nat.bit0_inj Nat.bit0_inj

protected theorem bit1_inj : ∀ {n m : ℕ}, bit1 n = bit1 m → n = m := @fun n m h =>
  have : succ (bit0 n) = succ (bit0 m) := by simp [Nat.bit1_eq_succ_bit0] at h; rw [h]
                                             -- ⊢ succ (bit0 n) = succ (bit0 m)
                                                                                -- 🎉 no goals
  have : bit0 n = bit0 m := by injection this
                               -- 🎉 no goals
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
               -- 🎉 no goals
  | succ n, _h => by
    rw [Nat.bit1_succ_eq]
    -- ⊢ 1 < succ (succ (bit1 n))
    apply succ_lt_succ
    -- ⊢ 0 < bit1 n + 1
    apply zero_lt_succ
    -- 🎉 no goals
#align nat.one_lt_bit1 Nat.one_lt_bit1

protected theorem one_lt_bit0 : ∀ {n : Nat}, n ≠ 0 → 1 < bit0 n
  | 0, h => by contradiction
               -- 🎉 no goals
  | succ n, _h => by
    rw [Nat.bit0_succ_eq]
    -- ⊢ 1 < succ (succ (bit0 n))
    apply succ_lt_succ
    -- ⊢ 0 < bit0 n + 1
    apply zero_lt_succ
    -- 🎉 no goals
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
                                           -- ⊢ succ (n + n) ≤ succ (m + m)
                                                          -- 🎉 no goals
    show succ (n + n) < succ (succ m + m) from lt_succ_of_le this
#align nat.bit1_lt_bit0 Nat.bit1_lt_bit0

protected theorem one_le_bit1 (n : ℕ) : 1 ≤ bit1 n :=
  show 1 ≤ succ (bit0 n) from succ_le_succ (bit0 n).zero_le
#align nat.one_le_bit1 Nat.one_le_bit1

protected theorem one_le_bit0 : ∀ n : ℕ, n ≠ 0 → 1 ≤ bit0 n
  | 0, h => absurd rfl h
  | n + 1, _h =>
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
  -- ⊢ B
  · exact H1 h
    -- 🎉 no goals
  · exact H2 _ h
    -- 🎉 no goals
#align nat.discriminate Nat.discriminate

theorem one_eq_succ_zero : 1 = succ 0 :=
  rfl
#align nat.one_succ_zero Nat.one_eq_succ_zero

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

#align nat.sub_le_sub_iff_right Nat.sub_le_sub_iff_right

#align nat.sub_self_add Nat.sub_self_add

protected theorem le_sub_iff_right {x y k : ℕ} (h : k ≤ y) : x ≤ y - k ↔ x + k ≤ y := by
  rw [← Nat.add_sub_cancel x k, Nat.sub_le_sub_iff_right h, Nat.add_sub_cancel]
  -- 🎉 no goals
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
  -- 🎉 no goals
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

#align nat.zero_min Nat.zero_min

#align nat.min_zero Nat.min_zero

#align nat.min_succ_succ Nat.min_succ_succ

#align nat.sub_eq_sub_min Nat.sub_eq_sub_min

#align nat.sub_add_min_cancel Nat.sub_add_min_cancel

/-! induction principles -/


def twoStepInduction {P : ℕ → Sort u} (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (_IH1 : P n) (_IH2 : P (succ n)), P (succ (succ n))) : ∀ a : ℕ, P a
  | 0 => H1
  | 1 => H2
  | succ (succ _n) => H3 _ (twoStepInduction H1 H2 H3 _) (twoStepInduction H1 H2 H3 _)
#align nat.two_step_induction Nat.twoStepInduction

def subInduction {P : ℕ → ℕ → Sort u} (H1 : ∀ m, P 0 m) (H2 : ∀ n, P (succ n) 0)
    (H3 : ∀ n m, P n m → P (succ n) (succ m)) : ∀ n m : ℕ, P n m
  | 0, _m => H1 _
  | succ _n, 0 => H2 _
  | succ n, succ m => H3 _ _ (subInduction H1 H2 H3 n m)
#align nat.sub_induction Nat.subInduction

#align nat.strong_rec_on Nat.strongRecOn

-- porting note: added `elab_as_elim`
@[elab_as_elim]
protected theorem strong_induction_on {p : Nat → Prop} (n : Nat)
    (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
  Nat.strongRecOn n h
#align nat.strong_induction_on Nat.strong_induction_on

protected theorem case_strong_induction_on {p : Nat → Prop} (a : Nat) (hz : p 0)
    (hi : ∀ n, (∀ m, m ≤ n → p m) → p (succ n)) : p a :=
  Nat.strong_induction_on a fun n =>
    match n with
    | 0 => fun _ => hz
    | n + 1 => fun h₁ => hi n fun _m h₂ => h₁ _ (lt_succ_of_le h₂)
#align nat.case_strong_induction_on Nat.case_strong_induction_on

/-! mod -/

#align nat.mod_def Nat.mod_eq

#align nat.mod_zero Nat.mod_zero

#align nat.mod_eq_of_lt Nat.mod_eq_of_lt

#align nat.zero_mod Nat.zero_mod

#align nat.mod_eq_sub_mod Nat.mod_eq_sub_mod

#align nat.mod_lt Nat.mod_lt

#align nat.mod_self Nat.mod_self

#align nat.mod_one Nat.mod_one

#align nat.mod_two_eq_zero_or_one Nat.mod_two_eq_zero_or_one

#align nat.mod_le Nat.mod_le

#align nat.add_mod_right Nat.add_mod_right

#align nat.add_mod_left Nat.add_mod_left

#align nat.add_mul_mod_self_left Nat.add_mul_mod_self_left

#align nat.add_mul_mod_self_right Nat.add_mul_mod_self_right

#align nat.mul_mod_right Nat.mul_mod_right

#align nat.mul_mod_left Nat.mul_mod_left

#align nat.mul_mod_mul_left Nat.mul_mod_mul_left

#align nat.mul_mod_mul_right Nat.mul_mod_mul_right

theorem cond_decide_mod_two (x : ℕ) [d : Decidable (x % 2 = 1)] :
    cond (@decide (x % 2 = 1) d) 1 0 = x % 2 := by
  by_cases h : x % 2 = 1
  -- ⊢ (bif decide (x % 2 = 1) then 1 else 0) = x % 2
  · simp! [*]
    -- 🎉 no goals
  · cases mod_two_eq_zero_or_one x <;> simp! [*, Nat.zero_ne_one]
    -- ⊢ (bif decide (x % 2 = 1) then 1 else 0) = x % 2
                                       -- 🎉 no goals
                                       -- 🎉 no goals
#align nat.cond_to_bool_mod_two Nat.cond_decide_mod_two

#align nat.sub_mul_mod Nat.sub_mul_mod

/-! div -/

#align nat.div_def Nat.div_eq

#align nat.mod_add_div Nat.mod_add_div

#align nat.div_one Nat.div_one

#align nat.div_zero Nat.div_zero

#align nat.zero_div Nat.zero_div

#align nat.div_le_of_le_mul Nat.div_le_of_le_mul

#align nat.div_le_self Nat.div_le_self

#align nat.div_eq_sub_div Nat.div_eq_sub_divₓ

#align nat.div_eq_of_lt Nat.div_eq_of_lt

#align nat.le_div_iff_mul_le Nat.le_div_iff_mul_le

#align nat.div_lt_iff_lt_mul Nat.div_lt_iff_lt_mul

#align nat.sub_mul_div Nat.sub_mul_div

#align nat.div_mul_le_self Nat.div_mul_le_self

#align nat.add_div_right Nat.add_div_right

#align nat.add_div_left Nat.add_div_left

#align nat.mul_div_right Nat.mul_div_right

#align nat.mul_div_left Nat.mul_div_left

#align nat.div_self Nat.div_self

#align nat.add_mul_div_left Nat.add_mul_div_left

#align nat.add_mul_div_right Nat.add_mul_div_right

#align nat.mul_div_cancel Nat.mul_div_cancel

#align nat.mul_div_cancel_left Nat.mul_div_cancel_left

#align nat.div_eq_of_eq_mul_left Nat.div_eq_of_eq_mul_leftₓ

#align nat.div_eq_of_eq_mul_right Nat.div_eq_of_eq_mul_rightₓ

#align nat.div_eq_of_lt_le Nat.div_eq_of_lt_leₓ

#align nat.mul_sub_div Nat.mul_sub_div

#align nat.div_div_eq_div_mul Nat.div_div_eq_div_mul

protected theorem mul_div_mul {m : ℕ} (n k : ℕ) (H : 0 < m) : m * n / (m * k) = n / k := by
  rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ H]
  -- 🎉 no goals
#align nat.mul_div_mul Nat.mul_div_mul

#align nat.div_lt_self Nat.div_lt_self

/-! dvd -/


#align nat.dvd_mul_right Nat.dvd_mul_right

#align nat.dvd_trans Nat.dvd_trans

#align nat.eq_zero_of_zero_dvd Nat.eq_zero_of_zero_dvd

#align nat.dvd_add Nat.dvd_add

#align nat.dvd_add_iff_right Nat.dvd_add_iff_right

#align nat.dvd_add_iff_left Nat.dvd_add_iff_left

#align nat.dvd_sub Nat.dvd_sub

#align nat.dvd_mod_iff Nat.dvd_mod_iff

#align nat.le_of_dvd Nat.le_of_dvd

#align nat.dvd_antisymm Nat.dvd_antisymm

#align nat.pos_of_dvd_of_pos Nat.pos_of_dvd_of_pos

#align nat.eq_one_of_dvd_one Nat.eq_one_of_dvd_one

#align nat.dvd_of_mod_eq_zero Nat.dvd_of_mod_eq_zero

#align nat.mod_eq_zero_of_dvd Nat.mod_eq_zero_of_dvd

#align nat.dvd_iff_mod_eq_zero Nat.dvd_iff_mod_eq_zero

instance decidableDvd : @DecidableRel ℕ (· ∣ ·) := fun _m _n =>
  decidable_of_decidable_of_iff (Nat.dvd_iff_mod_eq_zero _ _).symm
#align nat.decidable_dvd Nat.decidableDvd

#align nat.mul_div_cancel' Nat.mul_div_cancel'ₓ

#align nat.div_mul_cancel Nat.div_mul_cancelₓ

#align nat.mul_div_assoc Nat.mul_div_assocₓ

#align nat.dvd_of_mul_dvd_mul_left Nat.dvd_of_mul_dvd_mul_leftₓ

#align nat.dvd_of_mul_dvd_mul_right Nat.dvd_of_mul_dvd_mul_rightₓ

/-! iterate -/


def iterate {α : Sort u} (op : α → α) : ℕ → α → α
  | 0, a => a
  | succ k, a => iterate op k (op a)
#align nat.iterate Nat.iterate

notation:max f "^["n"]" => iterate f n

/-! find -/


section Find

variable {p : ℕ → Prop}

private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, ¬p k

variable [DecidablePred p] (H : ∃ n, p n)

private def wf_lbp : WellFounded (@lbp p) :=
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
        | _, ⟨rfl, _a⟩ => IH _ (by rw [Nat.add_right_comm]; exact kn)⟩⟩
                                   -- ⊢ n ≤ k + m + 1
                                                            -- 🎉 no goals

protected def findX : { n // p n ∧ ∀ m < n, ¬p m } :=
  @WellFounded.fix _ (fun k => (∀ n < k, ¬p n) → { n // p n ∧ ∀ m < n, ¬p m }) lbp (wf_lbp H)
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : ∀ n ≤ m, ¬p n := fun n h =>
          Or.elim (Decidable.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
                                                                  -- ⊢ ¬p m
                                                                          -- 🎉 no goals
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
  (Nat.findX H).1
#align nat.find Nat.find

protected theorem find_spec : p (Nat.find H) :=
  (Nat.findX H).2.left
#align nat.find_spec Nat.find_spec

protected theorem find_min : ∀ {m : ℕ}, m < Nat.find H → ¬p m :=
  @(Nat.findX H).2.right
#align nat.find_min Nat.find_min

protected theorem find_min' {m : ℕ} (h : p m) : Nat.find H ≤ m :=
  le_of_not_lt fun l => Nat.find_min H l h
#align nat.find_min' Nat.find_min'

lemma to_digits_core_lens_eq_aux (b f : Nat) :
  ∀ (n : Nat) (l1 l2 : List Char), l1.length = l2.length →
    (Nat.toDigitsCore b f n l1).length = (Nat.toDigitsCore b f n l2).length := by
  induction f with (simp only [Nat.toDigitsCore, List.length]; intro n l1 l2 hlen)
  | zero => assumption
  | succ f ih =>
    by_cases hx : n / b = 0
    case pos => simp only [hx, if_true, List.length, congrArg (fun l ↦ l + 1) hlen]
    case neg =>
      simp only [hx, if_false]
      specialize ih (n / b) (Nat.digitChar (n % b) :: l1) (Nat.digitChar (n % b) :: l2)
      simp only [List.length, congrArg (fun l ↦ l + 1) hlen] at ih
      exact ih trivial

lemma to_digits_core_lens_eq (b f : Nat) : ∀ (n : Nat) (c : Char) (tl : List Char),
    (Nat.toDigitsCore b f n (c :: tl)).length = (Nat.toDigitsCore b f n tl).length + 1 := by
  induction f with (intro n c tl; simp only [Nat.toDigitsCore, List.length])
  | succ f ih =>
    by_cases hnb : (n / b) = 0
    case pos => simp only [hnb, if_true, List.length]
    case neg =>
      generalize hx: Nat.digitChar (n % b) = x
      simp only [hx, hnb, if_false] at ih
      simp only [hnb, if_false]
      specialize ih (n / b) c (x :: tl)
      rw [← ih]
      have lens_eq : (x :: (c :: tl)).length = (c :: x :: tl).length := by simp
      apply to_digits_core_lens_eq_aux
      exact lens_eq

lemma nat_repr_len_aux (n b e : Nat) (h_b_pos : 0 < b) :  n < b ^ e.succ → n / b < b ^ e := by
  simp only [Nat.pow_succ]
  -- ⊢ n < b ^ e * b → n / b < b ^ e
  exact (@Nat.div_lt_iff_lt_mul b n (b ^ e) h_b_pos).mpr
  -- 🎉 no goals

/-- The String representation produced by toDigitsCore has the proper length relative to
the number of digits in `n < e` for some base `b`. Since this works with any base greater
than one, it can be used for binary, decimal, and hex. -/
lemma to_digits_core_length (b : Nat) (h : 2 <= b) (f n e : Nat)
    (hlt : n < b ^ e) (h_e_pos: 0 < e) : (Nat.toDigitsCore b f n []).length <= e := by
  induction f generalizing n e hlt h_e_pos with
    simp only [Nat.toDigitsCore, List.length, Nat.zero_le]
  | succ f ih =>
    cases e with
    | zero => exact False.elim (Nat.lt_irrefl 0 h_e_pos)
    | succ e =>
      by_cases h_pred_pos : 0 < e
      case pos =>
        have _ : 0 < b := Nat.lt_trans (by decide) h
        specialize ih (n / b) e (nat_repr_len_aux n b e ‹0 < b› hlt) h_pred_pos
        by_cases hdiv_ten : n / b = 0
        case pos => simp only [hdiv_ten]; exact Nat.le.step h_pred_pos
        case neg =>
          simp only [hdiv_ten,
            to_digits_core_lens_eq b f (n / b) (Nat.digitChar $ n % b), if_false]
          exact Nat.succ_le_succ ih
      case neg =>
        have _ : e = 0 := Nat.eq_zero_of_nonpos e h_pred_pos
        rw [‹e = 0›]
        have _ : b ^ 1 = b := by simp only [pow_succ, pow_zero, Nat.one_mul]
        have _ : n < b := ‹b ^ 1 = b› ▸ (‹e = 0› ▸ hlt : n < b ^ Nat.succ 0)
        simp only [(@Nat.div_eq_of_lt n b ‹n < b› : n / b = 0), if_true, List.length]

/-- The core implementation of `Nat.repr` returns a String with length less than or equal to the
number of digits in the decimal number (represented by `e`). For example, the decimal string
representation of any number less than 1000 (10 ^ 3) has a length less than or equal to 3. -/
lemma repr_length (n e : Nat) : 0 < e → n < 10 ^ e → (Nat.repr n).length <= e := by
  cases n with
    (intro e0 he; simp only [Nat.repr, Nat.toDigits, String.length, List.asString])
  | zero => assumption
  | succ n =>
    by_cases hterm : n.succ / 10 = 0
    case pos => simp only [hterm, Nat.toDigitsCore]; assumption
    case neg => exact to_digits_core_length 10 (by decide) (Nat.succ n + 1) (Nat.succ n) e he e0

end Find

end Nat
