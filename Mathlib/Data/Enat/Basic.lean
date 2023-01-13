/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.enat.basic
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.SuccPred
import Mathbin.Algebra.CharZero.Lemmas
import Mathbin.Algebra.Order.Sub.WithTop
import Mathbin.Algebra.Order.Ring.WithTop

/-!
# Definition and basic properties of extended natural numbers

In this file we define `enat` (notation: `ℕ∞`) to be `with_top ℕ` and prove some basic lemmas
about this type.
-/


/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_coe_t[has_coe_t] exprℕ() -/
/-- Extended natural numbers `ℕ∞ = with_top ℕ`. -/
def Enat : Type :=
  WithTop ℕ deriving Zero, AddCommMonoidWithOne, CanonicallyOrderedCommSemiring, Nontrivial,
  LinearOrder, OrderBot, OrderTop, Bot, Top, CanonicallyLinearOrderedAddMonoid, Sub, OrderedSub,
  LinearOrderedAddCommMonoidWithTop, SuccOrder, WellFoundedLt, WellFoundedRelation, CharZero,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_coe_t[has_coe_t] exprℕ()»
#align enat Enat

-- mathport name: «exprℕ∞»
notation "ℕ∞" => Enat

namespace Enat

instance : Inhabited ℕ∞ :=
  ⟨0⟩

instance : IsWellOrder ℕ∞ (· < ·) where

variable {m n : ℕ∞}

@[simp, norm_cast]
theorem coe_zero : ((0 : ℕ) : ℕ∞) = 0 :=
  rfl
#align enat.coe_zero Enat.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : ℕ) : ℕ∞) = 1 :=
  rfl
#align enat.coe_one Enat.coe_one

@[simp, norm_cast]
theorem coe_add (m n : ℕ) : ↑(m + n) = (m + n : ℕ∞) :=
  rfl
#align enat.coe_add Enat.coe_add

@[simp, norm_cast]
theorem coe_sub (m n : ℕ) : ↑(m - n) = (m - n : ℕ∞) :=
  rfl
#align enat.coe_sub Enat.coe_sub

@[simp, norm_cast]
theorem coe_mul (m n : ℕ) : ↑(m * n) = (m * n : ℕ∞) :=
  WithTop.coe_mul
#align enat.coe_mul Enat.coe_mul

instance canLift : CanLift ℕ∞ ℕ coe fun n => n ≠ ⊤ :=
  WithTop.canLift
#align enat.can_lift Enat.canLift

/-- Conversion of `ℕ∞` to `ℕ` sending `∞` to `0`. -/
def toNat : MonoidWithZeroHom ℕ∞ ℕ
    where
  toFun := WithTop.untop' 0
  map_one' := rfl
  map_zero' := rfl
  map_mul' := WithTop.untop'_zero_mul
#align enat.to_nat Enat.toNat

@[simp]
theorem to_nat_coe (n : ℕ) : toNat n = n :=
  rfl
#align enat.to_nat_coe Enat.to_nat_coe

@[simp]
theorem to_nat_top : toNat ⊤ = 0 :=
  rfl
#align enat.to_nat_top Enat.to_nat_top

@[simp]
theorem coe_to_nat_eq_self : ↑n.toNat = n ↔ n ≠ ⊤ :=
  WithTop.recTopCoe (by simp) (by simp) n
#align enat.coe_to_nat_eq_self Enat.coe_to_nat_eq_self

alias coe_to_nat_eq_self ↔ _ coe_to_nat
#align enat.coe_to_nat Enat.coe_to_nat

theorem coe_to_nat_le_self (n : ℕ∞) : ↑(toNat n) ≤ n :=
  WithTop.recTopCoe le_top (fun k => le_rfl) n
#align enat.coe_to_nat_le_self Enat.coe_to_nat_le_self

theorem to_nat_add {m n : ℕ∞} (hm : m ≠ ⊤) (hn : n ≠ ⊤) : toNat (m + n) = toNat m + toNat n :=
  by
  lift m to ℕ using hm
  lift n to ℕ using hn
  rfl
#align enat.to_nat_add Enat.to_nat_add

theorem to_nat_sub {n : ℕ∞} (hn : n ≠ ⊤) (m : ℕ∞) : toNat (m - n) = toNat m - toNat n :=
  by
  lift n to ℕ using hn
  induction m using WithTop.recTopCoe
  · rw [WithTop.top_sub_coe, to_nat_top, zero_tsub]
  · rw [← coe_sub, to_nat_coe, to_nat_coe, to_nat_coe]
#align enat.to_nat_sub Enat.to_nat_sub

theorem to_nat_eq_iff {m : ℕ∞} {n : ℕ} (hn : n ≠ 0) : m.toNat = n ↔ m = n := by
  induction m using WithTop.recTopCoe <;> simp [hn.symm]
#align enat.to_nat_eq_iff Enat.to_nat_eq_iff

@[simp]
theorem succ_def (m : ℕ∞) : Order.succ m = m + 1 := by cases m <;> rfl
#align enat.succ_def Enat.succ_def

theorem add_one_le_of_lt (h : m < n) : m + 1 ≤ n :=
  m.succ_def ▸ Order.succ_le_of_lt h
#align enat.add_one_le_of_lt Enat.add_one_le_of_lt

theorem add_one_le_iff (hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
  m.succ_def ▸ (Order.succ_le_iff_of_not_isMax <| by rwa [isMax_iff_eq_top])
#align enat.add_one_le_iff Enat.add_one_le_iff

theorem one_le_iff_pos : 1 ≤ n ↔ 0 < n :=
  add_one_le_iff WithTop.zero_ne_top
#align enat.one_le_iff_pos Enat.one_le_iff_pos

theorem one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 :=
  one_le_iff_pos.trans pos_iff_ne_zero
#align enat.one_le_iff_ne_zero Enat.one_le_iff_ne_zero

theorem le_of_lt_add_one (h : m < n + 1) : m ≤ n :=
  Order.le_of_lt_succ <| n.succ_def.symm ▸ h
#align enat.le_of_lt_add_one Enat.le_of_lt_add_one

@[elab_as_elim]
theorem nat_induction {P : ℕ∞ → Prop} (a : ℕ∞) (h0 : P 0) (hsuc : ∀ n : ℕ, P n → P n.succ)
    (htop : (∀ n : ℕ, P n) → P ⊤) : P a :=
  by
  have A : ∀ n : ℕ, P n := fun n => Nat.recOn n h0 hsuc
  cases a
  exacts[htop A, A a]
#align enat.nat_induction Enat.nat_induction

end Enat

