/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.enat.basic
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.SuccPred
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.Order.Sub.WithTop
import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Definition and basic properties of extended natural numbers

In this file we define `ENat` (notation: `ℕ∞`) to be `WithTop ℕ` and prove some basic lemmas
about this type.
-/

/-- Extended natural numbers `ℕ∞ = WithTop ℕ`. -/
def ENat : Type :=
  WithTop ℕ
deriving Zero, AddCommMonoidWithOne, CanonicallyOrderedCommSemiring, Nontrivial,
  LinearOrder, Bot, Top, CanonicallyLinearOrderedAddMonoid, Sub,
  LinearOrderedAddCommMonoidWithTop, WellFoundedRelation, Inhabited
  -- OrderBot, OrderTop, OrderedSub,  SuccOrder, WellFoundedLt, CharZero
#align enat ENat


/-- Extended natural numbers `ℕ∞ = WithTop ℕ`. -/
notation "ℕ∞" => ENat

namespace ENat

/-- The canonical map from `ℕ` to `ℕ∞` -/
@[coe] def ofNat (n : ℕ) : ℕ∞ := WithTop.some n

instance : Coe ℕ ℕ∞ := ⟨ofNat⟩

--Porting note: instances that derive failed to find
instance : OrderBot ℕ∞ := WithTop.orderBot
instance : OrderTop ℕ∞ := WithTop.orderTop
instance : OrderedSub ℕ∞ := by delta ENat; infer_instance
instance : SuccOrder ℕ∞ := by delta ENat; infer_instance
instance : WellFoundedLT ℕ∞ := by delta ENat; infer_instance
instance : CharZero ℕ∞ := by delta ENat; infer_instance
instance : IsWellOrder ℕ∞ (· < ·) where

variable {m n : ℕ∞}

--Porting note: `simp` and `norm_cast` can prove it
--@[simp, norm_cast]
theorem coe_zero : ((0 : ℕ) : ℕ∞) = 0 :=
  rfl
#align enat.coe_zero ENat.coe_zero

--Porting note: `simp` and `norm_cast` can prove it
--@[simp, norm_cast]
theorem coe_one : ((1 : ℕ) : ℕ∞) = 1 :=
  rfl
#align enat.coe_one ENat.coe_one

--Porting note: `simp` and `norm_cast` can prove it
--@[simp, norm_cast]
theorem coe_add (m n : ℕ) : ↑(m + n) = (m + n : ℕ∞) :=
  rfl
#align enat.coe_add ENat.coe_add

@[simp, norm_cast]
theorem coe_sub (m n : ℕ) : ↑(m - n) = (m - n : ℕ∞) :=
  rfl
#align enat.coe_sub ENat.coe_sub

--Porting note: `simp` and `norm_cast` can prove it
--@[simp, norm_cast]
theorem coe_mul (m n : ℕ) : ↑(m * n) = (m * n : ℕ∞) :=
  WithTop.coe_mul
#align enat.coe_mul ENat.coe_mul

instance canLift : CanLift ℕ∞ ℕ (↑) fun n => n ≠ ⊤ :=
  WithTop.canLift
#align enat.can_lift ENat.canLift

/-- Conversion of `ℕ∞` to `ℕ` sending `∞` to `0`. -/
def toNat : MonoidWithZeroHom ℕ∞ ℕ
    where
  toFun := WithTop.untop' 0
  map_one' := rfl
  map_zero' := rfl
  map_mul' := WithTop.untop'_zero_mul
#align enat.to_nat ENat.toNat

@[simp]
theorem toNat_coe (n : ℕ) : toNat n = n :=
  rfl
#align enat.to_nat_coe ENat.toNat_coe

@[simp]
theorem toNat_top : toNat ⊤ = 0 :=
  rfl
#align enat.to_nat_top ENat.toNat_top

--Porting note: new definition copied from `WithTop`
/-- Recursor for `ENat` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_elim]
def recTopCoe {C : ℕ∞ → Sort _} (h₁ : C ⊤) (h₂ : ∀ a : ℕ, C a) : ∀ n : ℕ∞, C n
| none => h₁
| Option.some a => h₂ a

--Porting note: new theorem copied from `WithTop`
@[simp]
theorem recTopCoe_top {C : ℕ∞ → Sort _} (d : C ⊤) (f : ∀ a : ℕ, C a) :
    @recTopCoe C d f ⊤ = d :=
  rfl

--Porting note: new theorem copied from `WithTop`
@[simp]
theorem recTopCoe_coe {C : ℕ∞ → Sort _} (d : C ⊤) (f : ∀ a : ℕ, C a) (x : ℕ) :
    @recTopCoe C d f ↑x = f x :=
  rfl

--Porting note: new theorem copied from `WithTop`
@[simp]
theorem top_ne_coe (a : ℕ) : ⊤ ≠ (a : ℕ∞) :=
  fun.

--Porting note: new theorem copied from `WithTop`
@[simp]
theorem coe_ne_top (a : ℕ) : (a : ℕ∞) ≠ ⊤ :=
  fun.

--Porting note: new theorem copied from `WithTop`
@[simp]
theorem top_sub_coe (a : ℕ) : (⊤ : ℕ∞) - a = ⊤ :=
  WithTop.top_sub_coe

--Porting note: new theorem copied from `WithTop`
theorem sub_top (a : ℕ∞) : a - ⊤ = 0 :=
  WithTop.sub_top

@[simp]
theorem coe_toNat_eq_self : ENat.toNat (n : ℕ∞) = n ↔ n ≠ ⊤ :=
  ENat.recTopCoe (by simp) (fun _ => by simp [toNat_coe]) n
#align enat.coe_to_nat_eq_self ENat.coe_toNat_eq_self

alias coe_toNat_eq_self ↔ _ coe_toNat
#align enat.coe_to_nat ENat.coe_toNat

theorem coe_toNat_le_self (n : ℕ∞) : ↑(toNat n) ≤ n :=
  ENat.recTopCoe le_top (fun _ => le_rfl) n
#align enat.coe_to_nat_le_self ENat.coe_toNat_le_self

theorem toNat_add {m n : ℕ∞} (hm : m ≠ ⊤) (hn : n ≠ ⊤) : toNat (m + n) = toNat m + toNat n := by
  lift m to ℕ using hm
  lift n to ℕ using hn
  rfl
#align enat.to_nat_add ENat.toNat_add

theorem toNat_sub {n : ℕ∞} (hn : n ≠ ⊤) (m : ℕ∞) : toNat (m - n) = toNat m - toNat n := by
  lift n to ℕ using hn
  induction m using ENat.recTopCoe
  · rw [top_sub_coe, toNat_top, zero_tsub]
  · rw [← coe_sub, toNat_coe, toNat_coe, toNat_coe]
#align enat.to_nat_sub ENat.toNat_sub

theorem toNat_eq_iff {m : ℕ∞} {n : ℕ} (hn : n ≠ 0) : toNat m = n ↔ m = n := by
  induction m using ENat.recTopCoe <;> simp [hn.symm]
#align enat.to_nat_eq_iff ENat.toNat_eq_iff

@[simp]
theorem succ_def (m : ℕ∞) : Order.succ m = m + 1 := by cases m <;> rfl
#align enat.succ_def ENat.succ_def

theorem add_one_le_of_lt (h : m < n) : m + 1 ≤ n :=
  m.succ_def ▸ Order.succ_le_of_lt h
#align enat.add_one_le_of_lt ENat.add_one_le_of_lt

theorem add_one_le_iff (hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
  m.succ_def ▸ (Order.succ_le_iff_of_not_isMax <| by rwa [isMax_iff_eq_top])
#align enat.add_one_le_iff ENat.add_one_le_iff

theorem one_le_iff_pos : 1 ≤ n ↔ 0 < n :=
  add_one_le_iff WithTop.zero_ne_top
#align enat.one_le_iff_pos ENat.one_le_iff_pos

theorem one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 :=
  one_le_iff_pos.trans pos_iff_ne_zero
#align enat.one_le_iff_ne_zero ENat.one_le_iff_ne_zero

theorem le_of_lt_add_one (h : m < n + 1) : m ≤ n :=
  Order.le_of_lt_succ <| n.succ_def.symm ▸ h
#align enat.le_of_lt_add_one ENat.le_of_lt_add_one

@[elab_as_elim]
theorem nat_induction {P : ℕ∞ → Prop} (a : ℕ∞) (h0 : P 0) (hsuc : ∀ n : ℕ, P n → P n.succ)
    (htop : (∀ n : ℕ, P n) → P ⊤) : P a := by
  have A : ∀ n : ℕ, P n := fun n => Nat.recOn n h0 hsuc
  cases a
  . exact htop A
  . exact A _
#align enat.nat_induction ENat.nat_induction

end ENat
