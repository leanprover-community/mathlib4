/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Sub.WithTop
public import Mathlib.Data.ENat.Defs
public import Mathlib.Order.Nat

import Mathlib.Algebra.Order.Group.Nat

/-!
# Definition and basic properties of extended natural numbers

In this file we define `ENat` (notation: `ℕ∞`) to be `WithTop ℕ` and prove some basic lemmas
about this type.

## Implementation details

There are two natural coercions from `ℕ` to `WithTop ℕ = ENat`: `WithTop.some` and `Nat.cast`. In
Lean 3, this difference was hidden in typeclass instances. Since these instances were definitionally
equal, we did not duplicate generic lemmas about `WithTop α` and `WithTop.some` coercion for `ENat`
and `Nat.cast` coercion. If you need to apply a lemma about `WithTop`, you may either rewrite back
and forth using `ENat.some_eq_natCast`, or restate the lemma for `ENat`.

## TODO

Unify `ENat.add_iSup`/`ENat.iSup_add` with `ENNReal.add_iSup`/`ENNReal.iSup_add`. The key property
of `ENat` and `ENNReal` we are using is that all `a` are either absorbing for addition (`a + b = a`
for all `b`), or that it's order-cancellable (`a + b ≤ a + c → b ≤ c` for all `b`, `c`), and
similarly for multiplication.
-/

@[expose] public section

open Function

assert_not_exists MonoidWithZero IsOrderedRing

deriving instance Nontrivial,
  Add, Sub, LE, LT, Bot, Zero, One, ZeroLEOneClass,
  Preorder, LinearOrder, OrderTop, OrderBot, WellFoundedLT
  for ENat

namespace ENat

variable {a b c d m n : ℕ∞}

/-- Lemmas about `WithTop` expect (and can output) `WithTop.some` but the normal form for coercion
`ℕ → ℕ∞` is `Nat.cast`. -/
@[simp] theorem some_eq_natCast : (WithTop.some : ℕ → ℕ∞) = Nat.cast := rfl

@[deprecated (since := "2026-07-17")] alias some_eq_coe := some_eq_natCast

theorem natCast_inj {a b : ℕ} : (a : ℕ∞) = b ↔ a = b := WithTop.coe_inj

@[deprecated (since := "2026-07-17")] alias coe_inj := natCast_inj

theorem natCast_zero : ((0 : ℕ) : ℕ∞) = 0 :=
  rfl

@[deprecated (since := "2026-07-17")] alias coe_zero := natCast_zero

theorem natCast_one : ((1 : ℕ) : ℕ∞) = 1 :=
  rfl

@[deprecated (since := "2026-07-17")] alias coe_one := natCast_one

theorem natCast_add (m n : ℕ) : ↑(m + n) = (m + n : ℕ∞) :=
  rfl

@[deprecated (since := "2026-07-17")] alias coe_add := natCast_add

@[simp, norm_cast]
theorem natCast_sub (m n : ℕ) : ↑(m - n) = (m - n : ℕ∞) :=
  rfl

@[deprecated (since := "2026-07-17")] alias coe_sub := natCast_sub

@[simp]
lemma natCast_lt_top (n : ℕ) : (n : ℕ∞) < ⊤ :=
  WithTop.coe_lt_top n

@[deprecated (since := "2026-07-17")] alias coe_lt_top := natCast_lt_top

/-- Convert a `ℕ∞` to a `ℕ` using a proof that it is not infinite. -/
def lift (x : ℕ∞) (h : x < ⊤) : ℕ := WithTop.untop x (WithTop.lt_top_iff_ne_top.mp h)

@[simp] theorem natCast_lift (x : ℕ∞) (h : x < ⊤) : (lift x h : ℕ∞) = x :=
  WithTop.coe_untop x (WithTop.lt_top_iff_ne_top.mp h)

@[deprecated (since := "2026-07-17")] alias coe_lift := natCast_lift

@[simp] theorem lift_natCast (n : ℕ) : lift (n : ℕ∞) (natCast_lt_top n) = n := rfl
@[simp] theorem lift_lt_iff {x : ℕ∞} {h} {n : ℕ} : lift x h < n ↔ x < n := WithTop.untop_lt_iff _
@[simp] theorem lift_le_iff {x : ℕ∞} {h} {n : ℕ} : lift x h ≤ n ↔ x ≤ n := WithTop.untop_le_iff _
@[simp] theorem lt_lift_iff {x : ℕ} {n : ℕ∞} {h} : x < lift n h ↔ x < n := WithTop.lt_untop_iff _
@[simp] theorem le_lift_iff {x : ℕ} {n : ℕ∞} {h} : x ≤ lift n h ↔ x ≤ n := WithTop.le_untop_iff _

@[deprecated (since := "2026-07-17")] alias lift_coe := lift_natCast

@[simp] theorem lift_zero : lift 0 (natCast_lt_top 0) = 0 := rfl
@[simp] theorem lift_one : lift 1 (natCast_lt_top 1) = 1 := rfl
@[simp] theorem lift_ofNat (n : ℕ) [n.AtLeastTwo] :
    lift ofNat(n) (natCast_lt_top n) = OfNat.ofNat n := rfl

@[simp] theorem add_lt_top {a b : ℕ∞} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := WithTop.add_lt_top
@[simp] theorem add_eq_top {a b : ℕ∞} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := WithTop.add_eq_top

instance canLift : CanLift ℕ∞ ℕ (↑) (· ≠ ⊤) := WithTop.canLift

instance : WellFoundedRelation ℕ∞ :=
  WellFoundedLT.toWellFoundedRelation

/-- Conversion of `ℕ∞` to `ℕ` sending `∞` to `0`. -/
def toNat : ℕ∞ → ℕ := WithTop.untopD 0

@[simp]
theorem toNat_natCast (n : ℕ) : toNat n = n :=
  rfl

@[deprecated (since := "2026-07-17")] alias toNat_coe := toNat_natCast

@[simp]
theorem toNat_zero : toNat 0 = 0 :=
  rfl

@[simp]
theorem toNat_one : toNat 1 = 1 :=
  rfl

@[simp]
theorem toNat_ofNat (n : ℕ) [n.AtLeastTwo] : toNat ofNat(n) = n :=
  rfl

@[simp]
theorem toNat_top : toNat ⊤ = 0 :=
  rfl

@[simp] theorem toNat_eq_zero : toNat n = 0 ↔ n = 0 ∨ n = ⊤ := WithTop.untopD_eq_self_iff

theorem toNat_pos (hn0 : n ≠ 0) (hxt : n ≠ ⊤) : 0 < n.toNat := by
  rw [Nat.pos_iff_ne_zero, ne_eq, ENat.toNat_eq_zero, not_or]
  exact ⟨hn0, hxt⟩

theorem lift_eq_toNat_of_lt_top {x : ℕ∞} (hx : x < ⊤) : x.lift hx = x.toNat := by
  rcases x with ⟨⟩ | x
  · contradiction
  · rfl

@[simp]
theorem recTopCoe_zero {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) : @recTopCoe C d f 0 = f 0 :=
  rfl

@[simp]
theorem recTopCoe_one {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) : @recTopCoe C d f 1 = f 1 :=
  rfl

@[simp]
theorem recTopCoe_ofNat {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) (x : ℕ) [x.AtLeastTwo] :
    @recTopCoe C d f ofNat(x) = f (OfNat.ofNat x) :=
  rfl

@[simp]
theorem top_ne_natCast (a : ℕ) : ⊤ ≠ (a : ℕ∞) :=
  nofun

@[deprecated (since := "2026-07-17")] alias top_ne_coe := top_ne_natCast

@[simp]
theorem top_ne_ofNat (a : ℕ) [a.AtLeastTwo] : ⊤ ≠ (ofNat(a) : ℕ∞) :=
  nofun

@[simp] lemma top_ne_zero : (⊤ : ℕ∞) ≠ 0 := nofun
@[simp] lemma top_ne_one : (⊤ : ℕ∞) ≠ 1 := nofun

@[simp]
theorem natCast_ne_top (a : ℕ) : (a : ℕ∞) ≠ ⊤ :=
  nofun

@[deprecated (since := "2026-07-17")] alias coe_ne_top := natCast_ne_top

@[simp]
theorem ofNat_ne_top (a : ℕ) [a.AtLeastTwo] : (ofNat(a) : ℕ∞) ≠ ⊤ :=
  nofun

@[simp] lemma zero_ne_top : 0 ≠ (⊤ : ℕ∞) := nofun
@[simp] lemma one_ne_top : 1 ≠ (⊤ : ℕ∞) := nofun

@[simp]
theorem top_sub_natCast (a : ℕ) : (⊤ : ℕ∞) - a = ⊤ :=
  rfl

@[deprecated (since := "2026-07-17")] alias top_sub_coe := top_sub_natCast

@[simp]
theorem top_sub_one : (⊤ : ℕ∞) - 1 = ⊤ :=
  rfl

@[simp]
theorem top_sub_ofNat (a : ℕ) [a.AtLeastTwo] : (⊤ : ℕ∞) - ofNat(a) = ⊤ :=
  rfl

@[simp]
theorem top_pos : (0 : ℕ∞) < ⊤ :=
  WithTop.top_pos

@[simp]
theorem one_lt_top : (1 : ℕ∞) < ⊤ :=
  WithTop.one_lt_top

@[simp] theorem sub_top (a : ℕ∞) : a - ⊤ = 0 := WithTop.sub_top

theorem natCast_toNat_le_self (n : ℕ∞) : ↑(toNat n) ≤ n :=
  ENat.recTopCoe le_top (fun _ => le_rfl) n

@[deprecated (since := "2026-07-17")] alias coe_toNat_le_self := natCast_toNat_le_self

theorem toNat_add {m n : ℕ∞} (hm : m ≠ ⊤) (hn : n ≠ ⊤) : toNat (m + n) = toNat m + toNat n := by
  lift m to ℕ using hm
  lift n to ℕ using hn
  rfl

theorem toNat_sub {n : ℕ∞} (hn : n ≠ ⊤) (m : ℕ∞) : toNat (m - n) = toNat m - toNat n := by
  lift n to ℕ using hn
  induction m
  · rw [top_sub_natCast, toNat_top, Nat.zero_sub]
  · rw [← natCast_sub, toNat_natCast, toNat_natCast, toNat_natCast]

theorem add_le_add_iff_left {m n k : ENat} (h : k ≠ ⊤) :
    k + n ≤ k + m ↔ n ≤ m :=
  WithTop.add_le_add_iff_left h

theorem add_le_add_iff_right {m n k : ENat} (h : k ≠ ⊤) :
    n + k ≤ m + k ↔ n ≤ m :=
  WithTop.add_le_add_iff_right h

theorem le_natCast_iff {n : ℕ∞} {k : ℕ} : n ≤ ↑k ↔ ∃ (n₀ : ℕ), n = n₀ ∧ n₀ ≤ k :=
  WithTop.le_coe_iff

@[deprecated (since := "2026-07-17")] alias le_coe_iff := le_natCast_iff

lemma add_lt_add_iff_right {k : ℕ∞} (h : k ≠ ⊤) : n + k < m + k ↔ n < m :=
  WithTop.add_lt_add_iff_right h

lemma add_lt_add_iff_left {k : ℕ∞} (h : k ≠ ⊤) : k + n < k + m ↔ n < m :=
  WithTop.add_lt_add_iff_left h

protected lemma add_lt_add (hac : a < c) (hbd : b < d) : a + b < c + d :=
  WithTop.add_lt_add hac hbd

protected theorem add_lt_add_of_le_of_lt : a ≠ ⊤ → a ≤ b → c < d → a + c < b + d :=
  WithTop.add_lt_add_of_le_of_lt

protected theorem add_lt_add_of_lt_of_le : c ≠ ⊤ → a < b → c ≤ d → a + c < b + d :=
  WithTop.add_lt_add_of_lt_of_le

-- Duplicate of `Nat.cast_lt`, but requires less imports.
@[norm_cast]
lemma natCast_lt_natCast {n m : ℕ} : (n : ℕ∞) < (m : ℕ∞) ↔ n < m := WithTop.coe_lt_coe

@[deprecated (since := "2026-07-17")] alias coe_lt_coe := natCast_lt_natCast

-- Duplicate of `Nat.cast_le`, but requires less imports.
@[norm_cast]
lemma natCast_le_natCast {n m : ℕ} : (n : ℕ∞) ≤ (m : ℕ∞) ↔ n ≤ m := WithTop.coe_le_coe

@[deprecated (since := "2026-07-17")] alias coe_le_coe := natCast_le_natCast

@[elab_as_elim]
theorem nat_induction {motive : ℕ∞ → Prop} (a : ℕ∞) (zero : motive 0)
    (succ : ∀ n : ℕ, motive n → motive n.succ)
    (top : (∀ n : ℕ, motive n) → motive ⊤) : motive a := by
  have A : ∀ n : ℕ, motive n := fun n => Nat.recOn n zero succ
  cases a
  · exact top A
  · exact A _

lemma ne_top_iff_exists : n ≠ ⊤ ↔ ∃ m : ℕ, ↑m = n := WithTop.ne_top_iff_exists

lemma eq_top_iff_forall_ne : n = ⊤ ↔ ∀ m : ℕ, ↑m ≠ n := WithTop.eq_top_iff_forall_ne
lemma forall_ne_top {p : ℕ∞ → Prop} : (∀ x, x ≠ ⊤ → p x) ↔ ∀ x : ℕ, p x := WithTop.forall_ne_top
lemma exists_ne_top {p : ℕ∞ → Prop} : (∃ x ≠ ⊤, p x) ↔ ∃ x : ℕ, p x := WithTop.exists_ne_top
lemma eq_top_iff_forall_gt : n = ⊤ ↔ ∀ m : ℕ, m < n := WithTop.eq_top_iff_forall_gt
lemma eq_top_iff_forall_ge : n = ⊤ ↔ ∀ m : ℕ, m ≤ n := WithTop.eq_top_iff_forall_ge

/-- Version of `WithTop.forall_natCast_le_iff_le` using `Nat.cast` rather than `WithTop.some`. -/
lemma forall_natCast_le_iff_le : (∀ a : ℕ, a ≤ m → a ≤ n) ↔ m ≤ n := WithTop.forall_coe_le_iff_le

/-- Version of `WithTop.eq_of_forall_natCast_le_iff` using `Nat.cast` rather than `WithTop.some`. -/
lemma eq_of_forall_natCast_le_iff (hm : ∀ a : ℕ, a ≤ m ↔ a ≤ n) : m = n :=
  WithTop.eq_of_forall_coe_le_iff hm

protected lemma exists_nat_gt (hn : n ≠ ⊤) : ∃ m : ℕ, n < m := by
  simp_rw [lt_iff_not_ge]
  exact not_forall.mp <| eq_top_iff_forall_ge.2.mt hn

@[simp] lemma sub_eq_top_iff : a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤ := WithTop.sub_eq_top_iff
lemma sub_ne_top_iff : a - b ≠ ⊤ ↔ a ≠ ⊤ ∨ b = ⊤ := WithTop.sub_ne_top_iff

lemma addLECancellable_of_ne_top : a ≠ ⊤ → AddLECancellable a := WithTop.addLECancellable_of_ne_top
lemma addLECancellable_of_lt_top : a < ⊤ → AddLECancellable a := WithTop.addLECancellable_of_lt_top
lemma addLECancellable_natCast (a : ℕ) : AddLECancellable (a : ℕ∞) := WithTop.addLECancellable_coe _

@[deprecated (since := "2026-07-17")] alias addLECancellable_coe := addLECancellable_natCast

variable {α : Type*}

/--
Specialization of `WithTop.map` to `ENat`.
-/
def map (f : ℕ → α) (k : ℕ∞) : WithTop α := WithTop.map f k

@[simp]
theorem map_top (f : ℕ → α) : map f ⊤ = ⊤ := rfl

@[simp]
theorem map_natCast (f : ℕ → α) (a : ℕ) : map f a = f a := rfl

@[deprecated (since := "2026-07-17")] alias map_coe := map_natCast

@[simp]
protected theorem map_zero (f : ℕ → α) : map f 0 = f 0 := rfl

@[simp]
protected theorem map_one (f : ℕ → α) : map f 1 = f 1 := rfl

@[simp]
theorem map_ofNat (f : ℕ → α) (n : ℕ) [n.AtLeastTwo] : map f ofNat(n) = f n := rfl

@[simp]
lemma map_eq_top_iff {f : ℕ → α} : map f n = ⊤ ↔ n = ⊤ := WithTop.map_eq_top_iff

@[simp]
theorem strictMono_map_iff {f : ℕ → α} [Preorder α] : StrictMono (ENat.map f) ↔ StrictMono f :=
  WithTop.strictMono_map_iff

@[simp]
theorem monotone_map_iff {f : ℕ → α} [Preorder α] : Monotone (ENat.map f) ↔ Monotone f :=
  WithTop.monotone_map_iff

@[simp]
protected theorem map_add {β F} [Add β] [FunLike F ℕ β] [AddHomClass F ℕ β]
    (f : F) (a b : ℕ∞) : (a + b).map f = a.map f + b.map f :=
  WithTop.map_add f a b

/-- A version of `ENat.map` for `OneHom`s. -/
-- @[to_additive (attr := simps -fullyApplied)
--   "A version of `ENat.map` for `ZeroHom`s"]
protected def _root_.OneHom.ENatMap {N : Type*} [One N] (f : OneHom ℕ N) :
    OneHom ℕ∞ (WithTop N) where
  toFun := ENat.map f
  map_one' := by simp

/-- A version of `ENat.map` for `ZeroHom`s. -/
protected def _root_.ZeroHom.ENatMap {N : Type*} [Zero N] (f : ZeroHom ℕ N) :
    ZeroHom ℕ∞ (WithTop N) where
  toFun := ENat.map f
  map_zero' := by simp

/-- A version of `WithTop.map` for `AddHom`s. -/
@[simps -fullyApplied]
protected def _root_.AddHom.ENatMap {N : Type*} [Add N] (f : AddHom ℕ N) :
    AddHom ℕ∞ (WithTop N) where
  toFun := ENat.map f
  map_add' := ENat.map_add f

end ENat

namespace ENat.WithBot

@[simp]
lemma coe_eq_natCast (n : ℕ) : (n : ℕ∞) = (n : WithBot ℕ∞) := rfl

lemma eq_top_iff_forall_ge {n : WithBot ℕ∞} : n = ⊤ ↔ ∀ m : ℕ, m ≤ n :=
  _root_.WithBot.eq_top_iff_forall_ge

end ENat.WithBot
