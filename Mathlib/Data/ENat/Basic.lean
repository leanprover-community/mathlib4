/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Nat.Units
public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.WithTop
public import Mathlib.Algebra.Order.Sub.WithTop
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.SuccPred

/-!
# Definition and basic properties of extended natural numbers

In this file we define `ENat` (notation: `ℕ∞`) to be `WithTop ℕ` and prove some basic lemmas
about this type.

## Implementation details

There are two natural coercions from `ℕ` to `WithTop ℕ = ENat`: `WithTop.some` and `Nat.cast`.  In
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

assert_not_exists Field

deriving instance Nontrivial,
  Add, Sub, LE, LT, Bot,
  Preorder, LinearOrder, OrderTop, OrderBot, WellFoundedLT, SuccOrder,
  AddMonoidWithOne, CommSemiring, LinearOrderedAddCommMonoidWithTop,
  ZeroLEOneClass, OrderedSub, CanonicallyOrderedAdd, IsOrderedRing,
  CharZero, NoZeroDivisors
  for ENat

namespace ENat

variable {a b c d m n : ℕ∞}

/-- Lemmas about `WithTop` expect (and can output) `WithTop.some` but the normal form for coercion
`ℕ → ℕ∞` is `Nat.cast`. -/
@[simp] theorem some_eq_natCast : (WithTop.some : ℕ → ℕ∞) = Nat.cast := rfl

@[deprecated (since := "2026-07-17")] alias some_eq_coe := some_eq_natCast

theorem natCast_inj {a b : ℕ} : (a : ℕ∞) = b ↔ a = b := WithTop.coe_inj

@[deprecated (since := "2026-07-17")] alias coe_inj := natCast_inj

@[simp] theorem succ_natCast (n : ℕ) : SuccOrder.succ (n : ℕ∞) = (n + 1 : ℕ) := WithTop.succ_coe

@[deprecated (since := "2026-07-17")] alias succ_coe := succ_natCast

@[simp] theorem succ_top : SuccOrder.succ (⊤ : ℕ∞) = ⊤ := rfl

instance : SuccAddOrder ℕ∞ where
  succ_eq_add_one x := by cases x <;> simp

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

@[simp] lemma natCast_mul (m n : ℕ) : ↑(m * n) = (m * n : ℕ∞) := rfl

@[deprecated (since := "2026-07-17")] alias coe_mul := natCast_mul

@[simp] theorem mul_top (hm : m ≠ 0) : m * ⊤ = ⊤ := WithTop.mul_top hm
@[simp] theorem top_mul (hm : m ≠ 0) : ⊤ * m = ⊤ := WithTop.top_mul hm

/-- A version of `mul_top` where the RHS is stated as an `ite` -/
theorem mul_top' : m * ⊤ = if m = 0 then 0 else ⊤ := WithTop.mul_top' m

/-- A version of `top_mul` where the RHS is stated as an `ite` -/
theorem top_mul' : ⊤ * m = if m = 0 then 0 else ⊤ := WithTop.top_mul' m

@[simp] lemma top_pow {n : ℕ} (hn : n ≠ 0) : (⊤ : ℕ∞) ^ n = ⊤ := WithTop.top_pow hn

@[simp] lemma pow_eq_top_iff {n : ℕ} : a ^ n = ⊤ ↔ a = ⊤ ∧ n ≠ 0 := WithTop.pow_eq_top_iff

lemma pow_ne_top_iff {n : ℕ} : a ^ n ≠ ⊤ ↔ a ≠ ⊤ ∨ n = 0 := WithTop.pow_ne_top_iff

@[simp] lemma pow_lt_top_iff {n : ℕ} : a ^ n < ⊤ ↔ a < ⊤ ∨ n = 0 := WithTop.pow_lt_top_iff

lemma eq_top_of_pow (n : ℕ) (ha : a ^ n = ⊤) : a = ⊤ := WithTop.eq_top_of_pow n ha

/-- Convert a `ℕ∞` to a `ℕ` using a proof that it is not infinite. -/
def lift (x : ℕ∞) (h : x < ⊤) : ℕ := WithTop.untop x (WithTop.lt_top_iff_ne_top.mp h)

@[simp] theorem natCast_lift (x : ℕ∞) (h : x < ⊤) : (lift x h : ℕ∞) = x :=
  WithTop.coe_untop x (WithTop.lt_top_iff_ne_top.mp h)

@[deprecated (since := "2026-07-17")] alias coe_lift := natCast_lift

@[simp] theorem lift_natCast (n : ℕ) : lift (n : ℕ∞) (WithTop.natCast_lt_top n) = n := rfl
@[simp] theorem lift_lt_iff {x : ℕ∞} {h} {n : ℕ} : lift x h < n ↔ x < n := WithTop.untop_lt_iff _
@[simp] theorem lift_le_iff {x : ℕ∞} {h} {n : ℕ} : lift x h ≤ n ↔ x ≤ n := WithTop.untop_le_iff _
@[simp] theorem lt_lift_iff {x : ℕ} {n : ℕ∞} {h} : x < lift n h ↔ x < n := WithTop.lt_untop_iff _
@[simp] theorem le_lift_iff {x : ℕ} {n : ℕ∞} {h} : x ≤ lift n h ↔ x ≤ n := WithTop.le_untop_iff _

@[deprecated (since := "2026-07-17")] alias lift_coe := lift_natCast

@[simp] theorem lift_zero : lift 0 (WithTop.natCast_lt_top 0) = 0 := rfl
@[simp] theorem lift_one : lift 1 (WithTop.natCast_lt_top 1) = 1 := rfl
@[simp] theorem lift_ofNat (n : ℕ) [n.AtLeastTwo] :
    lift ofNat(n) (WithTop.natCast_lt_top n) = OfNat.ofNat n := rfl

@[simp] theorem add_lt_top {a b : ℕ∞} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := WithTop.add_lt_top
@[simp] theorem add_eq_top {a b : ℕ∞} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := WithTop.add_eq_top

@[simp] theorem lift_add (a b : ℕ∞) (h : a + b < ⊤) :
    lift (a + b) h = lift a (add_lt_top.1 h).1 + lift b (add_lt_top.1 h).2 := by
  apply natCast_inj.1
  simp

instance canLift : CanLift ℕ∞ ℕ (↑) (· ≠ ⊤) := WithTop.canLift

instance : WellFoundedRelation ℕ∞ :=
  WellFoundedLT.toWellFoundedRelation

/-- Conversion of `ℕ∞` to `ℕ` sending `∞` to `0`. -/
def toNat : ℕ∞ → ℕ := WithTop.untopD 0

/-- Homomorphism from `ℕ∞` to `ℕ` sending `∞` to `0`. -/
def toNatHom : MonoidWithZeroHom ℕ∞ ℕ where
  toFun := toNat
  map_one' := rfl
  map_zero' := rfl
  map_mul' := WithTop.untopD_zero_mul

@[simp, norm_cast] lemma coe_toNatHom : toNatHom = toNat := rfl

lemma toNatHom_apply (n : ℕ) : toNatHom n = toNat n := rfl

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
  rw [pos_iff_ne_zero, ne_eq, ENat.toNat_eq_zero, not_or]
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

@[simp]
theorem natCast_toNat_eq_self : ENat.toNat n = n ↔ n ≠ ⊤ :=
  ENat.recTopCoe (by decide) (fun _ => by simp [toNat_natCast]) n

@[deprecated (since := "2026-07-17")] alias coe_toNat_eq_self := natCast_toNat_eq_self

alias ⟨_, natCast_toNat⟩ := natCast_toNat_eq_self

@[deprecated (since := "2026-07-17")] alias coe_toNat := natCast_toNat

@[simp] lemma toNat_eq_iff_eq_natCast (n : ℕ∞) (m : ℕ) [NeZero m] :
    n.toNat = m ↔ n = m := by
  cases n
  · simpa using NeZero.ne' m
  · simp

@[deprecated (since := "2026-07-17")] alias toNat_eq_iff_eq_coe := toNat_eq_iff_eq_natCast

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
  · rw [top_sub_natCast, toNat_top, zero_tsub]
  · rw [← natCast_sub, toNat_natCast, toNat_natCast, toNat_natCast]

@[simp] theorem toNat_mul (a b : ℕ∞) : (a * b).toNat = a.toNat * b.toNat := by
  cases a <;> cases b
  · simp
  · rename_i b; cases b <;> simp
  · rename_i a; cases a <;> simp
  · simp only [toNat_natCast]; rw [← natCast_mul, toNat_natCast]

theorem toNat_eq_iff {m : ℕ∞} {n : ℕ} (hn : n ≠ 0) : toNat m = n ↔ m = n := by
  induction m <;> simp [hn.symm]

lemma toNat_le_of_le_natCast {m : ℕ∞} {n : ℕ} (h : m ≤ n) : toNat m ≤ n := by
  lift m to ℕ using ne_top_of_le_ne_top (natCast_ne_top n) h
  simpa using h

@[deprecated (since := "2026-07-17")] alias toNat_le_of_le_coe := toNat_le_of_le_natCast

@[gcongr]
lemma toNat_le_toNat {m n : ℕ∞} (h : m ≤ n) (hn : n ≠ ⊤) : toNat m ≤ toNat n :=
  toNat_le_of_le_natCast <| h.trans_eq (natCast_toNat hn).symm

@[deprecated Order.succ_eq_add_one (since := "2026-05-25")]
theorem succ_def (m : ℕ∞) : Order.succ m = m + 1 :=
  Order.succ_eq_add_one m

theorem add_one_le_iff (hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
  Order.add_one_le_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hm)

theorem add_one_le_iff' (hn : n ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
  Order.add_one_le_iff_of_not_isMax' (not_isMax_iff_ne_top.mpr hn)

theorem natCast_add_one_le_iff {m : ℕ} {n : ℕ∞} : m + 1 ≤ n ↔ m < n :=
  add_one_le_iff <| natCast_ne_top m

@[deprecated (since := "2026-07-17")] alias coe_add_one_le_iff := natCast_add_one_le_iff

theorem add_one_le_natCast_iff {m : ℕ∞} {n : ℕ} : m + 1 ≤ n ↔ m < n :=
  add_one_le_iff' <| natCast_ne_top n

@[deprecated (since := "2026-07-17")] alias add_one_le_coe_iff := add_one_le_natCast_iff

@[deprecated Order.one_le_iff_ne_zero (since := "2026-05-25")]
protected theorem one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 :=
  Order.one_le_iff_ne_zero

@[deprecated Order.lt_one_iff (since := "2026-05-25")]
lemma lt_one_iff_eq_zero : n < 1 ↔ n = 0 :=
  Order.lt_one_iff

@[deprecated Order.le_one_iff (since := "2026-05-25")]
lemma le_one_iff_eq_zero_or_eq_one : n ≤ 1 ↔ n = 0 ∨ n = 1 :=
  Order.le_one_iff

theorem lt_add_one_iff (hn : n ≠ ⊤) : m < n + 1 ↔ m ≤ n :=
  Order.lt_add_one_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hn)

theorem lt_add_one_iff' (hm : m ≠ ⊤) : m < n + 1 ↔ m ≤ n :=
  Order.lt_add_one_iff_of_not_isMax' (not_isMax_iff_ne_top.mpr hm)

@[simp]
theorem lt_two_iff : n < 2 ↔ n ≤ 1 := by
  rw [← one_add_one_eq_two, lt_add_one_iff one_ne_top]

theorem add_le_add_iff_left {m n k : ENat} (h : k ≠ ⊤) :
    k + n ≤ k + m ↔ n ≤ m :=
  WithTop.add_le_add_iff_left h

theorem add_le_add_iff_right {m n k : ENat} (h : k ≠ ⊤) :
    n + k ≤ m + k ↔ n ≤ m :=
  WithTop.add_le_add_iff_right h

theorem lt_natCast_add_one_iff {m : ℕ∞} {n : ℕ} : m < n + 1 ↔ m ≤ n :=
  lt_add_one_iff (natCast_ne_top n)

@[deprecated (since := "2026-07-17")] alias lt_coe_add_one_iff := lt_natCast_add_one_iff

theorem natCast_lt_add_one_iff {m : ℕ} {n : ℕ∞} : m < n + 1 ↔ m ≤ n :=
  lt_add_one_iff' (natCast_ne_top m)

@[deprecated (since := "2026-07-17")] alias coe_lt_add_one_iff := natCast_lt_add_one_iff

theorem le_natCast_iff {n : ℕ∞} {k : ℕ} : n ≤ ↑k ↔ ∃ (n₀ : ℕ), n = n₀ ∧ n₀ ≤ k :=
  WithTop.le_coe_iff

@[deprecated (since := "2026-07-17")] alias le_coe_iff := le_natCast_iff

@[simp]
lemma natCast_lt_top (n : ℕ) : (n : ℕ∞) < ⊤ :=
  WithTop.natCast_lt_top n

@[deprecated (since := "2026-07-17")] alias coe_lt_top := natCast_lt_top

lemma natCast_lt_natCast {n m : ℕ} : (n : ℕ∞) < (m : ℕ∞) ↔ n < m := by simp

@[deprecated (since := "2026-07-17")] alias coe_lt_coe := natCast_lt_natCast

lemma natCast_le_natCast {n m : ℕ} : (n : ℕ∞) ≤ (m : ℕ∞) ↔ n ≤ m := by simp

@[deprecated (since := "2026-07-17")] alias coe_le_coe := natCast_le_natCast

@[elab_as_elim]
theorem nat_induction {motive : ℕ∞ → Prop} (a : ℕ∞) (zero : motive 0)
    (succ : ∀ n : ℕ, motive n → motive n.succ)
    (top : (∀ n : ℕ, motive n) → motive ⊤) : motive a := by
  have A : ∀ n : ℕ, motive n := fun n => Nat.recOn n zero succ
  cases a
  · exact top A
  · exact A _

@[deprecated add_pos_of_right (since := "2026-05-25")]
lemma add_one_pos : 0 < n + 1 :=
  add_pos_of_right zero_lt_one n

lemma natCast_lt_succ {n : ℕ} :
    (n : ℕ∞) < (n : ℕ∞) + 1 := by
  rw [← Nat.cast_one, ← Nat.cast_add, natCast_lt_natCast]
  exact lt_add_one n

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

protected lemma le_sub_of_add_le_left (ha : a ≠ ⊤) : a + b ≤ c → b ≤ c - a :=
  (addLECancellable_of_ne_top ha).le_tsub_of_add_le_left

protected lemma le_sub_of_add_le_right (hb : b ≠ ⊤) : a + b ≤ c → a ≤ c - b :=
  (addLECancellable_of_ne_top hb).le_tsub_of_add_le_right

protected lemma le_sub_one_of_lt (h : a < b) : a ≤ b - 1 := by
  cases b
  · simp
  · exact ENat.le_sub_of_add_le_right one_ne_top <| lt_natCast_add_one_iff.mp <|
      lt_tsub_iff_right.mp h

lemma lt_add_left {n k : ℕ∞} (h : n ≠ ⊤) (h' : 0 < k) : n < k + n := calc
    _ = 0 + n := (zero_add n).symm
    _ < k + n := (add_lt_add_iff_right h).mpr h'

protected lemma sub_sub_cancel (h : a ≠ ⊤) (h2 : b ≤ a) : a - (a - b) = b :=
  (addLECancellable_of_ne_top <| ne_top_of_le_ne_top h tsub_le_self).tsub_tsub_cancel_of_le h2

lemma add_left_injective_of_ne_top {n : ℕ∞} (hn : n ≠ ⊤) : Function.Injective (· + n) := by
  intro a b e
  exact le_antisymm
    ((WithTop.add_le_add_iff_right hn).mp e.le)
    ((WithTop.add_le_add_iff_right hn).mp e.ge)

lemma add_right_injective_of_ne_top {n : ℕ∞} (hn : n ≠ ⊤) : Function.Injective (n + ·) := by
  simp_rw [add_comm n _]
  exact add_left_injective_of_ne_top hn

lemma mul_right_strictMono (ha : a ≠ 0) (h_top : a ≠ ⊤) : StrictMono (a * ·) :=
  WithTop.mul_right_strictMono (pos_iff_ne_zero.2 ha) h_top

lemma mul_left_strictMono (ha : a ≠ 0) (h_top : a ≠ ⊤) : StrictMono (· * a) :=
  WithTop.mul_left_strictMono (pos_iff_ne_zero.2 ha) h_top

@[simp]
lemma mul_le_mul_left_iff {x y : ℕ∞} (ha : a ≠ 0) (h_top : a ≠ ⊤) : a * x ≤ a * y ↔ x ≤ y :=
  (ENat.mul_right_strictMono ha h_top).le_iff_le

@[simp]
lemma mul_le_mul_right_iff {x y : ℕ∞} (ha : a ≠ 0) (h_top : a ≠ ⊤) : x * a ≤ y * a ↔ x ≤ y :=
  (ENat.mul_left_strictMono ha h_top).le_iff_le

@[gcongr]
lemma mul_le_mul_of_le_right {x y : ℕ∞} (hxy : x ≤ y) (ha : a ≠ 0) (h_top : a ≠ ⊤) :
    x * a ≤ y * a := by
  simpa [ha, h_top]

lemma self_le_mul_right (a : ℕ∞) (hc : c ≠ 0) : a ≤ a * c := by
  obtain rfl | hne := eq_or_ne a ⊤
  · simp [top_mul hc]
  obtain rfl | h0 := eq_or_ne a 0
  · simp
  nth_rewrite 1 [← mul_one a, ENat.mul_le_mul_left_iff h0 hne, Order.one_le_iff_ne_zero]
  assumption

lemma self_le_mul_left (a : ℕ∞) (hc : c ≠ 0) : a ≤ c * a := by
  rw [mul_comm]
  exact ENat.self_le_mul_right a hc

instance : Unique ℕ∞ˣ where
  uniq x := by
    have := x.val_inv
    have x_top : x.val ≠ ⊤ := by
      intro h
      simp [h] at this
    have x_inv_top : x.inv ≠ ⊤ := by
      intro h
      simp only [h, ne_eq, x.ne_zero, not_false_eq_true, mul_top, top_ne_one] at this
    obtain ⟨y, x_y⟩ := ne_top_iff_exists.1 x_top
    obtain ⟨z, x_z⟩ := ne_top_iff_exists.1 x_inv_top
    replace x_y := x_y.symm
    rw [x_y, ← x_z, ← natCast_mul, ← natCast_one, natCast_inj, _root_.mul_eq_one] at this
    rwa [this.1, Nat.cast_one, Units.val_eq_one] at x_y

section withTop_enat

lemma add_one_natCast_le_withTop_of_lt {m : ℕ} {n : WithTop ℕ∞} (h : m < n) : (m + 1 : ℕ) ≤ n := by
  match n with
  | ⊤ => exact le_top
  | (⊤ : ℕ∞) => exact WithTop.coe_le_coe.2 (OrderTop.le_top _)
  | (n : ℕ) => simpa only [Nat.cast_le, ge_iff_le, Nat.cast_lt] using! h

@[simp] lemma coe_top_add_one : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = (⊤ : ℕ∞) := rfl

@[simp] lemma add_one_eq_coe_top_iff {n : WithTop ℕ∞} : n + 1 = (⊤ : ℕ∞) ↔ n = (⊤ : ℕ∞) := by
  match n with
  | ⊤ => exact Iff.rfl
  | (⊤ : ℕ∞) => simp
  | (n : ℕ) =>
    norm_cast
    simp only [natCast_ne_top]

@[simp] lemma natCast_ne_coe_top (n : ℕ) : (n : WithTop ℕ∞) ≠ (⊤ : ℕ∞) := nofun

lemma one_le_iff_ne_zero_withTop {n : WithTop ℕ∞} : 1 ≤ n ↔ n ≠ 0 :=
  ⟨fun h ↦ (zero_lt_one.trans_le h).ne',
    fun h ↦ add_one_natCast_le_withTop_of_lt (pos_iff_ne_zero.mpr h)⟩

lemma natCast_le_of_coe_top_le_withTop {N : WithTop ℕ∞} (hN : (⊤ : ℕ∞) ≤ N) (n : ℕ) : n ≤ N :=
  le_trans (mod_cast le_top) hN

lemma natCast_lt_of_coe_top_le_withTop {N : WithTop ℕ∞} (hN : (⊤ : ℕ∞) ≤ N) (n : ℕ) : n < N :=
  lt_of_lt_of_le (mod_cast lt_add_one n) (natCast_le_of_coe_top_le_withTop hN (n + 1))

end withTop_enat

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

section AddMonoidWithOne
variable [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α]

@[simp] lemma map_natCast_nonneg : 0 ≤ n.map (Nat.cast : ℕ → α) := by cases n <;> simp

variable [CharZero α]

lemma map_natCast_strictMono : StrictMono (map (Nat.cast : ℕ → α)) :=
  strictMono_map_iff.2 Nat.strictMono_cast

lemma map_natCast_injective : Injective (map (Nat.cast : ℕ → α)) := map_natCast_strictMono.injective

@[simp] lemma map_natCast_inj : m.map (Nat.cast : ℕ → α) = n.map Nat.cast ↔ m = n :=
  map_natCast_injective.eq_iff

@[simp] lemma map_natCast_eq_zero : n.map (Nat.cast : ℕ → α) = 0 ↔ n = 0 := by
  simp [← map_natCast_inj (α := α)]

end AddMonoidWithOne

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

/-- A version of `WithTop.map` for `AddMonoidHom`s. -/
@[simps -fullyApplied]
protected def _root_.AddMonoidHom.ENatMap {N : Type*} [AddZeroClass N]
    (f : ℕ →+ N) : ℕ∞ →+ WithTop N :=
  { ZeroHom.ENatMap f.toZeroHom, AddHom.ENatMap f.toAddHom with toFun := ENat.map f }

/-- A version of `ENat.map` for `MonoidWithZeroHom`s. -/
@[simps -fullyApplied]
protected def _root_.MonoidWithZeroHom.ENatMap {S : Type*} [MulZeroOneClass S] [DecidableEq S]
    [Nontrivial S] (f : ℕ →*₀ S)
    (hf : Function.Injective f) : ℕ∞ →*₀ WithTop S :=
  { f.toZeroHom.ENatMap, f.toMonoidHom.toOneHom.ENatMap with
    toFun := ENat.map f
    map_mul' := fun x y => by
      have : ∀ z, map f z = 0 ↔ z = 0 := fun z =>
        (WithTop.map_injective hf).eq_iff' f.toZeroHom.ENatMap.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      · simp
      rcases Decidable.eq_or_ne y 0 with (rfl | hy)
      · simp
      induction x with
      | top => simp [hy, this]
      | coe x =>
        induction y with
        | top =>
          have : (f x : WithTop S) ≠ 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
          simp [mul_top hx, WithTop.mul_top this]
        | coe y => simp [← Nat.cast_mul, -natCast_mul] }

/-- A version of `ENat.map` for `RingHom`s. -/
@[simps -fullyApplied]
protected def _root_.RingHom.ENatMap {S : Type*} [CommSemiring S] [PartialOrder S]
    [CanonicallyOrderedAdd S]
    [DecidableEq S] [Nontrivial S] (f : ℕ →+* S) (hf : Function.Injective f) : ℕ∞ →+* WithTop S :=
  { MonoidWithZeroHom.ENatMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.ENatMap with }

@[simp]
lemma map_natCast_mul {R : Type*} [NonAssocSemiring R] [DecidableEq R] [CharZero R] (a b : ℕ∞) :
    (map Nat.cast (a * b) : WithTop R) = map Nat.cast a * map Nat.cast b :=
  map_mul ((.ofClass (Nat.castRingHom R) : ℕ →*₀ R).ENatMap Nat.cast_injective) a b

end ENat

namespace ENat.WithBot

@[simp]
lemma coe_eq_natCast (n : ℕ) : (n : ℕ∞) = (n : WithBot ℕ∞) := rfl

lemma eq_top_iff_forall_ge {n : WithBot ℕ∞} : n = ⊤ ↔ ∀ m : ℕ, m ≤ n :=
  _root_.WithBot.eq_top_iff_forall_ge

lemma lt_add_one_iff {n : WithBot ℕ∞} {m : ℕ} : n < m + 1 ↔ n ≤ m := by
  rw [← WithBot.coe_one, ← ENat.natCast_one, WithBot.coe_natCast, ← Nat.cast_add,
    ← WithBot.coe_natCast]
  cases n
  · simp only [bot_le, WithBot.bot_lt_coe]
  · rw [WithBot.coe_lt_coe, Nat.cast_add, natCast_one, ENat.lt_add_one_iff (natCast_ne_top _),
      ← WithBot.coe_le_coe, WithBot.coe_natCast]

lemma add_one_le_iff {n : ℕ} {m : WithBot ℕ∞} : n + 1 ≤ m ↔ n < m := by
  rw [← WithBot.coe_one, ← natCast_one, WithBot.coe_natCast, ← Nat.cast_add, ← WithBot.coe_natCast]
  cases m
  · simp
  · rw [WithBot.coe_le_coe, natCast_add, natCast_one, ENat.add_one_le_iff (natCast_ne_top n),
      ← WithBot.coe_lt_coe, WithBot.coe_natCast]

lemma add_one_le_natCast_iff {n : WithBot ℕ∞} {m : ℕ} : n + 1 ≤ m ↔ n < m := by
  induction n with
  | bot => simp
  | coe n =>
    norm_cast
    simp [add_one_le_iff']

@[simp]
lemma add_one_le_zero_iff (n : WithBot ℕ∞) : n + 1 ≤ 0 ↔ n = ⊥ :=
  add_one_le_natCast_iff.trans (WithBot.lt_zero_iff_eq_bot n)

@[simp]
lemma add_natCast_cancel {a b : WithBot ℕ∞} {c : ℕ} : a + c = b + c ↔ a = b :=
  (IsAddRightRegular.all c).withTop.withBot.eq_iff

@[simp]
lemma add_one_cancel {a b : WithBot ℕ∞} : a + 1 = b + 1 ↔ a = b :=
  (IsAddRightRegular.all 1).withTop.withBot.eq_iff

lemma add_ofNat_cancel {a b : WithBot ℕ∞} {c : ℕ} [c.AtLeastTwo] :
    a + ofNat(c) = b + ofNat(c) ↔ a = b :=
  WithBot.add_natCast_cancel

@[simp]
lemma natCast_add_cancel {a b : WithBot ℕ∞} {c : ℕ} : c + a = c + b ↔ a = b :=
  (IsAddLeftRegular.all c).withTop.withBot.eq_iff

@[simp]
lemma one_add_cancel {a b : WithBot ℕ∞} : 1 + a = 1 + b ↔ a = b :=
  (IsAddLeftRegular.all 1).withTop.withBot.eq_iff

lemma ofNat_add_cancel {a b : WithBot ℕ∞} {c : ℕ} [c.AtLeastTwo] :
    ofNat(c) + a = ofNat(c) + b ↔ a = b :=
  WithBot.natCast_add_cancel

lemma add_le_add_natCast_right_iff {a b : WithBot ℕ∞} {c : ℕ} : a + c ≤ b + c ↔ a ≤ b :=
  (Contravariant.AddLECancellable (a := c)).withTop.withBot.add_le_add_iff_right

lemma add_le_add_one_right_iff {a b : WithBot ℕ∞} : a + 1 ≤ b + 1 ↔ a ≤ b :=
  WithBot.add_le_add_natCast_right_iff

lemma add_le_add_natCast_left_iff {a b : WithBot ℕ∞} {c : ℕ} : c + a ≤ c + b ↔ a ≤ b := by
  rw [add_comm _ a, add_comm _ b, WithBot.add_le_add_natCast_right_iff]

lemma add_le_add_one_left_iff {a b : WithBot ℕ∞} : 1 + a ≤ 1 + b ↔ a ≤ b :=
  WithBot.add_le_add_natCast_left_iff

theorem ne_bot_iff_zero_le {n : WithBot ℕ∞} : n ≠ ⊥ ↔ 0 ≤ n := by
  cases n <;> simp

end ENat.WithBot
