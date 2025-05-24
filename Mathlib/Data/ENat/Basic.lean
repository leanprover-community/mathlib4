/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Order.Sub.WithTop
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.SuccPred

/-!
# Definition and basic properties of extended natural numbers

In this file we define `ENat` (notation: `ℕ∞`) to be `WithTop ℕ` and prove some basic lemmas
about this type.

## Implementation details

There are two natural coercions from `ℕ` to `WithTop ℕ = ENat`: `WithTop.some` and `Nat.cast`.  In
Lean 3, this difference was hidden in typeclass instances. Since these instances were definitionally
equal, we did not duplicate generic lemmas about `WithTop α` and `WithTop.some` coercion for `ENat`
and `Nat.cast` coercion. If you need to apply a lemma about `WithTop`, you may either rewrite back
and forth using `ENat.some_eq_coe`, or restate the lemma for `ENat`.

## TODO

Unify `ENat.add_iSup`/`ENat.iSup_add` with `ENNReal.add_iSup`/`ENNReal.iSup_add`. The key property
of `ENat` and `ENNReal` we are using is that all `a` are either absorbing for addition (`a + b = a`
for all `b`), or that it's order-cancellable (`a + b ≤ a + c → b ≤ c` for all `b`, `c`), and
similarly for multiplication.
-/

open Function

assert_not_exists Field

deriving instance Zero, CommSemiring, Nontrivial,
  LinearOrder, Bot, Sub,
  LinearOrderedAddCommMonoidWithTop, WellFoundedRelation
  for ENat
-- The `CanonicallyOrderedAdd, OrderBot, OrderTop, OrderedSub, SuccOrder, WellFoundedLT, CharZero`
-- instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

-- In `Mathlib.Data.Nat.PartENat` proofs timed out when we included `deriving AddCommMonoidWithOne`,
-- and it seems to work without.

namespace ENat

instance : IsOrderedRing ℕ∞ := WithTop.instIsOrderedRing
instance : CanonicallyOrderedAdd ℕ∞ := WithTop.canonicallyOrderedAdd
instance : OrderBot ℕ∞ := WithTop.orderBot
instance : OrderTop ℕ∞ := WithTop.orderTop
instance : OrderedSub ℕ∞ := inferInstanceAs (OrderedSub (WithTop ℕ))
instance : SuccOrder ℕ∞ := inferInstanceAs (SuccOrder (WithTop ℕ))
instance : WellFoundedLT ℕ∞ := inferInstanceAs (WellFoundedLT (WithTop ℕ))
instance : CharZero ℕ∞ := inferInstanceAs (CharZero (WithTop ℕ))

variable {a b c m n : ℕ∞}

/-- Lemmas about `WithTop` expect (and can output) `WithTop.some` but the normal form for coercion
`ℕ → ℕ∞` is `Nat.cast`. -/
@[simp] theorem some_eq_coe : (WithTop.some : ℕ → ℕ∞) = Nat.cast := rfl

theorem coe_inj {a b : ℕ} : (a : ℕ∞) = b ↔ a = b := WithTop.coe_inj

instance : SuccAddOrder ℕ∞ where
  succ_eq_add_one x := by cases x <;> simp [SuccOrder.succ]

theorem coe_zero : ((0 : ℕ) : ℕ∞) = 0 :=
  rfl

theorem coe_one : ((1 : ℕ) : ℕ∞) = 1 :=
  rfl

theorem coe_add (m n : ℕ) : ↑(m + n) = (m + n : ℕ∞) :=
  rfl

@[simp, norm_cast]
theorem coe_sub (m n : ℕ) : ↑(m - n) = (m - n : ℕ∞) :=
  rfl

@[simp] lemma coe_mul (m n : ℕ) : ↑(m * n) = (m * n : ℕ∞) := rfl

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

@[simp]
theorem add_eq_top {x y : ℕ∞} : x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤ :=
  WithTop.add_eq_top

theorem add_ne_top {x y : ℕ∞} : x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ :=
  by simp

/-- Convert a `ℕ∞` to a `ℕ` using a proof that it is not infinite. -/
def lift (x : ℕ∞) (h : x < ⊤) : ℕ := WithTop.untop x (WithTop.lt_top_iff_ne_top.mp h)

@[simp] theorem coe_lift (x : ℕ∞) (h : x < ⊤) : (lift x h : ℕ∞) = x :=
  WithTop.coe_untop x (WithTop.lt_top_iff_ne_top.mp h)
@[simp] theorem lift_coe (n : ℕ) : lift (n : ℕ∞) (WithTop.coe_lt_top n) = n := rfl
@[simp] theorem lift_lt_iff {x : ℕ∞} {h} {n : ℕ} : lift x h < n ↔ x < n := WithTop.untop_lt_iff _
@[simp] theorem lift_le_iff {x : ℕ∞} {h} {n : ℕ} : lift x h ≤ n ↔ x ≤ n := WithTop.untop_le_iff _
@[simp] theorem lt_lift_iff {x : ℕ} {n : ℕ∞} {h} : x < lift n h ↔ x < n := WithTop.lt_untop_iff _
@[simp] theorem le_lift_iff {x : ℕ} {n : ℕ∞} {h} : x ≤ lift n h ↔ x ≤ n := WithTop.le_untop_iff _

@[simp] theorem lift_zero : lift 0 (WithTop.coe_lt_top 0) = 0 := rfl
@[simp] theorem lift_one : lift 1 (WithTop.coe_lt_top 1) = 1 := rfl
@[simp] theorem lift_ofNat (n : ℕ) [n.AtLeastTwo] :
    lift ofNat(n) (WithTop.coe_lt_top n) = OfNat.ofNat n := rfl

@[simp] theorem add_lt_top {a b : ℕ∞} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := WithTop.add_lt_top

@[simp] theorem lift_add (a b : ℕ∞) (h : a + b < ⊤) :
    lift (a + b) h = lift a (add_lt_top.1 h).1 + lift b (add_lt_top.1 h).2 := by
  apply coe_inj.1
  simp

instance canLift : CanLift ℕ∞ ℕ (↑) (· ≠ ⊤) := WithTop.canLift

instance : WellFoundedRelation ℕ∞ where
  rel := (· < ·)
  wf := IsWellFounded.wf

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
theorem toNat_coe (n : ℕ) : toNat n = n :=
  rfl

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
theorem top_ne_coe (a : ℕ) : ⊤ ≠ (a : ℕ∞) :=
  nofun

@[simp]
theorem top_ne_ofNat (a : ℕ) [a.AtLeastTwo] : ⊤ ≠ (ofNat(a) : ℕ∞) :=
  nofun

@[simp] lemma top_ne_zero : (⊤ : ℕ∞) ≠ 0 := nofun
@[simp] lemma top_ne_one : (⊤ : ℕ∞) ≠ 1 := nofun

@[simp]
theorem coe_ne_top (a : ℕ) : (a : ℕ∞) ≠ ⊤ :=
  nofun

@[simp]
theorem ofNat_ne_top (a : ℕ) [a.AtLeastTwo] : (ofNat(a) : ℕ∞) ≠ ⊤ :=
  nofun

@[simp] lemma zero_ne_top : 0 ≠ (⊤ : ℕ∞) := nofun
@[simp] lemma one_ne_top : 1 ≠ (⊤ : ℕ∞) := nofun

@[simp]
theorem top_sub_coe (a : ℕ) : (⊤ : ℕ∞) - a = ⊤ :=
  WithTop.top_sub_coe

@[simp]
theorem top_sub_one : (⊤ : ℕ∞) - 1 = ⊤ :=
  top_sub_coe 1

@[simp]
theorem top_sub_ofNat (a : ℕ) [a.AtLeastTwo] : (⊤ : ℕ∞) - ofNat(a) = ⊤ :=
  top_sub_coe a

@[simp]
theorem top_pos : (0 : ℕ∞) < ⊤ :=
  WithTop.top_pos

@[deprecated ENat.top_pos (since := "2024-10-22")]
alias zero_lt_top := top_pos

@[simp] theorem sub_top (a : ℕ∞) : a - ⊤ = 0 := WithTop.sub_top

@[simp]
theorem coe_toNat_eq_self : ENat.toNat n = n ↔ n ≠ ⊤ :=
  ENat.recTopCoe (by decide) (fun _ => by simp [toNat_coe]) n

alias ⟨_, coe_toNat⟩ := coe_toNat_eq_self

@[simp] lemma toNat_eq_iff_eq_coe (n : ℕ∞) (m : ℕ) [NeZero m] :
    n.toNat = m ↔ n = m := by
  cases n
  · simpa using NeZero.ne' m
  · simp

theorem coe_toNat_le_self (n : ℕ∞) : ↑(toNat n) ≤ n :=
  ENat.recTopCoe le_top (fun _ => le_rfl) n

theorem toNat_add {m n : ℕ∞} (hm : m ≠ ⊤) (hn : n ≠ ⊤) : toNat (m + n) = toNat m + toNat n := by
  lift m to ℕ using hm
  lift n to ℕ using hn
  rfl

theorem toNat_sub {n : ℕ∞} (hn : n ≠ ⊤) (m : ℕ∞) : toNat (m - n) = toNat m - toNat n := by
  lift n to ℕ using hn
  induction m
  · rw [top_sub_coe, toNat_top, zero_tsub]
  · rw [← coe_sub, toNat_coe, toNat_coe, toNat_coe]

@[simp] theorem toNat_mul (a b : ℕ∞) : (a * b).toNat = a.toNat * b.toNat := by
  cases a <;> cases b <;> simp
  · rename_i b; cases b <;> simp
  · rename_i a; cases a <;> simp
  · rw [← coe_mul, toNat_coe]

theorem toNat_eq_iff {m : ℕ∞} {n : ℕ} (hn : n ≠ 0) : toNat m = n ↔ m = n := by
  induction m <;> simp [hn.symm]

lemma toNat_le_of_le_coe {m : ℕ∞} {n : ℕ} (h : m ≤ n) : toNat m ≤ n := by
  lift m to ℕ using ne_top_of_le_ne_top (coe_ne_top n) h
  simpa using h

@[gcongr]
lemma toNat_le_toNat {m n : ℕ∞} (h : m ≤ n) (hn : n ≠ ⊤) : toNat m ≤ toNat n :=
  toNat_le_of_le_coe <| h.trans_eq (coe_toNat hn).symm

@[simp]
theorem succ_def (m : ℕ∞) : Order.succ m = m + 1 :=
  Order.succ_eq_add_one m

theorem add_one_le_iff (hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
  Order.add_one_le_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hm)

theorem one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 :=
  Order.one_le_iff_pos.trans pos_iff_ne_zero

lemma lt_one_iff_eq_zero : n < 1 ↔ n = 0 :=
  not_le.symm.trans one_le_iff_ne_zero.not_left

theorem lt_add_one_iff (hm : n ≠ ⊤) : m < n + 1 ↔ m ≤ n :=
  Order.lt_add_one_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hm)

theorem lt_coe_add_one_iff {m : ℕ∞} {n : ℕ} : m < n + 1 ↔ m ≤ n :=
  lt_add_one_iff (coe_ne_top n)

theorem le_coe_iff {n : ℕ∞} {k : ℕ} : n ≤ ↑k ↔ ∃ (n₀ : ℕ), n = n₀ ∧ n₀ ≤ k :=
  WithTop.le_coe_iff

@[simp]
lemma not_lt_zero (n : ℕ∞) : ¬ n < 0 := by
  cases n <;> simp

@[simp]
lemma coe_lt_top (n : ℕ) : (n : ℕ∞) < ⊤ :=
  WithTop.coe_lt_top n

lemma coe_lt_coe {n m : ℕ} : (n : ℕ∞) < (m : ℕ∞) ↔ n < m := by simp

lemma coe_le_coe {n m : ℕ} : (n : ℕ∞) ≤ (m : ℕ∞) ↔ n ≤ m := by simp

@[elab_as_elim]
theorem nat_induction {P : ℕ∞ → Prop} (a : ℕ∞) (h0 : P 0) (hsuc : ∀ n : ℕ, P n → P n.succ)
    (htop : (∀ n : ℕ, P n) → P ⊤) : P a := by
  have A : ∀ n : ℕ, P n := fun n => Nat.recOn n h0 hsuc
  cases a
  · exact htop A
  · exact A _

lemma add_one_pos : 0 < n + 1 :=
  succ_def n ▸ Order.bot_lt_succ n

lemma add_lt_add_iff_right {k : ℕ∞} (h : k ≠ ⊤) : n + k < m + k ↔ n < m :=
  WithTop.add_lt_add_iff_right h

lemma add_lt_add_iff_left {k : ℕ∞} (h : k ≠ ⊤) : k + n < k + m ↔ n < m :=
  WithTop.add_lt_add_iff_left h

lemma ne_top_iff_exists : n ≠ ⊤ ↔ ∃ m : ℕ, ↑m = n := WithTop.ne_top_iff_exists

lemma eq_top_iff_forall_ne : n = ⊤ ↔ ∀ m : ℕ, ↑m ≠ n := WithTop.eq_top_iff_forall_ne
lemma eq_top_iff_forall_gt : n = ⊤ ↔ ∀ m : ℕ, m < n := WithTop.eq_top_iff_forall_gt
lemma eq_top_iff_forall_ge : n = ⊤ ↔ ∀ m : ℕ, m ≤ n := WithTop.eq_top_iff_forall_ge

/-- Version of `WithTop.forall_coe_le_iff_le` using `Nat.cast` rather than `WithTop.some`. -/
lemma forall_natCast_le_iff_le : (∀ a : ℕ, a ≤ m → a ≤ n) ↔ m ≤ n := WithTop.forall_coe_le_iff_le

/-- Version of `WithTop.eq_of_forall_coe_le_iff` using `Nat.cast` rather than `WithTop.some`. -/
lemma eq_of_forall_natCast_le_iff (hm : ∀ a : ℕ, a ≤ m ↔ a ≤ n) : m = n :=
  WithTop.eq_of_forall_coe_le_iff hm

protected lemma exists_nat_gt (hn : n ≠ ⊤) : ∃ m : ℕ, n < m := by
  simp_rw [lt_iff_not_ge n]
  exact not_forall.mp <| eq_top_iff_forall_ge.2.mt hn

@[simp] lemma sub_eq_top_iff : a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤ := WithTop.sub_eq_top_iff
lemma sub_ne_top_iff : a - b ≠ ⊤ ↔ a ≠ ⊤ ∨ b = ⊤ := WithTop.sub_ne_top_iff

lemma addLECancellable_of_ne_top : a ≠ ⊤ → AddLECancellable a := WithTop.addLECancellable_of_ne_top
lemma addLECancellable_of_lt_top : a < ⊤ → AddLECancellable a := WithTop.addLECancellable_of_lt_top
lemma addLECancellable_coe (a : ℕ) : AddLECancellable (a : ℕ∞) := WithTop.addLECancellable_coe _

protected lemma le_sub_of_add_le_left (ha : a ≠ ⊤) : a + b ≤ c → b ≤ c - a :=
  (addLECancellable_of_ne_top ha).le_tsub_of_add_le_left

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

lemma mul_left_strictMono (ha : a ≠ 0) (h_top : a ≠ ⊤) : StrictMono (a * ·) := by
  lift a to ℕ using h_top
  intro x y hxy
  induction x with
  | top => simp at hxy
  | coe x =>
  induction y with
  | top =>
    simp only [mul_top ha, ← ENat.coe_mul]
    exact coe_lt_top (a * x)
  | coe y =>
  simp only
  rw [← ENat.coe_mul, ← ENat.coe_mul, ENat.coe_lt_coe]
  rw [ENat.coe_lt_coe] at hxy
  exact Nat.mul_lt_mul_of_pos_left hxy (Nat.pos_of_ne_zero (by simpa using ha))

lemma mul_right_strictMono (ha : a ≠ 0) (h_top : a ≠ ⊤) : StrictMono (· * a) := by
  simpa [show (· * a) = (a * ·) by simp [mul_comm]] using mul_left_strictMono ha h_top

@[simp]
lemma mul_le_mul_left_iff {x y : ℕ∞} (ha : a ≠ 0) (h_top : a ≠ ⊤) : a * x ≤ a * y ↔ x ≤ y :=
  (ENat.mul_left_strictMono ha h_top).le_iff_le

@[simp]
lemma mul_le_mul_right_iff {x y : ℕ∞} (ha : a ≠ 0) (h_top : a ≠ ⊤) : x * a ≤ y * a ↔ x ≤ y :=
  (ENat.mul_right_strictMono ha h_top).le_iff_le

@[gcongr]
lemma mul_le_mul_of_le_right {x y : ℕ∞} (hxy : x ≤ y) (ha : a ≠ 0) (h_top : a ≠ ⊤) :
    x * a ≤ y * a := by
  simpa [ha, h_top]

lemma self_le_mul_right (a : ℕ∞) (hc : c ≠ 0) : a ≤ a * c := by
  obtain rfl | hne := eq_or_ne a ⊤
  · simp [top_mul hc]
  obtain rfl | h0 := eq_or_ne a 0
  · simp
  nth_rewrite 1 [← mul_one a, ENat.mul_le_mul_left_iff h0 hne, ENat.one_le_iff_ne_zero]
  assumption

lemma self_le_mul_left (a : ℕ∞) (hc : c ≠ 0) : a ≤ c * a := by
  rw [mul_comm]
  exact ENat.self_le_mul_right a hc

section withTop_enat

lemma add_one_natCast_le_withTop_of_lt {m : ℕ} {n : WithTop ℕ∞} (h : m < n) : (m + 1 : ℕ) ≤ n := by
  match n with
  | ⊤ => exact le_top
  | (⊤ : ℕ∞) => exact WithTop.coe_le_coe.2 (OrderTop.le_top _)
  | (n : ℕ) => simpa only [Nat.cast_le, ge_iff_le, Nat.cast_lt] using h

@[simp] lemma coe_top_add_one : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = (⊤ : ℕ∞) := rfl

@[simp] lemma add_one_eq_coe_top_iff {n : WithTop ℕ∞} : n + 1 = (⊤ : ℕ∞) ↔ n = (⊤ : ℕ∞) := by
  match n with
  | ⊤ => exact Iff.rfl
  | (⊤ : ℕ∞) => simp
  | (n : ℕ) =>
    norm_cast
    simp only [coe_ne_top, iff_false, ne_eq]

@[simp] lemma natCast_ne_coe_top (n : ℕ) : (n : WithTop ℕ∞) ≠ (⊤ : ℕ∞) := nofun

@[deprecated (since := "2024-10-22")]
alias nat_ne_coe_top := natCast_ne_coe_top

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
theorem map_coe (f : ℕ → α) (a : ℕ) : map f a = f a := rfl

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
        (Option.map_injective hf).eq_iff' f.toZeroHom.ENatMap.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      · simp
      rcases Decidable.eq_or_ne y 0 with (rfl | hy)
      · simp
      induction' x with x
      · simp [hy, this]
      induction' y with y
      · have : (f x : WithTop S) ≠ 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
        simp [mul_top hx, WithTop.mul_top this]
      · simp [← Nat.cast_mul, ← coe_mul] }

/-- A version of `ENat.map` for `RingHom`s. -/
@[simps -fullyApplied]
protected def _root_.RingHom.ENatMap {S : Type*} [CommSemiring S] [PartialOrder S]
    [CanonicallyOrderedAdd S]
    [DecidableEq S] [Nontrivial S] (f : ℕ →+* S) (hf : Function.Injective f) : ℕ∞ →+* WithTop S :=
  {MonoidWithZeroHom.ENatMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.ENatMap with}

end ENat

lemma WithBot.lt_add_one_iff {n : WithBot ℕ∞} {m : ℕ} : n < m + 1 ↔ n ≤ m := by
  rw [← WithBot.coe_one, ← ENat.coe_one, WithBot.coe_natCast, ← Nat.cast_add, ← WithBot.coe_natCast]
  cases n
  · simp only [bot_le, iff_true, WithBot.bot_lt_coe]
  · rw [WithBot.coe_lt_coe, Nat.cast_add, ENat.coe_one, ENat.lt_add_one_iff (ENat.coe_ne_top _),
      ← WithBot.coe_le_coe, WithBot.coe_natCast]

lemma WithBot.add_one_le_iff {n : ℕ} {m : WithBot ℕ∞} : n + 1 ≤ m ↔ n < m := by
  rw [← WithBot.coe_one, ← ENat.coe_one, WithBot.coe_natCast, ← Nat.cast_add, ← WithBot.coe_natCast]
  cases m
  · simp
  · rw [WithBot.coe_le_coe, ENat.coe_add, ENat.coe_one, ENat.add_one_le_iff (ENat.coe_ne_top n),
      ← WithBot.coe_lt_coe, WithBot.coe_natCast]
