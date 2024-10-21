/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Order.Sub.WithTop
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Nat

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
-/

deriving instance Zero, CanonicallyOrderedCommSemiring, Nontrivial,
  LinearOrder, Bot, CanonicallyLinearOrderedAddCommMonoid, Sub,
  LinearOrderedAddCommMonoidWithTop, WellFoundedRelation
  for ENat
  -- AddCommMonoidWithOne,
  -- OrderBot, OrderTop, OrderedSub, SuccOrder, WellFoundedLt, CharZero

-- Porting Note: In `Data.Nat.ENatPart` proofs timed out when having
-- the `deriving AddCommMonoidWithOne`, and it seems to work without.

namespace ENat

-- Porting note: instances that derive failed to find
instance : OrderBot ℕ∞ := WithTop.orderBot
instance : OrderTop ℕ∞ := WithTop.orderTop
instance : OrderedSub ℕ∞ := inferInstanceAs (OrderedSub (WithTop ℕ))
instance : SuccOrder ℕ∞ := inferInstanceAs (SuccOrder (WithTop ℕ))
instance : WellFoundedLT ℕ∞ := inferInstanceAs (WellFoundedLT (WithTop ℕ))
instance : CharZero ℕ∞ := inferInstanceAs (CharZero (WithTop ℕ))
instance : IsWellOrder ℕ∞ (· < ·) where

variable {a b c m n : ℕ∞}

/-- Lemmas about `WithTop` expect (and can output) `WithTop.some` but the normal form for coercion
`ℕ → ℕ∞` is `Nat.cast`. -/
@[simp] theorem some_eq_coe : (WithTop.some : ℕ → ℕ∞) = Nat.cast := rfl

instance : SuccAddOrder ℕ∞ where
  succ_eq_add_one x := by cases x <;> simp [SuccOrder.succ]

-- Porting note: `simp` and `norm_cast` can prove it
--@[simp, norm_cast]
theorem coe_zero : ((0 : ℕ) : ℕ∞) = 0 :=
  rfl

-- Porting note: `simp` and `norm_cast` can prove it
--@[simp, norm_cast]
theorem coe_one : ((1 : ℕ) : ℕ∞) = 1 :=
  rfl

-- Porting note: `simp` and `norm_cast` can prove it
--@[simp, norm_cast]
theorem coe_add (m n : ℕ) : ↑(m + n) = (m + n : ℕ∞) :=
  rfl

@[simp, norm_cast]
theorem coe_sub (m n : ℕ) : ↑(m - n) = (m - n : ℕ∞) :=
  rfl

@[simp] lemma coe_mul (m n : ℕ) : ↑(m * n) = (m * n : ℕ∞) := rfl

@[simp] theorem mul_top (hm : m ≠ 0) : m * ⊤ = ⊤ := WithTop.mul_top hm
@[simp] theorem top_mul (hm : m ≠ 0) : ⊤ * m = ⊤ := WithTop.top_mul hm

theorem top_pow {n : ℕ} (n_pos : 0 < n) : (⊤ : ℕ∞) ^ n = ⊤ := WithTop.top_pow n_pos

instance canLift : CanLift ℕ∞ ℕ (↑) (· ≠ ⊤) := WithTop.canLift

instance : WellFoundedRelation ℕ∞ where
  rel := (· < ·)
  wf := IsWellFounded.wf

/-- Conversion of `ℕ∞` to `ℕ` sending `∞` to `0`. -/
def toNat : ℕ∞ → ℕ := WithTop.untop' 0

/-- Homomorphism from `ℕ∞` to `ℕ` sending `∞` to `0`. -/
def toNatHom : MonoidWithZeroHom ℕ∞ ℕ where
  toFun := toNat
  map_one' := rfl
  map_zero' := rfl
  map_mul' := WithTop.untop'_zero_mul

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

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem toNat_ofNat (n : ℕ) [n.AtLeastTwo] : toNat (no_index (OfNat.ofNat n)) = n :=
  rfl

@[simp]
theorem toNat_top : toNat ⊤ = 0 :=
  rfl

@[simp] theorem toNat_eq_zero : toNat n = 0 ↔ n = 0 ∨ n = ⊤ := WithTop.untop'_eq_self_iff

@[simp]
theorem recTopCoe_zero {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) : @recTopCoe C d f 0 = f 0 :=
  rfl

@[simp]
theorem recTopCoe_one {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) : @recTopCoe C d f 1 = f 1 :=
  rfl

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem recTopCoe_ofNat {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) (x : ℕ) [x.AtLeastTwo] :
    @recTopCoe C d f (no_index (OfNat.ofNat x)) = f (OfNat.ofNat x) :=
  rfl

@[simp]
theorem top_ne_coe (a : ℕ) : ⊤ ≠ (a : ℕ∞) :=
  nofun

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem top_ne_ofNat (a : ℕ) [a.AtLeastTwo] : ⊤ ≠ (no_index (OfNat.ofNat a : ℕ∞)) :=
  nofun

@[simp] lemma top_ne_zero : (⊤ : ℕ∞) ≠ 0 := nofun
@[simp] lemma top_ne_one : (⊤ : ℕ∞) ≠ 1 := nofun

@[simp]
theorem coe_ne_top (a : ℕ) : (a : ℕ∞) ≠ ⊤ :=
  nofun

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_ne_top (a : ℕ) [a.AtLeastTwo] : (no_index (OfNat.ofNat a : ℕ∞)) ≠ ⊤ :=
  nofun

@[simp] lemma zero_ne_top : 0 ≠ (⊤ : ℕ∞) := nofun
@[simp] lemma one_ne_top : 1 ≠ (⊤ : ℕ∞) := nofun

@[simp]
theorem top_sub_coe (a : ℕ) : (⊤ : ℕ∞) - a = ⊤ :=
  WithTop.top_sub_coe

@[simp]
theorem top_sub_one : (⊤ : ℕ∞) - 1 = ⊤ :=
  top_sub_coe 1

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem top_sub_ofNat (a : ℕ) [a.AtLeastTwo] : (⊤ : ℕ∞) - (no_index (OfNat.ofNat a)) = ⊤ :=
  top_sub_coe a

@[simp]
theorem zero_lt_top : (0 : ℕ∞) < ⊤ :=
  WithTop.zero_lt_top

theorem sub_top (a : ℕ∞) : a - ⊤ = 0 :=
  WithTop.sub_top

@[simp]
theorem coe_toNat_eq_self : ENat.toNat n = n ↔ n ≠ ⊤ :=
  ENat.recTopCoe (by decide) (fun _ => by simp [toNat_coe]) n

alias ⟨_, coe_toNat⟩ := coe_toNat_eq_self

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

@[deprecated Order.add_one_le_of_lt (since := "2024-09-04")]
theorem add_one_le_of_lt (h : m < n) : m + 1 ≤ n :=
  Order.add_one_le_of_lt h

theorem add_one_le_iff (hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
  Order.add_one_le_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hm)

@[deprecated Order.one_le_iff_pos (since := "2024-09-04")]
theorem one_le_iff_pos : 1 ≤ n ↔ 0 < n :=
  Order.one_le_iff_pos

theorem one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 :=
  Order.one_le_iff_pos.trans pos_iff_ne_zero

lemma lt_one_iff_eq_zero : n < 1 ↔ n = 0 :=
  not_le.symm.trans one_le_iff_ne_zero.not_left

@[deprecated Order.le_of_lt_add_one (since := "2024-09-04")]
theorem le_of_lt_add_one (h : m < n + 1) : m ≤ n :=
  Order.le_of_lt_add_one h

theorem lt_add_one_iff (hm : n ≠ ⊤) : m < n + 1 ↔ m ≤ n :=
  Order.lt_add_one_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hm)

theorem le_coe_iff {n : ℕ∞} {k : ℕ} : n ≤ ↑k ↔ ∃ (n₀ : ℕ), n = n₀ ∧ n₀ ≤ k :=
  WithTop.le_coe_iff

@[simp]
lemma not_lt_zero (n : ℕ∞) : ¬ n < 0 := by
  cases n <;> simp

@[simp]
lemma coe_lt_top (n : ℕ) : (n : ℕ∞) < ⊤ :=
  WithTop.coe_lt_top n

@[elab_as_elim]
theorem nat_induction {P : ℕ∞ → Prop} (a : ℕ∞) (h0 : P 0) (hsuc : ∀ n : ℕ, P n → P n.succ)
    (htop : (∀ n : ℕ, P n) → P ⊤) : P a := by
  have A : ∀ n : ℕ, P n := fun n => Nat.recOn n h0 hsuc
  cases a
  · exact htop A
  · exact A _

protected lemma exists_nat_gt {n : ℕ∞} (hn : n ≠ ⊤) : ∃ m : ℕ, n < m := by
  lift n to ℕ using hn
  obtain ⟨m, hm⟩ := exists_gt n
  exact ⟨m, Nat.cast_lt.2 hm⟩

@[simp] lemma sub_eq_top : a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤ := WithTop.sub_eq_top
lemma sub_ne_top : a - b ≠ ⊤ ↔ a ≠ ⊤ ∨ b = ⊤ := WithTop.sub_ne_top

lemma addLECancellable_of_ne_top : a ≠ ⊤ → AddLECancellable a := WithTop.addLECancellable_of_ne_top
lemma addLECancellable_of_lt_top : a < ⊤ → AddLECancellable a := WithTop.addLECancellable_of_lt_top

protected lemma le_sub_of_add_le_left (ha : a ≠ ⊤) : a + b ≤ c → b ≤ c - a :=
  (addLECancellable_of_ne_top ha).le_tsub_of_add_le_left

protected lemma sub_sub_cancel (h : a ≠ ⊤) (h2 : b ≤ a) : a - (a - b) = b :=
  (addLECancellable_of_ne_top <| ne_top_of_le_ne_top h tsub_le_self).tsub_tsub_cancel_of_le h2

lemma add_one_natCast_le_withTop_of_lt {m : ℕ} {n : WithTop ℕ∞} (h : m < n) : (m + 1 : ℕ) ≤ n := by
  match n with
  | ⊤ => exact le_top
  | (⊤ : ℕ∞) => exact WithTop.coe_le_coe.2 (OrderTop.le_top _)
  | (n : ℕ) => simpa only [Nat.cast_le, ge_iff_le, Nat.cast_lt] using h

@[simp] lemma coe_top_add_one : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = (⊤ : ℕ∞) := rfl

@[simp] lemma add_one_eq_coe_top_iff : n + 1 = (⊤ : ℕ∞) ↔ n = (⊤ : ℕ∞) := by
  match n with
  | ⊤ => exact Iff.rfl
  | (n : ℕ) => norm_cast; simp only [coe_ne_top, iff_false, ne_eq]

@[simp] lemma natCast_ne_coe_top (n : ℕ) : (n : WithTop ℕ∞) ≠ (⊤ : ℕ∞) := nofun

lemma one_le_iff_ne_zero_withTop {n : WithTop ℕ∞} : 1 ≤ n ↔ n ≠ 0 :=
  ⟨fun h ↦ (zero_lt_one.trans_le h).ne',
    fun h ↦ add_one_natCast_le_withTop_of_lt (pos_iff_ne_zero.mpr h)⟩

end ENat
