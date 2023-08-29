/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Nat.SuccPred
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.Order.Sub.WithTop
import Mathlib.Algebra.Order.Ring.WithTop

#align_import data.enat.basic from "leanprover-community/mathlib"@"ceb887ddf3344dab425292e497fa2af91498437c"

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

/-- Extended natural numbers `ℕ∞ = WithTop ℕ`. -/
def ENat : Type :=
  WithTop ℕ
deriving Zero,
  -- AddCommMonoidWithOne,
  CanonicallyOrderedCommSemiring, Nontrivial,
  LinearOrder, Bot, Top, CanonicallyLinearOrderedAddMonoid, Sub,
  LinearOrderedAddCommMonoidWithTop, WellFoundedRelation, Inhabited
  -- OrderBot, OrderTop, OrderedSub, SuccOrder, WellFoundedLt, CharZero
#align enat ENat

-- Porting Note: In `Data.Nat.ENatPart` proofs timed out when having
-- the `deriving AddCommMonoidWithOne`, and it seems to work without.

/-- Extended natural numbers `ℕ∞ = WithTop ℕ`. -/
notation "ℕ∞" => ENat

namespace ENat

--Porting note: instances that derive failed to find
instance : OrderBot ℕ∞ := WithTop.orderBot
instance : OrderTop ℕ∞ := WithTop.orderTop
instance : OrderedSub ℕ∞ := inferInstanceAs (OrderedSub (WithTop ℕ))
instance : SuccOrder ℕ∞ := inferInstanceAs (SuccOrder (WithTop ℕ))
instance : WellFoundedLT ℕ∞ := inferInstanceAs (WellFoundedLT (WithTop ℕ))
instance : CharZero ℕ∞ := inferInstanceAs (CharZero (WithTop ℕ))
instance : IsWellOrder ℕ∞ (· < ·) where

variable {m n : ℕ∞}

/-- Lemmas about `WithTop` expect (and can output) `WithTop.some` but the normal form for coercion
`ℕ → ℕ∞` is `Nat.cast`. -/
@[simp] theorem some_eq_coe : (WithTop.some : ℕ → ℕ∞) = Nat.cast := rfl

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

instance : WellFoundedRelation ℕ∞ where
  rel := (· < ·)
  wf := IsWellFounded.wf

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
def recTopCoe {C : ℕ∞ → Sort*} (h₁ : C ⊤) (h₂ : ∀ a : ℕ, C a) : ∀ n : ℕ∞, C n
| none => h₁
| Option.some a => h₂ a

--Porting note: new theorem copied from `WithTop`
@[simp]
theorem recTopCoe_top {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) :
    @recTopCoe C d f ⊤ = d :=
  rfl

--Porting note: new theorem copied from `WithTop`
@[simp]
theorem recTopCoe_coe {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) (x : ℕ) :
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
                     -- 🎉 no goals
                                        -- 🎉 no goals
#align enat.coe_to_nat_eq_self ENat.coe_toNat_eq_self

alias ⟨_, coe_toNat⟩ := coe_toNat_eq_self
#align enat.coe_to_nat ENat.coe_toNat

theorem coe_toNat_le_self (n : ℕ∞) : ↑(toNat n) ≤ n :=
  ENat.recTopCoe le_top (fun _ => le_rfl) n
#align enat.coe_to_nat_le_self ENat.coe_toNat_le_self

theorem toNat_add {m n : ℕ∞} (hm : m ≠ ⊤) (hn : n ≠ ⊤) : toNat (m + n) = toNat m + toNat n := by
  lift m to ℕ using hm
  -- ⊢ ↑toNat (↑m + n) = ↑toNat ↑m + ↑toNat n
  lift n to ℕ using hn
  -- ⊢ ↑toNat (↑m + ↑n) = ↑toNat ↑m + ↑toNat ↑n
  rfl
  -- 🎉 no goals
#align enat.to_nat_add ENat.toNat_add

theorem toNat_sub {n : ℕ∞} (hn : n ≠ ⊤) (m : ℕ∞) : toNat (m - n) = toNat m - toNat n := by
  lift n to ℕ using hn
  -- ⊢ ↑toNat (m - ↑n) = ↑toNat m - ↑toNat ↑n
  induction m using ENat.recTopCoe
  -- ⊢ ↑toNat (⊤ - ↑n) = ↑toNat ⊤ - ↑toNat ↑n
  · rw [top_sub_coe, toNat_top, zero_tsub]
    -- 🎉 no goals
  · rw [← coe_sub, toNat_coe, toNat_coe, toNat_coe]
    -- 🎉 no goals
#align enat.to_nat_sub ENat.toNat_sub

theorem toNat_eq_iff {m : ℕ∞} {n : ℕ} (hn : n ≠ 0) : toNat m = n ↔ m = n := by
  induction m using ENat.recTopCoe <;> simp [hn.symm]
  -- ⊢ ↑toNat ⊤ = n ↔ ⊤ = ↑n
                                       -- 🎉 no goals
                                       -- 🎉 no goals
#align enat.to_nat_eq_iff ENat.toNat_eq_iff

@[simp]
theorem succ_def (m : ℕ∞) : Order.succ m = m + 1 := by cases m <;> rfl
                                                       -- ⊢ Order.succ none = none + 1
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align enat.succ_def ENat.succ_def

theorem add_one_le_of_lt (h : m < n) : m + 1 ≤ n :=
  m.succ_def ▸ Order.succ_le_of_lt h
#align enat.add_one_le_of_lt ENat.add_one_le_of_lt

theorem add_one_le_iff (hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
  m.succ_def ▸ (Order.succ_le_iff_of_not_isMax <| by rwa [isMax_iff_eq_top])
                                                     -- 🎉 no goals
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

theorem le_coe_iff {n : ℕ∞} {k : ℕ} : n ≤ ↑k ↔ ∃ (n₀ : ℕ), n = n₀ ∧ n₀ ≤ k :=
  WithTop.le_coe_iff

@[elab_as_elim]
theorem nat_induction {P : ℕ∞ → Prop} (a : ℕ∞) (h0 : P 0) (hsuc : ∀ n : ℕ, P n → P n.succ)
    (htop : (∀ n : ℕ, P n) → P ⊤) : P a := by
  have A : ∀ n : ℕ, P n := fun n => Nat.recOn n h0 hsuc
  -- ⊢ P a
  cases a
  -- ⊢ P none
  · exact htop A
    -- 🎉 no goals
  · exact A _
    -- 🎉 no goals
#align enat.nat_induction ENat.nat_induction

end ENat
