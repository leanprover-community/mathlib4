/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.PNat.Notation
import Mathlib.Order.Basic
import Mathlib.Tactic.Coe
import Mathlib.Tactic.Lift

/-!
# The positive natural numbers

This file contains the definitions, and basic results.
Most algebraic facts are deferred to `Data.PNat.Basic`, as they need more imports.
-/

deriving instance LinearOrder for PNat

instance : One ℕ+ :=
  ⟨⟨1, Nat.zero_lt_one⟩⟩

instance (n : ℕ) [NeZero n] : OfNat ℕ+ n :=
  ⟨⟨n, Nat.pos_of_ne_zero <| NeZero.ne n⟩⟩

namespace PNat

-- Note: similar to Subtype.coe_mk
@[simp]
theorem mk_coe (n h) : (PNat.val (⟨n, h⟩ : ℕ+) : ℕ) = n :=
  rfl

/-- Predecessor of a `ℕ+`, as a `ℕ`. -/
def natPred (i : ℕ+) : ℕ :=
  i - 1

@[simp]
theorem natPred_eq_pred {n : ℕ} (h : 0 < n) : natPred (⟨n, h⟩ : ℕ+) = n.pred :=
  rfl

end PNat

namespace Nat

/-- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
def toPNat (n : ℕ) (h : 0 < n := by decide) : ℕ+ :=
  ⟨n, h⟩

/-- Write a successor as an element of `ℕ+`. -/
def succPNat (n : ℕ) : ℕ+ :=
  ⟨succ n, succ_pos n⟩

@[simp]
theorem succPNat_coe (n : ℕ) : (succPNat n : ℕ) = succ n :=
  rfl

@[simp]
theorem natPred_succPNat (n : ℕ) : n.succPNat.natPred = n :=
  rfl

@[simp]
theorem _root_.PNat.succPNat_natPred (n : ℕ+) : n.natPred.succPNat = n :=
  Subtype.ext <| succ_pred_eq_of_pos n.2

/-- Convert a natural number to a `PNat`. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
def toPNat' (n : ℕ) : ℕ+ :=
  succPNat (pred n)

@[simp]
theorem toPNat'_zero : Nat.toPNat' 0 = 1 := rfl

@[simp]
theorem toPNat'_coe : ∀ n : ℕ, (toPNat' n : ℕ) = ite (0 < n) n 1
  | 0 => rfl
  | m + 1 => by
    rw [if_pos (succ_pos m)]
    rfl

end Nat

namespace PNat

open Nat

/-- We now define a long list of structures on ℕ+ induced by
similar structures on ℕ. Most of these behave in a completely
obvious way, but there are a few things to be said about
subtraction, division and powers.
-/
theorem mk_le_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) ≤ ⟨k, hk⟩ ↔ n ≤ k := by simp

theorem mk_lt_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) < ⟨k, hk⟩ ↔ n < k := by simp

@[simp, norm_cast]
theorem coe_le_coe (n k : ℕ+) : (n : ℕ) ≤ k ↔ n ≤ k :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_lt_coe (n k : ℕ+) : (n : ℕ) < k ↔ n < k :=
  Iff.rfl

@[simp]
theorem pos (n : ℕ+) : 0 < (n : ℕ) :=
  n.2

theorem eq {m n : ℕ+} : (m : ℕ) = n → m = n :=
  Subtype.ext

theorem coe_injective : Function.Injective PNat.val :=
  Subtype.coe_injective

@[simp]
theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 :=
  n.2.ne'

instance _root_.NeZero.pnat {a : ℕ+} : NeZero (a : ℕ) :=
  ⟨a.ne_zero⟩

theorem toPNat'_coe {n : ℕ} : 0 < n → (n.toPNat' : ℕ) = n :=
  succ_pred_eq_of_pos

@[simp]
theorem coe_toPNat' (n : ℕ+) : (n : ℕ).toPNat' = n :=
  eq (toPNat'_coe n.pos)

@[simp]
theorem one_le (n : ℕ+) : (1 : ℕ+) ≤ n :=
  n.2

@[simp]
theorem not_lt_one (n : ℕ+) : ¬n < 1 :=
  not_lt_of_ge n.one_le

instance : Inhabited ℕ+ :=
  ⟨1⟩

-- Some lemmas that rewrite `PNat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp]
theorem mk_one {h} : (⟨1, h⟩ : ℕ+) = (1 : ℕ+) :=
  rfl

@[norm_cast]
theorem one_coe : ((1 : ℕ+) : ℕ) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_one_iff {m : ℕ+} : (m : ℕ) = 1 ↔ m = 1 :=
  Subtype.coe_injective.eq_iff' one_coe

instance : WellFoundedRelation ℕ+ :=
  measure (fun (a : ℕ+) => (a : ℕ))

/-- Strong induction on `ℕ+`. -/
def strongInductionOn {p : ℕ+ → Sort*} (n : ℕ+) : (∀ k, (∀ m, m < k → p m) → p k) → p n
  | IH => IH _ fun a _ => strongInductionOn a IH
termination_by n.1

/-- We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def modDivAux : ℕ+ → ℕ → ℕ → ℕ+ × ℕ
  | k, 0, q => ⟨k, q.pred⟩
  | _, r + 1, q => ⟨⟨r + 1, Nat.succ_pos r⟩, q⟩

/-- `mod_div m k = (m % k, m / k)`.
  We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def modDiv (m k : ℕ+) : ℕ+ × ℕ :=
  modDivAux k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ))

/-- We define `m % k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` This ensures that `m % k` is always positive.
-/
def mod (m k : ℕ+) : ℕ+ :=
  (modDiv m k).1

/-- We define `m / k` in the same way as for `ℕ` except that when `m = n * k` we take
  `m / k = n - 1`. This ensures that `m = (m % k) + k * (m / k)` in all cases. Later we
  define a function `div_exact` which gives the usual `m / k` in the case where `k` divides `m`.
-/
def div (m k : ℕ+) : ℕ :=
  (modDiv m k).2

theorem mod_coe (m k : ℕ+) :
    (mod m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) (k : ℕ) ((m : ℕ) % (k : ℕ)) := by
  dsimp [mod, modDiv]
  cases (m : ℕ) % (k : ℕ) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl

theorem div_coe (m k : ℕ+) :
    (div m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) ((m : ℕ) / (k : ℕ)).pred ((m : ℕ) / (k : ℕ)) := by
  dsimp [div, modDiv]
  cases (m : ℕ) % (k : ℕ) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl

/-- If `h : k | m`, then `k * (div_exact m k) = m`. Note that this is not equal to `m / k`. -/
def divExact (m k : ℕ+) : ℕ+ :=
  ⟨(div m k).succ, Nat.succ_pos _⟩

end PNat

section CanLift

instance Nat.canLiftPNat : CanLift ℕ ℕ+ (↑) (fun n => 0 < n) :=
  ⟨fun n hn => ⟨Nat.toPNat' n, PNat.toPNat'_coe hn⟩⟩

instance Int.canLiftPNat : CanLift ℤ ℕ+ (↑) ((0 < ·)) :=
  ⟨fun n hn =>
    ⟨Nat.toPNat' (Int.natAbs n), by
      rw [Nat.toPNat'_coe, if_pos (Int.natAbs_pos.2 hn.ne'),
        Int.natAbs_of_nonneg hn.le]⟩⟩

end CanLift
