/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/

import Mathlib.Algebra.NeZero
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Basic

#align_import data.pnat.defs from "leanprover-community/mathlib"@"c4658a649d216f57e99621708b09dcb3dcccbd23"

/-!
# The positive natural numbers

This file contains the definitions, and basic results.
Most algebraic facts are deferred to `Data.PNat.Basic`, as they need more imports.
-/


/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
def PNat := { n : ℕ // 0 < n }
  deriving DecidableEq, LinearOrder
#align pnat PNat

@[inherit_doc]
notation "ℕ+" => PNat

instance : One ℕ+ :=
  ⟨⟨1, Nat.zero_lt_one⟩⟩

/-- The underlying natural number -/
@[coe]
def PNat.val : ℕ+ → ℕ := Subtype.val

instance coePNatNat : Coe ℕ+ ℕ :=
  ⟨PNat.val⟩
#align coe_pnat_nat coePNatNat

instance : Repr ℕ+ :=
  ⟨fun n n' => reprPrec n.1 n'⟩

--Porting note: New instance not in Lean3
instance (n : ℕ) : OfNat ℕ+ (n+1) :=
  ⟨⟨n + 1, Nat.succ_pos n⟩⟩

namespace PNat

-- Note: similar to Subtype.coe_mk
@[simp]
theorem mk_coe (n h) : (PNat.val (⟨n, h⟩ : ℕ+) : ℕ) = n :=
  rfl
#align pnat.mk_coe PNat.mk_coe

/-- Predecessor of a `ℕ+`, as a `ℕ`. -/
def natPred (i : ℕ+) : ℕ :=
  i - 1
#align pnat.nat_pred PNat.natPred

@[simp]
theorem natPred_eq_pred {n : ℕ} (h : 0 < n) : natPred (⟨n, h⟩ : ℕ+) = n.pred :=
  rfl
#align pnat.nat_pred_eq_pred PNat.natPred_eq_pred

end PNat

namespace Nat

/-- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
def toPNat (n : ℕ) (h : 0 < n := by decide) : ℕ+ :=
  ⟨n, h⟩
#align nat.to_pnat Nat.toPNat

/-- Write a successor as an element of `ℕ+`. -/
def succPNat (n : ℕ) : ℕ+ :=
  ⟨succ n, succ_pos n⟩
#align nat.succ_pnat Nat.succPNat

@[simp]
theorem succPNat_coe (n : ℕ) : (succPNat n : ℕ) = succ n :=
  rfl
#align nat.succ_pnat_coe Nat.succPNat_coe

@[simp]
theorem natPred_succPNat (n : ℕ) : n.succPNat.natPred = n :=
  rfl
#align nat.nat_pred_succ_pnat Nat.natPred_succPNat

@[simp]
theorem _root_.PNat.succPNat_natPred (n : ℕ+) : n.natPred.succPNat = n :=
  Subtype.eq <| succ_pred_eq_of_pos n.2
#align pnat.succ_pnat_nat_pred PNat.succPNat_natPred

/-- Convert a natural number to a `PNat`. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
def toPNat' (n : ℕ) : ℕ+ :=
  succPNat (pred n)
#align nat.to_pnat' Nat.toPNat'

@[simp]
theorem toPNat'_coe : ∀ n : ℕ, (toPNat' n : ℕ) = ite (0 < n) n 1
  | 0 => rfl
  | m + 1 => by
    rw [if_pos (succ_pos m)]
    -- ⊢ ↑(toPNat' (m + 1)) = m + 1
    rfl
    -- 🎉 no goals
#align nat.to_pnat'_coe Nat.toPNat'_coe

end Nat

namespace PNat

open Nat

/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/
-- Porting note: no `simp`  because simp can prove it
theorem mk_le_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) ≤ ⟨k, hk⟩ ↔ n ≤ k :=
  Iff.rfl
#align pnat.mk_le_mk PNat.mk_le_mk

-- Porting note: no `simp`  because simp can prove it
theorem mk_lt_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) < ⟨k, hk⟩ ↔ n < k :=
  Iff.rfl
#align pnat.mk_lt_mk PNat.mk_lt_mk

@[simp, norm_cast]
theorem coe_le_coe (n k : ℕ+) : (n : ℕ) ≤ k ↔ n ≤ k :=
  Iff.rfl
#align pnat.coe_le_coe PNat.coe_le_coe

@[simp, norm_cast]
theorem coe_lt_coe (n k : ℕ+) : (n : ℕ) < k ↔ n < k :=
  Iff.rfl
#align pnat.coe_lt_coe PNat.coe_lt_coe

@[simp]
theorem pos (n : ℕ+) : 0 < (n : ℕ) :=
  n.2
#align pnat.pos PNat.pos

theorem eq {m n : ℕ+} : (m : ℕ) = n → m = n :=
  Subtype.eq
#align pnat.eq PNat.eq

theorem coe_injective : Function.Injective (fun (a : ℕ+) => (a : ℕ)) :=
  Subtype.coe_injective
#align pnat.coe_injective PNat.coe_injective

@[simp]
theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 :=
  n.2.ne'
#align pnat.ne_zero PNat.ne_zero

instance _root_.NeZero.pnat {a : ℕ+} : NeZero (a : ℕ) :=
  ⟨a.ne_zero⟩
#align ne_zero.pnat NeZero.pnat

theorem toPNat'_coe {n : ℕ} : 0 < n → (n.toPNat' : ℕ) = n :=
  succ_pred_eq_of_pos
#align pnat.to_pnat'_coe PNat.toPNat'_coe

@[simp]
theorem coe_toPNat' (n : ℕ+) : (n : ℕ).toPNat' = n :=
  eq (toPNat'_coe n.pos)
#align pnat.coe_to_pnat' PNat.coe_toPNat'

@[simp]
theorem one_le (n : ℕ+) : (1 : ℕ+) ≤ n :=
  n.2
#align pnat.one_le PNat.one_le

@[simp]
theorem not_lt_one (n : ℕ+) : ¬n < 1 :=
  not_lt_of_le n.one_le
#align pnat.not_lt_one PNat.not_lt_one

instance : Inhabited ℕ+ :=
  ⟨1⟩

-- Some lemmas that rewrite `PNat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp]
theorem mk_one {h} : (⟨1, h⟩ : ℕ+) = (1 : ℕ+) :=
  rfl
#align pnat.mk_one PNat.mk_one

@[simp, norm_cast]
theorem one_coe : ((1 : ℕ+) : ℕ) = 1 :=
  rfl
#align pnat.one_coe PNat.one_coe

@[simp, norm_cast]
theorem coe_eq_one_iff {m : ℕ+} : (m : ℕ) = 1 ↔ m = 1 :=
  Subtype.coe_injective.eq_iff' one_coe
#align pnat.coe_eq_one_iff PNat.coe_eq_one_iff

instance : WellFoundedRelation ℕ+ :=
  measure (fun (a : ℕ+) => (a : ℕ))

/-- Strong induction on `ℕ+`. -/
def strongInductionOn {p : ℕ+ → Sort*} (n : ℕ+) : (∀ k, (∀ m, m < k → p m) → p k) → p n
  | IH => IH _ fun a _ => strongInductionOn a IH
termination_by _ => n.1
#align pnat.strong_induction_on PNat.strongInductionOn

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
#align pnat.mod_div_aux PNat.modDivAux

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
#align pnat.mod_div PNat.modDiv

/-- We define `m % k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` This ensures that `m % k` is always positive.
-/
def mod (m k : ℕ+) : ℕ+ :=
  (modDiv m k).1
#align pnat.mod PNat.mod

/-- We define `m / k` in the same way as for `ℕ` except that when `m = n * k` we take
  `m / k = n - 1`. This ensures that `m = (m % k) + k * (m / k)` in all cases. Later we
  define a function `div_exact` which gives the usual `m / k` in the case where `k` divides `m`.
-/
def div (m k : ℕ+) : ℕ :=
  (modDiv m k).2
#align pnat.div PNat.div

theorem mod_coe (m k : ℕ+) :
  (mod m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) (k : ℕ) ((m : ℕ) % (k : ℕ)) := by
  dsimp [mod, modDiv]
  -- ⊢ ↑(modDivAux k (↑m % ↑k) (↑m / ↑k)).fst = if ↑m % ↑k = 0 then ↑k else ↑m % ↑k
  cases (m : ℕ) % (k : ℕ) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl
#align pnat.mod_coe PNat.mod_coe

theorem div_coe (m k : ℕ+) :
  (div m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) ((m : ℕ) / (k : ℕ)).pred ((m : ℕ) / (k : ℕ)) := by
  dsimp [div, modDiv]
  -- ⊢ (modDivAux k (↑m % ↑k) (↑m / ↑k)).snd = if ↑m % ↑k = 0 then pred (↑m / ↑k) e …
  cases (m : ℕ) % (k : ℕ) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl
#align pnat.div_coe PNat.div_coe

/-- If `h : k | m`, then `k * (div_exact m k) = m`. Note that this is not equal to `m / k`. -/
def divExact (m k : ℕ+) : ℕ+ :=
  ⟨(div m k).succ, Nat.succ_pos _⟩
#align pnat.div_exact PNat.divExact

end PNat

section CanLift

instance Nat.canLiftPNat : CanLift ℕ ℕ+ (↑) (fun n => 0 < n) :=
  ⟨fun n hn => ⟨Nat.toPNat' n, PNat.toPNat'_coe hn⟩⟩
#align nat.can_lift_pnat Nat.canLiftPNat

instance Int.canLiftPNat : CanLift ℤ ℕ+ (↑) ((0 < ·)) :=
  ⟨fun n hn =>
    ⟨Nat.toPNat' (Int.natAbs n), by
      rw [Nat.toPNat'_coe, if_pos (Int.natAbs_pos.2 hn.ne'),
        Int.natAbs_of_nonneg hn.le]⟩⟩
#align int.can_lift_pnat Int.canLiftPNat

end CanLift
