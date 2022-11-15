/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/

import Mathlib.Algebra.NeZero
import Mathlib.Order.Basic

/-!
# The positive natural numbers

This file contains the definitions, and basic results.
Most algebraic facts are deferred to `data.pnat.basic`, as they need more imports.
-/


/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
def Pnat :=
  { n : ℕ // 0 < n }
  deriving DecidableEq, LinearOrder
#align pnat Pnat

@[inherit_doc]
notation "ℕ+" => Pnat

instance : One ℕ+ :=
  ⟨⟨1, Nat.zero_lt_one⟩⟩

instance coePnatNat : Coe ℕ+ ℕ :=
  ⟨Subtype.val⟩
#align coe_pnat_nat coePnatNat

instance : Repr ℕ+ :=
  ⟨fun n n' => reprPrec n.1 n'⟩

namespace Pnat

-- Porting note: no `simp` due to eagerly elaborated coercions
theorem mk_coe (n h) : ((⟨n, h⟩ : ℕ+) : ℕ) = n :=
  rfl
#align pnat.mk_coe Pnat.mk_coe

/-- Predecessor of a `ℕ+`, as a `ℕ`. -/
def natPred (i : ℕ+) : ℕ :=
  i - 1
#align pnat.natPred Pnat.natPred

@[simp]
theorem natPred_eq_pred {n : ℕ} (h : 0 < n) : natPred (⟨n, h⟩ : ℕ+) = n.pred :=
  rfl
#align pnat.natPred_eq_pred Pnat.natPred_eq_pred

end Pnat

namespace Nat

/-- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
def toPnat (n : ℕ) (h : 0 < n := by decide) : ℕ+ :=
  ⟨n, h⟩
#align nat.to_pnat Nat.toPnat

/-- Write a successor as an element of `ℕ+`. -/
def succPnat (n : ℕ) : ℕ+ :=
  ⟨succ n, succ_pos n⟩
#align nat.succ_pnat Nat.succPnat

@[simp]
theorem succPnat_coe (n : ℕ) : (succPnat n : ℕ) = succ n :=
  rfl
#align nat.succ_pnat_coe Nat.succPnat_coe

@[simp]
theorem natPred_succPnat (n : ℕ) : n.succPnat.natPred = n :=
  rfl
#align nat.nat_pred_succ_pnat Nat.natPred_succPnat

@[simp]
theorem _root_.Pnat.succPnat_natPred (n : ℕ+) : n.natPred.succPnat = n :=
  Subtype.eq <| succ_pred_eq_of_pos n.2
#align nat._root_.pnat.succ_pnat_nat_pred nat._root_.Pnat.succPnat_natPred

/-- Convert a natural number to a pnat. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
def toPnat' (n : ℕ) : ℕ+ :=
  succPnat (pred n)
#align nat.to_pnat' Nat.toPnat'

@[simp]
theorem toPnat'_coe : ∀ n : ℕ, (toPnat' n : ℕ) = ite (0 < n) n 1
  | 0 => rfl
  | m + 1 => by
    rw [if_pos (succ_pos m)]
    rfl
#align nat.to_pnat'_coe Nat.toPnat'_coe

end Nat

namespace Pnat

open Nat

/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/
-- Porting note: no `simp`  because simp can prove it
theorem mk_le_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) ≤ ⟨k, hk⟩ ↔ n ≤ k :=
  Iff.rfl
#align pnat.mk_le_mk Pnat.mk_le_mk

-- Porting note: no `simp`  because simp can prove it
theorem mk_lt_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) < ⟨k, hk⟩ ↔ n < k :=
  Iff.rfl
#align pnat.mk_lt_mk Pnat.mk_lt_mk

-- Porting note: no `norm_cast` due to eagerly elaborated coercions
-- Porting note: no `simp`  because simp can prove it
theorem coe_le_coe (n k : ℕ+) : (n : ℕ) ≤ k ↔ n ≤ k :=
  Iff.rfl
#align pnat.coe_le_coe Pnat.coe_le_coe

-- Porting note: no `norm_cast` due to eagerly elaborated coercions
-- Porting note: no `simp`  because simp can prove it
theorem coe_lt_coe (n k : ℕ+) : (n : ℕ) < k ↔ n < k :=
  Iff.rfl
#align pnat.coe_lt_coe Pnat.coe_lt_coe

@[simp]
theorem pos (n : ℕ+) : 0 < (n : ℕ) :=
  n.2
#align pnat.pos Pnat.pos

theorem eq {m n : ℕ+} : (m : ℕ) = n → m = n :=
  Subtype.eq
#align pnat.eq Pnat.eq

theorem coe_injective : Function.Injective (fun (a : ℕ+) => (a : ℕ)) :=
  Subtype.coe_injective
#align pnat.coe_injective Pnat.coe_injective

@[simp]
theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 :=
  n.2.ne'
#align pnat.ne_zero Pnat.ne_zero

instance _root_.NeZero.pnat {a : ℕ+} : NeZero (a : ℕ) :=
  ⟨a.ne_zero⟩
#align pnat._root_.ne_zero.pnat pnat._root_.NeZero.pnat

theorem toPnat'_coe {n : ℕ} : 0 < n → (n.toPnat' : ℕ) = n :=
  succ_pred_eq_of_pos
#align pnat.to_pnat'_coe Pnat.toPnat'_coe

@[simp]
theorem coe_toPnat' (n : ℕ+) : (n : ℕ).toPnat' = n :=
  eq (toPnat'_coe n.pos)
#align pnat.coe_to_pnat' Pnat.coe_toPnat'

@[simp]
theorem one_le (n : ℕ+) : (1 : ℕ+) ≤ n :=
  n.2
#align pnat.one_le Pnat.one_le

@[simp]
theorem not_lt_one (n : ℕ+) : ¬n < 1 :=
  not_lt_of_le n.one_le
#align pnat.not_lt_one Pnat.not_lt_one

instance : Inhabited ℕ+ :=
  ⟨1⟩

-- Some lemmas that rewrite `pnat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp]
theorem mk_one {h} : (⟨1, h⟩ : ℕ+) = (1 : ℕ+) :=
  rfl
#align pnat.mk_one Pnat.mk_one

-- Porting note: no `norm_cast` due to eagerly elaborated coercions
theorem one_coe : ((1 : ℕ+) : ℕ) = 1 :=
  rfl
#align pnat.one_coe Pnat.one_coe

-- Porting note: no `norm_cast` due to eagerly elaborated coercions
@[simp]
theorem coe_eq_one_iff {m : ℕ+} : (m : ℕ) = 1 ↔ m = 1 :=
  Subtype.coe_injective.eq_iff' one_coe
#align pnat.coe_eq_one_iff Pnat.coe_eq_one_iff

instance : WellFoundedRelation ℕ+ :=
  measure (fun (a : ℕ+) => (a : ℕ))

/-- Strong induction on `ℕ+`. -/
def strongInductionOn {p : ℕ+ → Sort _} (n : ℕ+) : (∀ k, (∀ m, m < k → p m) → p k) → p n
  | IH => IH _ fun a _ => strongInductionOn a IH
termination_by _ => n.1

#align pnat.strong_induction_on Pnat.strongInductionOn

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
#align pnat.mod_div_aux Pnat.modDivAux

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
#align pnat.mod_div Pnat.modDiv

/-- We define `m % k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` This ensures that `m % k` is always positive.
-/
def mod (m k : ℕ+) : ℕ+ :=
  (modDiv m k).1
#align pnat.mod Pnat.mod

/-- We define `m / k` in the same way as for `ℕ` except that when `m = n * k` we take
  `m / k = n - 1`. This ensures that `m = (m % k) + k * (m / k)` in all cases. Later we
  define a function `div_exact` which gives the usual `m / k` in the case where `k` divides `m`.
-/
def div (m k : ℕ+) : ℕ :=
  (modDiv m k).2
#align pnat.div Pnat.div

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

#align pnat.mod_coe Pnat.mod_coe

theorem div_coe (m k : ℕ+) :
  (div m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) ((m : ℕ) / (k : ℕ)).pred ((m : ℕ) / (k : ℕ)) :=
  by
  dsimp [div, modDiv]
  cases (m : ℕ) % (k : ℕ) with
  | zero =>
    rw [if_pos rfl]
    rfl

  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl

#align pnat.div_coe Pnat.div_coe

/-- If `h : k | m`, then `k * (div_exact m k) = m`. Note that this is not equal to `m / k`. -/
def divExact (m k : ℕ+) : ℕ+ :=
  ⟨(div m k).succ, Nat.succ_pos _⟩
#align pnat.div_exact Pnat.divExact

end Pnat

/-
section CanLift

instance Nat.canLiftPnat : CanLift ℕ ℕ+ coe ((· < ·) 0) :=
  ⟨fun n hn => ⟨Nat.toPnat' n, Pnat.toPnat'_coe hn⟩⟩
#align nat.can_lift_pnat Nat.canLiftPnat

instance Int.canLiftPnat : CanLift ℤ ℕ+ coe ((· < ·) 0) :=
  ⟨fun n hn =>
    ⟨Nat.toPnat' (Int.natAbs n), by
      rw [coe_coe, Nat.toPnat'_coe, if_pos (Int.nat_abs_pos_of_ne_zero hn.ne'),
        Int.nat_abs_of_nonneg hn.le]⟩⟩
#align int.can_lift_pnat Int.canLiftPnat

end CanLift
-/
