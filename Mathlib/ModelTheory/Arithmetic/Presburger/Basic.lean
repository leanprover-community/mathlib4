/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.ModelTheory.Semantics

/-!
# Presburger arithmetic

This file defines the first-order language of Presburger arithmetic as (0,1,+).

## Main Definitions

- `FirstOrder.Language.presburger`: the language of Presburger arithmetic.

## TODO

- Generalize `presburger.sum` (maybe also `NatCast` and `SMul`) for classes like
  `FirstOrder.Language.IsOrdered`.
- Define the theory of Presburger arithmetic and prove its properties (quantifier elimination,
  completeness, etc).
-/

variable {α : Type*}

namespace FirstOrder

/-- The type of Presburger arithmetic functions, defined as (0, 1, +). -/
inductive presburgerFunc : ℕ → Type
  | zero : presburgerFunc 0
  | one : presburgerFunc 0
  | add : presburgerFunc 2
  deriving DecidableEq

/-- The language of Presburger arithmetic, defined as (0, 1, +). -/
def Language.presburger : Language :=
  { Functions := presburgerFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

namespace Language.presburger

variable {t t₁ t₂ : presburger.Term α}

instance : Zero (presburger.Term α) where
  zero := Constants.term .zero

instance : One (presburger.Term α) where
  one := Constants.term .one

instance : Add (presburger.Term α) where
  add := Functions.apply₂ .add

instance : NatCast (presburger.Term α) where
  natCast := Nat.unaryCast

@[simp, norm_cast] theorem natCast_zero : (0 : ℕ) = (0 : presburger.Term α) := rfl

@[simp, norm_cast] theorem natCast_succ (n : ℕ) : (n + 1 : ℕ) = (n : presburger.Term α) + 1 := rfl

instance : SMul ℕ (presburger.Term α) where
  smul := nsmulRec

@[simp] theorem zero_nsmul : 0 • t = 0 := rfl

@[simp] theorem succ_nsmul {n : ℕ} : (n + 1) • t = n • t + t := rfl

/-- Summation over a finite set of terms in Presburger arithmetic.

It is defined via choice, so the result only makes sense when the structure satisfies
commutativity (see `realize_sum`). -/
noncomputable def sum {β : Type*} (s : Finset β) (f : β → presburger.Term α) : presburger.Term α :=
  (s.toList.map f).sum

variable {M : Type*} {v : α → M}

section

variable [Zero M] [One M] [Add M]

instance : presburger.Structure M where
  funMap
  | .zero, _ => 0
  | .one, v => 1
  | .add, v => v 0 + v 1

@[simp] theorem funMap_zero {v} :
    Structure.funMap (L := presburger) (M := M) presburgerFunc.zero v = 0 := rfl

@[simp] theorem funMap_one {v} :
    Structure.funMap (L := presburger) (M := M) presburgerFunc.one v = 1 := rfl

@[simp] theorem funMap_add {v} :
    Structure.funMap (L := presburger) (M := M) presburgerFunc.add v = v 0 + v 1 := rfl

@[simp] theorem realize_zero : Term.realize v (0 : presburger.Term α) = 0 := rfl

@[simp] theorem realize_one : Term.realize v (1 : presburger.Term α) = 1 := rfl

@[simp] theorem realize_add :
    Term.realize v (t₁ + t₂) = Term.realize v t₁ + Term.realize v t₂ := rfl

end

@[simp] theorem realize_natCast [AddMonoidWithOne M] {n : ℕ} :
    Term.realize v (n : presburger.Term α) = n := by
  induction n with simp [*]

@[simp] theorem realize_nsmul [AddMonoidWithOne M] {n : ℕ} :
    Term.realize v (n • t) = n • Term.realize v t := by
  induction n with simp [*, add_nsmul]

@[simp] theorem realize_sum [AddCommMonoidWithOne M]
    {β : Type*} {s : Finset β} {f : β → presburger.Term α} :
    Term.realize v (sum s f) = ∑ i ∈ s, Term.realize v (f i) := by
  classical
  simp only [sum]
  conv => rhs; rw [← s.toList_toFinset, List.sum_toFinset _ s.nodup_toList]
  generalize s.toList = l
  induction l with simp [*]

end FirstOrder.Language.presburger
