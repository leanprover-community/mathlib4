/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.ModelTheory.Semantics

/-!
# Presburger arithmetic

This file defines the first-order language of Presburger arithmetic as (0,S,+).

## Main Definitions

- `FirstOrder.Language.presburger`: the language of Presburger arithmetic.

## TODO

- Generalize `presburger.finsum` (maybe also `presburger.natCast` and `presburger.nsmul`) for
  classes like `FirstOrder.Language.IsOrdered`.
- Define the theory of Presburger arithmetic and prove its properties (quantifier elimination,
  completeness, etc).

-/

variable {α : Type*}

namespace FirstOrder

/-- The type of Presburger arithmetic functions, defined as (0,S,+) -/
inductive presburgerFunc : ℕ → Type
  | zero : presburgerFunc 0
  | succ : presburgerFunc 1
  | add : presburgerFunc 2
  deriving DecidableEq

/-- The language of Presburger arithmetic, defined as (0,S,+). -/
def Language.presburger : Language :=
  { Functions := presburgerFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

namespace Language.presburger

variable {t t₁ t₂ : presburger.Term α}

instance : Zero (presburger.Term α) where
  zero := Constants.term .zero

/-- `presburger.succ t` is the successor of `t`, applying `presburgerFunc.succ` on `t`. -/
def succ (t : presburger.Term α) := Functions.apply₁ presburgerFunc.succ t

instance : Add (presburger.Term α) where
  add := Functions.apply₂ .add

protected def natCast : ℕ → presburger.Term α
| 0 => 0
| n + 1 => succ (presburger.natCast n)

instance : NatCast (presburger.Term α) where
  natCast := presburger.natCast

@[simp] theorem natCast_zero : NatCast.natCast 0 = (0 : presburger.Term α) := rfl

@[simp] theorem natCast_succ {n : ℕ} : NatCast.natCast (n + 1) = succ (n : presburger.Term α) := rfl

protected def nsmul : ℕ → presburger.Term α → presburger.Term α
| 0, _ => 0
| n + 1, t => presburger.nsmul n t + t

instance : SMul ℕ (presburger.Term α) where
  smul := presburger.nsmul

@[simp] theorem zero_nsmul : 0 • t = 0 := rfl

@[simp] theorem succ_nsmul {n : ℕ} : (n + 1) • t = n • t + t := rfl

/-- Summation over a finite set of terms in Presburger arithmetic.
  
  It is defined via choice, and therefore the result only makes sense when the structure satisfies
  commutativity (see `realize_finsum`). -/
noncomputable def finsum {β : Type*} [Fintype β] (f : β → presburger.Term α) : presburger.Term α :=
  ((Finset.univ : Finset β).toList.map f).foldr (· + ·) 0

variable {M : Type*} {v : α → M}

section

variable [Zero M] [One M] [Add M]

instance : presburger.Structure M where
  funMap
  | .zero, _ => 0
  | .succ, v => v 0 + 1
  | .add, v => v 0 + v 1

@[simp] theorem funMap_zero {v} :
    @Structure.funMap presburger M _ _ presburgerFunc.zero v = 0 := rfl

@[simp] theorem funMap_succ {v} :
    @Structure.funMap presburger M _ _ presburgerFunc.succ v = v 0 + 1 := rfl

@[simp] theorem funMap_add {v} :
    @Structure.funMap presburger M _ _ presburgerFunc.add v = v 0 + v 1 := rfl

@[simp] theorem realize_zero : Term.realize v (0 : presburger.Term α) = 0 := rfl

@[simp] theorem realize_succ : Term.realize v (succ t) = Term.realize v t + 1 := rfl

@[simp] theorem realize_add :
    Term.realize v (t₁ + t₂) = Term.realize v t₁ + Term.realize v t₂ := rfl

end

@[simp] theorem realize_natCast [AddMonoidWithOne M] {n : ℕ} :
    Term.realize v (n : presburger.Term α) = n := by
  induction n with simp [*]

@[simp] theorem realize_nsmul [AddMonoidWithOne M] {n : ℕ} :
    Term.realize v (n • t) = n • Term.realize v t := by
  induction n with simp [*, _root_.zero_nsmul, add_nsmul]

@[simp] theorem realize_finsum [AddCommMonoidWithOne M]
    {β : Type*} [Fintype β] {f : β → presburger.Term α} :
    Term.realize v (finsum f) = ∑ i, Term.realize v (f i) := by
  classical
  simp only [finsum, Finset.sum_eq_fold]
  conv => rhs; rw [←Finset.toList_toFinset Finset.univ]
  have hnodup := Finset.nodup_toList (Finset.univ : Finset β)
  generalize (Finset.univ : Finset β).toList = l at *
  induction l with
  | nil => rfl
  | cons =>
    rw [List.nodup_cons, ←List.mem_toFinset] at hnodup
    simp [*, Finset.fold_insert (β := M) (op := (· + ·)) hnodup.1]

end FirstOrder.Language.presburger
