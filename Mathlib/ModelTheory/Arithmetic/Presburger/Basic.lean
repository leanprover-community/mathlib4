/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.ModelTheory.Algebra.Classes

/-!
# Presburger arithmetic

This file defines the first-order language of Presburger arithmetic as (0,1,+).

## Main Definitions

- `FirstOrder.Language.presburger`: the language of Presburger arithmetic.

## TODO

- Define the theory of Presburger arithmetic and prove its properties (quantifier elimination,
  completeness, etc).
-/

@[expose] public section

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

instance : ZeroConstant presburger where
  zero := presburgerFunc.zero

instance : OneConstant presburger where
  one := presburgerFunc.one

instance : AddFunction presburger where
  add := presburgerFunc.add

@[simp] theorem zero_def : presburgerFunc.zero = Constants.zero (L := presburger) := rfl

@[simp] theorem one_def : presburgerFunc.one = Constants.one (L := presburger) := rfl

@[simp] theorem add_def : presburgerFunc.add = Functions.add (L := presburger) := rfl

open Structure

class CompatibleStructure (M : Type*) [Zero M] [One M] [Add M]
    extends presburger.Structure M, CompatibleZero presburger M, CompatibleOne presburger M,
      CompatibleAdd presburger M

instance {M : Type*} [Zero M] [One M] [Add M] : presburger.Structure M where
  funMap
  | .zero, _ => 0
  | .one, v => 1
  | .add, v => v 0 + v 1

instance {M : Type*} [Zero M] [One M] [Add M] : CompatibleStructure M where
  funMap_zero _ := rfl
  funMap_one _ := rfl
  funMap_add _ := rfl

end FirstOrder.Language.presburger
