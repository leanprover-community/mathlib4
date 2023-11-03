/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum.Core
import Mathlib.Algebra.CharZero.Defs

/-!
# Helper functions for synthesizing `CharZero` expressions.
-/

set_option autoImplicit true

open Lean Meta Qq

namespace Mathlib.Meta.NormNum

/-- Helper function to synthesize a typed `CharZero α` expression given `Ring α`. -/
def inferCharZeroOfRing {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM Q(CharZero $α) :=
  return ← synthInstanceQ (q(CharZero $α) : Q(Prop)) <|>
    throwError "not a characteristic zero ring"

/-- Helper function to synthesize a typed `CharZero α` expression given `Ring α`, if it exists. -/
def inferCharZeroOfRing? {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

/-- Helper function to synthesize a typed `CharZero α` expression given `AddMonoidWithOne α`. -/
def inferCharZeroOfAddMonoidWithOne {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
  return ← synthInstanceQ (q(CharZero $α) : Q(Prop)) <|>
    throwError "not a characteristic zero AddMonoidWithOne"

/-- Helper function to synthesize a typed `CharZero α` expression given `AddMonoidWithOne α`, if it
exists. -/
def inferCharZeroOfAddMonoidWithOne? {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) :
      MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

/-- Helper function to synthesize a typed `CharZero α` expression given `DivisionRing α`. -/
def inferCharZeroOfDivisionRing {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
  return ← synthInstanceQ (q(CharZero $α) : Q(Prop)) <|>
    throwError "not a characteristic zero division ring"

/-- Helper function to synthesize a typed `CharZero α` expression given `DivisionRing α`, if it
exists. -/
def inferCharZeroOfDivisionRing? {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

end Mathlib.Meta.NormNum
