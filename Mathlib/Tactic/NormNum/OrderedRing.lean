/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum.Core
import Mathlib.Algebra.Order.Field.Defs

/-!
# Helper functions for working with ordered rings.
-/

set_option autoImplicit true

open Lean Meta Qq

namespace Mathlib.Meta.NormNum

/-- Helper function to synthesize a typed `OrderedSemiring α` expression. -/
def inferOrderedSemiring (α : Q(Type u)) : MetaM Q(OrderedSemiring $α) :=
  return ← synthInstanceQ (q(OrderedSemiring $α) : Q(Type u)) <|>
    throwError "not an ordered semiring"

/-- Helper function to synthesize a typed `OrderedRing α` expression. -/
def inferOrderedRing (α : Q(Type u)) : MetaM Q(OrderedRing $α) :=
  return ← synthInstanceQ (q(OrderedRing $α) : Q(Type u)) <|> throwError "not an ordered ring"

/-- Helper function to synthesize a typed `LinearOrderedField α` expression. -/
def inferLinearOrderedField (α : Q(Type u)) : MetaM Q(LinearOrderedField $α) :=
  return ← synthInstanceQ (q(LinearOrderedField $α) : Q(Type u)) <|>
    throwError "not a linear ordered field"

end Mathlib.Meta.NormNum
