import Mathlib.Tactic.RelCongr.Core

namespace Mathlib.Tactic.Rel
open Lean Meta

/-- See if the term is `a = b` and the goal is `a ∼ b` or `b ∼ a`, with `∼` reflexive. -/
@[rel_congr_forward] def exactRefl : RelCongrForwardExt where
  eval h goal := do
    let m ← mkFreshExprMVar none
    goal.exact (← mkAppOptM ``Eq.subst #[h, m])
    goal.rfl

/-- See if the term is `a < b` and the goal is `a ≤ b`. -/
@[rel_congr_forward] def exactLeOfLt : RelCongrForwardExt where
  eval h goal := do goal.exact (← mkAppM ``le_of_lt #[h])

/-- The term is `a ∼ b` with `∼` symmetric and the goal is `b ∼ a`. -/
@[rel_congr_forward] def symmExact : RelCongrForwardExt where
  eval h goal := do (← goal.symm).exact h

@[rel_congr_forward] def exact : RelCongrForwardExt where
  eval := MVarId.exact
