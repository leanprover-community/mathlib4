/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public meta import Lean.Meta.UnificationHint
public import Mathlib.Init

/-!
# The `unificationHint` linter

A unification hint `unif_hint h xs where a₁ ≟ b₁ … aₙ ≟ bₙ ⊢ lhs ≟ rhs` tells the unifier that
`lhs` and `rhs` are definitionally equal once the constraints `aᵢ ≟ bᵢ` are solved. When a hint is
declared, Lean only checks that its two sides unify, which they may do by identifying variables of
the hint ([lean4#8982](https://github.com/leanprover/lean4/issues/8982)). For example, with
`F α β := α → β`, the hint `F α β ≟ (β' → α')` with the constraints `α ≟ α'` and `β ≟ β'` is
accepted, because its two sides unify once `α` and `β` are identified.

The `unificationHint` environment linter checks every unification hint as a proposition: once each
constraint `x ≟ t` or `t ≟ x` on a variable `x` of the hint is solved by replacing `x` with `t`, the
two sides of the hint must be definitionally equal. The kernel decides this: the elaborator would
consult the unification hints themselves.
-/

meta section

open Lean Meta

namespace Mathlib.Linter

/-- Whether `declName` is registered as a unification hint, in the current scope or in the scope of
some namespace. -/
def isUnificationHint (env : Environment) (declName : Name) : Bool :=
  (unificationHintExtension.getState env).discrTree.containsValueP (· == declName) ||
    (unificationHintExtension.ext.getState env).scopedEntries.map.fold
      (fun found _ entries ↦ found || entries.any (·.val == declName)) false

/-- The constraints `(aᵢ, bᵢ)` and the two sides `(lhs, rhs)` of a unification hint with body
`a₁ = b₁ → ⋯ → aₙ = bₙ → lhs = rhs`, read as `Lean.Meta.addUnificationHint` reads them. -/
def decodeUnificationHint : Expr → Option (List (Expr × Expr) × Expr × Expr)
  | .forallE _ d b _ => do
    let (_, a, a') ← d.eq?
    guard !b.hasLooseBVars
    let (cs, sides) ← decodeUnificationHint b
    return ((a, a') :: cs, sides)
  | e => do
    let (_, lhs, rhs) ← e.eq?
    return ([], lhs, rhs)

/-- Solves the constraints `cs` of a unification hint with variables `xs` in order, by substitution:
a constraint `x ≟ t` or `t ≟ x`, where `x` is a variable that occurs neither in `t` nor in the type
of a variable, is solved by replacing `x` with `t` in the constraints and in `lhs` and `rhs`, and a
constraint `t ≟ t` is solved as it stands. Returns `lhs` and `rhs` after these replacements, and the
constraints not solved this way. -/
def solveBySubstitution (xs : Array Expr) (cs : List (Expr × Expr)) (lhs rhs : Expr) :
    MetaM (Expr × Expr × Array (Expr × Expr)) := do
  let canReplace (x t : Expr) : MetaM Bool := do
    unless x.isFVar && !t.containsFVar x.fvarId! do return false
    xs.allM fun y ↦ return !(← inferType y).containsFVar x.fvarId!
  let assignment? (a b : Expr) : MetaM (Option (Expr × Expr)) := do
    if (← canReplace b a) then return some (b, a)
    if (← canReplace a b) then return some (a, b)
    return none
  let mut cs := cs.toArray
  let mut lhs := lhs
  let mut rhs := rhs
  let mut unsolved := #[]
  for i in [:cs.size] do
    let (a, b) := cs[i]!
    if a == b then continue
    match ← assignment? a b with
    | none => unsolved := unsolved.push (a, b)
    | some (x, t) =>
      let replace (e : Expr) := e.replaceFVar x t
      cs := cs.map fun (c, d) ↦ (replace c, replace d)
      lhs := replace lhs
      rhs := replace rhs
  return (lhs, rhs, unsolved)

/-- The `unificationHint` linter checks every unification hint as a proposition: once its
constraints `x ≟ t` on variables `x` of the hint are solved by replacing `x` with `t`, the two sides
of the hint must be definitionally equal, as the kernel decides. A constraint that is not solved
this way is left out, so a hint that needs such a constraint to hold is reported too. To silence
such a report on a correct hint, name the hint and add `attribute [nolint unificationHint] name`
after it. -/
@[env_linter] public def unificationHint : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "all unification hints hold definitionally."
  errorsFound := "FOUND UNIFICATION HINTS WHOSE TWO SIDES ARE NOT DEFINITIONALLY EQUAL."
  test declName := do
    let env ← getEnv
    let some (.defnInfo info) := env.find? declName | return none
    unless isUnificationHint env declName do return none
    lambdaTelescope info.value fun xs body ↦ do
      let some (cs, lhs, rhs) := decodeUnificationHint body | return none
      let (lhs, rhs, unsolved) ← solveBySubstitution xs cs lhs rhs
      let unused := if unsolved.isEmpty then m!"" else
        let shown := MessageData.andList <| unsolved.toList.map fun (a, b) ↦ m!"`{a} ≟ {b}`"
        m!"\nThe check leaves out the constraints not solved by substitution: {shown}."
      match Kernel.isDefEq env (← getLCtx) lhs rhs with
      | .ok true => return none
      | .ok false => return some (← addMessageContextFull m!"once its constraints are solved \
          by substitution, its two sides{indentExpr lhs}\nand{indentExpr rhs}\nare not \
          definitionally equal.{unused}")
      | .error e => return some (← addMessageContextFull m!"the kernel fails to compare its two \
          sides{indentExpr lhs}\nand{indentExpr rhs}\n{e.toMessageData (← getOptions)}")

end Mathlib.Linter
