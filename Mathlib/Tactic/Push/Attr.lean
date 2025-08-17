/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Init

/-!
# The `@[push]` attribute for the `push`, `push_neg` and `pull` tactics

This file defines the `@[push]` attribute, so that it can be used without importing
the tactic itself.
-/

namespace Mathlib.Tactic.Push

open Lean Meta

/-- The type for a constant to be pushed by `push`. -/
inductive Head where
| name (const : Name)
| lambda
| forall
deriving Inhabited, BEq

/-- Converts a `Head` to a string. -/
def Head.toString : Head → String
  | .name const => const.toString
  | .lambda => "fun _ => ·"
  | .forall => "∀ _, ·"

/-- Returns the head of an expression. -/
def Head.ofExpr? (e : Expr) : Option Head :=
  match e with
  | .app f _ => f.getAppFn.constName?.map .name
  | .lam .. => some .lambda
  | .forallE .. => some .forall
  | _ => none

/-- The `push` environment extension -/
initialize pushExt : SimpleScopedEnvExtension SimpTheorem (DiscrTree SimpTheorem) ←
  registerSimpleScopedEnvExtension {
    initial  := {}
    addEntry := fun d e => d.insertCore e.keys e
  }

/--
Checks if the theorem is suitable for the `pull` tactic. That is,
check if it is of the form `f as = b` where `b` contains the head `f`.
-/
def isPullThm (declName : Name) (inv : Bool) : MetaM (Option Head) := do
  let cinfo ← getConstInfo declName
  forallTelescope cinfo.type fun _ type => do
    let some (lhs, rhs) := type.eqOrIff? | return none
    let (lhs, rhs) := if inv then (rhs, lhs) else (lhs, rhs)
    let some head := Head.ofExpr? lhs | return none
    if (findHead rhs head).isSome then
      return head
    return none
where
  /-- Check if the expression has the head in any subexpression-/
  findHead (e : Expr) : Head → Option Expr
  | .name n => e.find? fun | .const n' _ => n' == n | _ => false
  | .lambda => e.find? (· matches .lam ..)
  | .forall => e.find? (· matches .forallE ..)

/-- A theorem for the `pull` tactic -/
abbrev PullTheorem := SimpTheorem × Head

/-- The `pull` environment extension -/
initialize pullExt : SimpleScopedEnvExtension PullTheorem (DiscrTree PullTheorem) ←
  registerSimpleScopedEnvExtension {
    initial  := {}
    addEntry := fun d e => d.insertCore e.1.keys e
  }

/--
The `push` attribute is used to tag lemmas that "push" a constant into an expression.

For example:
```lean
@[push] theorem not_not (p : Prop) : ¬¬p ↔ p

@[push] theorem not_imp (p q : Prop) : ¬(p → q) ↔ p ∧ ¬q

@[push] theorem not_iff (p q : Prop) : ¬(p ↔ q) ↔ (p ∧ ¬q) ∨ (¬p ∧ q)
```
-/
syntax (name := pushAttr) "push" (" ←" <|> " <-")? (ppSpace prio)? : attr

@[inherit_doc pushAttr]
initialize registerBuiltinAttribute {
  name := `pushAttr
  descr := "attribute for push"
  add := fun declName stx kind => MetaM.run' do
    let inv := !stx[1].isNone
    let prio ← getAttrParamOptPrio stx[2]
    for thm in ← mkSimpTheoremFromConst declName (inv := inv) do
      pushExt.add thm
    if let some head ← isPullThm declName inv then
      for thm in ← mkSimpTheoremFromConst declName (inv := !inv) do
        pullExt.add (thm, head)
}

end Mathlib.Tactic.Push
