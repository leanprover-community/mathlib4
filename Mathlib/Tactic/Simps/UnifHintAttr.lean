/-
Copyright (c) 2025 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public meta import Lean.AddDecl
public meta import Lean.Meta.UnificationHint

/-!
# The `@[unifHint]` attribute

This file defines the `@[unifHint]` attribute. When applied to an equality lemma
`theorem foo (args) : lhs = rhs`, it generates an auxiliary `abbrev` declaration
whose value is the equality proposition and registers it as a `@[unification_hint]`.
This allows Lean's unifier to recognize `lhs` as definitionally equal to `rhs`
even under reducible transparency.
-/

public meta section

open Lean Meta

/-- `addUnifHintFromLemma declName kind` creates a `@[unification_hint]` declaration derived from
the equality lemma `declName`. The lemma must have type `∀ args, lhs = rhs`. It generates an
auxiliary `abbrev` named `declName.unifHint` whose value is the equality proposition, and
registers it as a unification hint. -/
def addUnifHintFromLemma (declName : Name) (kind : AttributeKind) : MetaM Unit := do
  let info ← getConstInfo declName
  let hintDeclName := .str declName "unifHint"
  forallTelescope info.type fun args body => do
    let some _ := body.eq? | throwError
      "@[unifHint] can only be applied to equality lemmas, but {.ofConstName declName} \
       has type{indentExpr info.type}"
    let hintValue ← mkLambdaFVars args body
    let hintType ← mkForallFVars args (mkSort Level.zero)
    addDecl <| .defnDecl {
      name := hintDeclName
      levelParams := info.levelParams
      type := hintType
      value := hintValue
      hints := .abbrev
      safety := .safe }
    addUnificationHint hintDeclName kind

/-- The `@[unifHint]` attribute can be applied to an equality lemma to generate a unification hint
for the equality it proves. Concretely, `@[unifHint] theorem foo (args) : lhs = rhs` generates an
auxiliary `abbrev foo.unifHint (args) : Prop := lhs = rhs` and registers it as a
`@[unification_hint]`. This allows Lean's unifier to unify `lhs` with `rhs` (and thus prove goals
of the form `lhs = rhs` by `with_reducible rfl`) even when `lhs` does not reduce to `rhs` under
reducible transparency. -/
initialize registerBuiltinAttribute {
  name := `unifHint
  descr := "Generate a `@[unification_hint]` declaration from an equality lemma."
  add := fun declName stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    discard <| addUnifHintFromLemma declName kind |>.run
}
