/-
Copyright (c) 2022 Brendan Murphy, Scott Morrison, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy, Scott Morrison, Kyle Miller
-/
import Mathlib.Util.AddRelatedDecl
import Mathlib.Lean.Meta.Simp
import Mathlib.Lean.Meta

/-!
# The `reassocM` attribute

Adding `@[reassocM]` to a lemma named `F` of shape `∀ .., f = g`,
where `f g : m α` for some monad `m : Type u → Type v`
will create a new lemmas named `F_assoc` of shape
`∀ .. {β : Type u} (h : α → m β), f >>= h = g >>= h`
but with the conclusions simplified used the monad laws
(this may not recover the original lemma unless `m` is a `LawfulMonad`)

This is useful for generating lemmas which the simplifier can use even on expressions
that are already right associated.

There is also a term elaborator `reassocM_of% t` for use within proofs.
-/

open Lean Meta Elab Tactic
open Mathlib.Tactic

namespace LawfulMonad

universe u v

theorem eq_bind (m : Type u → Type v) [Monad m] {α} {x y : m α} (w : x = y)
  {β} (f : α → m β) : x >>= f = y >>= f := by rw [w]

/-- Simplify an expression using only(?) the monad laws. -/
def monadSimp (e : Expr) : MetaM Simp.Result :=
  getAllSimpDecls `monad_norm >>=
  (simpOnlyNames . e (config := { decide := false }))

/--
Given an equation `x = y` between `m α`-computations in (possibly after a `∀` binder),
produce the equation `∀ {β} (h : α → m β), x >>= h = y >>= h`,
but with binds fully right associated and `>>= pure`'s removed.
-/
def reassocMExpr (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do
    let ety ← instantiateMVars (← inferType e)
    let some (ty, _, _) := ety.eq? | throwError "Expecting an equality, not{indentD ety}"
    let .app m _ := ty | throwError "Expecting an equality for a monad, not{indentD ty}"
    simpType monadSimp (← mkAppM ``eq_bind #[m, e])) e

/-- Syntax for the `reassoc` attribute -/
syntax (name := reassocM) "reassocM" (" (" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr

initialize registerBuiltinAttribute {
  name := `reassocM
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| reassocM $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`reassocM` can only be used as a global attribute"
    addRelatedDecl src "_assoc" ref stx? fun type value levels => do
      pure (← reassocMExpr (← mkExpectedTypeHint value type), levels)
  | _ => throwUnsupportedSyntax }

open Term in
/--
`reassocM_of% t`, where `t` is
an equation `x = y` between `m α`-computations in (possibly after a `∀` binder),
produce the equation `∀ {β} (h : α → m β), x >>= h = y >>= h`,
but with binds fully right associated and `>>= pure`'s removed.
-/
elab "reassocM_of% " t:term : term => do
  reassocMExpr (← elabTerm t none)

end LawfulMonad
