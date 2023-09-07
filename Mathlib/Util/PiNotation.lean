/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Std.Util.ExtendedBinder

/-! # Pi type notation

Provides the `Π x : α, β x` notation as an alternative to Lean 4's built-in
`(x : α) → β x` notation. To get all non-`∀` pi types to pretty print this way
then do `open scoped PiNotation`.

The notation also accepts extended binders, like `Π x ∈ s, β x` for `Π x, x ∈ s → β x`.
-/

namespace PiNotation
open Lean.Parser Term
open Lean.PrettyPrinter.Delaborator

/-- Dependent function type (a "pi type"). The notation `Π x : α, β x` can
also be written as `(x : α) → β x`. -/
-- A direct copy of forall notation but with `Π`/`Pi` instead of `∀`/`Forall`.
@[term_parser]
def piNotation := leading_parser:leadPrec
  unicodeSymbol "Π" "Pi" >>
  many1 (ppSpace >> (binderIdent <|> bracketedBinder)) >>
  optType >> ", " >> termParser

/-- Dependent function type (a "pi type"). The notation `Π x ∈ s, β x` is
short for `Π x, x ∈ s → β x`. -/
-- A copy of forall notation from `Std.Util.ExtendedBinder` for pi notation
syntax "Π " binderIdent binderPred ", " term : term

macro_rules
  | `(Π $x:ident $pred:binderPred, $p) => `(Π $x:ident, satisfies_binder_pred% $x $pred → $p)
  | `(Π _ $pred:binderPred, $p) => `(Π x, satisfies_binder_pred% x $pred → $p)

/-- Since pi notation and forall notation are interchangeable, we can
parse it by simply using the pre-existing forall parser. -/
@[macro PiNotation.piNotation] def replacePiNotation : Lean.Macro
  | .node info _ args => return .node info ``Lean.Parser.Term.forall args
  | _ => Lean.Macro.throwUnsupported

/-- Override the Lean 4 pi notation delaborator with one that uses `Π`.
Note that this takes advantage of the fact that `(x : α) → p x` notation is
never used for propositions, so we can match on this result and rewrite it. -/
@[scoped delab forallE]
def delabPi : Delab := whenPPOption Lean.getPPNotation do
  let stx ← delabForall
  -- Replacements
  let stx : Term ←
    match stx with
    | `($group:bracketedBinder → $body) => `(Π $group:bracketedBinder, $body)
    | _ => pure stx
  -- Merging
  match stx with
  | `(Π $group, Π $groups*, $body) => `(Π $group $groups*, $body)
  | _ => pure stx

end PiNotation
