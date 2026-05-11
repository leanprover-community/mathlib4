/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

module
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header

/-!
# Linter against deprecated simp lemmas

We prefer to avoid using `deprecated` lemmas, so these should not be tagged with the `simp`
attribute. This linter is designed to flag such occurences.
-/

meta section

open Lean Elab Meta Std Linter Parser Term Command

namespace Mathlib.Linter

register_option linter.deprecatedSimpLemma : Bool := {
  defValue := true
  descr := "enable the deprecatedSimpLemma linter"
}

/-- Extract the attributes from a `Syntax` term. -/
private def extractAttributes (stx : Syntax) : Array (TSyntax `Lean.Parser.Term.attrInstance) :=
  match stx with
  | `(declModifiers| $(_)? @[$[$atts],*] $(_)? $(_)? $(_)? $(_)?) => atts
  | _ => panic! s!"No attributes found in {stx}."

private def getAttributesFromDecl {m : Type → Type} [Monad m] [MonadEnv m] [MonadResolveName m]
    [MonadError m] [MonadMacroAdapter m] [MonadRecDepth m] [MonadTrace m] [MonadOptions m]
    [AddMessageContext m] [MonadLiftT IO m] [MonadFinally m][MonadLog m] (stx : Syntax) :
    m (Array Attribute) := do
  let some modifiersStx := stx.find? (·.isOfKind ``Parser.Command.declModifiers)
    | throwError s!"{stx} does not have any declaration modifiers."
  elabAttrs (extractAttributes modifiersStx)

/-- The deprecated simp lemma linter flags when a deprecated declaration has the `simp` attribute. -/
def deprecatedSimpLemmaLinter : Linter where run stx := do
  unless getLinterValue linter.deprecatedSimpLemma (← getLinterOptions) do return
  if (← get).messages.hasErrors then return
  unless [``Lean.Parser.Command.declaration, `lemma].contains stx.getKind do return
  let attributeNames := (← getAttributesFromDecl stx).map (·.name)
  unless attributeNames.contains `simp && attributeNames.contains `deprecated do return
  Lean.logInfo "Deprecated declarations should not have the simp attribute"

initialize addLinter deprecatedSimpLemmaLinter

end Linter

end Mathlib
