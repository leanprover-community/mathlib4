/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

open Lean Elab Meta Std Linter Parser Term Command

namespace Mathlib.Linter

register_option linter.deprecatedSimpLemma : Bool := {
  defValue := true
  descr := "enable the deprecatedSimpLemma linter"
}

/-- Extract the attributes from a `Syntax` term.  -/
private def extractAttributes (stx : Syntax) :
     (Array <| TSyntax ``attrInstance) :=
  match stx with
  | `(declModifiers| $_? @[$[$atts],*] $_? $_? $_? $_?) => atts
  | _ => #[]

/-- Check if a `Syntax` term corresponds to a deprecation tag. -/
def isDeprecationAttr (stx : Syntax) : Bool :=
  match stx with
  | `(attr| deprecated $[$id?]? $[$text?]? $[(since := $since?)]?) => true
  | _ => false

/-- Check if a `Syntax` term corresponds to a simp tag. -/
def isSimpAttr (stx : Syntax) : Bool :=
  match stx with
  | `(attr| simp $[$pre]? $[$_]? $[$prio]?) => true
  | _ => false


/-- The deprecated simp lemma linter flags when a deprecated declaration has the `simp` attribute. -/
def deprecatedSimpLemmaLinter : Linter where run stx := do
  unless getLinterValue linter.deprecatedSimpLemma (← getLinterOptions) do return
  if (← get).messages.hasErrors then return
  unless [``Lean.Parser.Command.declaration, `lemma].contains stx.getKind do return
  let some modifiersStx := stx.find? (·.isOfKind ``Parser.Command.declModifiers) | pure ()
  match modifiersStx.find? isDeprecationAttr, modifiersStx.find? isSimpAttr with
  | some _, some _ =>
    Lean.logInfo "Deprecated results should not have the simp attribute"
  | _, _ => return

initialize addLinter deprecatedSimpLemmaLinter

end Linter

end Mathlib
