/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Init
import Lean.Elab.Tactic.Basic
import Lean.PrettyPrinter
import Lean.Elab.SyntheticMVars

/-!
# `#check` tactic

This module defines a tactic version of the `#check` command.
While `#check t` is similar to `have := t`, it is a little more convenient
since it elaborates `t` in a more tolerant way and so it can be possible to get a result.
For example, `#check` allows metavariables.
-/

open Lean Elab Command PrettyPrinter Delaborator in
/-- The `#check'` command is like `#check`, but only prints explicit arguments in the signature
(i.e., omitting implicit and typeclass arguments). -/
elab tk:"#check' " name:ident : command => runTermElabM fun _ => do
  for c in (← realizeGlobalConstWithInfos name) do
    addCompletionInfo <| .id name name.getId (danglingDot := false) {} none
    let info ← getConstInfo c
    let delab : Delab := do
      delabForallParamsWithSignature fun binders type => do
        let binders := binders.filter fun binder => binder.raw.isOfKind ``Parser.Term.explicitBinder
        return ⟨← `(declSigWithId| $(mkIdent c) $binders* : $type)⟩
    logInfoAt tk <| .ofFormatWithInfosM (PrettyPrinter.ppExprWithInfos (delab := delab) info.type)

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

/-- Core routine for the `#check` tactic: show a signature for `#check term`, assuming `term`
is an identifier. Info messages are placed at `tk`.
`c` contains the resolved name of `term`, in case there are several. -/
def checkInner (tk : Syntax) (term : Term) (c : Name) : TacticM Unit := do
  addCompletionInfo <| .id term c (danglingDot := false) {} none
  logInfoAt tk <| MessageData.signature c
  return

open Lean Elab Command PrettyPrinter Delaborator in
def checkPrimeInner (tk : Syntax) (term : Term) (c : Name) : TacticM Unit := do
  addCompletionInfo <| .id term c (danglingDot := false) {} none
  let info ← getConstInfo c
  let delab : Delab := do
    delabForallParamsWithSignature fun binders type => do
      let binders := binders.filter fun binder => binder.raw.isOfKind ``Parser.Term.explicitBinder
      return ⟨← `(declSigWithId| $(mkIdent c) $binders* : $type)⟩
  logInfoAt tk <| .ofFormatWithInfosM (PrettyPrinter.ppExprWithInfos (delab := delab) info.type)
  return

/-- Workhorse method for the `#check` and `#check'` tactic.
This does all the set-up; the actual behaviour is governed by the function `inner` passed in. -/
def elabCheckTacticInner (tk : Syntax) (ignoreStuckTC : Bool) (term : Term)
    (inner : Syntax → Term → Name → TacticM Unit): TacticM Unit :=
  withoutModifyingStateWithInfoAndMessages <| withMainContext do
    if let `($_:ident) := term then
      -- show signature for `#check ident`
      try
        for c in (← realizeGlobalConstWithInfos term) do
          inner tk term c
      catch _ => pure ()  -- identifier might not be a constant but constant + projection
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := ignoreStuckTC)
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    let type ← inferType e
    if e.isSyntheticSorry then
      return
    logInfoAt tk m!"{e} : {type}"

/--
Tactic version of `Lean.Elab.Command.elabCheck`.
Elaborates `term` without modifying tactic/elab/meta state.
Info messages are placed at `tk`.
-/
def elabCheckTactic (tk : Syntax) (ignoreStuckTC : Bool) (term : Term) : TacticM Unit :=
  elabCheckTacticInner tk ignoreStuckTC term checkInner

/--
Tactic version of the `#check'` command:
like `#check`, but only shows explicit arguments in the signature.
Elaborates `term` without modifying tactic/elab/meta state.
Info messages are placed at `tk`.
-/
def elabCheckPrimeTactic (tk : Syntax) (ignoreStuckTC : Bool) (term : Term) : TacticM Unit :=
  elabCheckTacticInner tk ignoreStuckTC term checkPrimeInner

/--
The `#check t` tactic elaborates the term `t` and then pretty prints it with its type as `e : ty`.

If `t` is an identifier, then it pretty prints a type declaration form
for the global constant `t` instead.
Use `#check (t)` to pretty print it as an elaborated expression.

Like the `#check` command, the `#check` tactic allows stuck typeclass instance problems.
These become metavariables in the output.
-/
elab tk:"#check " colGt term:term : tactic => elabCheckTactic tk true term

/--
The `#check' t` tactic elaborates the term `t` and then pretty prints it with its type as `e : ty`.
In contrast to `#check t`, we only pretty-print explicit arguments, and omit implicit or type class
arguments.

If `t` is an identifier, then it pretty prints a type declaration form
for the global constant `t` instead.
Use `#check' (t)` to pretty print it as an elaborated expression.

Like the `#check'` command, the `#check'` tactic allows stuck typeclass instance problems.
These become metavariables in the output.
-/
elab tk:"#check' " colGt term:term : tactic => elabCheckPrimeTactic tk true term

end Mathlib.Tactic
