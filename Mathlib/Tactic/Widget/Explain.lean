/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Init
import ProofWidgets.Component.HtmlDisplay

/-!

# Explanation Widgets

This file defines some simple widgets wrapped in a tactic, term and command elaborator
that display nicely rendered markdown in the infoview.

Example tactic usage:
```
example : True := by
  explain "This is the first step."
  explain "This is the last step." in
    exact trivial
```
Placing the cursor on each line results will render the explanation in the infoview.

Example term usage:
```
example : Nat := explain "This is zero" in
  0
```
Placing the cursor on the term will render the explanation in the infoview.


Example command usage:
```
#explain "This is an explanation."
```
This will render the provided text in the infoview.


# Implementation

This code uses `MarkdownDisplay` from `ProofWidgets`, and thus supports
markdown and latex via mathjax.

-/

namespace Mathlib.Tactic

open Lean Elab ProofWidgets ProofWidgets.Jsx

/-- Displays the markdown source in `md` in a widget when the cursor is placed at `stx`. -/
def displayMarkdown (md : String) (stx : Syntax) : CoreM Unit := do
  let html : Html := <MarkdownDisplay contents={md}/>
  Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
    stx

/-- Syntax for the `explain` tactic elaborator. -/
syntax (name := explainTacStx) "explain" str ("in" ppIndent(tactic))? : tactic

/-- Syntax for the `explain` term elaborator. -/
syntax (name := explainTermStx) "explain" str "in" ppIndent(term) : term

/-- Syntax for the `#explain` command. -/
syntax (name := explainCmdStx) "#explain" str : command

open Tactic in
/-- A tactic that adds an explanation widget in markdown form. -/
@[tactic explainTacStx]
def elabExplainTac : Tactic := fun stx =>
  match stx with
  | `(tactic|explain%$tk $s:str) => do
    displayMarkdown s.getString tk
  | `(tactic|explain%$tk $s:str in $t:tactic) => do
    displayMarkdown s.getString tk
    evalTactic t
  | _ => throwUnsupportedSyntax

open Term in
/-- A term elaborator that adds an explanation widget in markdown form. -/
@[term_elab explainTermStx]
def elabExplainTerm : TermElab := fun stx type? =>
  match stx with
  | `(explain%$tk $s:str in $t:term) => do
    displayMarkdown s.getString tk
    elabTerm t type?
  | _ => throwUnsupportedSyntax

open Command in
/-- A command that displays an explanation widget in markdown form. -/
@[command_elab explainCmdStx]
def elabExplainCommand : CommandElab := fun stx =>
  match stx with
  | `(command|#explain%$tk $s:str) => do
    Command.liftCoreM <| displayMarkdown s.getString tk
  | _ => throwUnsupportedSyntax

end Mathlib.Tactic
