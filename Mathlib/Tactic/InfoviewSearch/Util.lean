/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Init
public import ProofWidgets.Data.Html
public import ProofWidgets.Component.MakeEditLink

/-!
## Utilities for the `infoview_suggest` framework
-/

public meta section

namespace InfoviewSearch

open Lean Meta Widget ProofWidgets Jsx Server

/-- The information required for pasting a suggestion into the editor -/
structure PasteInfo where
  /-- The current document -/
  doc : FileWorker.EditableDocument
  /-- The range that should be replaced.
  In tactic mode, this should be the range of the suggestion tactic (e.g. `hint`).
  In infoview mode, the start and end of the range should both be the cursor position. -/
  replaceRange : Lsp.Range

/-- The information required for pasting a rewrite tactic suggestion into the editor. -/
structure RwPasteInfo extends PasteInfo where
  /-- The occurence at which to rewrite, to be used as `nth_rw n`. -/
  occ : Option Nat
  /-- The hypothesis at which to rewrite, to be used as `at h`. -/
  hyp? : Option Name

/-- Prepend an insert button to `html`, aligning the button with the first line in `html`.
Clicking the insert button will insert the tactic into the editor.
Hovering over the insert button will show the tactic string.

This should always be used in combination with `mkInsertList`.

TODO(Requires an addition to ProofWidgets): Make the button recursively hoverable. -/
def mkInsert (tactic : String) (pasteInfo : PasteInfo) (html : Html) : Html :=
  let button := Html.ofComponent MakeEditLink
    (.ofReplaceRange pasteInfo.doc.meta pasteInfo.replaceRange tactic)
    #[<div
      className={"codicon codicon-insert"}
      -- The small offset of `0.15em` makes the button visually aligned with the following line.
      style={json% { position: "relative", top: "0.15em" }}
      title={tactic} />];
  -- The margin of `1em` visually separates consecutive suggestions.
  <li style={json% { display: "flex", "align-items": "flex-start", "margin-bottom": "1em" }}>
    <div style={json% { "margin-right": "0.5em" }}> {button} </div> {html}
  </li>

/-- Create a list of tactic suggestions given by `mkInsert`. -/
def mkInsertList (header : Html) (htmls : Array Html) : Html :=
  <details «open»={true}>
    <summary className="mv2 pointer"> {header} </summary>
    {.element "ul" #[("style", json% { "padding-left": 0, "list-style": "none"})] htmls}
  </details>

end InfoviewSearch
