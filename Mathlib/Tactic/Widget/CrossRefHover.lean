/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import Lean.Server.Rpc.Basic
public meta import Lean.Elab.Command
public meta import Mathlib.Tactic.CrossRef.Fetch
public meta import ProofWidgets.Component.HtmlDisplay
public meta import ProofWidgets.Component.OfRpcMethod

/-!
# A live info-view widget for `@[stacks]`, `@[kerodon]`, and `@[wikidata]`

When `Mathlib.Tactic.CrossRefAttribute` attaches a cross-reference attribute
to a declaration, it now also attaches a panel widget to the attribute's
syntax range. Place the cursor inside `@[wikidata Q12345]` (or one of the
sibling attributes) and the info view will fetch the upstream label and
description and render them — including a clickable link to the source page.

The fetch happens on-demand via an RPC call from the widget to the Lean
server, which shells out to `curl`. We deliberately do **not** fetch at
attribute-elaboration time: that would make every build hit the network,
and offline builds would have to stub it out. The trade-off is that the
first hover after opening a file pauses briefly while the request runs.

If `curl` isn't on `PATH`, or the upstream site is unreachable, the widget
shows an error message rather than blocking the server.
-/

public meta section

namespace Mathlib.CrossRef

open Lean Server Elab ProofWidgets

/-- Props passed to the cross-reference hover widget. -/
structure CrossRefHoverProps where
  /-- The short database name (`"stacks"`, `"kerodon"`, or `"wikidata"`). -/
  database : String
  /-- The tag identifier (`"01AB"`, `"Q42"`, …). -/
  tag : String
  /-- The author's optional comment on the attribute, if any. -/
  comment : String := ""
  deriving RpcEncodable

open scoped ProofWidgets.Jsx in
/-- Render the result of a snippet fetch as HTML for the info view. -/
private def renderOutcome (db : Database) (tag : String) (comment : String) :
    SnippetOutcome → Html
  | .ok title description =>
    let titleHtml : Html :=
      if title.isEmpty then <span/>
      else <span className="b mr1">{.text title}</span>
    let descHtml : Html :=
      if description.isEmpty then <span/>
      else <span>{.text description}</span>
    let commentHtml : Html :=
      if comment.isEmpty then <span/>
      else <div className="i mt1 gray">"author note: " {.text comment}</div>
    let url : String := databaseURL db ++ tag
    let linkText : String := s!"{databaseLabel db} {tag} ↗"
    Html.element "div" #[("className", "pa2")] #[
      <div>{titleHtml} {descHtml}</div>,
      <div className="mt1">
        <a href={url} target="_blank">{.text linkText}</a>
      </div>,
      commentHtml
    ]
  | .missing =>
    let url : String := databaseURL db ++ tag
    Html.element "div" #[("className", "pa2 red")] #[
      .text s!"⚠ This {db.name} tag is not present on {databaseLabel db}: ",
      <a href={url} target="_blank">{.text s!"{tag} ↗"}</a>
    ]
  | .network reason =>
    Html.element "div" #[("className", "pa2 orange")] #[
      .text s!"Could not reach {databaseLabel db}: {reason}. \
              (Is curl on PATH? Are we offline?)"
    ]

open scoped ProofWidgets.Jsx in
/-- The RPC method behind the cross-reference hover widget. It runs once on
the server when the widget mounts; results are not cached on the server
(the script in PR 1 of this stack honours `CROSSREF_CACHE_DIR` for batch
usage). -/
@[server_rpc_method]
def CrossRefHoverPanel.rpc (props : CrossRefHoverProps) :
    RequestM (RequestTask Html) :=
  RequestM.asTask do
    let some db := Database.ofName? props.database
      | return <span className="red">{.text s!"unknown database '{props.database}'"}</span>
    let outcome ← fetchSnippet db props.tag
    return renderOutcome db props.tag props.comment outcome

/-- The info-view widget rendered when the cursor sits on the syntax of a
`@[stacks ...]`, `@[kerodon ...]`, or `@[wikidata ...]` attribute. It fetches
the upstream label/description on the server via `CrossRefHoverPanel.rpc` and
renders the result (or an error) as HTML in the info view. -/
@[widget_module]
def CrossRefHoverPanel : Component CrossRefHoverProps :=
  mk_rpc_widget% CrossRefHoverPanel.rpc

end Mathlib.CrossRef
