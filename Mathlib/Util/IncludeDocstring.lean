/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:  David Thrane Christiansen, Michael Rothgang
-/
module

public meta import Lean.DocString
public meta import Lean.Elab.DocString

/-! # Verso code to include one docstring in another

This module defines the `insertDocstringOf` command: into a verso doc-string, writing
`{insertDocstringOf foo}` inside a verso doc-string inserts the doc-string of
declaration `foo` in the current environment, as a separate paragraph.
If `foo` does not exist or has no doc-string, it throws an error.

This can be used, for example, in custom elaborators to provide custom notation.
-/

open Lean Doc Elab

public section

open Doc in
/-- Writing `{insertDocstringOf foo}` inside a verso doc-string inserts the doc-string of
declaration `foo` in the current environment, as a separate paragraph.
If `foo` does not exist or has no doc-string, it throws an error.
-/
@[doc_command] meta def _root_.insertDocstringOf (n : Ident) :
    DocM <| Block ElabInline ElabBlock := do
  let doc ← realizeGlobalConstNoOverloadWithInfo n
  let some docStr ← findInternalDocString? (← getEnv) doc
    | throwError "No doc-string for `{.ofConstName doc}`"
  match docStr with
  | .inl t => return .para #[.text t]
  | .inr v => return .concat v.text
