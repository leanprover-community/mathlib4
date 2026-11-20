/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:  David Thrane Christiansen, Michael Rothgang
-/
module

public meta import Lean.DocString
public meta import Lean.Elab.DocString
meta import Lean.Parser.Term.Doc

/-! # Verso code to include one docstring in another

This module defines the `insertDocstringOf` command: into a verso doc-string, writing
`{insertDocstringOf foo}` inside a verso doc-string inserts the doc-string of
declaration `foo` in the current environment, as a separate paragraph.
If `foo` does not exist or has no doc-string, it throws an error.

This can be used, for example, in custom elaborators or custom notation, to make the elaborator
or notation doc-string also explain the main notation.
-/

open Lean Doc Elab

public section

open Doc Parser in
/-- Writing `{insertDocstringOf foo}` inside a verso doc-string inserts the doc-string of
declaration `foo` in the current environment, as a separate paragraph.
If `foo` does not exist or has no doc-string, it throws an error.
-/
@[doc_command] meta def insertDocstringOf (n : Ident) :
    DocM <| Block ElabInline ElabBlock := do
  let doc ← realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let some docStr ← findInternalDocString? env doc
    | throwError "No doc-string for `{.ofConstName doc}`"
  let body : Block ElabInline ElabBlock := match docStr with
    | .inl t => .para #[.text t]
    | .inr v => .concat (v.text ++ v.subsections.flatMap Part.content)
  -- Copy over any `recommended_spellings` information.
  let spellings : Array (Block ElabInline ElabBlock) :=
    (Term.Doc.getRecommendedSpellingsForName env doc).map fun s ↦
      let info := match s.additionalInformation? with
        | some i => #[.text s!" ({i.trimAscii})"]
        | none => #[]
      .para (#[.text "The recommended spelling of ", .code s.notation,
              .text " in identifiers is ", .code s.recommendedSpelling] ++ info ++ #[.text "."])
  -- Copy over information in the `tactic_alt` and `tactic_extra` attributes.
  let mut tacticExtras : Array (Block ElabInline ElabBlock) := #[]
  if let some canonical := Tactic.Doc.alternativeOfTactic env doc then
    tacticExtras := tacticExtras.push <|
      .para #[.text "This is an alternative form of the tactic ", .code canonical.toString,
              .text "."]
  let alts ← Tactic.Doc.aliases doc
  unless alts.isEmpty do
    let names := alts.toArray.qsort (·.toString < ·.toString)
    let inlines : Array (Inline ElabInline) :=
      names.foldl (init := #[]) fun acc a ↦
        (if acc.isEmpty then acc else acc.push (.text ", ")).push (.code a.toString)
    tacticExtras := tacticExtras.push <|
      .para (#[.text "Alternative forms of this tactic: "] ++ inlines)
  let exts := Tactic.Doc.getTacticExtensions env doc
  unless exts.isEmpty do
    tacticExtras := tacticExtras.push <| .para #[.bold #[.text "Extensions:"]]
    tacticExtras := tacticExtras.push <|
      .ul (exts.map fun e ↦ { contents := #[.para #[.text e]] })
  return .concat (#[body] ++ spellings)
