/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa
-/
module

public meta import Mathlib.Tactic.Linter.Header  -- shake: keep
public import Lean.Parser.Command

/-!
# The "DocString" style linter

The "DocString" linter validates style conventions regarding doc-string formatting.
-/
set_option backward.defeqAttrib.useBackward true

meta section

open Lean Elab Linter

namespace Mathlib.Linter

/--
The "DocString" linter validates style conventions regarding doc-string formatting.
-/
public register_option linter.style.docString : Bool := {
  defValue := false
  descr := "enable the style.docString linter"
}

/--
The "empty doc string" warns on empty doc-strings.
-/
public register_option linter.style.docString.empty : Bool := {
  defValue := true
  descr := "enable the style.docString.empty linter"
}

/--
The `docStringVerso` linter warns on docstrings that cannot be parsed by Verso.
Since this linter only checks syntax, not semantics, it is no assurance that complying docstrings
are actually accepted by Verso.
-/
public register_option linter.style.docStringVerso : Bool := {
  defValue := false
  descr := "enable the style.docStringVerso linter"
}

/--
Extract all `declModifiers` from the input syntax. We later extract the `docstring` from it,
but we avoid extracting directly the `docComment` node, to skip `#adaptation_note`s.
-/
public def getDeclModifiers : Syntax → Array Syntax
  | s@(.node _ kind args) =>
    (if kind == ``Parser.Command.declModifiers then #[s] else #[]) ++ args.flatMap getDeclModifiers
  | _ => #[]

/--
Currently, this function simply removes `currIndent` spaces after each `\n`
in the input string `docString`.

If/when the `docString` linter expands, it may take on more string processing.
-/
def deindentString (currIndent : Nat) (docString : String) : String :=
  let indent : String := String.ofList ('\n' :: List.replicate currIndent ' ')
  docString.replace indent " "

open Parser in
/--
Try to parse `docComment` as a Verso docstring, and report any parse errors.

`fileName` is the file where this docstring is defined (default: the file currently being
elaborated).

This is a copy of the first half of `versoDocStringFromString`, which also does elaboration
(but here we only report parse errors).
-/
def checkVersoSyntax (fileName : Option String := none) (docComment : String) :
    Elab.TermElabM (Array (String.Pos.Raw × SyntaxStack × Error)) := do
  let fileName := fileName.getD (← getFileName)
  let env ← getEnv
  let ictx : InputContext := .mk docComment fileName
  let text := ictx.fileMap
  let pmctx : ParserModuleContext := {
    env,
    options := ← getOptions,
    currNamespace := (← getCurrNamespace),
    openDecls := (← getOpenDecls)
  }
  let s := mkParserState docComment
  let s := Doc.Parser.document.run ictx pmctx (getTokenTable env) s
  return s.allErrors

namespace Style

@[inherit_doc Mathlib.Linter.linter.style.docString]
def docStringLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.style.docString (← getLinterOptions) ||
      getLinterValue linter.style.docString.empty (← getLinterOptions) ||
      getLinterValue linter.style.docStringVerso (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let fm ← getFileMap
  for declMods in getDeclModifiers stx do
    -- `docStx` extracts the `Lean.Parser.Command.docComment` node from the declaration modifiers.
    -- In particular, this ignores parsing `#adaptation_note`s.
    let docStx := declMods[0][0]

    let some pos := docStx.getPos? | continue
    let currIndent := fm.toPosition pos |>.column

    if docStx.isMissing then continue -- this is probably superfluous, thanks to `some pos` above.
    -- `docString` contains e.g. trailing spaces before the `-/`, but does not contain
    -- any leading whitespace before the actual string starts.
    let docString ← try getDocStringText ⟨docStx⟩ catch _ => continue
    if docString.trimAscii.isEmpty then
      Linter.logLintIf linter.style.docString.empty docStx m!"warning: this doc-string is empty"
      continue
    -- `startSubstring` is the whitespace between `/--` and the actual doc-string text.
    let startSubstring := match docStx with
      | .node _ _ #[(.atom si ..), _] => si.getTrailing?.getD default
      | _ => default
    -- We replace all line-breaks followed by `currIndent` spaces with a single space.
    let start := deindentString currIndent startSubstring.toString
    if !#["\n", " "].contains start then
      let startRange := {start := startSubstring.startPos, stop := startSubstring.stopPos}
      Linter.logLintIf linter.style.docString (.ofRange startRange)
        s!"error: doc-strings should start with a single space or newline"

    let deIndentedDocString := deindentString currIndent docString

    let docTrim := deIndentedDocString.trimAsciiEnd.copy
    let tail := docTrim.length
    -- `endRange` creates an 0-wide range `n` characters from the end of `docStx`
    let endRange (n : Nat) : Syntax := .ofRange
      {start := docStx.getTailPos?.get!.unoffsetBy ⟨n⟩, stop := docStx.getTailPos?.get!.unoffsetBy ⟨n⟩}
    if docTrim.takeEnd 1 == ",".toSlice then
      Linter.logLintIf linter.style.docString (endRange (docString.length - tail + 3))
        s!"error: doc-strings should not end with a comma"
    if tail + 1 != deIndentedDocString.length then
      Linter.logLintIf linter.style.docString (endRange 3)
        s!"error: doc-strings should end with a single space or newline"
    -- Check for verso syntax, but only if it is not already enabled.
    -- If Verso is already enabled for docstrings, then this check would be superfluous.
    if !doc.verso.get (← getOptions) &&
        getLinterValue linter.style.docStringVerso (← getLinterOptions) then do
      let errs ← Command.liftTermElabM (checkVersoSyntax (docComment := docString))
      for (pos, stxStack, err) in errs do
        Linter.logLint linter.style.docStringVerso stxStack.back m!"{err}"

initialize addLinter docStringLinter

/-- Lint module docs for Verso syntax errors.

Verso syntax in declaration docstrings is already handled by the `docStringLinter`. -/
def moduleDocVersoLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.style.docStringVerso (← getLinterOptions) do
    return
  -- Check for verso syntax, but only if it is not already enabled.
  -- If Verso is already enabled for module docs, then this check would be superfluous.
  let opts ← getOptions
  if (doc.verso.module.get? opts).getD (doc.verso.get opts) then return
  if (← get).messages.hasErrors then
    return
  let some moduleDoc := (match stx with
  | s@(.node _ ``Parser.Command.moduleDoc args) => some s
  | _ => none) | return
  try
    let docString ← getDocStringText ⟨moduleDoc⟩
    let errs ← Command.liftTermElabM (checkVersoSyntax (docComment := docString))
    for (pos, stxStack, err) in errs do
      Linter.logLint linter.style.docStringVerso stxStack.back m!"{err}"
  catch _ => return

initialize addLinter moduleDocVersoLinter

end Style

end Mathlib.Linter
