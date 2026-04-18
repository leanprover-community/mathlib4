/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas R. Murrills
-/
module

public import Lean.Elab.Command
public import Lean.Syntax
public import Lean.Data.Lsp.Utf16
import Mathlib.Init
import Lean.Meta.Tactic.TryThis

/-!
# Utilities for suggesting attribute insertions

WIP.
-/

-- `getDeclsAfter` hasn't landed in mathlib yet, so recreate it here.

public section FromBatteries

namespace Lean

/--
If `pos` is a `Lean.Position`, then `pos.getDeclsAfter` returns the array of names of declarations
whose selection range begins in position at least `pos`. By using the `selectionRange`, which is
usually smaller than the `range`, we err on the side of including declarations when possible.

By default, this only inspects the local branch of the environment. This is compatible with being
used to find declarations from the current command in a linter, where we have already waited for
async tasks/parallel branches to complete. Further, since the environment exposed to linters does
not include constants added after the elaboration of the current command, it is safe to use this on
the command's start position without picking up later declarations.
-/
protected def Position.getDeclsAfter (env : Environment) (pos : Position)
    (asyncMode := EnvExtension.AsyncMode.local) : Array Name :=
  declRangeExt.getState env asyncMode |>.foldl (init := #[])
    fun acc name { selectionRange .. } =>
      if selectionRange.pos.lt pos then acc else acc.push name

/--
If `pos` is a `String.Pos.Raw`, then `pos.getDeclsAfter` returns the array of names of declarations
whose selection range begins in position at least `pos`. By using the `selectionRange`, which is
usually smaller than the `range`, we err on the side of including declarations when possible.

By default, this is intended for use in linters, where only the current environment branch needs to
be checked. See the docstring for `Lean.Position.getDeclsAfter` for details.
-/
@[inline] protected def _root_.String.Pos.Raw.getDeclsAfter (env : Environment) (map : FileMap)
    (pos : String.Pos.Raw) (asyncMode := EnvExtension.AsyncMode.local) : Array Name :=
  map.toPosition pos |>.getDeclsAfter env asyncMode

/-- Converts a `DeclarationRange` to a `Syntax.Range`. This assumes that the
`DeclarationRange` is sourced in the given `FileMap`. -/
def DeclarationRange.toSyntaxRange (map : FileMap) (range : DeclarationRange) : Syntax.Range :=
  ⟨map.ofPosition range.pos, map.ofPosition range.endPos⟩

/-- Yields the `Syntax.Range` for the declaration `decl` in the current file. If `decl` is not in
the current file, yields `none`.

By default, this provides the "selection range", which is usually the declaration's identifier or
e.g. the `instance` token for an unnamed instance. If `fullRange` is instead set to `true`, this
returns the full declaration range (which includes modifiers, such as the docstring). -/
@[inline] def findDeclarationSyntaxRange? {m : Type → Type} [Monad m] [MonadEnv m]
    [MonadLiftT BaseIO m]
    [MonadFileMap m] (decl : Name) (fullRange := false) : m (Option Syntax.Range) := do
  if (← getEnv).isImportedConst decl then return none
  let some ranges ← findDeclarationRanges? decl | return none
  return (if fullRange then ranges.range else ranges.selectionRange).toSyntaxRange (← getFileMap)

/-- Finds the declaration syntax, either a typical declaration or `lemma`, and returns it. Not the
best type signature or function behavior; there are many more ways to create declarations (e.g.
`to_additive`, meta things like `syntax`, etc.). Strictly temporary. -/
def findDeclarationSyntax? {m : Type → Type} [Monad m] [MonadEnv m] [MonadLiftT BaseIO m]
    [MonadFileMap m] (decl : Name) (enclosingStx : Syntax) :
    m (Option ((kind : SyntaxNodeKind) × TSyntax kind)) := do
  let some range ← findDeclarationSyntaxRange? decl true | return none
  for stx in enclosingStx.topDown do
    if stx.isOfKind ``Parser.Command.declaration then
      if stx.getRange? (canonicalOnly := true) |>.isEqSome range then
        return some ⟨``Parser.Command.declaration, ⟨stx⟩⟩
    else if stx.isOfKind `lemma then
      if stx.getRange? (canonicalOnly := true) |>.isEqSome range then
        return some ⟨`lemma, ⟨stx⟩⟩
  return none

open Elab Command
/-
def declModifiers (inline : Bool) := leading_parser
  optional docComment >>
  optional (Term.«attributes» >> if inline then skip else ppDedent ppLine) >>
  optional visibility >>
  optional «protected» >>
  optional («meta» <|> «noncomputable») >>
  optional «unsafe» >>
  optional («partial» <|> «nonrec»)
-/
/-- Takes the attribute string and figures out where and how to insert it. In the future we'd pass
the attribute syntax to be inserted instead of the already pretty-printed `insertedAttrStr`, and
pretty-print it relative to the other attributes, or something. -/
private def insertion (stx : TSyntax ``Parser.Command.declModifiersF) (declStart : String.Pos.Raw)
    (insertedAttrStr : String) : CoreM (Syntax.Range × String) :=
  match stx with
  | `(Parser.Command.declModifiersF|
      $[$doc]?
      $[$attrs]?
      $[$vis]?
      $[$protectedTk]?
      $[$metaOrNc]?
      $[$unsafeTk]?
      $[$partialOrNonRec]?) => do
    if let some attrs := attrs then
      match attrs with
      | `(Parser.Term.attributes| @[$attrs,*]) => do
        let some head := attrs.getElems[0]? | throwError "Empty attribute syntax"
        let some pos := head.raw.getPos? | throwError "No position info for {head}"
        return (⟨pos, pos⟩, s!"{insertedAttrStr}, ")
      | _ => throwIllFormedSyntax
    else -- No attribute syntax
      let startPosAfter : String.Pos.Raw :=
        (vis.bind (·.raw.getPos?)
          <|> protectedTk.bind (·.raw.getPos?)
          <|> metaOrNc.bind (·.raw.getPos?)
          <|> unsafeTk.bind (·.raw.getPos?)
          <|> partialOrNonRec.bind (·.raw.getPos?)).getD declStart
      if let some endOfDocstring := doc.bind (·.raw.getTailPos? true) then -- docstring exists
        return (⟨endOfDocstring, startPosAfter⟩, s!"\n@[{insertedAttrStr}]\n")
      else
        return (⟨startPosAfter, startPosAfter⟩, s!"@[{insertedAttrStr}]\n")
  | _ => throwIllFormedSyntax

/-- Suggests inserting the attribute syntax at the appropriate point inside the modifier syntax
`mods`, or else just before `declStartAfterMods` if no post-attribute mods exist. -/
def suggestAttrForDeclMods
    (attrStx : Array (TSyntax ``Parser.Term.attrInstance))
    (mods : TSyntax ``Parser.Command.declModifiersF)
    (declStartAfterMods : String.Pos.Raw) :
    CoreM Unit := do
  let attrStx ← attrStx.mapM fun stx =>
    -- bit of a hack, not a syntax category
    -- column three to account for `@[]` (not all cases, but still)
    return (← PrettyPrinter.ppCategory ``Parser.Term.attrInstance stx).pretty (column := 3)
  let attrStx := ", ".intercalate attrStx.toList
  let (range, sugg) ← insertion mods declStartAfterMods attrStx
  Meta.Tactic.TryThis.addSuggestion (.ofRange range) sugg

/-- For each `declName` appearing in `cmd`, suggests inserting the attribute syntax produced by
`mkAttrs declName cmd`, or warns if it can't. Note that `cmd` is the full command, not the
declaration syntax. -/
@[specialize mkAttrs] def insertAttrsOnDecls
    (mkAttrs : Name → Syntax → CommandElabM (Array (TSyntax ``Parser.Term.attrInstance)))
    (cmd : Syntax) : CommandElabM Unit := do
  let some pos := cmd.getPos? | return
  let decls := pos.getDeclsAfter (← getEnv) (← getFileMap)
  for decl in decls do
    let attrs ← mkAttrs decl cmd
    unless attrs.isEmpty do
      let some ⟨kind, stx⟩ ← findDeclarationSyntax? decl cmd
        | logWarning m!"`{.ofConstName decl}`: \
          need to insert `@[{attrs}]`, but couldn't find syntax"
      unless kind ∈ [`lemma, ``Parser.Command.declaration] do
        throwError "Can't handle syntax {stx} of kind {kind}"
      let some declStart := stx.raw[1].getPos?
        | throwError "Couldn't find start position of declaration {stx}"
      liftCoreM <| suggestAttrForDeclMods attrs ⟨stx.raw[0]⟩ declStart

end Lean
