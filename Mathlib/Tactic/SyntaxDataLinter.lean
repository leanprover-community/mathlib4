/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.App
import Lean.Elab.Command
import Lean.Linter.Util
import Std.Data.Array.Merge

/-!
#  The "syntax data" linter
-/

/-- The rev-lexicographic order on pairs. -/
def revLexOrd {α β} [Ord α] [Ord β] : Ord (α × β) where
  compare p1 p2 := match compare p1.2 p2.2 with
    | .eq => compare p1.1 p2.1
    | o   => o

/-- print a range as the pair `(beginning, end)`. -/
local instance : ToString String.Range where
  toString rg := s!"{(rg.start, rg.stop)}"

open Lean Elab Parser Command

namespace Mathlib.Linter

/-- The "syntax data" linter prints range information for "syntax data". -/
register_option linter.syntaxData : Bool := {
  defValue := true
  descr := "enable the syntax data linter"
}

namespace syntaxData

/--  Checks if a declaration has a doc-string as part of its syntax.
This misses out on doc-strings added post-hoc, such as via `add_decl_doc`. -/
partial
def hasDocs : Syntax → Bool
  | .node _ ``docComment _ => true
  | .node _ _ args => (args.map hasDocs).any (·)
  | _ => false

/-- Extract all `declId`s from the given syntax.
Typically, there is at most one such `declId`: the name of a `theorem/lemma/def/instance/...`. -/
partial
def getIds : Syntax → Array Syntax
  | .node _ `Std.Tactic.Alias.alias args => #[args[2]!]
  | .node _ ``Command.export args => #[args[3]![0]]
  | stx@(.node _ _ args) =>
    ((args.map fun a => getIds a).foldl (· ++ ·) #[stx]).filter (·.getKind == ``declId)
  | _ => default

abbrev exclusions : HashSet SyntaxNodeKind := HashSet.empty
  -- Scott's `isSubstantive` filter
  |>.insert `null
  |>.insert ``cdot
  |>.insert ``cdotTk
  |>.insert ``Lean.Parser.Term.byTactic
  |>.insert ``Lean.Parser.Tactic.tacticSeq
  |>.insert ``Lean.Parser.Tactic.tacticSeq1Indented
  |>.insert ``Lean.Parser.Tactic.«tactic_<;>_»
  |>.insert ``Lean.Parser.Tactic.paren
  -- further exclusions
  |>.insert `by
  |>.insert `«;»
  |>.insert `«]»
  |>.insert `«<;>»

/-- scans the input `InfoTree` and accumulates `Expr`s and `Range`s in a `HashSet`. -/
partial
def getTerms :
    InfoTree → HashSet (Expr × String.Range) → HashSet (Expr × String.Range)
  | .node k args, col =>
    let rargs := (args.map (getTerms · col)).toArray
    Id.run do
    let mut tot := col
    for r in rargs do
      for (a, rg) in r do
          tot := tot.insert (a, rg)
    if let .ofTermInfo i := k then
      let stx := i.stx
      if let .original .. := stx.getHeadInfo then  -- make sure that the syntax is `original`
        if let some rg := stx.getRange? then  -- and that it has a `Range`
          tot := tot.insert (i.expr, rg)
      tot
    else tot
  | .context _ t, col => getTerms t col
  | _, _ => default

/-- scans the input `InfoTree` and accumulates `SyntaxNodeKind`s and `Range`s in a `HashSet`. -/
partial
def getRanges :
    InfoTree → HashSet (SyntaxNodeKind × String.Range) → HashSet (SyntaxNodeKind × String.Range)
  | .node k args, col =>
    let rargs := (args.map (getRanges · col)).toArray
    Id.run do
    let mut tot := col
    for r in rargs do
      for (a, rg) in r.toArray do
        if !exclusions.contains a then
          tot := tot.insert (a, rg)
    if let .ofTacticInfo i := k then
      let stx := i.stx
      if let .original .. := stx.getHeadInfo then  -- make sure that the syntax is `original`
        if let some rg := stx.getRange? then  -- and that it has a `Range`
          tot := tot.insert (stx.getKind, rg)
      tot
    else tot
  | .context _ t, col => getRanges t col
  | _, _ => default

/-- Gets the value of the `linter.syntaxData` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.syntaxData o

def _root_.List.condense {α β} [BEq α] [Inhabited β] [BEq β] [Hashable β] (i : List (α × β)) :
    HashMap β (Array α) :=
  let init := (i.map Prod.fst).toArray
  init.groupByKey (fun a => (i.lookup a).get!)

/-- The main implementation of the terminal refine linter. -/
def syntaxDataLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterHash (← getOptions) && (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  let _ : Ord SyntaxNodeKind := ⟨(compare ·.toString ·.toString)⟩
  let _ : Ord Expr := ⟨fun e f => compare (toString e) (toString f)⟩
  let _ : Ord String.Range := ⟨(compare ·.start.byteIdx ·.start.byteIdx)⟩
  let _ := @lexOrd
  let mut tacMsg := .empty
  let mut exprMsg := .empty
  for t in trees.toArray do
    exprMsg := getTerms t exprMsg
    tacMsg := getRanges t tacMsg
  let tacDat  := tacMsg.toArray.qsort (compare · ·|>.isLT)
  let _exprDat := exprMsg.toArray.qsort (compare · ·|>.isLT)
  let exprDat := (exprMsg.toList.map fun (a, b) => (b, a)).condense.toArray.qsort
    (fun (a, _) (b, _) => compare a b|>.isLT)
  let exprDat := exprDat.map fun (a, b) => (a, b.sortAndDeduplicate)
  if tacDat != #[] then
    let ids ← (getIds stx).mapM fun d => resolveGlobalConstNoOverload d[0]
    let docs? := if ! hasDocs stx then "-- no docs" else ""
    Linter.logLint linter.syntaxData stx <|
      m!"{ids} {docs?}\nTactic info:" ++ indentD m!"{tacDat}" ++
                       "\nExpr info:" ++ indentD m!"{exprDat}"

initialize addLinter syntaxDataLinter
