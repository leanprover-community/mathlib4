/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean
import NoExpose.Paths
import NoExpose.SourceScan

/-!
# `NoExpose.Env` — env-walk pieces (enumeration + static refs)

Three responsibilities, all running inside a `Lean.withImportModules`
block opened by the `collect` orchestrator:

* **enumerate**: emit one record per "candidate" decl in the project's
  scope (a def whose body is in the exported view, isn't a compiler
  helper, isn't an instance whose exposure is automatic).
* **staticRefs**: per-(refModule, refName) cross-reference counts, with
  a `theorem_count` split for same-module rfl detection.
* **declRefs**: per-decl direct reference list, used downstream by
  `Report` for one-hop transitive closure.

This module does NOT `import Mathlib`; the exe links against just Lean
core + Lake so it builds in seconds.
-/

open Lean Core

namespace NoExpose

/-- Run a `CoreM α` against a fresh `Environment` populated by
importing `modules`. -/
def withImportModules {α : Type} (modules : Array Name) (run : CoreM α)
    (searchPath : Option SearchPath := none) (options : Options := {})
    (trustLevel : UInt32 := 0) (fileName := "") :
    IO α := unsafe do
  if let some sp := searchPath then searchPathRef.set sp
  Lean.withImportModules (modules.map ({ module := · })) options
    (trustLevel := trustLevel) fun env => do
      let ctx : Core.Context := { fileName, options, fileMap := default }
      let state : Core.State := { env }
      let (a, _) ← Core.CoreM.toIO run ctx state
      pure a

/-! ## Enumeration -/

/-- One row of the eventual `exposed.jsonl`. Each record represents
one source `@[expose]` occurrence intersected with one env decl whose
range falls inside it. `name`/`module` come from the env (so we don't
hand-parse identifiers); `line`/`col` are the decl's own start (used
by `edit`). `attrLine` is the line of the `@[expose]` text that covers
this decl; `sectionLine` is set iff the `@[expose]` came from a
section attribute (and points at the `@[expose] section` line). -/
structure DeclRecord where
  name : String
  kind : String
  «module» : String
  file : String
  line : Nat
  col : Nat
  «effect» : String
  attrLine : Nat
  sectionLine : Option Nat := none
  deriving Inhabited

/-- Suffixes Lean uses for compiler-generated structure/inductive
helpers; we exclude them since they aren't user-written `@[expose]`
candidates. -/
private def autoGenSuffixes : Array String := #[
  "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow", "ndrec",
  "ndrecOn", "recAux", "rec", "noConfusion", "noConfusionType", "sizeOf",
  "sizeOf_spec", "injEq"
]

/-- True if `name` is a compiler helper we should exclude from
enumeration. -/
def isAutoGen (env : Environment) (name : Name) : CoreM Bool := do
  if Lean.isAuxRecursor env name then return true
  if Lean.isNoConfusion env name then return true
  if (env.getProjectionFnInfo? name).isSome then return true
  if ← Lean.Meta.isMatcher name then return true
  if let .str _ last := name then
    if autoGenSuffixes.contains last then return true
  return false

/-- True if `name`'s body is in the *exported* view of `env`. -/
def isBodyExported (env : Environment) (name : Name) : Bool :=
  match (env.setExporting true).find? name with
  | some info => info.hasValue
  | none => false

/-- Map `Mathlib.Foo.Bar` → `"Mathlib/Foo/Bar.lean"`. -/
def moduleToPath (m : Name) : String :=
  String.intercalate "/" (m.toString.splitOn ".") ++ ".lean"

/-- Constant `name` lives in one of the project's modules — i.e. the
declaring module's name has one of `scopePrefix` as a `Name`-prefix. -/
private def isInScope (env : Environment) (scopePrefix : Array Name) (name : Name) :
    Option Name := do
  let idx ← env.getModuleIdxFor? name
  let mod := env.header.moduleNames[idx]!
  if scopePrefix.any fun p => p.isPrefixOf mod || p == mod then
    some mod
  else
    none

/-- Per-decl info we need to perform the source-occurrence × env-range
intersection: the project file the decl came from, its name/kind/etc.,
and the line range its declaration source spans. -/
private structure EnvDecl where
  name : Name
  kind : String
  «module» : Name
  file : String
  startLine : Nat
  endLine : Nat
  col : Nat
  isAbbrev : Bool

/-- Walk the env, returning every project-scope decl that could carry
`@[expose]`. The source-occurrence scanner will pick out which of these
are actually covered by an `@[expose]` attribute. -/
private def collectEnvDecls (scopePrefix : Array Name) : CoreM (Array EnvDecl) := do
  let env ← getEnv
  let mut out : Array EnvDecl := #[]
  for (name, info) in env.constants.toList do
    let .defnInfo defnVal := info | continue
    let some mod := isInScope env scopePrefix name | continue
    if name.hasMacroScopes then continue
    if name.isInternal then continue
    if ← isAutoGen env name then continue
    unless isBodyExported env name do continue
    let some ranges ← Lean.findDeclarationRanges? name | continue
    out := out.push {
      name
      kind := "def"
      «module» := mod
      file := moduleToPath mod
      startLine := ranges.range.pos.line
      endLine := ranges.range.endPos.line
      col := ranges.range.pos.column
      isAbbrev := defnVal.hints.isAbbrev
    }
  return out

/-- Source-occurrence-driven enumeration: scan each project file for
`@[expose]` text occurrences, intersect with env decl ranges, and emit
one `DeclRecord` per (occurrence, covered env decl) pair.

This replaces the previous "walk every body-exposed def, then classify
how it got exposed" approach. The new approach is honest about what
the tool can actually edit: by construction every record corresponds
to a literal `@[expose]` in source. -/
unsafe def enumerate (scopePrefix : Array Name) : CoreM (Array DeclRecord) := do
  let envDecls ← collectEnvDecls scopePrefix
  -- Group decls by their source file.
  let mut byFile : Std.HashMap String (Array EnvDecl) := {}
  for d in envDecls do
    byFile := byFile.insert d.file ((byFile.getD d.file #[]).push d)
  IO.eprintln s!"[no_expose enumerate] {envDecls.size} candidate env decls \
    across {byFile.size} files"
  -- For each file, scan source for `@[expose]` occurrences and
  -- intersect with the env decls in that file.
  let mut out : Array DeclRecord := #[]
  let mut filesDone : Nat := 0
  for (file, decls) in byFile do
    let path : System.FilePath := file
    unless ← System.FilePath.pathExists path do
      filesDone := filesDone + 1
      continue
    let text ← IO.FS.readFile path
    let occurrences := scanExposeOccurrences text
    -- Sort decls once by startLine for cheap binary-search-style lookup.
    let sortedDecls := decls.qsort fun a b => a.startLine < b.startLine
    for occ in occurrences do
      match occ.scope with
      | .decl =>
        -- The covered decl is the one whose range starts on the
        -- next line after `occ.attrLine` (allowing for the decl's
        -- modifiers spanning the attribute line itself).
        for d in sortedDecls do
          if d.startLine ≥ occ.attrLine && d.startLine ≤ occ.attrLine + 1 then
            out := out.push (declRecordOf d occ.attrLine none)
      | .section_ closeLine =>
        for d in sortedDecls do
          if d.startLine ≥ occ.attrLine && d.startLine ≤ closeLine then
            out := out.push (declRecordOf d occ.attrLine (some occ.attrLine))
    filesDone := filesDone + 1
    if filesDone % 500 == 0 then
      IO.eprintln s!"[no_expose enumerate] scanned {filesDone} files \
        ({out.size} records so far)"
  IO.eprintln s!"[no_expose enumerate] {out.size} records from {filesDone} files"
  return out
where
  declRecordOf (d : EnvDecl) (attrLine : Nat) (sectionLine : Option Nat) :
      DeclRecord := {
    name := d.name.toString
    kind := d.kind
    «module» := d.module.toString
    file := d.file
    line := d.startLine
    col := d.col
    «effect» := if d.isAbbrev then "noop-always-exported" else "exposed"
    attrLine
    sectionLine
  }

/-! ## Static references -/

/-- For each (referencing module, referenced name),
`(total_count, theorem_count)`. -/
abbrev RefMap := Std.HashMap (Nat × Name) (Nat × Nat)

/-- Walk every constant in env; aggregate by (refModule, refName). -/
def collectStaticRefs : CoreM RefMap := do
  let env ← getEnv
  let mut acc : RefMap := {}
  for (name, info) in env.constants.toList do
    let some refModIdx := env.getModuleIdxFor? name | continue
    if name.hasMacroScopes then continue
    if name.isInternal then continue
    let isThm := info matches .thmInfo _
    let refs := info.getUsedConstantsAsSet
    acc := refs.foldl (init := acc) fun acc referenced =>
      let key := (refModIdx, referenced)
      let (cTot, cThm) := acc.getD key (0, 0)
      acc.insert key (cTot + 1, if isThm then cThm + 1 else cThm)
  return acc

/-! ## JSON serialisation -/

def DeclRecord.toJsonLine (d : DeclRecord) : String :=
  let sectionField := match d.sectionLine with
    | none   => ""
    | some l => ",\"section_line\":" ++ toString l
  "{\"name\":\"" ++ jsonEscape d.name ++
  "\",\"kind\":\"" ++ d.kind ++
  "\",\"module\":\"" ++ jsonEscape d.module ++
  "\",\"file\":\"" ++ jsonEscape d.file ++
  "\",\"line\":" ++ toString d.line ++
  ",\"col\":" ++ toString d.col ++
  ",\"effect\":\"" ++ d.effect ++
  "\",\"attr_line\":" ++ toString d.attrLine ++
  sectionField ++ "}"

/-- Write a `RefMap` aggregation as one JSONL record per pair. -/
def writeStaticRefs (env : Environment) (acc : RefMap)
    (h : IO.FS.Handle) : IO Unit := do
  for ((modIdx, decl), (count, thmCount)) in acc.toList do
    let some mod := env.header.moduleNames[modIdx]? | continue
    let file := moduleToPath mod
    h.putStrLn <|
      "{\"file\":\"" ++ jsonEscape file ++
      "\",\"decl\":\"" ++ jsonEscape decl.toString ++
      "\",\"count\":" ++ toString count ++
      ",\"theorem_count\":" ++ toString thmCount ++
      ",\"category\":\"static/ref\"}"

/-- Write per-decl direct reference lists for transitive closure. -/
def writeDeclRefs (env : Environment) (h : IO.FS.Handle) : IO Unit := do
  for (name, info) in env.constants.toList do
    if name.hasMacroScopes then continue
    if name.isInternal then continue
    if (env.getModuleIdxFor? name).isNone then continue
    let refs := info.getUsedConstantsAsSet
    if refs.isEmpty then continue
    let body : String := String.intercalate "," <|
      refs.foldl (init := []) (fun acc n => ("\"" ++ jsonEscape n.toString ++ "\"") :: acc)
    h.putStrLn <|
      "{\"decl\":\"" ++ jsonEscape name.toString ++
      "\",\"refs\":[" ++ body ++ "]}"

end NoExpose
