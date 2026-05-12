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

/-- One row of the eventual `exposed.jsonl`. `name` and `module` are
stringified inside `enumerate` so the record carries no references
back into the imported environment after `withImportModules` closes.
`exposeSource` is filled in by `augmentAndWrite` after the env walk
closes; the env walk itself leaves it at `.unknown`. -/
structure DeclRecord where
  name : String
  kind : String
  «module» : String
  file : String
  line : Nat
  col : Nat
  «effect» : String
  exposeSource : ExposeSource := .unknown
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

/-- Collect the enumeration records. -/
def enumerate (scopePrefix : Array Name) : CoreM (Array DeclRecord) := do
  let env ← getEnv
  let instSet := (Lean.Meta.instanceExtension.getState env).instanceNames
  let mut out : Array DeclRecord := #[]
  let mut instSkipped : Nat := 0
  for (name, info) in env.constants.toList do
    let .defnInfo defnVal := info | continue
    let some mod := isInScope env scopePrefix name | continue
    if name.hasMacroScopes then continue
    if name.isInternal then continue
    if ← isAutoGen env name then continue
    unless isBodyExported env name do continue
    if instSet.contains name then
      instSkipped := instSkipped + 1
      continue
    let isAbbrev := defnVal.hints.isAbbrev
    let kind := "def"
    let «effect» := if isAbbrev then "noop-always-exported" else "exposed"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let pos := ranges.range.pos
    out := out.push {
      name := name.toString
      kind
      «module» := mod.toString
      file := moduleToPath mod
      line := pos.line
      col := pos.column
      «effect»
    }
  IO.eprintln s!"[no_expose enumerate] excluded {instSkipped} instances (expose is a no-op)"
  return out

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
  "{\"name\":\"" ++ jsonEscape d.name ++
  "\",\"kind\":\"" ++ d.kind ++
  "\",\"module\":\"" ++ jsonEscape d.module ++
  "\",\"file\":\"" ++ jsonEscape d.file ++
  "\",\"line\":" ++ toString d.line ++
  ",\"col\":" ++ toString d.col ++
  ",\"effect\":\"" ++ d.effect ++
  "\",\"expose_source\":\"" ++ d.exposeSource.toJsonString ++ "\"}"

/-- Source-scan every file mentioned by `recs` and return a parallel
array of `ExposeSource` (indexed the same as `recs`) plus a
per-source count summary. Intended to be called inside the
`withImportModules` block that produced `recs`, so the records are
valid for the duration of the scan. -/
def sourceScanRecords (recs : Array DeclRecord) :
    IO (Array ExposeSource × Std.HashMap String Nat) := do
  -- Group record indices by file.
  let mut byFile : Std.HashMap String (Array Nat) := {}
  let mut fileOrder : Array String := #[]
  let mut seenFile : Std.HashSet String := {}
  for h : i in [:recs.size] do
    let f := recs[i].file
    unless seenFile.contains f do
      seenFile := seenFile.insert f
      fileOrder := fileOrder.push f
    byFile := byFile.insert f ((byFile.getD f #[]).push i)
  IO.eprintln s!"[no_expose source-scan] grouped {recs.size} records into \
    {fileOrder.size} files"
  -- Per-file scan; each file's scan map is bounded by candidate count
  -- (via `wanted`) and dropped before moving on.
  let mut sources : Array ExposeSource := Array.replicate recs.size .unknown
  let mut counts : Std.HashMap String Nat := {}
  let mut filesDone : Nat := 0
  for f in fileOrder do
    let indices := byFile.getD f #[]
    let wanted : Std.HashSet Nat :=
      indices.foldl (init := {}) fun acc i => acc.insert recs[i]!.line
    let pth : System.FilePath := f
    let mut byLine : Std.HashMap Nat ExposeSource := {}
    if ← System.FilePath.pathExists pth then
      let text ← IO.FS.readFile pth
      for (ln, src) in scanFile text do
        if wanted.contains ln then byLine := byLine.insert ln src
    for i in indices do
      let src := byLine.getD recs[i]!.line .unknown
      sources := sources.set! i src
      let k := src.toJsonString
      counts := counts.insert k ((counts.getD k 0) + 1)
    filesDone := filesDone + 1
    if filesDone % 500 == 0 then
      IO.eprintln s!"[no_expose source-scan] scanned {filesDone} files"
  IO.eprintln s!"[no_expose source-scan] scanned {filesDone} files total"
  return (sources, counts)

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
