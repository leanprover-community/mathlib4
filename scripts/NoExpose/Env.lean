/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean

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

This module does NOT `import Mathlib`. The
`CoreM.withImportModules` helper is inlined from `Mathlib.Lean.CoreM`
(11 lines, MIT-licensed) so the exe links against just Lean core +
Lake.
-/

open Lean Core

namespace NoExpose

/-- Inlined from `Mathlib/Lean/CoreM.lean`: run a `CoreM α` against a
fresh `Environment` populated by importing `modules`. Mathlib import
removed; depends only on Lean core APIs. -/
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

/-- One row of the eventual `exposed.jsonl`. -/
structure DeclRecord where
  name : Name
  kind : String
  «module» : Name
  file : String
  line : Nat
  col : Nat
  «effect» : String

/-- Suffixes Lean uses for compiler-generated structure/inductive
helpers; we exclude them since they aren't user-written `@[expose]`
candidates. -/
private def autoGenSuffixes : Array String := #[
  "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow", "ndrec",
  "ndrecOn", "recAux", "rec", "noConfusion", "noConfusionType", "sizeOf",
  "sizeOf_spec", "injEq"
]

/-- True if `name` is a compiler helper we should exclude from
enumeration. Mirrors the predicate in the legacy `expose_enumerate`. -/
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
      name
      kind
      «module» := mod
      file := moduleToPath mod
      line := pos.line
      col := pos.column
      «effect»
    }
  IO.eprintln s!"[no_expose enumerate] excluded {instSkipped} instances (expose is a no-op)"
  return out

/-! ## Static references -/

/-- Mirrors the legacy `expose_static_refs.lean`: for each
(referencing module, referenced name), `(total_count, theorem_count)`. -/
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

/-- JSON-string-escape `s`. -/
private def jsonEscape (s : String) : String :=
  s.foldl (init := "") fun acc c => acc ++
    match c with
    | '"'  => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c    => c.toString

def DeclRecord.toJsonLine (d : DeclRecord) : String :=
  "{\"name\":\"" ++ jsonEscape d.name.toString ++
  "\",\"kind\":\"" ++ d.kind ++
  "\",\"module\":\"" ++ jsonEscape d.module.toString ++
  "\",\"file\":\"" ++ jsonEscape d.file ++
  "\",\"line\":" ++ toString d.line ++
  ",\"col\":" ++ toString d.col ++
  ",\"effect\":\"" ++ d.effect ++ "\"}"

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
