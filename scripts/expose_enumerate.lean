/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Lean.CoreM

/-!
# expose_enumerate

Enumerates all `def` and `instance` declarations in Mathlib whose bodies are
present in the exported view of the environment — i.e., are currently being
exposed to downstream modules, whether via an explicit `@[expose]` attribute
or via an enclosing `@[expose] public section`.

This produces one half of the input needed by `scripts/expose_report.py`;
the other half comes from a Mathlib build with `diagnostics=true`.

Output: JSONL on stdout, one record per decl with fields:
  * `name` — full constant name (e.g. `"FreeAlgebra.lift"`)
  * `kind` — `"def"` or `"instance"`
  * `module` — module declaring the decl (e.g. `"Mathlib.Algebra.FreeAlgebra"`)
  * `file` — relative path to source (e.g. `"Mathlib/Algebra/FreeAlgebra.lean"`)
  * `line`, `col` — 1-based declaration position
  * `effect` — `"exposed"` or `"noop-always-exported"`

`noop-always-exported` marks decls for which `@[expose]` is redundant: their
bodies end up in the exported view regardless (e.g. `abbrev`s). Removing
`@[expose]` from these is trivially safe; they're kept in the report
primarily so users can see them.

Usage:
  lake exe expose_enumerate > exposed.jsonl

Limitations:
  * Does not distinguish "individual `@[expose]` attribute" from "enclosing
    `@[expose] public section`" — the attribute is stripped before a decl
    enters the environment (see Lean/Elab/MutualDef.lean). The source file
    is reported so the user can inspect.
  * Non-`Prop`-returning instances are always exported by the module system
    regardless of `@[expose]`; this script does not currently flag them as
    `noop-always-exported`. Treat a `kind = instance` row as potentially
    noop.
  * Captures only decls declared in modules whose name starts with
    `Mathlib` (excludes `Cache`, `MathlibTest`, third-party deps).
-/

open Lean Core

namespace Mathlib.ExposeReport

/-- Is the declaration's body present in the *exported* view of the env? -/
def isBodyExported (env : Environment) (name : Name) : Bool :=
  (env.setExporting true |>.find? name).any (·.hasValue)

/-- Return the declaring Mathlib module, if the constant lives in Mathlib.* -/
def declaringMathlibModule? (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  let some mod := env.header.moduleNames[idx]? | none
  guard (mod.getRoot == `Mathlib)
  return mod

/-- Convert `Mathlib.Foo.Bar` → `"Mathlib/Foo/Bar.lean"`. -/
def moduleToPath (m : Name) : String :=
  let parts := m.toString.splitOn "."
  "/".intercalate parts ++ ".lean"

/-- Escape a string for inclusion in a JSON string literal. -/
def escapeJson (s : String) : String :=
  s.foldl (init := "") fun acc c => acc ++
    match c with
    | '"'  => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c    => c.toString

structure DeclRecord where
  name : Name
  kind : String
  «module» : Name
  file : String
  line : Nat
  col : Nat
  «effect» : String

def DeclRecord.toJsonLine (d : DeclRecord) : String :=
  "{\"name\":\"" ++ escapeJson d.name.toString ++
  "\",\"kind\":\"" ++ d.kind ++
  "\",\"module\":\"" ++ escapeJson d.module.toString ++
  "\",\"file\":\"" ++ escapeJson d.file ++
  "\",\"line\":" ++ toString d.line ++
  ",\"col\":" ++ toString d.col ++
  ",\"effect\":\"" ++ d.effect ++ "\"}"

/-- Name suffixes used for compiler-generated helpers of structures / inductives. -/
def autoGenSuffixes : Array String := #[
  "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow", "ndrec",
  "ndrecOn", "recAux", "rec", "noConfusion", "noConfusionType", "sizeOf",
  "sizeOf_spec", "injEq"
]

/-- True if `name` looks like a compiler-generated helper we should exclude. -/
def isAutoGen (env : Environment) (name : Name) : CoreM Bool := do
  if Lean.isAuxRecursor env name then return true
  if Lean.isNoConfusion env name then return true
  if (env.getProjectionFnInfo? name).isSome then return true
  if ← Lean.Meta.isMatcher name then return true
  -- name ends in one of the standard auto-generated helper suffixes
  if let .str _ last := name then
    if autoGenSuffixes.contains last then return true
  -- structure field-like: `Parent.toChild` when Parent extends Child
  -- (caught by getProjectionFnInfo? in most cases)
  return false

/-- Collect records for every `def` in Mathlib whose body is exported and
whose exposure is not trivially guaranteed by some other mechanism (such as
being an abbrev or a non-Prop instance).

`instance` decls are excluded: per the module system, a non-`Prop` instance
always has its body in the exported view regardless of `@[expose]`, and a
`Prop` instance's body is a proof (irrelevant to unfolding). Either way,
`@[expose]` on an instance has no semantic effect, so un-exposing one is
trivially safe — these decls aren't useful rows in the report and are
excluded to reduce noise.
-/
def collect : CoreM (Array DeclRecord) := do
  let env ← getEnv
  let instSet := (Lean.Meta.instanceExtension.getState env).instanceNames
  let mut out : Array DeclRecord := #[]
  let mut instSkipped : Nat := 0
  for (name, info) in env.constants.toList do
    let .defnInfo defnVal := info | continue
    let some mod := declaringMathlibModule? env name | continue
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
  IO.eprintln s!"[expose_enumerate] excluded {instSkipped} instances (expose is a no-op)"
  return out

end Mathlib.ExposeReport

/-- Read module names to import from a file, one per line, blank lines and
`#`-comments ignored. -/
def readModulesFile (path : System.FilePath) : IO (Array Name) := do
  let text ← IO.FS.readFile path
  let mut out : Array Name := #[]
  for line in text.splitOn "\n" do
    let line := line.trim
    if line.isEmpty || line.startsWith "#" then continue
    out := out.push line.toName
  return out

open Mathlib.ExposeReport in
unsafe def main (args : List String) : IO UInt32 := do
  let searchPath ← addSearchPathFromEnv (← getBuiltinSearchPath (← findSysroot))
  -- If a file path is given as the first argument, import the modules listed
  -- there (one per line). Otherwise, default to the single `Mathlib` module.
  let modules ← match args with
    | path :: _ => readModulesFile path
    | _         => pure #[`Mathlib]
  IO.eprintln s!"[expose_enumerate] importing {modules.size} module(s)..."
  CoreM.withImportModules modules (searchPath := searchPath) (trustLevel := 1024) do
    let records ← collect
    let stdout ← IO.getStdout
    for r in records do
      stdout.putStrLn r.toJsonLine
  return 0
