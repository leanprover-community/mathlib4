/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Lean.CoreM

/-!
# expose_static_refs

Static reference analyzer for the `@[expose]` removal pipeline.

Walks the built Mathlib environment and, for every constant `C`, computes
the set of constants referenced in its type or value (via
`ConstantInfo.getUsedConstantsAsSet`). Aggregates by `(referenced_decl,
referencing_file)` and emits one JSONL record per pair.

Together with the build-time `diagnostics.jsonl` produced by
`scripts/build_with_diagnostics.py`, this provides a complementary
signal: diagnostics catches *unfold-based* uses (WHNF, kernel reduction,
type-class resolution); static refs catches *literal-occurrence* uses
(any place a referenced const appears in an elaborated body), including
typeclass-projection sources that diagnostics misses.

Output JSONL shape matches `diagnostics.jsonl` so `expose_report.py` can
merge the two:

  {"file": "Mathlib/Foo/Bar.lean", "decl": "Other.Module.name",
   "count": 1, "category": "static/ref"}

`count` is the number of constants in `file` whose body or type
literally references `decl` at least once (`getUsedConstantsAsSet`
deduplicates per-constant, so `count` is "how many decls in this file
mention `decl`").

Limitations:
  * Only sees bodies that are actually stored in the environment. A
    non-`@[expose]` def's body is replaced by an axiom in the exported
    view; references inside it are invisible. Theorem proofs are
    similarly unobservable in module mode.
  * The reference set of a non-Mathlib constant is not emitted, but
    references *to* Mathlib constants from anywhere in the loaded env
    are included.

Usage:
  lake exe expose_static_refs > scripts/.expose_report/static_refs.jsonl
-/

open Lean Core

namespace Mathlib.ExposeReport

/-- Convert `Mathlib.Foo.Bar` → `"Mathlib/Foo/Bar.lean"`. -/
def moduleToFilePath (m : Name) : String :=
  let parts := m.toString.splitOn "."
  "/".intercalate parts ++ ".lean"

/-- Escape a string for inclusion in a JSON string literal. -/
def jsonEscape (s : String) : String :=
  s.foldl (init := "") fun acc c => acc ++
    match c with
    | '"'  => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c    => c.toString

/-- For each pair (referencing module, referenced const name), the count of
constants in that module whose stored body or type mentions the referenced
name. -/
abbrev RefMap := Std.HashMap (Nat × Name) Nat

/-- Walk every constant in the env, accumulating reference pairs. -/
def collectRefs : CoreM RefMap := do
  let env ← getEnv
  let mut acc : RefMap := {}
  let mut considered : Nat := 0
  for (name, info) in env.constants.toList do
    -- Determine the module the referencing constant lives in.
    let some refModIdx := env.getModuleIdxFor? name | continue
    -- Skip compiler-generated helpers (they reflect implementation
    -- details rather than user-written use).
    if name.hasMacroScopes then continue
    if name.isInternal then continue
    considered := considered + 1
    let refs := info.getUsedConstantsAsSet
    acc := refs.foldl (init := acc) fun acc referenced =>
      let key := (refModIdx, referenced)
      acc.insert key ((acc.getD key 0) + 1)
  IO.eprintln (s!"[expose_static_refs] scanned {considered} constants, " ++
    s!"recorded {acc.size} (module,decl) reference pairs")
  return acc

/-- For every constant whose stored body is non-empty, emit a
`decl_refs` JSONL line listing the constants its body/type literally
references. Used by `expose_report.py` to walk one-hop transitivity:
if a downstream module uses decl `K`, it indirectly uses every decl
referenced by `K`'s body too (relevant for typeclass-projection chains
like `instLattice → instSemilatticeSup`). -/
def emitDeclRefs (out : IO.FS.Stream) : CoreM Unit := do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    if name.hasMacroScopes then continue
    if name.isInternal then continue
    -- only emit for decls declared somewhere we care about (any module);
    -- the consumer filters to Mathlib decls via the enumeration anyway.
    if (env.getModuleIdxFor? name).isNone then continue
    let refs := info.getUsedConstantsAsSet
    if refs.isEmpty then continue
    let arr := refs.foldl (init := #[]) fun a n => a.push n
    let body : String := ",".intercalate <|
      arr.toList.map fun n => "\"" ++ jsonEscape n.toString ++ "\""
    out.putStrLn <|
      "{\"decl\":\"" ++ jsonEscape name.toString ++
      "\",\"refs\":[" ++ body ++ "]}"

unsafe def mainUnsafe (args : List String) : IO UInt32 := do
  let searchPath ← addSearchPathFromEnv (← getBuiltinSearchPath (← findSysroot))
  -- args[0] = output mode: "module" (default) or "decl".
  let mode := args.head?.getD "module"
  CoreM.withImportModules #[`Mathlib] (searchPath := searchPath) (trustLevel := 1024) do
    let stdout ← IO.getStdout
    match mode with
    | "decl" =>
      emitDeclRefs stdout
    | _ =>
      -- module mode: aggregate by (refModule, refName)
      let acc ← collectRefs
      let env ← getEnv
      for ((modIdx, decl), count) in acc.toList do
        let some mod := env.header.moduleNames[modIdx]? | continue
        let file := moduleToFilePath mod
        stdout.putStrLn <|
          "{\"file\":\"" ++ jsonEscape file ++
          "\",\"decl\":\"" ++ jsonEscape decl.toString ++
          "\",\"count\":" ++ toString count ++
          ",\"category\":\"static/ref\"}"
  return 0

end Mathlib.ExposeReport

open Mathlib.ExposeReport in
unsafe def main (args : List String) : IO UInt32 := mainUnsafe args
