/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Cli.Basic
import Lean.Elab.Frontend

/-!
# Script to automatically update deprecated declarations

This file contains the code to perform the auto-replacements of `deprecated` declarations.

Running `lake exe update_deprecations` assumes that there is a working cache and
uses the information from deprecations to automatically substitute deprecated declarations.

The script handles namespacing, replacing a possibly non-fully-qualified, deprecated name with the
fully-qualified non-deprecated name.

It also handles dot-notation.

It is also possible to use
```bash
lake exe update_deprecations --mods One.Two.Three,Dd.Ee.Ff
```
to limit the scope of the replacements to the modules `One.Two.Three` and `Dd.Ee.Ff`.
-/

namespace UpdateDeprecations

/-- `List.getCommon left right` takes as input two lists `left` and `right`.
It returns a triple `(common, left', right')` with the property that
`left = common ++ left'` and `right = common ++ right'`.
-/
def List.getCommon {α} [BEq α] : List α → List α → List α × List α × List α
  | [], r => ([], [], r)
  | l, [] => ([], l, [])
  | l::ls, r::rs =>
    let (common, left, right) := List.getCommon ls rs
    if l == r then
      (l::common, left, right)
    else
      (common, l::left, r::right)

/-- `splitWithNamespace fullName dotNot` returns `(common, declName, (termName, rightComponents))`,
where
* `fullName = declName ++ common`;
* `dotNot = termName ++ common ++ rightComponents`

and `common` is as large as possible, subject to the constraint that `rightComponents` does *not*
contain a segment equal to the last segment of `fullName`.

For example, with input `Nat.Prime.ne_two` and `hp.ne_two.symm` it returns
`(["ne_two"], ["Nat", "Prime"], (["hp"], ["symm"]))`.
Assuming the restriction on the right-most occurrence mentioned above, we can therefore deduce that
* the type of `hp` is `Nat.Prime`, i.e. `hp : Nat.Prime`;
* the lemma `Nat.Prime.ne_two` exists;
* the type of `hp.ne_two` is something that has a `.symm` in its namespace, i.e. `hp.ne_two : xx`
  and `xx.symm` exists
  (in this case, `xx = Ne`).
-/
def splitWithNamespace (fullName dotNot : String) :
    List String × List String × (List String × List String) :=
  let fns := (fullName.splitOn ".").reverse
  let dotns := (dotNot.splitOn ".").reverse
  let tail := fns.headD ""
  let rightMostCommon := dotns.dropWhile (· != tail)  -- consider using matches further left as well
  let (common, fns', rm') := (List.getCommon fns) rightMostCommon
  (common.reverse, fns'.reverse, (rm'.reverse, (dotns.takeWhile (· != tail)).reverse))

/-- `mIntercalate l` similar to `".".intercalate l`, except that
it returns `[]` if the input list if `[]` and
it returns the singleton list `[".".intercalate l]` otherwise. -/
def mIntercalate (l : List String) : List String :=
  match ".".intercalate l with
    | "" => []
    | str => [str]

/-- `recombineNamespace fullName dotNot newName` returns a candidate for "fixing" a deprecation
in a namespace.
* `dotNot` is a string representing dot-notation being used and involving a deprecated name
* `fullName` is the fully-qualified string associated to the name that is deprecated and
  appears in `dotNot`
* `newName` is the fully-qualified string associated to the name that is the non-deprecated version
  of `fullName`

It returns `none` if the final segment of `fullName` does not appear in `dotName`.
-/
def recombineNamespace (fullName dotNot newName : String) : Option String :=
  let (common, declName, (termName, rightComponents)) := splitWithNamespace fullName dotNot
  let beginning :=
    if (".".intercalate declName).isPrefixOf newName then
      -- we can still use the same dot-notation
      [".".intercalate termName,
        (newName.drop ((".".intercalate declName).length)).dropWhile (· == '.')]
    else
      -- dot-notation is no longer available
      [s!"({newName} {".".intercalate termName})", ".".intercalate common]
  if common == [] then none else
  if termName == [] then newName else
  ".".intercalate <| beginning ++ (mIntercalate rightComponents)

/--
`ReplData` is the data extracted from the warning emitted by `lake build` for a deprecated name:
|`ReplData.` | Description                                     |
|      -     |   :-                                            |
| `fullName` | the old, deprecated, fully-qualified name       |
| `newName`  | the new, fully-qualified name                   |
| `line`     | the line on which the replacement should happen |
| `col`      | the column where the replacement should happen  |
-/
structure ReplData :=
  /--`fullName` is the fully qualified, deprecated name -/
  fullName : String
  /--`newName` is the fully qualified, new name -/
  newName  : String
  /--`line` is the line number -/
  line     : Nat
  /--`col` is the column number -/
  col      : Nat
  deriving BEq, Inhabited

/-- `ReplData.newLine r` returns the new line obtained by performing the substitution,
taking into account the deprecation.
If no substitution is necessary, then it returns `none`: this is an indication that something went
wrong. -/
def ReplData.newLine (r : ReplData) (lines : Array String) : Option String :=
  let line := lines.getD (r.line - 1) ""
  line.take r.col ++ " (since := \"2024-06-12\")" ++ line.drop r.col

/-- We put the lexicographic order on the pairs `(line, col)` of `ReplData`,
placing first positions that happen later.
Most substitutions work on a line-by-line basis, so this is not necessary for "line information".
However, in order to preserve column information, it is easier to perform the replacements on any
given line from right to left.
Since in the future some replacements may span several lines (or remove some of them),
working backwards on the lines seems reasonable as well. -/
instance : LT ReplData where
  lt a b := (b.line < a.line) || (a.line == b.line && b.col < a.col)

theorem ReplData.lt_iff {a b : ReplData} :
    a < b ↔ (b.line < a.line) || (a.line == b.line && b.col < a.col) := by
  rfl

instance : DecidableRel (LT.lt (α := ReplData)) := fun _ _ => decidable_of_iff' _ ReplData.lt_iff

/-- `substitutions lines dat` takes as input the array `lines` of strings and the "instructions"
`dat : Array ReplData`.
The elements of `dat` contain the `(line, col)` information of the start of each
`(deprecatedName, newName)` pair.

For each replacement instruction, if the substring of `lines[line]!` starting at `col` is
"compatible" with being a `deprecatedName`, then `substitutions` replaces `deprecatedName`
with a possible use of `newName`.
Otherwise, it leaves the string unchanged.

Once all the instructions have been parsed, `substitutions` returns a count of the number of
successful substitutions, the number of unsuccessful substitutions and the array of strings
incorporating all the substitutions.
-/
def substitutions (lines : Array String) (dat : Array ReplData) : (Nat × Nat) × Array String :=
  Id.run do
  let mut new := lines
  let mut replaced := 0
  let mut unreplaced := 0
  -- sort the corrections, so that the lines are parsed in reverse order and, within each line,
  -- the corrections are applied also in reverse order
  for rd in dat.qsort (· < ·) do
    let l := rd.line - 1
    match rd.newLine new with
      | none =>
        dbg_trace s!"Could not replace '{rd.fullName}' with '{rd.newName}' in '{new[l]!}'"
        unreplaced := unreplaced + 1
      | some newLine =>
        (new, replaced) := (new.modify l (fun _ => newLine), replaced + 1)
  return ((replaced, unreplaced), new)

/-- `getBuild` checks if there is an available cache.  If this is the case, then it returns
the replayed build, otherwise it asks to build/download the cache.
The optional `mods` argument is an array of module names, limiting the build to the given
array, if `mods ≠ #[]`. -/
def getBuild (mods : Array String := #[]) : IO String := do
  -- for the entries of `mods` that end in `.lean`, remove the ending and replace `/` with `.`
  let mods := mods.map fun mod =>
    if mod.takeRight 5 == ".lean" then
      (mod.dropRight 5).replace ⟨[System.FilePath.pathSeparator]⟩ "." else mod
  let build ← IO.Process.output { cmd := "lake", args := #["build", "--no-build"] ++ mods }
  if build.exitCode != 0 then
    IO.println s!"`lake build --no-build` failed: the oleans may be out of date oleans. \
                Try running `lake build{mods.foldl (init := "") fun x y => s!"{x} {y}"}` or \
                `lake exe cache get` first"
    return default
  return build.stdout

open Lean

section build_syntax

/-- A custom syntax category for parsing the output lines of `lake build`:
a `buildSeq` consists of a sequence of `build` followed by `Build completed successfully.` -/
declare_syntax_cat buildSeq

/-- A custom syntax category for parsing the output lines of `lake build`. -/
declare_syntax_cat build

/-- Syntax for a successfully built file. -/
syntax "ℹ [" num "/" num "]" ident ident : build

/-- Syntax for a file with warnings. -/
syntax "⚠ [" num "/" num "]" ident ident : build

/-- A `buildSeq` consists of a sequence of `build` followed by `Build completed successfully.` -/
syntax build* "Build completed successfully." : buildSeq

/-- Syntax for disabling a linter. -/
syntax "note: this linter can be disabled with `set_option " ident term &"`" : build

/-- Syntax for the output of a file in `lake build`, e.g. `././././MyProject/Path/To/File.lean`. -/
syntax "././././" sepBy(ident, "/") : build

/-- a deprecated declaration. -/
syntax "warning:" build ":" num ":" num ": `" ident
  "` has been deprecated, use `" ident "` instead" : build

/-- a `deprecated` with a missing `since` -/
syntax "warning:" build ":" num ":" num ": After here, please add (since := " str
  ") or whatever date is appropriate `⟨"num "," num "⟩`" : build

end build_syntax

open System.FilePath in
/-- `toFile bld` takes as input a `` `build``-syntax representing a file and returns
the corresponding `System.FilePath`. -/
def toFile : TSyntax `build → System.FilePath
  | `(build| ././././ $xs/*) =>
    let xs := xs.getElems
    let last := match xs.back.getId.toString.splitOn ⟨[extSeparator]⟩ with
                      | [fil, "lean"] => addExtension fil "lean"
                      | [f] => f
                      | _ => default
    xs.pop.foldr (·.getId.toString / ·) last
  | _ => default

section elabs

/-- `FromLinter` is the `HashMap` storing information about corrections that can be read off
from the output of `lake build`.
Each `System.FilePath` contains an array of `ReplData` containing information about
`(deprecatedName, newName)` and the `(line, col)` pairs with the start of the deprecation.
-/
abbrev FromLinter := HashMap System.FilePath (Array ReplData)

/-- extracts the corrections from a `build` syntax. -/
def getFromLinter (fl : FromLinter) : TSyntax `build → FromLinter
  | `(build| warning: $fil:build: $s : $f : `$depr` has been deprecated, use `$new` instead) =>
    let rd : ReplData :=  { fullName := depr.getId.toString
                            newName  := new.getId.toString
                            line     := s.getNat
                            col      := f.getNat }
    let fil := toFile fil
    fl.insert fil <| ((fl.find? fil).getD #[]).push rd
  | `(build| warning: $fil:build:$_ :$_ : After here, please add (since := $_
        ) or whatever date is appropriate `⟨$line, $col⟩`) =>
    let rd : ReplData :=  { fullName := default
                            newName  := default
                            line     := line.getNat
                            col      := col.getNat }
    let fil := toFile fil
    dbg_trace fil
    fl.insert fil <| ((fl.find? fil).getD #[]).push rd
  | _ => fl
open UpdateDeprecations

/-- Parse the output of `lake build` and perform the relevant substitutions. -/
elab bds:build* tk:"Build completed successfully." : command => do
  let mut fl : FromLinter := {}
  for bd in bds do
    fl := getFromLinter fl bd
  let modifiedFiles ← fl.foldM (init := {}) fun summary fil arr => do
    let mut summary : HashMap System.FilePath (Nat × Nat) := summary
    let lines ← IO.FS.lines fil
    let ((replaced, unreplaced), replacedLines) := substitutions lines arr
    let (m, n) := (summary.find? fil).getD (0, 0)
    summary := summary.insert fil (m + replaced, n + unreplaced)
    if replacedLines != lines then
      let newFile := ("\n".intercalate replacedLines.toList).trimRight.push '\n'
      IO.FS.writeFile fil newFile
    return summary
  let noFiles := modifiedFiles.size
  let msg :=
    if noFiles == 0 then m!"No modifications needed"
    else if modifiedFiles.toArray.all (fun (_, _, x) => x == 0) then
      let totalModifications := modifiedFiles.fold (fun a _ (x, _) => a + x) 0
      let toMo := m!"{totalModifications} modification" ++
        if totalModifications == 1 then m!"" else "s"
      let moFi := m!" across {noFiles} file" ++ if noFiles == 1 then m!"" else "s"
      toMo ++ moFi ++ ", all successful"
    else
      modifiedFiles.fold (init := "| File | mods | unmods |\n|-|-|")
        fun msg fil (modified, unmodified) =>
          let mods := if modified == 0 then " 0" else s!"+{modified}"
          let unmods := if unmodified == 0 then " 0" else s!"-{unmodified}"
          msg ++ s!"\n| {fil} | {mods} | {unmods} |"
  logInfoAt tk m!"{msg}"
  logInfoAt tk m!"{noFiles}"
end elabs

open Cli in
/-- Implementation of the `update_deprecations` command line program.
The exit code is the number of files that the command updates/creates. -/
def updateDeprecationsCLI (args : Parsed) : IO UInt32 := do
  let mods := ← match args.flag? "mods" with
              | some mod => return mod.as! (Array String)
              | none => return #[]
  let buildOutput ← getBuild mods
  if buildOutput.isEmpty then return 1
  Lean.initSearchPath (← Lean.findSysroot)
  -- create the environment with `import Mathlib.Tactic.DeprSinceAction`
  let env : Environment
    ← importModules (leakEnv := true) #[{module := `Mathlib.Tactic.DeprSinceAction}] {}
  -- process the `lake build` output, catching messages
  let (_, msgLog) ← Lean.Elab.process buildOutput env {}
  let exitCode := ← match msgLog.unreported.toArray with
    | #[msg, exCode] => do
      IO.println f!"{(← msg.toString).trimRight}"
      return String.toNat! (← exCode.toString).trimRight
    | msgs => do
      IO.println f!"{← msgs.mapM (·.toString)}"
      return 1
  if exitCode == 0 then return 0
  -- the exit code is the total number of changes that should have happened, whether or not they
  -- actually took place modulo `UInt32.size = 4294967296` (returning 1 if the remainder is `0`).
  -- In particular, the exit code is `0` if and only if no replacement was necessary.
  else return ⟨max 1 (exitCode % UInt32.size), by unfold UInt32.size; omega⟩

/-- Setting up command line options and help text for `lake exe update_deprecations`. -/
def updateDeprecations : Cli.Cmd := `[Cli|
  updateDeprecations VIA updateDeprecationsCLI; ["0.0.1"]
  "\nPerform the substitutions suggested by the output of `lake build` on the whole project. \
  You can run this on some modules only, using the optional `--mods`-flag: running\n\n\
  lake exe update_deprecations --mods One.Two.Three,Dd.Ee.Ff\n\n\
  only updates the deprecations in `One.Two.Three` and `Dd.Ee.Ff`. \
  Note that you should provide a comma-separated list of module names, with no spaces between \
  them. \
  As a convenience, the script tries to parse *paths* instead of *module names*: \
  passing\n\n\
  lake exe update_deprecations --mods One/Two/Three.lean,Dd.Ee.Ff\n\n\
  has the same effect as the command above."

  FLAGS:
    mods : Array String; "you can pass an array of modules using the `--mods`-flag \
                          e.g. `--mods One.Two.Three,Dd.Ee.Ff`"
]

end UpdateDeprecations
