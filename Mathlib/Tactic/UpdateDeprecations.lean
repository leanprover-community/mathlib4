/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command

/-!
This file contains the code to perform the auto-replacements of `deprecated` declarations.
-/

/-- `findNamespaceMatch fullName s` assumes that
* `fullName` is a string representing the fully-qualified name of a declaration
  (e.g. `Nat.succ` instead of `succ` or `.succ`);
* `s` is a string beginning with a possibly non-fully qualified name
  (e.g. any of `Nat.succ`, `succ`, `.succ`, possibly continuing with more characters).

If `fullName` and `s` could represent the same declaration, then `findNamespaceMatch` returns
`some <prefix of s matching namespaced fullName>` else it returns `none`
-/
def findNamespaceMatch (fullName s : String) : Option String :=
  Id.run do
  let mut comps := fullName.splitOn "."
  for _ in comps do
    let noDot := ".".intercalate comps
    if noDot.isPrefixOf s then return noDot
    let withDot := "." ++ noDot
    if withDot.isPrefixOf s then return withDot
    comps := comps.drop 1
  return none

/-- `String.replaceCheck s check repl st` takes as input
* a "source" `String` `s`;
* a `String` `check` representing what should be replaced;
* a replacement `String` `repl`;
* a natural number `st` representing the number of characters in `s` until the beginning of `check`.

If `check` coincides with the substring of `s` beginning at `st`, then it returns `some s` with the
identified occurrence of `check` replaced by `repl`.
Otherwise, it returns `none`.
-/
def String.replaceCheck (s check repl : String) (st : Nat) : Option String :=
  match findNamespaceMatch check (s.drop st) with
    | none => none
    | some check =>
      let sc := s.toList
      let fi := st + check.length
      some ⟨sc.take st ++ repl.toList ++ sc.drop fi⟩

/-- `substitutions lines dat` takes as input the array `lines` of strings and the "instructions"
`dat : Array ((String × String) × (Nat × Nat))`.
The elements of `dat` are of the form `((old, new), (line, column))` where
* `(old, new)` is a pair of strings, representing
  the current text `old` and the replacement text `new`;
* `(line, column)` is a pair of natural number representing the position of the start of the `old`
  text.

For each replacement instruction, if the substring of `lines[line]!` starting at `column` is `old`,
then `substitutions` replaces `old` with `new`, otherwise, it leaves the string unchanged.

Once all the instructions have been parsed, `substitutions` returns a count of the number of
successful substitutions, the number of unsuccessful substitutions and the array of strings
incorporating all the substitutions.
-/
def substitutions (lines : Array String) (dat : Array ((String × String) × (Nat × Nat))) :
    (Nat × Nat) × Array String := Id.run do
  let mut new := lines
  let mut replaced := 0
  let mut unreplaced := 0
  for ((check, repl), (l', c)) in dat do
    let l := l' - 1
    match new[l]!.replaceCheck check repl c with
      | some newLine => (new, replaced) := (new.modify l (fun _ => newLine), replaced + 1)
      | none         =>
        dbg_trace "Could not replace '{check}' with '{repl}'"
        unreplaced := unreplaced + 1
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
    IO.println "There are out of date oleans. Run `lake build` or `lake exe cache get` first"
    return default
  return build.stdout

open Lean

section build_syntax

/-- `Corrections` is the `HashMap` storing information about corrections.
The entries of the array associated to each `System.FilePath` are the two pairs
* `(oldString, newString)`,
* `(row, column)`.
-/
abbrev Corrections := HashMap System.FilePath (Array ((String × String) × (Nat × Nat)))

/-- extend the input `Corrections` with the given data. -/
def extend (s : Corrections) (fil : System.FilePath) (oldNew : String × String) (pos : Nat × Nat) :
    Corrections :=
  let corrections := (s.find? fil).getD default
  s.insert fil (corrections.push (oldNew, pos))

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

/-- Syntax for the output of a file in `lake build`, e.g. `././././Mathlib/Data/Nat/Defs.lean`. -/
syntax "././././" sepBy(ident, "/") : build

/-- a deprecated declaration. -/
syntax "warning:" build ":" num ":" num ": `" ident
  "` has been deprecated, use `" ident "` instead" : build

/-- an unnecessary `set_option ... in`. -/
syntax "warning:" build ":" num ":" num ": unnecessary `set_option " ident term &"`" : build

/-- instruction to silence the linter -/
example := Nat
syntax "note: this linter can be disabled with `set_option " ident term &"`" : build

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

/-- extracts the corrections from a `build` syntax. -/
def getCorrections : TSyntax `build → Option (System.FilePath × (String × String) × (Nat × Nat))
  | `(build| warning: $fil:build: $s : $f : `$depr` has been deprecated, use `$new` instead) =>
    let oldNewName := (depr.getId.toString, new.getId.toString)
    (toFile fil, oldNewName, s.getNat, f.getNat)
  | `(build|warning: $fil:build: $s : $f : unnecessary `set_option $optN:ident $opt:ident`) =>
    (toFile fil, (s!"set_option {optN.getId.toString} {opt.getId.toString} in",
      "/-set_option {optN.getId.toString} {opt.getId.toString} in-/"),
      s.getNat, f.getNat)
  | _ => default

/-- Parse the output of `lake build` and perform the relevant substitutions. -/
elab bds:build* tk:"Build completed successfully." : command => do
  let mut s : Corrections := {}
  for bd in bds do
    if let some (fil, oldNew, pos) := getCorrections bd then
      s := extend s fil oldNew pos
  let modifiedFiles ← s.foldM (init := {}) fun summary fil arr => do
    let mut summary : HashMap System.FilePath (Nat × Nat) := summary
    -- sort the corrections, so that the lines are parsed in reverse order and, within each line,
    -- the corrections are applied also in reverse order
    let arr := arr.qsort fun (_, (l1, c1)) (_, (l2, c2)) => l2 < l1 || (l1 == l2 && c2 < c1)
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
      m!"{(modifiedFiles.fold (fun a _ (x, _) => a + x) 0)} modifications \
          across {noFiles} files, all successful"
    else
      modifiedFiles.fold (init := "| File | mods | unmods |\n|-|-|")
        fun msg fil (modified, unmodified) =>
          let mods := if modified == 0 then " 0" else s!"+{modified}"
          let unmods := if unmodified == 0 then " 0" else s!"-{unmodified}"
          msg ++ s!"\n| {fil} | {mods} | {unmods} |"
  logInfoAt tk m!"{msg}"
  logInfoAt tk m!"{noFiles}"
end elabs
