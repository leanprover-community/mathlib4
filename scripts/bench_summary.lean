/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command

/-!
# Summary of `!bench` results

This file contains a script that converts data retrieved from the speed-center into a
shorter, more accessible format.
-/

namespace BenchAction

open Lean

/-- `Bench` is a structure with the data used to compute the `!bench` summary.
It contains
* a string `file` (that could be `build`, `lint` or `~Mathlib.Path.To.File`);
* an integer `diff` representing the change in number of instructions for `file`;
* a float `reldiff` representing the percentage change in number of instructions for `file`.
-/
structure Bench :=
  file    : String
  diff    : Int
  reldiff : Float
  deriving FromJson, ToJson, Inhabited

/-- `intDecs z exp prec` is a "generic" formatting of an integer `z`.
It writes the number as `x.y * 10 ^ exp`, where `y` has `prec` digits and returns
* the sign of `z` as a string (in fact, just either `+` or `-`);
* the integer `x`;
* the natural number `y` (that has `prec` digits).
-/
def intDecs (z : Int) (exp : Nat := 9) (prec : Nat := 3) : String × Int × Nat :=
  let sgn := z.sign
  let z := sgn * z
  let p10 : Int := 10 ^ (exp - prec)
  let idec := z / p10
  (if sgn < 0 then "-" else "+", idec / (10 ^ prec), (idec % 10 ^ prec).toNat)

/-- `formatDiff z` uses `intDecs` to format the integer `z` as `±x.y⬝10⁹`. -/
def formatDiff (z : Int) : String :=
  let (sgn, intDigs, decDigs) := intDecs z
  s!"{sgn}{intDigs}.{decDigs}⬝10⁹"

/-- Convert a `Float` into a formatted string of the form `±z.w%`. -/
def formatPercent (reldiff : Float) : String :=
  -- shift by `2` twice: the first one, to get a `%`; the second, for 2 decimal digits of precision
  let reldiff := reldiff * 10 ^ 4
  let sgn : Int := if reldiff < 0 then -1 else 1
  let reldiff := (.ofInt sgn) * reldiff
  let (sgn, intDigs, decDigs) := intDecs (sgn * reldiff.toUInt32.val) 0 2
  s!"({sgn}{intDigs}.{decDigs}%)"

/--
info: [(+0.0%), (+14.28%), (+0.20%), (-0.60%)]
---
info: [+0.0⬝10⁹, +1.0⬝10⁹, +30.200⬝10⁹, -0.460⬝10⁹]
-/
#guard_msgs in
run_cmd
  let floats : Array Float := #[0, 1/7, 0.002, -0.006]
  logInfo m!"{floats.map formatPercent}"
  let ints : Array Int := #[0, 10^9, 302*10^8, -460000000]
  logInfo m!"{ints.map formatDiff}"

/--
`formatFile file` converts a `String` into a formatted string of the form `` `file` ``,
removing leading non-letters. It is expected that `~` is the only leading non-letter.
-/
def formatFile (file : String) : String :=
  "`" ++ file.dropWhile (!·.isAlpha) ++ "`"

/--
`summary bc` converts a `Bench` into a formatted string of the form
`| file | ±x.y⬝10⁹ | ±z.w% |` (technically, without the spaces).
-/
def summary (bc : Bench) : String :=
  let reldiff := bc.reldiff
  let (sgnf : Float) := if reldiff < 0 then -1 else 1
  let middle := [formatFile bc.file, formatDiff bc.diff, formatPercent (sgnf * reldiff)]
  "|".intercalate (""::middle ++ [""])

/--
`toTable bcs` formats an array of `Bench`es into a markdown table whose columns are
`File`, `Instructions` and `%`.
A typical entry may look like ``|`Mathlib.Analysis.Seminorm`|+2.509⬝10⁹|(+1.41%)|``
-/
def toTable (bcs : Array Bench) : String :=
  let header := "|File|Instructions|%|\n|-|-:|:-:|"
  "\n".intercalate (header :: (bcs.map summary).toList)

/--
`toCollapsibleTable bcs roundDiff` is similar to `toTable bcs`, except that it encloses it
in a `<details><summary>` html-block.
The `<summary>` part tallies the number of entries in `bcs` and the significant change in
number of instructions `roundDiff`.
-/
def toCollapsibleTable (bcs : Array Bench) (roundDiff : Int) : String :=
  s!"<details><summary>{bcs.size} files, Instructions {formatDiff <| roundDiff * 10 ^ 9}\
    </summary>\n\n{toTable (bcs.qsort (·.diff > ·.diff))}\n</details>\n"

/-- Assuming that the input is a `json`-string formatted to produce an array of `Bench`,
`benchOutput` returns the "significant" changes in numbers of instructions as a string. -/
def benchOutput (jsonInput : String) : IO String := do
  let dats ← IO.ofExcept (Json.parse jsonInput >>= fromJson? (α := Array Bench))
  -- `head` contains `build` and `lint`, `dats` contains the filenames, prefixed by `~`
  let (head, dats) := dats.partition (·.file.take 1 != "~")
  -- gather together `Bench`es into subsets each containing `Bench`es with difference of
  -- instructions in a `[n·10⁹, (n+1)·10⁹)` range
  let grouped := ((dats.groupByKey (·.diff / (10 ^ 9))).toArray.qsort (·.1 > ·.1)).toList
  -- we sort `build` and `lint` and consider them as their own individual groups
  let sortHead := (head.qsort (·.file < ·.file)).toList.map (0, #[·])
  let togetherSorted := sortHead ++ grouped
  -- for better formatting, we collapse consecutive entries with singleton *file* entries
  -- into a single entry. This covers the two steps `ts1` and `ts2`.
  -- E.g. `[..., (bound₁, #[a₁]), (bound₂, #[a₂]), (bound₃, #[a₃]), ...]` collapses to
  -- `[..., (none, #[a₁, a₂, a₃]), ...]`.
  -- The `boundᵢ` entry become `none` for the collapsed entries, so that we know that these
  -- should be printed individually instead of inside a `<details><summary>`-block.
  let ts1 := togetherSorted.groupBy (·.2.size == 1 && ·.2.size == 1)
  let ts2 := List.join <| ts1.map fun l =>
    if (l.getD 0 default).2.size == 1 then
      [(none, l.foldl (· ++ ·.2) #[])]
    else
      l.map fun (n, ar) => (some n, ar)
  let mut tot := []
  for (bound, gs) in ts2 do
    tot := tot ++ [
      match bound with
        | none => -- `bound = none`: these entries are "singleton" files in their range
          toTable gs
        | some roundedDiff => -- these instead should be a collapsible summary
          toCollapsibleTable gs roundedDiff]
  return "\n".intercalate tot

open Lean Elab Command in
def addBenchSummaryComment (PR : Nat) (repo : String) (jsonFile : String := "benchOutput.json") :
    CommandElabM Unit := do
  let PR := s!"{PR}" --"12"
  let jq := ".comments | last | select(.author.login==\"leanprover-bot\") | .body"
  let gh_pr_comments : IO.Process.SpawnArgs :=
    { cmd := "gh", args := #["pr", "view", PR, "--repo", repo, "--json", "comments", "--jq", jq] }
  let output ← IO.Process.run gh_pr_comments
  let frags := output.split (· == '/')
  let some compIdx := frags.findIdx? (· == "compare") |
    logInfo "No 'compare' found in URL."
    return
  let src := frags.getD (compIdx + 1) ""
  let tgt := (frags.getD (compIdx + 3) "").takeWhile (· != ')')
  if (src.length, tgt.length) != (36, 36) then
    logInfo m!"Found\nsrc: '{src}'\ntgt: '{tgt}'\ninstead of two commit hashes."
    return
  dbg_trace s!"Using commits\nsrc: '{src}'\ntgt: '{tgt}'\n"
  let curlSpeedCenter : IO.Process.SpawnArgs :=
    { cmd := "curl"
      args := #[s!"http://speed.lean-fro.org/mathlib4/api/compare/{src}/to/{tgt}?all_values=true"] }
  let bench ← IO.Process.run curlSpeedCenter
  IO.FS.writeFile jsonFile bench
  let threshold := s!"{10 ^ 9}"
  let jq1 : IO.Process.SpawnArgs :=
    { cmd := "jq"
      args := #["-r", "--arg", "thr", threshold,
        ".differences | .[] | ($thr|tonumber) as $th |
        select(.dimension.metric == \"instructions\" and ((.diff >= $th) or (.diff <= -$th)))",
        jsonFile] }
  let firstFilter ← IO.Process.run jq1
  IO.FS.writeFile jsonFile firstFilter
  let jq2 : IO.Process.SpawnArgs :=
    { cmd := "jq"
      args := #["-c", "[{file: .dimension.benchmark, diff: .diff, reldiff: .reldiff}]", jsonFile] }
  let secondFilter ← IO.Process.run jq2
  IO.FS.writeFile jsonFile secondFilter
  let jq3 : IO.Process.SpawnArgs :=
    { cmd := "jq", args := #["-n", "reduce inputs as $in (null; . + $in)", jsonFile] }
  let thirdFilter ← IO.Process.run jq3
  let report ← benchOutput thirdFilter
  IO.println report
  let add_comment : IO.Process.SpawnArgs :=
    { cmd := "gh", args := #["pr", "comment", PR, "--repo", repo, "--body", report] }
  let _ ← IO.Process.run add_comment

--run_cmd addBenchSummaryComment putPR "leanprover-community/mathlib4"

end BenchAction
