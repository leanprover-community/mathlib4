/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command

/-!
# Summary of `!bench` results

This file contains a script that converts data retrieved from the speed-center into a
shorter, more accessible format, and post a comment with this summary on github.
-/

namespace BenchAction

open Lean

/-- `Bench` is a structure with the data used to compute the `!bench` summary.
It contains
* a string `file` (that could be `build`, `lint` or `~Mathlib.Path.To.File`);
* an integer `diff` representing the change in number of instructions for `file`;
* a float `reldiff` representing the percentage change in number of instructions for `file`.
-/
structure Bench where
  file    : String
  diff    : Int
  reldiff : Float
  deriving FromJson, ToJson, Inhabited

/-- `intDecs z exp prec` is a "generic" formatting of an integer `z`.
It writes `z` in the form `x.y * 10 ^ exp` (for non-negative integers `x`, `y` and `z`),
such that `y` has `prec` digits and returns
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

/-- `formatDiff z` uses `intDecs` to format an integer `z` as `±x.y⬝10⁹`. -/
def formatDiff (z : Int) : String :=
  let (sgn, intDigs, decDigs) := intDecs z
  s!"{sgn}{intDigs}.{decDigs}⬝10⁹"

/-- Convert a `Float` into a formatted string of the form `±z.w%`. -/
def formatPercent (reldiff : Float) : String :=
  -- shift by `2` twice: once to get a percentage, again for two decimal digits of precision
  let reldiff := reldiff * 10 ^ 4
  let sgn : Int := if reldiff < 0 then -1 else 1
  let reldiff := (.ofInt sgn) * reldiff
  let (sgn, intDigs, decDigs) := intDecs (sgn * reldiff.toUInt32.toFin) 0 2
  -- the `if ... then ... else ...` makes sure that the output includes leading `0`s
  s!"({sgn}{intDigs}.{if decDigs < 10 then "0" else ""}{decDigs}%)"

/--
info: [(+0.00%), (+14.28%), (+0.20%), (-0.60%), (-0.08%), (+1.02%)]
---
info: [+0.0⬝10⁹, +1.0⬝10⁹, +30.200⬝10⁹, -0.460⬝10⁹]
-/
#guard_msgs in
run_cmd
  let floats : Array Float := #[0, 1/7, 0.002, -0.006, -8.253600406145226E-4, 0.0102]
  logInfo m!"{floats.map formatPercent}"
  let ints : Array Int := #[0, 10^9, 302*10^8, -460000000]
  logInfo m!"{ints.map formatDiff}"

/--
`formatFile file` converts a `String` into a formatted string of the form `` `file` ``,
removing leading non-letters. It is expected that `~` is the only leading non-letter.
-/
def formatFile (file : String) : String := s!"`{file.dropWhile (!·.isAlpha)}`"

/--
`summary bc` converts a `Bench` into a formatted string of the form
``| `file` | ±x.y⬝10⁹ | ±z.w% |`` (technically, without the spaces).
-/
def summary (bc : Bench) : String :=
  let middle := [formatFile bc.file, formatDiff bc.diff, formatPercent bc.reldiff]
  "|".intercalate (""::middle ++ [""])

/--
`toTable bcs` formats an array of `Bench`es into a markdown table whose columns are
the file name, the absolute change in instruction counts and the relative change as a percentage.
A typical entry may look like ``|`Mathlib/Analysis/Seminorm.lean`|+2.509⬝10⁹|(+1.41%)|``.
-/
def toTable (bcs : Array Bench) : String :=
  let header := "|File|Instructions|%|\n|-|-:|:-:|"
  "\n".intercalate (header :: (bcs.map summary).toList)

/--
`toCollapsibleTable bcs roundDiff` is similar to `toTable bcs`, except that it returns
output enclosed in a `<details><summary>` html-block.
The `<summary>` part tallies the number of entries in `bcs` whose instructions increased
resp. decreased by at least the amount `roundDiff`.
-/
def toCollapsibleTable (bcs : Array Bench) (roundDiff : Int) : String :=
  s!"<details><summary>{bcs.size} files, Instructions {formatDiff <| roundDiff * 10 ^ 9}\
    </summary>\n\n{toTable (bcs.qsort (·.diff > ·.diff))}\n</details>\n"

/-- Assuming that the input is a `json`-string formatted to produce an array of `Bench`,
`benchOutput` returns the "significant" changes in numbers of instructions as a string. -/
def benchOutput (jsonInput : String) : IO String := do
  let data ← IO.ofExcept (Json.parse jsonInput >>= fromJson? (α := Array Bench))
  -- `head` contains the changes for `build` and `lint`,
  -- `data` contains the instruction changes for individual files:
  -- each filename is prefixed by `~`.
  let (head, data) := data.partition (·.file.take 1 != "~")
  -- Partition the `Bench`es into "bins", i.e. the subsets of all `Bench`es whose difference
  -- in instructions lies in an interval `[n·10⁹, (n+1)·10⁹)`.
  -- The values `n` need not be consecutive: we only retain non-empty bins.
  let grouped := ((data.groupByKey (·.diff / (10 ^ 9))).toArray.qsort (·.1 > ·.1)).toList
  -- We consider `build` and `lint` as their own groups, in this order.
  let sortHead := (head.qsort (·.file < ·.file)).toList.map (0, #[·])
  let togetherSorted := sortHead ++ grouped
  -- For better formatting, we merge consecutive bins with just a single *file* into one.
  -- This covers the two steps `ts1` and `ts2`.
  -- For example, `[..., (bound₁, #[a₁]), (bound₂, #[a₂]), (bound₃, #[a₃]), ...]` gets collapsed to
  -- `[..., (none, #[a₁, a₂, a₃]), ...]`.
  -- The `boundᵢ` entry becomes `none` for the collapsed entries, so that we know that these
  -- should be printed individually instead of inside a `<details><summary>`-block.
  -- A single bin with just a single file is also marked with `none`, for the same reason.
  let ts1 := togetherSorted.splitBy (·.2.size == 1 && ·.2.size == 1)
  let ts2 := List.flatten <| ts1.map fun l ↦
    if (l.getD 0 default).2.size == 1 then
      [(none, l.foldl (· ++ ·.2) #[])]
    else
      l.map fun (n, ar) ↦ (some n, ar)

  let mut overall := []
  for (bound, gs) in ts2 do
    overall := overall ++ [
      match bound with
        -- These entries are from "singleton" files in their range; we print them individually.
        | none => toTable gs
        -- These get a collapsible summary instead.
        | some roundedDiff => toCollapsibleTable gs roundedDiff]
  return "\n".intercalate overall

open Lean Elab Command in
/-- `addBenchSummaryComment PR repo tempFile` adds a summary of benchmarking results
as a comment to a pull request.  It takes as input
* the number `PR` and the name `repo` as a `String` containing the relevant pull-request
  (it reads and posts comments there)
* the optional `jobID` numeral for reporting the action that produced the output
  (`jobID` is a natural number, even though it gets converted to a `String` -- this is mostly
  due to the fact that it is easier to get CI to pass a number, than a string with quotations)
* the `String` `tempFile` of a temporary file where the command stores transient information.

The code itself interfaces with the shell to retrieve and process json data and eventually
uses `benchOutput`.
Here is a summary of the steps:
* retrieve the last comment to the PR (using `gh pr view ...`),
* check if it was posted by `leanprover-bot`,
* try to retrieve the source and target commits from the url that the bot posts
  and store them in `source` and `target`,
* query the speed center for the benchmarking data (using `curl url`),
* format and filter the returned JSON data (various times),
  saving intermediate steps into `tempFile` (using `jq` multiple times),
* process the final string to produce a summary (using `benchOutput`),
* finally post the resulting output to the PR (using `gh pr comment ...`).
-/
def addBenchSummaryComment (PR : Nat) (repo : String) (jobID : Nat := 0)
    (author : String := "leanprover-bot") (tempFile : String := "benchOutput.json") :
    CommandElabM Unit := do
  let PR := s!"{PR}"
  let jq := s!".comments | last | select(.author.login==\"{author}\") | .body"

  -- retrieve the relevant comment
  let gh_pr_comments : IO.Process.SpawnArgs :=
    { cmd := "gh", args := #["pr", "view", PR, "--repo", repo, "--json", "comments", "--jq", jq] }
  -- This is the content of the last comment made by `leanprover-bot` to the PR `PR`.
  let output ← IO.Process.run gh_pr_comments
  -- URLs of benchmarking results have the form {something}/compare/source_sha/to/target_sha,
  -- where source_sha and target_sha are the commit hashes of the revisions being benchmarked.
  -- The comment contains such a URL (and only one); parse the revisions from the comment.
  let frags := output.split (· == '/')
  let some compIdx := frags.findIdx? (· == "compare") |
    logInfo "No 'compare' found in URL."
    return
  let source := frags.getD (compIdx + 1) ""
  let target := (frags.getD (compIdx + 3) "").takeWhile (· != ')')
  if (source.length, target.length) != (36, 36) then
    logInfo m!"Found\nsource: '{source}'\ntarget: '{target}'\ninstead of two commit hashes."
    return
  dbg_trace s!"Using commits\nsource: '{source}'\ntarget: '{target}'\n"

  let job_msg := s!"\n[CI run](https://github.com/{repo}/actions/runs/{jobID}) [Lakeprof report](https://speed.lean-lang.org/mathlib4-out/{target}/)"

  -- retrieve the data from the speed-center
  let curlSpeedCenter : IO.Process.SpawnArgs :=
    { cmd := "curl"
      args := #[s!"https://speed.lean-lang.org/mathlib4/api/compare/{source}/to/{target}?all_values=true"] }
  dbg_trace "\n#running\n\
    curl https://speed.lean-lang.org/mathlib4/api/compare/{source}/to/{target}?all_values=true > {tempFile}.src"
  let bench ← IO.Process.run curlSpeedCenter
  IO.FS.writeFile (tempFile ++ ".src") bench

  -- Extract all instruction changes whose magnitude is larger than `threshold`.
  let threshold := 10 ^ 9
  let jq1 : IO.Process.SpawnArgs :=
    { cmd := "jq"
      args := #["-r", "--arg", "thr", s!"{threshold}",
        ".differences | .[] | ($thr|tonumber) as $th |
        select(.dimension.metric == \"instructions\" and ((.diff >= $th) or (.diff <= -$th)))",
        (tempFile ++ ".src")] }
  dbg_trace "\n#running\n\
    jq -r --arg thr {threshold} '.differences | .[] | ($thr|tonumber) as $th |\n  \
      select(.dimension.metric == \"instructions\" and ((.diff >= $th) or (.diff <= -$th)))' \
      {tempFile}.src > {tempFile}"
  let firstFilter ← IO.Process.run jq1
  -- we leave `tempFile.src` unchanged and we switch to updating `tempfile`: this is useful for
  -- debugging, as it preserves the original data downloaded from the speed-center
  IO.FS.writeFile tempFile firstFilter
  -- Write these in compact form, in the format suitable for `benchOutput`.
  let jq2 : IO.Process.SpawnArgs :=
    { cmd := "jq"
      args := #["-c", "[{file: .dimension.benchmark, diff: .diff, reldiff: .reldiff}]", tempFile] }
  dbg_trace "\n#running\n\
    jq -c '[\{file: .dimension.benchmark, diff: .diff, reldiff: .reldiff}]' {tempFile} > \
      {tempFile}.2"
  let secondFilter ← IO.Process.run jq2
  if secondFilter == "" then
    let _ ← IO.Process.run
      { cmd := "gh", args := #["pr", "comment", PR, "--repo", repo, "--body",
        s!"No benchmark entry differed by at least {formatDiff threshold} instructions." ++
          job_msg] }
  else
  IO.FS.writeFile tempFile secondFilter
  let jq3 : IO.Process.SpawnArgs :=
    { cmd := "jq", args := #["-n", "reduce inputs as $in (null; . + $in)", tempFile] }
  dbg_trace "\n#running\n\
    jq -n 'reduce inputs as $in (null; . + $in)' {tempFile}.2 > {tempFile}.3"
  let thirdFilter ← IO.Process.run jq3
  let report ← benchOutput thirdFilter
  IO.println report
  -- Post the computed summary as a github comment.
  let add_comment : IO.Process.SpawnArgs :=
    { cmd := "gh", args := #["pr", "comment", PR, "--repo", repo, "--body", report ++ job_msg] }
  let _ ← IO.Process.run add_comment

end BenchAction

-- CI adds the following line, replacing `putPR` with the PR number:
--run_cmd BenchAction.addBenchSummaryComment putPR "leanprover-community/mathlib4"
