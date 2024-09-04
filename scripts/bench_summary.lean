/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Data.Json.FromToJson
import Lean.Data.Json.Parser

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
It writes the number as `x.y * 10 ^ expr`, where `y` has `prec` digits and returns
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

/-- converts a `Float` into a formatted string of the form `±z.w%`. -/
def formatPercent (reldiff : Float) : String :=
  -- shift by `2` twice: the first one, to get a `%`; the second, for 2 decimal digits of precision
  let reldiff := reldiff * 10 ^ 4
  let (sgn : Int) := if reldiff < 0 then -1 else 1
  let (sgnf : Float) := .ofInt sgn
  let reldiff := sgnf * reldiff
  let (sgn, intDigs, decDigs) := intDecs (sgn * reldiff.toUInt32.val) 0 2
  s!"({sgn}{intDigs}.{decDigs}%)"

/-- info: #["(+0.0%)", "(+14.28%)", "(+0.20%)", "(-0.60%)"] -/
#guard_msgs in
#eval
  let floats : Array Float := #[0, 1/7, 0.002, -0.006]
  floats.map formatPercent

/--
`formatFile file` converts a `String` into a formatted string of the form `` `file``,
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
`toTable bcs` formats an array of `Bench`es into an md-table whose columns are
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
`benchOutput` prints the "significant" changes in numbers of instructions. -/
def benchOutput (js : System.FilePath) : IO Unit := do
  let dats ← IO.ofExcept (Json.parse (← IO.FS.readFile js) >>= fromJson? (α := Array Bench))
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
  for (bound, gs) in ts2 do
    IO.println <|
      match bound with
        | none => -- `bound = none`: these entries are "singleton" files in their range
          toTable gs
        | some roundedDiff => -- these instead should be a collapsible summary
          toCollapsibleTable gs roundedDiff

#eval benchOutput "benchOutput.json"

end BenchAction
