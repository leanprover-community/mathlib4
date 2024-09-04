import Lean.Data.Json.FromToJson
import Lean.Data.Json.Parser

open Lean

/-- `Bench` is a structure with the data used to compute the `!bench` summary.
It contains
* a string `file` (that could be `build`);
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

/-- uses `intDecs` to format an integer as `±x.y⬝10⁹`. -/
def formatDiff (z : Int) : String :=
  let (sgn, intDigs, decDigs) := intDecs z
  s!"{sgn}{intDigs}.{decDigs}⬝10⁹"

/-- uses `intDecs` to format an integer as `±x.y%`. -/
def formatPerc (z : Int) (exp : Nat := 9) (prec : Nat := 3) : String :=
  let (sgn, intDigs, decDigs) := intDecs z exp prec
  s!"({sgn}{intDigs}.{decDigs}%)"

/-- converts a `Bench.reldiff` into a formatted string of the form `±z.w%`. -/
def formatPercent (reldiff : Float) : String :=
  let reldiff := reldiff * 10 ^ 4
  let (sgn : Int) := if reldiff < 0 then -1 else 1
  let (sgnf : Float) := if reldiff < 0 then -1 else 1
  let reldiff := sgnf * reldiff
  formatPerc (sgn * reldiff.toUInt32.val) 0 2

def formatFile (file : String) : String :=
  "`" ++ file.dropWhile (!·.isAlpha) ++ "`"

/-- converts a `Bench` into a formatted string of the form `| file | ±x.y⬝10⁹ | ±z.w% |`. -/
def summary (bc : Bench) : String :=
  let reldiff := bc.reldiff --* 10 ^ 4
  --let (sgn : Int) := if reldiff < 0 then -1 else 1
  let (sgnf : Float) := if reldiff < 0 then -1 else 1
  let middle := [formatFile bc.file, formatDiff bc.diff, formatPercent (sgnf * reldiff)]
  "|".intercalate (""::middle ++ [""])

def formatArrayBench (bound : Int) (arr : Array Bench) : String :=
  if arr.size ≤ 2 then
    "\n".intercalate (arr.map summary).toList
    --"".intercalate (files.map fun (b, f) => s!"|{f.file}|{b}|{f.reldiff}|").toList
  else
    let fils := s!"<details><summary>{arr.size} files </summary>{", ".intercalate (arr.toList.map (s!"{·.file.dropWhile (!·.isAlpha)}"))}</details>"
    let files := arr.map (s!"{bound}·10⁹", ·)
    "|<" ++ (summary {file := fils, diff := bound*10^9, reldiff := default}).drop 1
    --s!"|<details><summary>{arr.size} files </summary>{", ".intercalate (files.toList.map (fun (_, f) => s!"{f.file}, {f.reldiff}%"))}</details>|~{bound}||"

def tableArrayBench (arr : Array Bench) : String :=
  let header := "|File|Instructions|%|\n|-|-:|:-:|"
  "\n".intercalate (header :: (arr.map summary).toList)

/-- Assuming that the input is a `json`-string formatted to produce an array of `Bench`,
`benchOutput` prints the "significant" changes in numbers of instructions. -/
def benchOutput (js : System.FilePath) : IO Unit := do
  let dats ← IO.ofExcept (Json.parse (← IO.FS.readFile js) >>= fromJson? (α := Array Bench))
  --let dats := dats.push {file := "neg1", diff := -10^10, reldiff := -0.5}
  --let dats := dats.push {file := "neg2", diff := -10^11, reldiff := -0.3}
  let (head, dats) := dats.partition (·.file.take 1 != "~")
  let (pos, neg) := dats.partition (0 < ·.diff)
  let grouped := dats.groupByKey (·.diff / (10 ^ 9))
  --let mut (tallied) := (#[])
  --for gp@(_i, arr) in grouped do
    --if (arr.getD 0 default).file == "build" then
    --  head := #[gp] ++ head
    --else
    --if (arr.getD 0 default).file == "lint" then
    --  head := head.push gp
    --else
  --    tallied := tallied.push gp
  let sortHead := (head.qsort (·.file < ·.file)).map (0, #[·])
  let togetherSorted := sortHead ++ grouped.toArray.qsort (·.1 > ·.1)
  let ts1 := togetherSorted.toList.groupBy (·.2.size == 1 && ·.2.size == 1)
  let ts2 := List.join <| ts1.map fun l =>
    if (l.getD 0 default).2.size == 1 then
      [(none, (l.map Prod.snd).foldl (· ++ ·) #[])]
    else l.map fun (n, ar) => (some n, ar)
/-
  for (roundedDiff, g) in togetherSorted do
    --let instrs := (g.getD 0 default).diff / 10^9
    --let (s, a) :=
    --  match g with
    --    | #[g] => (g.file.dropWhile (!·.isAlpha), [formatDiff g.diff, formatPercent g.reldiff])
    --    | _ => (s!"{g.size} files", [formatDiff <| roundedDiff * 10 ^ 9])
    let entry :=
      match g with
        | #[g] => (formatFile g.file ++ s!", Instructions {", ".intercalate [formatDiff g.diff, formatPercent (g.reldiff)]}\n")
        | _ => s!"<details><summary>{g.size} files, Instructions {formatDiff <| roundedDiff * 10 ^ 9}</summary>\n\n{tableArrayBench (g.qsort (·.diff > ·.diff))}\n</details>"
-/
  for (roundedDiff, gs) in ts2 do
    --let instrs := (g.getD 0 default).diff / 10^9
    --let (s, a) :=
    --  match g with
    --    | #[g] => (g.file.dropWhile (!·.isAlpha), [formatDiff g.diff, formatPercent g.reldiff])
    --    | _ => (s!"{g.size} files", [formatDiff <| roundedDiff * 10 ^ 9])
    let entry :=
      match roundedDiff with
        | none => tableArrayBench gs
        | some roundedDiff => s!"<details><summary>{gs.size} files, Instructions {formatDiff <| roundedDiff * 10 ^ 9}</summary>\n\n" ++ tableArrayBench (gs.qsort (·.diff > ·.diff)) ++ "\n</details>"
        --(s!"{g.size} files", [formatDiff <| roundedDiff * 10 ^ 9])
    --let summ := s!"<summary>{s}, Instructions {", ".intercalate a}</summary>"
    --let indentTable := (tableArrayBench g).replace "\n" "\n  "
    --IO.println <| s!"\n* <details>{summ}\n\n  {indentTable}\n  </details>"
    IO.println <| entry
  IO.println <| s!"\n* <details><summary>{grouped.size} files</summary>\n\n  ".intercalate (""::((grouped.toArray.map Prod.snd).map tableArrayBench).toList.map (·.replace "\n" "\n  " ++ "\n  </details>"))
  let head := (head.qsort (·.file < ·.file)).map fun d => (d.diff / (10 ^ 9), #[d])
  let withSize := head ++ grouped.toArray.qsort (·.1 > ·.1)
  let fmt := withSize.map (fun (a, b) => formatArrayBench a b)
  let header := "|File|Instructions|%|\n|-|-:|:-:|"
  IO.println <| "\n".intercalate (header :: fmt.toList)
  --for (i, arr) in withSize do
  --  dbg_trace (i, arr.map (·.file))
  let mut msg := #["Report", s!"{header}\n|`Increase`|||"]
  --let mut msg' := #["Report", s!"{header}\n|`Increase`|||"]
  for d in pos.qsort (·.diff > ·.diff) do
    msg := msg.push (summary d)
  msg := msg.push s!"|`Decrease`|||"
  for d in neg.qsort (·.diff < ·.diff) do
    msg := msg.push (summary d)
  --IO.println ("\n".intercalate msg.toList)

#eval #[0, 1, -1, -2].qsort (· > ·)
#eval #["~M", "b"].qsort (· > ·)
#check List.groupBy

#eval
  benchOutput "benchOutput.json"
#check List.groupBy
#check Array.groupByKey
