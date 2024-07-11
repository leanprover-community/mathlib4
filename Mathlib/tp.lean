import Lean.Elab.Command

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
  deriving FromJson, ToJson

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

/-- converts a `Bench` into a formatted string of the form `| file | ±x.y⬝10⁹ | ±z.w% |`. -/
def summary (bc : Bench) :=
  let instrs := bc.diff
  let reldiff := bc.reldiff * 10 ^ 4
  let (sgn : Int) := if reldiff < 0 then -1 else 1
  let (sgnf : Float) := if reldiff < 0 then -1 else 1
  let reldiff := sgnf * reldiff
  let middle :=
    [bc.file.dropWhile (!·.isAlpha), formatDiff instrs, formatPerc (sgn * reldiff.toUInt32.val) 0 2]
  "|".intercalate (""::middle ++ [""])

/-- Assuming that the input is a `json`-string formatted to produce an array of `Bench`,
`benchOutput` prints the "significant" changes in numbers of instructions. -/
def benchOutput (js : System.FilePath) : IO Unit := do
  let dats ← IO.ofExcept (Json.parse (← IO.FS.readFile js) >>= fromJson? (α := Array Bench))
  let (pos, neg) := dats.partition (0 < ·.diff)
  let header := "|File|Instructions|%|\n|-|-:|:-:|"
  let mut msg := #[s!"{header}\n|`Increase`|||"]
  for d in pos.qsort (·.diff > ·.diff) do
    msg := msg.push (summary d)
  msg := msg.push s!"|`Decrease`|||"
  for d in neg.qsort (·.diff < ·.diff) do
    msg := msg.push (summary d)
  IO.println ("\n".intercalate msg.toList)

run_cmd benchOutput "benchOutput.json"
