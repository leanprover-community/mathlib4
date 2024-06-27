import Lean --Mathlib.Tactic
--import Batteries
import Batteries.Data.Rat.Basic
--import Mathlib.adomaniLeanUtils.inspect_syntax

open Lean Elab Command

structure Bench' :=
  file    : String
  diff    : Int
  reldiff : Float
  deriving FromJson, ToJson

  --let exp := 9  -- expected number of digits of the number
  --let prec := 3 -- output number of significant decimal digits
def intDecs (z : Int) (exp : Nat := 9) (prec : Nat := 3) : String × Int × Nat :=
  let sgn := z.sign
  let z := sgn * z
  let p10 : Int := 10 ^ (exp - prec)
  let idec := z / p10
  (if sgn < 0 then "-" else "+", idec / (10 ^ prec), (idec % 10 ^ prec).toNat)

def formatDiff (z : Int) : String :=
  let (sg, intDigs, decDigs) := intDecs z
  s!"{sg}{intDigs}.{decDigs}⬝10⁹"

def formatPerc (z : Int) (exp : Nat := 9) (prec : Nat := 3) : String :=
  let (sgn, intDigs, decDigs) := intDecs z exp prec
  s!"({sgn}{intDigs}.{decDigs}%)"

def summary (bc : Bench') :=
  let instrs := bc.diff
  let reldiff := bc.reldiff * 10 ^ 4
  let (sgn : Int) := if reldiff < 0 then -1 else 1
  let reldiff := (Rat.toFloat sgn) * reldiff
  "|".intercalate ["", bc.file.dropWhile (!·.isAlpha), formatDiff instrs, formatPerc (sgn * reldiff.toUInt32.val) 0 2, ""]

#eval show IO _ from do
  let dats ← IO.ofExcept (Json.parse (← IO.FS.readFile "t2.json") >>= fromJson? (α := List Bench'))
  let (pos, neg) := dats.partition (0 < ·.diff)
  let header := "|File|Instructions|%|\n|-|-:|:-:|"
  IO.println s!"{header}\n|`Increase`|||"
  for d in pos.toArray.qsort fun a b => b.diff < a.diff do
    IO.println (summary d)
  IO.println s!"|`Decrease`|||"
  for d in neg.toArray.qsort fun a b => a.diff < b.diff  do
    IO.println (summary d)
