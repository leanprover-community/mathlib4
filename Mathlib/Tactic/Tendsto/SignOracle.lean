import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

inductive SignOracleResult (x : ℝ)
| pos : 0 < x → SignOracleResult x
| zero : x = 0 → SignOracleResult x
| neg : x < 0 → SignOracleResult x

inductive SignOracleException
| OracleFailed

abbrev SignOracleM := Except SignOracleException

abbrev SignOracle := (x : ℝ) → SignOracleM <| SignOracleResult x


namespace SignOracle

inductive CompareResult (x y : ℝ)
| lt : x < y → CompareResult x y
| eq : x = y → CompareResult x y
| gt : y < x → CompareResult x y

def compare (oracle : SignOracle) (x y : ℝ) : SignOracleM <| CompareResult x y := do
  return match ← oracle (y - x) with
  | .pos _ => .lt (by linarith)
  | .zero _ => .eq (by linarith)
  | .neg _ => .gt (by linarith)

end SignOracle
