import Mathlib.Lean.Expr.Basic
import Mathlib

open Lean

-- Mostly courtesy of Floris van Doorn
run_cmd do
  -- all constants in imported files
  let constants := (← getEnv).constants.map₁.toList.map (·.1)
  -- remove some auto-generated constants
  let constants ← constants.filterM fun nm ↦ return !(← nm.isBlackListed)
  IO.FS.writeFile (System.FilePath.mk "constants.txt") (String.intercalate "\n" (constants.map toString))
  -- print first 100
  logInfo m!"{constants.length}"
