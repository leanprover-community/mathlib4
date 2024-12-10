-- import Mathlib.Tactic.Tendsto.SignOracle
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

namespace TendstoTactic

open Filter in
inductive FindLimitResult (f : ℝ → ℝ)
| top : Tendsto f atTop atTop → FindLimitResult f
| bot : Tendsto f atTop atBot → FindLimitResult f
| fin (c : ℝ) : Tendsto f atTop (nhds c) → FindLimitResult f

-- structure TendstoConfig where
--   signOracle : SignOracle

-- inductive TendstoException
-- | signOracleException
-- | trimmingException

-- abbrev TendstoM := ExceptT TendstoException <| ReaderM TendstoConfig

-- def runOracle (x : ℝ) : TendstoM <| SignOracleResult x := do
--   match (← read).signOracle x with
--   | .ok cr => return cr
--   | .error _ => throw TendstoException.signOracleException


-- -- todo: rewrite this and remove `signOracle.compare`
-- def compare (x y : ℝ) : TendstoM <| SignOracle.CompareResult x y := do
--   let r := (← read).signOracle.compare x y
--   match r with
--   | .ok cr => return cr
--   | .error _ => throw TendstoException.signOracleException

end TendstoTactic
