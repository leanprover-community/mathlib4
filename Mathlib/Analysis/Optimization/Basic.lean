import Mathlib.Data.Real.Basic

structure MinimizationProblem (𝕜 : Type _) [LE 𝕜] (V : Type _) where
  objective : V → 𝕜
  constraint : Set V

namespace MinimizationProblem

variable {𝕜 : Type _} [LE 𝕜]
variable {V : Type _}
variable (P : MinimizationProblem 𝕜 V)

def IsSolution (x : V) := x ∈ P.constraint

def FeasibleSet := { x | P.IsSolution x }

def IsFeasible := Nonempty P.FeasibleSet

def FeasibleValues := P.objective '' P.FeasibleSet

def OptimalValue [SupSet 𝕜] := sSup P.FeasibleValues

def IsBounded := ∃ k, ∀ l ∈ P.FeasibleValues, l ≤ k

def IsOptimalSolution (x : V) := P.IsSolution x ∧ ∀ y, P.IsSolution y → P.objective x ≤ P.objective y

def HasOptimalSolution := ∃ x, P.IsOptimalSolution x

end MinimizationProblem
