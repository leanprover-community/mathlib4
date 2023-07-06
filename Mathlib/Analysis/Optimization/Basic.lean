import Mathlib.Data.Real.Basic

structure MinimizationProblem (𝕜 : Type _) [Preorder 𝕜] (V : Type _) where
  cost : V → 𝕜
  constraint : Set V

namespace MinimizationProblem

variable {𝕜 : Type _} [Preorder 𝕜]
variable {V : Type _}
variable (P : MinimizationProblem 𝕜 V)

def IsFeasible := Nonempty P.constraint

def IsSolution (x : V) := x ∈ P.constraint

def IsOptimalSolution (x : V) := P.IsSolution x ∧ ∀ y, P.IsSolution y → P.cost x ≤ P.cost y

def Costs := P.cost '' { x | P.IsSolution x }

lemma nonempty_costs_of_feasible (h : P.IsFeasible) : P.Costs.Nonempty := by
  rcases h with ⟨v, hv⟩
  use P.cost v, v
  exact ⟨hv, by rfl⟩

def OptimalCost [SupSet 𝕜] := sSup P.Costs

end MinimizationProblem
