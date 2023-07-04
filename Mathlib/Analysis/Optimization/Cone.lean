import Mathlib.Data.Real.EReal
import Mathlib.Analysis.Convex.Cone.Proper
import Mathlib.Analysis.Optimization.Basic

open Filter Set


structure ConeProgram
  (V : Type _) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (W : Type _) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  where
  c : V
  b : W
  A : V →L[ℝ] W
  K : ProperCone ℝ V
  L : ProperCone ℝ W

namespace ConeProgram

variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {W : Type _} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
variable (P : ConeProgram V W)

def toMinProb (P : ConeProgram V W) : MinimizationProblem EReal V where
  objective := fun v => ⟪P.c, v⟫_ℝ
  constraint := {x | x ∈ P.K ∧ P.A x - P.b ∈ P.L}

def IsSubsolution (seq : ℕ → V × W) : Prop :=
  Tendsto (fun n => P.A (seq n).1 + (seq n).2) atTop (nhds P.b)

def SubfeasibleSet := { seq | P.IsSubsolution seq }

noncomputable def OptimalSubvalue :=
  sSup <| (fun seq => iSup <| fun n => P.toMinProb.objective (seq n).1) '' P.SubfeasibleSet

def SlaterCondition := Nonempty <| interior <| P.toMinProb.constraint

theorem value_le_subvalue (h : Bounded P.OptimalSubvalue)
  : P.toMinProb.OptimalValue ≤ P.OptimalSubvalue := by
  unfold MinimizationProblem.OptimalValue
  apply @sSup_le _ _ P.toMinProb.FeasibleValues P.OptimalSubvalue
  unfold ConeProgram.OptimalSubvalue

  sorry


theorem value_subvalue (h : P.SlaterCondition) : P.toMinProb.OptimalValue = P.OptimalSubvalue := by
  rcases h with ⟨v, openSet, ⟨hIsOpen, hIsSubset⟩, hv⟩
  unfold MinimizationProblem.OptimalValue
  unfold ConeProgram.OptimalSubvalue
  simp
  sorry

end ConeProgram





-- def isFeasibleSolution (x : V) : Prop :=
--   x ∈ P.K ∧ ∃ l ∈ P.L, P.RHS = P.LHS x + P.RHS

-- def FeasibleSet := { x | P.isFeasibleSolution x }

-- def isFeasible : Prop := Nonempty { x | P.isFeasibleSolution x}

-- noncomputable def Value := sSup <| P.obj '' P.FeasibleSet

-- noncomputable def OptimalSolution (x : V) : Prop :=
--   P.isFeasibleSolution x ∧ ∀ y, P.isFeasibleSolution y → P.obj y ≤ P.obj x






-- end Primal
