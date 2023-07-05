import Mathlib.Data.Real.EReal
import Mathlib.Analysis.Convex.Cone.Proper
import Mathlib.Analysis.Optimization.Basic

open Filter Set

structure ConeProgram
  (V : Type _) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (W : Type _) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  where
  K : ProperCone ℝ V
  L : ProperCone ℝ W
  c : V
  b : W
  A : V →L[ℝ] W

namespace ConeProgram

variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {W : Type _} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
variable (P : ConeProgram V W)

def toMinProb (P : ConeProgram V W) : MinimizationProblem EReal V where
  cost := fun v => ⟪P.c, v⟫_ℝ
  constraint := {x | x ∈ P.K ∧ P.b - P.A x ∈ P.L}

def IsSubSolution (seqV : ℕ → V) :=
  ∃ seqW : ℕ → W,
  (∀ n, seqV n ∈ P.K) ∧
  (∀ n, seqW n ∈ P.L) ∧
  (Tendsto (fun n => P.A (seqV n) + (seqW n)) atTop (nhds P.b))

def IsSubFeasible := Nonempty { x : ℕ → V | P.IsSubSolution x }

-- def Costs :=  { x | P.SubSolution x }

noncomputable def Subcost (seqV : ℕ → V) :=
  iSup <| fun n => P.toMinProb.cost <| seqV n


lemma subsolution_of_solution (hx : P.toMinProb.IsSolution x) : P.IsSubSolution <| fun _ => x := by
  use fun _ => P.b - P.A x
  simpa only [forall_const, add_sub_cancel'_right, tendsto_const_nhds_iff, and_true]

lemma cost_eq_subsolution_of_solution : P.toMinProb.cost x = P.Subcost (fun _ => x) := by
  simp_rw [subsolution_of_solution, ConeProgram.Subcost, ciSup_const]

def IsOptimalSubSolution (x : ℕ → V) :=
  P.IsSubSolution x ∧ ∀ y, P.IsSubSolution y → P.Subcost x ≤ P.Subcost y

def Subcosts := P.Subcost '' {x | P.IsSubSolution x}

noncomputable def OptimalSubcost  := sSup P.Subcosts


theorem OptimalCost_le_OptimalSubcost (_ : BddAbove P.Subcosts) :
  P.toMinProb.OptimalCost ≤ P.OptimalSubcost := by
    apply sSup_le
    rintro x ⟨v, ⟨hv, heq⟩⟩
    apply le_sSup
    simp_rw [mem_image, mem_setOf_eq]
    use fun _ => v
    constructor
    . apply subsolution_of_solution
      assumption
    . rw [← cost_eq_subsolution_of_solution]
      assumption


  -- unfold MinimizationProblem.OptimalValue
  -- apply @sSup_le _ _ P.toMinProb.FeasibleValues P.OptimalSubvalue
  -- sorry
-- noncomputable def OptimalSubvalue := sSup <| P.Subvalues
-- def SubfeasibleSet := { seq | P.IsSubsolution seq }
-- noncomputable def Subvalues := (fun seq => iSup <| fun n => P.toMinProb.objective (seq n).1) '' P.SubfeasibleSet

def SlaterCondition := Nonempty <| interior <| P.toMinProb.constraint





-- theorem value_subvalue (h : P.SlaterCondition) : P.toMinProb.OptimalValue = P.OptimalSubvalue := by
--   rcases h with ⟨v, openSet, ⟨hIsOpen, hIsSubset⟩, hv⟩
--   unfold MinimizationProblem.OptimalValue
--   unfold ConeProgram.OptimalSubvalue
--   simp
--   sorry

end ConeProgram





-- def isFeasibleSolution (x : V) : Prop :=
--   x ∈ P.K ∧ ∃ l ∈ P.L, P.RHS = P.LHS x + P.RHS

-- def FeasibleSet := { x | P.isFeasibleSolution x }

-- def isFeasible : Prop := Nonempty { x | P.isFeasibleSolution x}

-- noncomputable def Value := sSup <| P.obj '' P.FeasibleSet

-- noncomputable def OptimalSolution (x : V) : Prop :=
--   P.isFeasibleSolution x ∧ ∀ y, P.isFeasibleSolution y → P.obj y ≤ P.obj x






-- end Primal
