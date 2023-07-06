import Mathlib.Analysis.Convex.Cone.Proper

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

def Objective (v : V) := ⟪P.c, v⟫_ℝ

-- def Constraint := {v | v ∈ P.K ∧ P.b - P.A v ∈ P.L}

def FeasibleSolution (v : V) := v ∈ P.K ∧ P.b - P.A v ∈ P.L

protected def Nonempty := Nonempty { v | P.FeasibleSolution v }

def OptimalSolution (v : V) :=
  IsGreatest (P.Objective ''  { v | P.FeasibleSolution v }) (P.Objective v)
  -- P.FeasibleSolution v ∧ ∀ v', P.FeasibleSolution v' → P.Objective v' ≤ P.Objective v

def Values := P.Objective '' { v | P.FeasibleSolution v }

noncomputable def Value := sSup <| P.Values

lemma nonempty_values_of_feasible (h : P.Nonempty) : P.Values.Nonempty := by
  unfold Values
  rw [nonempty_image_iff]
  unfold ConeProgram.Nonempty at h
  rwa [nonempty_subtype] at h

lemma value_of_optimal (h : P.OptimalSolution x) : P.Value = P.Objective x := by
  apply IsLUB.csSup_eq <| IsGreatest.isLUB h
  simp
  use x
  let t := h.1
  simp at t

  sorry

----------------------------------------------------------------------------------------------------

def IsFeasibleSeq (seqV : ℕ → V) :=
  ∃ seqW : ℕ → W,
  (∀ n, seqV n ∈ P.K) ∧
  (∀ n, seqW n ∈ P.L) ∧
  (Tendsto (fun n => P.A (seqV n) + (seqW n)) atTop (nhds P.b))

lemma subsolution_of_solution (hx : P.FeasibleSolution x) : P.IsFeasibleSeq <| fun _ => x := by
  use fun _ => P.b - P.A x
  simpa only [forall_const, add_sub_cancel'_right, tendsto_const_nhds_iff, and_true]

def IsSubFeasible := Nonempty { x : ℕ → V | P.IsFeasibleSeq x }

noncomputable def SeqValue (seqV : ℕ → V) := limsup (fun n => P.Objective (seqV n)) atTop

def SeqValues := P.SeqValue '' { seqV | P.IsFeasibleSeq seqV}

noncomputable def SubValue := sSup <| P.SeqValues

----------------------------------------------------------------------------------------------------

def SlaterCondition := ∃ v : P.K, P.b - P.A v ∈ interior P.L

theorem Value_eq_SubValue (sl : P.SlaterCondition) :
  P.Value = P.SubValue := by
  -- unfold Value
  unfold SubValue
  unfold SeqValues
  unfold SeqValue


end ConeProgram
