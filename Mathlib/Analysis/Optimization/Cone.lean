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
variable {P : ConeProgram V W}

def Objective (v : V) := ⟪P.c, v⟫_ℝ

def IsSolution (v : V) := v ∈ P.K ∧ P.b - P.A v ∈ P.L

def IsFeasible := Nonempty { v | P.IsSolution v }

def IsOptimalSolution (v : V) :=
  P.IsSolution v ∧
  IsGreatest (P.Objective ''  { v | P.IsSolution v }) (P.Objective v)

example (x : ℕ) (S : Set ℕ) (h : IsGreatest S x) : x ∈ S := by exact mem_of_mem_inter_left h

@[simp] lemma IsSolution_of_IsOptimalSolution (v : V) (h : P.IsOptimalSolution x) :
  P.IsSolution x := h.1

def Values := P.Objective '' { v | P.IsSolution v }

@[simp] lemma nonempty_values_iff : (P.Values).Nonempty ↔ P.IsFeasible := by
    unfold Values
    unfold IsFeasible
    rw [nonempty_image_iff]
    exact Iff.symm nonempty_coe_sort

noncomputable def Value := sSup <| P.Values

@[simp] lemma value_optimal (h : P.IsOptimalSolution v) : P.Value = P.Objective v := by
  apply IsLUB.csSup_eq <| IsGreatest.isLUB h.2
  rw [nonempty_image_iff]
  exact ⟨v, h.1⟩

----------------------------------------------------------------------------------------------------

def IsSubSolution (seqV : ℕ → V) :=
  ∃ seqW : ℕ → W,
  (∀ n, seqV n ∈ P.K) ∧
  (∀ n, seqW n ∈ P.L) ∧
  (Tendsto (fun n => P.A (seqV n) + (seqW n)) atTop (nhds P.b))

noncomputable def Objective' (seqV : ℕ → V) := limsup (fun n => P.Objective (seqV n)) atTop

@[simp] lemma SubSolution_of_Solution (hx : P.IsSolution x) : P.IsSubSolution <| fun _ => x := by
  use fun _ => P.b - P.A x
  simpa only [forall_const, add_sub_cancel'_right, tendsto_const_nhds_iff, and_true]

@[simp] lemma SubSolution_of_Solution_Value : P.Objective' (fun _ => x) = P.Objective x :=
  limsup_const (inner P.c x)

def IsSubFeasible := Nonempty { x : ℕ → V | P.IsSubSolution x }

def SubValues := P.Objective' '' { seqV | P.IsSubSolution seqV }

noncomputable def SubValue := sSup <| P.SubValues

----------------------------------------------------------------------------------------------------

@[simp] lemma Values_subset_SubValues : P.Values ⊆ P.SubValues := fun r ⟨v, hv, hvr⟩ =>
  ⟨fun _ => v, P.SubSolution_of_Solution hv, by rwa [P.SubSolution_of_Solution_Value]⟩

lemma Value_le_Subvalue (fs : P.IsFeasible) (bdd : BddAbove P.SubValues) :
-- lemma Value_le_Subvalue (ne: Set.Nonempty P.Values) (bdd : BddAbove P.SubValues) :
  P.Value ≤ P.SubValue := csSup_le_csSup bdd (nonempty_values_iff.2 fs) Values_subset_SubValues

def SlaterCondition := ∃ v : P.K, P.b - P.A v ∈ interior P.L

example (x y : ℕ) : x ≤ y → y ≤ x → x = y := by exact fun a a_1 ↦ Nat.le_antisymm a a_1

theorem Value_eq_SubValue  (fs : P.IsFeasible) (bdd : BddAbove P.SubValues)
  (sl : P.SlaterCondition) : P.Value = P.SubValue := by
  apply le_antisymm (P.Value_le_Subvalue fs bdd)
  by_contra'

--   -- unfold Value
--   unfold SubValue
--   unfold SubValues
--   unfold SeqValue


end ConeProgram
