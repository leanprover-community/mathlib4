/-
Copyright (c) 2023 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Analysis.Convex.Cone.Proper

/-!

# Cone Programs

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/

open Filter Set Topology ContinuousLinearMap

structure ConeProgram
  (V : Type _) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (W : Type _) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  where
  K : ProperCone ℝ V
  L : ProperCone ℝ W
  obj : V
  lhs : V →L[ℝ] W
  rhs : W

namespace ConeProgram

variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {W : Type _} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
variable (P : ConeProgram V W)

def Objective (v : V) := ⟪P.obj, v⟫_ℝ

def IsSolution (v : V) := v ∈ P.K ∧ P.rhs - P.lhs v ∈ P.L

-- TODO: Show that the set `Solutions := { v | P.IsSolution v }` is itself a `ConvexCone`.

def IsFeasible := Nonempty { v | P.IsSolution v }

def IsOptimalSolution (v : V) :=
  P.IsSolution v ∧ IsGreatest (P.Objective ''  { v | P.IsSolution v }) (P.Objective v)

lemma solution_of_optimalSolution (v : V) (h : P.IsOptimalSolution x) :
  P.IsSolution x := h.1

def Values := P.Objective '' { v | P.IsSolution v }

lemma nonempty_values_iff_feasible : (P.Values).Nonempty ↔ P.IsFeasible := by
    rw [Values, nonempty_image_iff]
    exact Iff.symm nonempty_coe_sort

noncomputable def Value := sSup <| P.Values

lemma value_optimal (h : P.IsOptimalSolution v) : P.Value = P.Objective v := by
  apply IsLUB.csSup_eq <| IsGreatest.isLUB h.2
  rw [nonempty_image_iff]
  exact ⟨v, h.1⟩

----------------------------------------------------------------------------------------------------

def IsSubSolution (seqV : ℕ → V) :=
  ∃ seqW : ℕ → W,
  (∀ n, seqV n ∈ P.K) ∧
  (∀ n, seqW n ∈ P.L) ∧
  (Tendsto (fun n => P.lhs (seqV n) + (seqW n)) atTop (𝓝 P.rhs))

noncomputable def SubObjective (seqV : ℕ → V) := limsup (fun n => P.Objective (seqV n)) atTop

lemma subSolution_of_solution (hx : P.IsSolution x) : P.IsSubSolution <| fun _ => x := by
  use fun _ => P.rhs - P.lhs x
  simpa only [forall_const, add_sub_cancel'_right, tendsto_const_nhds_iff, and_true]

@[simp] lemma subSolution_of_solution_value : P.SubObjective (fun _ => x) = P.Objective x :=
  limsup_const (inner P.obj x)

def IsSubFeasible := Nonempty { x : ℕ → V | P.IsSubSolution x }

lemma subFeasible_of_feasible (h : P.IsFeasible) : P.IsSubFeasible :=
  let ⟨v, hv⟩ := h
  ⟨fun _ => v, P.subSolution_of_solution hv⟩

def SubValues := P.SubObjective '' { seqV | P.IsSubSolution seqV }

lemma nonempty_subValues_iff_subFeasible : (P.SubValues).Nonempty ↔ P.IsSubFeasible := by
    rw [SubValues, nonempty_image_iff]
    exact Iff.symm nonempty_coe_sort

noncomputable def SubValue := sSup <| P.SubValues

----------------------------------------------------------------------------------------------------

@[simp] lemma values_subset_subValues : P.Values ⊆ P.SubValues := fun r ⟨v, hv, hvr⟩ =>
  ⟨fun _ => v, P.subSolution_of_solution hv, by rwa [P.subSolution_of_solution_value]⟩

lemma value_le_subValue (fs : P.IsFeasible) (bdd : BddAbove P.SubValues) :
  P.Value ≤ P.SubValue :=
  csSup_le_csSup bdd (P.nonempty_values_iff_feasible.2 fs) P.values_subset_subValues

----------------------------------------------------------------------------------------------------

noncomputable def Dual : ConeProgram W V where
  K := (P.L).dual
  L := (P.K).dual
  obj := -P.rhs
  lhs := -adjoint P.lhs
  rhs := -P.obj

theorem dual_dual : (P.Dual).Dual = P := by dsimp [Dual] ; simp

theorem weak_duality_aux (seqV : ℕ → V) (hv : P.IsSubSolution seqV) (hw : (P.Dual).IsSolution w) :
  P.SubObjective seqV ≤ - (P.Dual).Objective w := by
    rcases hv with ⟨seqW, hseqV, hseqW, htends⟩
    rcases hw with ⟨hw1, hw2⟩
    dsimp [Dual] at hw2
    have h : ∀ n, 0 ≤ ⟪w, P.lhs (seqV n) + seqW n⟫_ℝ - ⟪P.obj, seqV n⟫_ℝ := fun n => by
      calc 0
        ≤ ⟪adjoint P.lhs w - P.obj, seqV n⟫_ℝ + ⟪w, seqW n⟫_ℝ := by {
          refine' add_nonneg _ _
          . specialize hw2 (seqV n) (hseqV n)
            rwa [sub_neg_eq_add, neg_add_eq_sub, real_inner_comm _ _] at hw2
          . specialize hw1 (seqW n) (hseqW n)
            rwa [real_inner_comm _ _] }
      _ = ⟪adjoint P.lhs w, seqV n⟫_ℝ - ⟪P.obj, seqV n⟫_ℝ + ⟪w, seqW n⟫_ℝ := by rw [← inner_sub_left]
      _ = ⟪adjoint P.lhs w, seqV n⟫_ℝ + ⟪w, seqW n⟫_ℝ - ⟪P.obj, seqV n⟫_ℝ := by rw [add_sub_right_comm]
      _ = ⟪w, P.lhs (seqV n)⟫_ℝ + ⟪w, seqW n⟫_ℝ - ⟪P.obj, seqV n⟫_ℝ := by rw [ContinuousLinearMap.adjoint_inner_left]
      _ = ⟪w, P.lhs (seqV n) + seqW n⟫_ℝ - ⟪P.obj, seqV n⟫_ℝ := by rw [inner_add_right]
    have : P.SubObjective seqV ≤ ⟪w, P.rhs⟫_ℝ := by
      calc
        P.SubObjective seqV
          = limsup (fun n => P.Objective (seqV n)) atTop := by rfl
          = limsup (fun n => ⟪P.obj, seqV n⟫_ℝ) atTop := by rfl
        _ ≤ ⟪w, P.rhs⟫_ℝ := by sorry
    rwa [Objective, Dual, inner_neg_left, neg_neg, real_inner_comm]

theorem weak_duality (hP : P.IsSubFeasible) (hD : (P.Dual).IsFeasible) :
  P.SubValue ≤ -(P.Dual).Value := by
    apply csSup_le <| P.nonempty_subValues_iff_subFeasible.2 hP
    rintro x ⟨v, hv1, hv2⟩
    rw [le_neg]
    apply csSup_le <| (P.Dual).nonempty_values_iff_feasible.2 hD
    rintro y ⟨w, hw1, hw2⟩
    simp at *
    rw [← hv2, ← hw2, le_neg]
    apply P.weak_duality_aux v hv1 hw1

theorem weak_duality_aux' (hv : P.IsSolution v) (hw : (P.Dual).IsSolution w) :
  P.Objective v ≤ - (P.Dual).Objective w := by
    rw [← subSolution_of_solution_value]
    apply weak_duality_aux
    apply P.subSolution_of_solution hv
    exact hw

theorem weak_duality' (hP : P.IsFeasible) (hD : (P.Dual).IsFeasible) :
  P.Value ≤ -(P.Dual).Value := by
    apply csSup_le <| P.nonempty_values_iff_feasible.2 hP
    rintro v ⟨_, hv2, hv3⟩
    rw [le_neg]
    apply csSup_le <| (P.Dual).nonempty_values_iff_feasible.2 hD
    rintro w ⟨_, hw2, hw3⟩
    rw [← hv3, ← hw3, le_neg]
    exact P.weak_duality_aux' hv2 hw2

-- def SlaterCondition := ∃ v : P.K, P.rhs - P.lhs v ∈ interior P.L

-- theorem Value_eq_SubValue  (fs : P.IsFeasible) (bdd : BddAbove P.SubValues)
--   (sl : P.SlaterCondition) : P.Value = P.SubValue := by
--   apply le_antisymm (P.Value_le_Subvalue fs bdd)
--   by_contra'

-- example
--   (v w : V)
--   (seq : ℕ → V)
--   (htends : Tendsto (fun n => seq n) atTop (nhds v)) :
--   Tendsto (fun n => ⟪seq n, w⟫_ℝ) atTop (nhds ⟪v, w⟫_ℝ) := htends.inner tendsto_const_nhds

-- example
--   (v w : V)
--   (seq : ℕ → V)
--   (htends : Tendsto (fun n => seq n) atTop (nhds v)) :
--   limsup (fun n => ⟪seq n, w⟫_ℝ) atTop = ⟪v, w⟫_ℝ := (htends.inner tendsto_const_nhds).limsup_eq

end ConeProgram
