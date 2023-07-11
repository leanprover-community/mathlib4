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

def Solution (v : V) := v ∈ P.K ∧ P.b - P.A v ∈ P.L

def IsFeasible := Nonempty { v | P.Solution v }

def OptimalSolution (v : V) :=
  P.Solution v ∧
  IsGreatest (P.Objective ''  { v | P.Solution v }) (P.Objective v)

example (x : ℕ) (S : Set ℕ) (h : IsGreatest S x) : x ∈ S := by exact mem_of_mem_inter_left h

@[simp] lemma Solution_of_OptimalSolution (v : V) (h : P.OptimalSolution x) :
  P.Solution x := h.1

def Values := P.Objective '' { v | P.Solution v }

@[simp] lemma nonempty_values_iff : (P.Values).Nonempty ↔ P.IsFeasible := by
    unfold Values
    rw [nonempty_image_iff]
    exact Iff.symm nonempty_coe_sort

noncomputable def Value := sSup <| P.Values

@[simp] lemma value_optimal (h : P.OptimalSolution v) : P.Value = P.Objective v := by
  apply IsLUB.csSup_eq <| IsGreatest.isLUB h.2
  rw [nonempty_image_iff]
  exact ⟨v, h.1⟩

----------------------------------------------------------------------------------------------------

def SubSolution (seqV : ℕ → V) :=
  ∃ seqW : ℕ → W,
  (∀ n, seqV n ∈ P.K) ∧
  (∀ n, seqW n ∈ P.L) ∧
  (Tendsto (fun n => P.A (seqV n) + (seqW n)) atTop (nhds P.b))

noncomputable def Objective' (seqV : ℕ → V) := limsup (fun n => P.Objective (seqV n)) atTop

@[simp] lemma SubSolution_of_Solution (hx : P.Solution x) : P.SubSolution <| fun _ => x := by
  use fun _ => P.b - P.A x
  simpa only [forall_const, add_sub_cancel'_right, tendsto_const_nhds_iff, and_true]

@[simp] lemma SubSolution_of_Solution_Value : P.Objective' (fun _ => x) = P.Objective x :=
  limsup_const (inner P.c x)

def IsSubFeasible := Nonempty { x : ℕ → V | P.SubSolution x }

def SubValues := P.Objective' '' { seqV | P.SubSolution seqV }

noncomputable def SubValue := sSup <| P.SubValues

----------------------------------------------------------------------------------------------------

@[simp] lemma Values_subset_SubValues : P.Values ⊆ P.SubValues := fun r ⟨v, hv, hvr⟩ =>
  ⟨fun _ => v, P.SubSolution_of_Solution hv, by rwa [P.SubSolution_of_Solution_Value]⟩

lemma Value_le_Subvalue (fs : P.IsFeasible) (bdd : BddAbove P.SubValues) :
  P.Value ≤ P.SubValue := csSup_le_csSup bdd (P.nonempty_values_iff.2 fs) P.Values_subset_SubValues


----------------------------------------------------------------------------------------------------

noncomputable def Dual : ConeProgram W V where
  K := (P.L).dual
  L := (P.K).dual
  c := -P.b
  b := -P.c
  A := -ContinuousLinearMap.adjoint (P.A)

theorem weak_duality_aux
  (hv : P.Solution v) (hw : (P.Dual).Solution w) :
  P.Objective v ≤ - (P.Dual).Objective w := by
    rcases hv with ⟨hv1, hv2⟩
    rcases hw with ⟨hw1, hw2⟩
    specialize @hw2 v hv1
    dsimp [Dual, Objective] at *
    simp_rw [inner_sub_right, inner_neg_right, sub_nonneg, ContinuousLinearMap.adjoint_inner_right,
      neg_le, neg_neg] at hw2
    specialize hw1 (P.b - P.A v) hv2
    rw [inner_sub_left, sub_nonneg] at hw1
    rw [inner_neg_left, neg_neg, real_inner_comm v P.c]
    apply le_trans hw2 hw1

theorem weak_duality (hP : P.IsFeasible) (hD : (P.Dual).IsFeasible) :
  P.Value ≤ -(P.Dual).Value := by
    apply csSup_le (P.nonempty_values_iff.2 hP)
    rintro v ⟨_, hv2, hv3⟩
    rw [le_neg]
    apply csSup_le ((P.Dual).nonempty_values_iff.2 hD)
    rintro w ⟨_, hw2, hw3⟩
    rw [← hv3, ← hw3, le_neg]
    apply P.weak_duality_aux hv2 hw2

-- def SlaterCondition := ∃ v : P.K, P.b - P.A v ∈ interior P.L

-- theorem Value_eq_SubValue  (fs : P.IsFeasible) (bdd : BddAbove P.SubValues)
--   (sl : P.SlaterCondition) : P.Value = P.SubValue := by
--   apply le_antisymm (P.Value_le_Subvalue fs bdd)
--   by_contra'

end ConeProgram
