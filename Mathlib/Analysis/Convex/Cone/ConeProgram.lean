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

open Filter Set Topology

structure ConeProgram
  (V : Type _) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (W : Type _) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  where
  K : ProperCone ℝ V
  L : ProperCone ℝ W
  obj : V
  rhs : W
  lhs : V →L[ℝ] W

namespace ConeProgram

variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {W : Type _} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
variable (P : ConeProgram V W)

def Objective (v : V) := ⟪P.obj, v⟫_ℝ

scoped[ConeProgram] notation x "≼[" L "] " y => y - x ∈ L

def IsSolution (v : V) := v ∈ P.K ∧ P.lhs v ≼[P.L] P.rhs

def IsFeasible := Nonempty { v | P.IsSolution v }

def IsOptimalSolution (v : V) :=
  P.IsSolution v ∧ IsGreatest (P.Objective ''  { v | P.IsSolution v }) (P.Objective v)

@[simp] lemma solution_of_optimalSolution (v : V) (h : P.IsOptimalSolution x) :
  P.IsSolution x := h.1

def Values := P.Objective '' { v | P.IsSolution v }

@[simp] lemma nonempty_values_iff : (P.Values).Nonempty ↔ P.IsFeasible := by
    unfold Values
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
  (Tendsto (fun n => P.lhs (seqV n) + (seqW n)) atTop (𝓝 P.rhs))

noncomputable def SubObjective (seqV : ℕ → V) := limsup (fun n => P.Objective (seqV n)) atTop

@[simp] lemma subSolution_of_solution (hx : P.IsSolution x) : P.IsSubSolution <| fun _ => x := by
  use fun _ => P.rhs - P.lhs x
  simpa only [forall_const, add_sub_cancel'_right, tendsto_const_nhds_iff, and_true]

@[simp] lemma subSolution_of_solution_value : P.SubObjective (fun _ => x) = P.Objective x :=
  limsup_const (inner P.obj x)

def IsSubFeasible := Nonempty { x : ℕ → V | P.IsSubSolution x }

def SubValues := P.SubObjective '' { seqV | P.IsSubSolution seqV }

noncomputable def SubValue := sSup <| P.SubValues

----------------------------------------------------------------------------------------------------

@[simp] lemma Values_subset_SubValues : P.Values ⊆ P.SubValues := fun r ⟨v, hv, hvr⟩ =>
  ⟨fun _ => v, P.subSolution_of_solution hv, by rwa [P.subSolution_of_solution_value]⟩

lemma Value_le_Subvalue (fs : P.IsFeasible) (bdd : BddAbove P.SubValues) :
  P.Value ≤ P.SubValue := csSup_le_csSup bdd (P.nonempty_values_iff.2 fs) P.Values_subset_SubValues

----------------------------------------------------------------------------------------------------

noncomputable def Dual : ConeProgram W V where
  K := (P.L).dual
  L := (P.K).dual
  obj := -P.rhs
  rhs := -P.obj
  lhs := -ContinuousLinearMap.adjoint (P.lhs)

theorem weak_duality_aux (hv : P.IsSolution v) (hw : (P.Dual).IsSolution w) :
  P.Objective v ≤ - (P.Dual).Objective w := by
    rcases hv with ⟨hv1, hv2⟩
    rcases hw with ⟨hw1, hw2⟩
    specialize @hw2 v hv1
    dsimp [Dual, Objective] at *
    simp_rw [inner_sub_right, inner_neg_right, sub_nonneg, ContinuousLinearMap.adjoint_inner_right,
      neg_le, neg_neg] at hw2
    specialize hw1 (P.rhs - P.lhs v) hv2
    rw [inner_sub_left, sub_nonneg] at hw1
    rw [inner_neg_left, neg_neg, real_inner_comm v P.obj]
    exact le_trans hw2 hw1

theorem weak_duality (hP : P.IsFeasible) (hD : (P.Dual).IsFeasible) :
  P.Value ≤ -(P.Dual).Value := by
    apply csSup_le (P.nonempty_values_iff.2 hP)
    rintro v ⟨_, hv2, hv3⟩
    rw [le_neg]
    apply csSup_le ((P.Dual).nonempty_values_iff.2 hD)
    rintro w ⟨_, hw2, hw3⟩
    rw [← hv3, ← hw3, le_neg]
    exact P.weak_duality_aux hv2 hw2

theorem weak_duality_aux' (seqV : ℕ → V) (hv : P.IsSubSolution seqV) (hw : (P.Dual).IsSolution w) :
  P.SubObjective seqV ≤ - (P.Dual).Objective w := by
    rcases hv with ⟨seqW, hseqV, hseqW, htends⟩
    rcases hw with ⟨hw1, hw2⟩
    dsimp [Objective, SubObjective]
    apply limsSup_le_of_le sorry
    dsimp [Dual] at *
    simp at *
    simp only [inner_add_right, inner_neg_right, le_neg_add_iff_add_le, add_zero, ContinuousLinearMap.adjoint_inner_right] at hw2
    use 0 -- fix this
    rintro n hn
    specialize @hw1 (seqW n) (hseqW n)
    specialize @hw2 (seqV n) (hseqV n)
    rw [real_inner_comm (seqV n) _]
    have htends' : Tendsto (fun n => ⟪P.lhs (seqV n), w⟫_ℝ + ⟪seqW n, w⟫_ℝ) atTop (𝓝 ⟪P.rhs, w⟫_ℝ) := by sorry
    have :  ⟪P.lhs (seqV n), w⟫_ℝ ≤ ⟪P.rhs, w⟫_ℝ := by sorry
    exact le_trans hw2 this

theorem weak_duality' (hP : P.IsFeasible) (hD : (P.Dual).IsSubFeasible) :
  P.Value ≤ -(P.Dual).SubValue := by sorry

example (seq : ℕ → ℝ) (c : ℝ) (h : Tendsto seq atTop (nhds c)) (f : ℝ → ℝ) (hf : ContinuousAt f c) :
  Tendsto (fun n => f (seq n)) atTop (nhds (f c)) := by sorry

-- def SlaterCondition := ∃ v : P.K, P.rhs - P.lhs v ∈ interior P.L

-- theorem Value_eq_SubValue  (fs : P.IsFeasible) (bdd : BddAbove P.SubValues)
--   (sl : P.SlaterCondition) : P.Value = P.SubValue := by
--   apply le_antisymm (P.Value_le_Subvalue fs bdd)
--   by_contra'

end ConeProgram

-- local notation "⟪" x ", " y "⟫" => @inner 𝕜 F _ x y
