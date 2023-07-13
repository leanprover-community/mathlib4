/-
Copyright (c) 2023 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Analysis.Convex.Cone.Proper
import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.EReal

/-!

# Cone Programs

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/

open Filter Set Topology ContinuousLinearMap

structure MaxConeLinearProgram
  (V : Type _) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (W : Type _) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  where
  decision_cone : ProperCone ℝ V
  slack_cone : ProperCone ℝ W
  cost : V
  lhs : V →L[ℝ] W
  rhs : W

namespace MaxConeLinearProgram

variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {W : Type _} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
variable (P : MaxConeLinearProgram V W)

def Objective (v : V) := Real.toEReal ⟪v, P.cost⟫_ℝ

def IsSolution (v : V) := v ∈ P.decision_cone ∧ P.rhs - P.lhs v ∈ P.slack_cone

def HasSolutions := Nonempty { v | P.IsSolution v }

def Values := P.Objective '' { v | P.IsSolution v }

noncomputable def Value := sSup <| P.Values

----------------------------------------------------------------------------------------------------

def IsSubSolution (seqV : ℕ → V) :=
  ∃ seqW : ℕ → W,
  (∀ n, seqV n ∈ P.decision_cone)
  ∧ (∀ n, seqW n ∈ P.slack_cone)
  ∧ (Tendsto (fun n => P.lhs (seqV n) + (seqW n)) atTop (𝓝 P.rhs))

noncomputable def SubObjective (seqV : ℕ → V) := limsup (fun n => P.Objective (seqV n)) atTop

lemma subSolution_of_solution (hx : P.IsSolution x) : P.IsSubSolution <| fun _ => x :=
  let ⟨hx1, _⟩ := hx
  ⟨fun _ => P.rhs - P.lhs x, fun _ => hx1, by simpa⟩

lemma subSolution_of_solution_value : P.SubObjective (fun _ => x) = P.Objective x :=
  limsup_const _

def SubValues := P.SubObjective '' { seqV | P.IsSubSolution seqV }

noncomputable def SubValue := sSup <| P.SubValues

----------------------------------------------------------------------------------------------------

@[simp] lemma values_subset_subValues : P.Values ⊆ P.SubValues := fun r ⟨v, hv, hvr⟩ =>
  ⟨fun _ => v, P.subSolution_of_solution hv, by rwa [P.subSolution_of_solution_value]⟩

lemma value_le_subValue : P.Value ≤ P.SubValue  := sSup_le_sSup P.values_subset_subValues

----------------------------------------------------------------------------------------------------

noncomputable def Dual : MaxConeLinearProgram W V where
  decision_cone := (P.slack_cone).dual
  slack_cone := (P.decision_cone).dual
  cost := -P.rhs
  lhs := -adjoint P.lhs
  rhs := -P.cost

theorem dual_dual : (P.Dual).Dual = P := by dsimp [Dual]; simp

theorem weak_duality_aux {seqV : ℕ → V} (hv : P.IsSubSolution seqV) (hw : (P.Dual).IsSolution w) :
  P.SubObjective seqV ≤ -(P.Dual).Objective w := by

    rcases hv with ⟨seqW, hseqV, hseqW, htends⟩
    have htends' : Tendsto (fun n => ⟪P.lhs (seqV n) + seqW n, w⟫_ℝ) atTop (𝓝 ⟪P.rhs, w⟫_ℝ) :=
      htends.inner tendsto_const_nhds
    rw [← EReal.tendsto_coe] at htends'

    rcases hw with ⟨hw1, hw2⟩
    dsimp [Dual] at hw2

    have h : ∀ n, 0 ≤ ⟪P.lhs (seqV n) + seqW n, w⟫_ℝ - ⟪seqV n, P.cost⟫_ℝ := fun n => by
      calc 0
        ≤ ⟪seqV n, adjoint P.lhs w - P.cost⟫_ℝ + ⟪seqW n, w⟫_ℝ := by {
            refine' add_nonneg _ (hw1 (seqW n) (hseqW n))
            specialize hw2 (seqV n) (hseqV n)
            rwa [sub_neg_eq_add, neg_add_eq_sub] at hw2 }
      _ = ⟪seqV n, adjoint P.lhs w⟫_ℝ - ⟪seqV n, P.cost⟫_ℝ + ⟪seqW n, w⟫_ℝ := by
        rw [← inner_sub_right]
      _ = ⟪seqV n, adjoint P.lhs w⟫_ℝ + ⟪seqW n, w⟫_ℝ - ⟪seqV n, P.cost⟫_ℝ := by
        rw [add_sub_right_comm]
      _ = ⟪P.lhs (seqV n), w⟫_ℝ + ⟪seqW n, w⟫_ℝ - ⟪seqV n, P.cost⟫_ℝ := by
        rw [ContinuousLinearMap.adjoint_inner_right]
      _ = ⟪P.lhs (seqV n) + seqW n, w⟫_ℝ - ⟪seqV n, P.cost⟫_ℝ := by rw [inner_add_left]
    simp_rw [sub_nonneg, ← EReal.coe_le_coe_iff] at h

    rw [Objective, Dual, inner_neg_right, real_inner_comm _ _,
       EReal.coe_neg, neg_neg]

    calc P.SubObjective seqV
          = limsup (fun n => P.Objective (seqV n)) atTop := by rfl
        _ = limsup (fun n => Real.toEReal ⟪seqV n, P.cost⟫_ℝ) atTop := by rfl
        _ ≤ limsup (fun n => Real.toEReal ⟪P.lhs (seqV n) + seqW n, w⟫_ℝ) atTop :=
          limsup_le_limsup (eventually_of_forall h) (by isBoundedDefault) (by isBoundedDefault)
        _ = ⟪P.rhs, w⟫_ℝ := htends'.limsup_eq

theorem weak_duality : P.SubValue ≤ -(P.Dual).Value := sSup_le <| fun _ ⟨v, hv1, hv2⟩ => by
  apply EReal.le_neg_of_le_neg
  apply sSup_le
  rintro _ ⟨_, hw1, hw2⟩
  rw [← hv2, ← hw2]
  apply EReal.le_neg_of_le_neg
  apply P.weak_duality_aux hv1 hw1

theorem weak_duality_aux' (hv : P.IsSolution v) (hw : (P.Dual).IsSolution w) :
  P.Objective v ≤ - (P.Dual).Objective w := by
    rw [← subSolution_of_solution_value]
    apply weak_duality_aux
    apply P.subSolution_of_solution hv
    exact hw

theorem weak_duality' : P.Value ≤ -(P.Dual).Value := sSup_le <| fun v ⟨_, hv1, hv2⟩ => by
  apply EReal.le_neg_of_le_neg
  apply sSup_le
  rintro _ ⟨_, hw1, hw2⟩
  rw [← hv2, ← hw2]
  apply EReal.le_neg_of_le_neg
  exact P.weak_duality_aux' hv1 hw1

----------------------------------------------------------------------------------------------------

def SlaterCondition := ∃ v : P.decision_cone, P.rhs - P.lhs v ∈ interior P.slack_cone

end MaxConeLinearProgram
