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

structure ConeLinearProgram
  (V : Type _) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (W : Type _) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  where
  decision_cone : ProperCone ℝ V
  slack_cone : ProperCone ℝ W
  cost : V
  lhs : V →L[ℝ] W
  rhs : W

namespace ConeLinearProgram

variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {W : Type _} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
variable (P : ConeLinearProgram V W)

def Objective (v : V) := Real.toEReal ⟪v, P.cost⟫_ℝ

def IsSolution (v : V) := v ∈ P.decision_cone ∧ P.rhs - P.lhs v ∈ P.slack_cone

-- TODO: Show that the set `Solutions := { v | P.IsSolution v }` is itself a `ConvexCone`.

def HasSolutions := Nonempty { v | P.IsSolution v }

-- def IsOptimalSolution (v : V) :=
--   P.IsSolution v ∧ IsLeast (P.Objective ''  { v | P.IsSolution v }) (P.Objective v)

-- lemma solution_of_optimalSolution (h : P.IsOptimalSolution v) : P.IsSolution v := h.1

def Values := P.Objective '' { v | P.IsSolution v }

-- lemma nonempty_values_iff_feasible : (P.Values).Nonempty ↔ P.HasSolutions := by
--   rw [Values, nonempty_image_iff]
--   exact Iff.symm nonempty_coe_sort

noncomputable def Value := sInf <| P.Values

-- lemma value_optimal (h : P.IsOptimalSolution v) : P.Value = P.Objective v :=
--   IsGLB.sInf_eq <| IsLeast.isGLB <| h.2

----------------------------------------------------------------------------------------------------

def IsSubSolution (seqV : ℕ → V) :=
  ∃ seqW : ℕ → W,
  (∀ n, seqV n ∈ P.decision_cone)
  ∧ (∀ n, seqW n ∈ P.slack_cone)
  ∧ (Tendsto (fun n => P.lhs (seqV n) + (seqW n)) atTop (𝓝 P.rhs))

noncomputable def SubObjective (seqV : ℕ → V) := liminf (fun n => P.Objective (seqV n)) atTop

lemma subSolution_of_solution (hx : P.IsSolution x) : P.IsSubSolution <| fun _ => x :=
  let ⟨hx1, _⟩ := hx
  ⟨fun _ => P.rhs - P.lhs x, fun _ => hx1, by simpa⟩

lemma subSolution_of_solution_value : P.SubObjective (fun _ => x) = P.Objective x :=
  liminf_const _

-- def HasSubSolutions := Nonempty { x : ℕ → V | P.IsSubSolution x }

-- lemma subFeasible_of_feasible (h : P.HasSolutions) : P.HasSubSolutions :=
--   let ⟨v, hv⟩ := h
--   ⟨fun _ => v, P.subSolution_of_solution hv⟩

def SubValues := P.SubObjective '' { seqV | P.IsSubSolution seqV }

-- lemma nonempty_subValues_iff_subFeasible : (P.SubValues).Nonempty ↔ P.HasSubSolutions := by
--     rw [SubValues, nonempty_image_iff]
--     exact Iff.symm nonempty_coe_sort

noncomputable def SubValue := sInf <| P.SubValues

----------------------------------------------------------------------------------------------------

@[simp] lemma values_subset_subValues : P.Values ⊆ P.SubValues := fun r ⟨v, hv, hvr⟩ =>
  ⟨fun _ => v, P.subSolution_of_solution hv, by rwa [P.subSolution_of_solution_value]⟩

lemma value_le_subValue : P.SubValue ≤ P.Value  := sInf_le_sInf P.values_subset_subValues

----------------------------------------------------------------------------------------------------

noncomputable def Dual : ConeLinearProgram W V where
  K := (P.slack_cone).dual
  L := (P.decision_cone).dual
  obj := -P.rhs
  lhs := -adjoint P.lhs
  rhs := -P.cost

theorem dual_dual : (P.Dual).Dual = P := by dsimp [Dual]; simp

theorem weak_duality_aux (seqV : ℕ → V) (hv : P.IsSubSolution seqV) (hw : (P.Dual).IsSolution w) :
  -(P.Dual).Objective w ≤ P.SubObjective seqV := by

    rcases hv with ⟨seqW, hseqV, hseqW, htends⟩
    have htends' : Tendsto (fun n => ⟪P.lhs (seqV n) + seqW n, w⟫_ℝ) atTop (𝓝 ⟪P.rhs, w⟫_ℝ) :=
      htends.inner tendsto_const_nhds
    rw [← EReal.tendsto_coe] at htends'

    rcases hw with ⟨hw1, hw2⟩
    dsimp [Dual] at hw2

    have h : ∀ n, ⟪P.lhs (seqV n) + seqW n, w⟫_ℝ - ⟪seqV n, P.cost⟫_ℝ ≤ 0 := by sorry
    simp_rw [sub_nonneg, ← EReal.coe_le_coe_iff] at h

    rw [Objective, Dual, inner_neg_right, real_inner_comm _ _,
      EReal.neg_le, EReal.coe_neg, EReal.neg_le_neg_iff]

    calc EReal.toReal ⟪P.rhs, w⟫_ℝ ≤ P.SubObjective seqV := sorry
    -- have h : ∀ n, 0 ≤ ⟪P.lhs (seqV n) + seqW n, w⟫_ℝ - ⟪seqV n, P.cost⟫_ℝ := fun n => by
    --   calc 0
    --     ≤ ⟪seqV n, adjoint P.lhs w - P.cost⟫_ℝ + ⟪seqW n, w⟫_ℝ := by {
    --         refine' add_nonneg _ (hw1 (seqW n) (hseqW n))
    --         specialize hw2 (seqV n) (hseqV n)
    --         rwa [sub_neg_eq_add, neg_add_eq_sub] at hw2 }
    --   _ = ⟪seqV n, adjoint P.lhs w⟫_ℝ - ⟪seqV n, P.cost⟫_ℝ + ⟪seqW n, w⟫_ℝ := by
    --     rw [← inner_sub_right]
    --   _ = ⟪seqV n, adjoint P.lhs w⟫_ℝ + ⟪seqW n, w⟫_ℝ - ⟪seqV n, P.cost⟫_ℝ := by
    --     rw [add_sub_right_comm]
    --   _ = ⟪P.lhs (seqV n), w⟫_ℝ + ⟪seqW n, w⟫_ℝ - ⟪seqV n, P.cost⟫_ℝ := by
    --     rw [ContinuousLinearMap.adjoint_inner_right]
    --   _ = ⟪P.lhs (seqV n) + seqW n, w⟫_ℝ - ⟪seqV n, P.cost⟫_ℝ := by rw [inner_add_left]
    -- simp_rw [sub_nonneg, ← EReal.coe_le_coe_iff] at h
    -- have htends' : Tendsto (fun n => ⟪P.lhs (seqV n) + seqW n, w⟫_ℝ) atTop (𝓝 ⟪P.rhs, w⟫_ℝ) :=
    --   htends.inner tendsto_const_nhds
    -- rw [← EReal.tendsto_coe] at htends'
    -- have : P.SubObjective seqV ≤ ⟪P.rhs, w⟫_ℝ := by
    --   calc P.SubObjective seqV
    --       = limsup (fun n => P.Objective (seqV n)) atTop := by rfl
    --     _ = limsup (fun n => Real.toEReal ⟪seqV n, P.cost⟫_ℝ) atTop := by rfl
    --     _ ≤ limsup (fun n => Real.toEReal ⟪P.lhs (seqV n) + seqW n, w⟫_ℝ) atTop := by
    --         norm_cast
    --         refine' limsup_le_limsup (eventually_of_forall h) isCobounded_le_of_bot isBounded_le_of_top
    --     _ = ⟪P.rhs, w⟫_ℝ := htends'.limsup_eq
    -- rw [Objective, Dual, inner_neg_right, real_inner_comm _ _]
    -- simpa

theorem weak_duality : -(P.Dual).Value ≤ P.SubValue := le_sInf <| by
  rintro x ⟨v, hv1, hv2⟩
  rw [EReal.neg_le]
  apply le_sInf
  rintro y ⟨w, hw1, hw2⟩
  rw [EReal.neg_le, ← hv2, ← hw2]
  apply P.weak_duality_aux v hv1 hw1

-- theorem weak_duality_aux' (hv : P.IsSolution v) (hw : (P.Dual).IsSolution w) :
--   P.Objective v ≤ - (P.Dual).Objective w := by
--     rw [← subSolution_of_solution_value]
--     apply weak_duality_aux
--     apply P.subSolution_of_solution hv
--     exact hw

-- theorem weak_duality' (hP : P.HasSolutions) (hD : (P.Dual).HasSolutions) :
--   P.Value ≤ -(P.Dual).Value := by
--     apply csSup_le <| P.nonempty_values_iff_feasible.2 hP
--     rintro v ⟨_, hv2, hv3⟩
--     apply EReal.le_neg_of_le_neg
--     apply csSup_le <| (P.Dual).nonempty_values_iff_feasible.2 hD
--     rintro w ⟨_, hw2, hw3⟩
--     rw [← hv3, ← hw3]
--     apply EReal.le_neg_of_le_neg
--     exact P.weak_duality_aux' hv2 hw2

----------------------------------------------------------------------------------------------------

def SlaterCondition := ∃ v : P.decision_cone, P.rhs - P.lhs v ∈ interior P.slack_cone

end ConeLinearProgram
