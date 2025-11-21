/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Transfer algebraic structures across `Equiv`s

In this file, we transfer a (pseudo-)metric space, (semi-)normed additive commutive group
and normed space structures across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

variable {α β : Type*}

namespace Equiv

variable (e : α ≃ β)

/-- Transfer a `Dist` across an `Equiv` -/
protected abbrev dist (e : α ≃ β) : ∀ [Dist β], Dist α := ⟨fun x y ↦ dist (e x) (e y)⟩

/-- Transfer a `PseudoMetricSpace` across an `Equiv` -/
protected abbrev pseudometricSpace (e : α ≃ β) : ∀ [PseudoMetricSpace β], PseudoMetricSpace α := by
  intros
  let := e.dist
  exact {
    dist_self x := PseudoMetricSpace.dist_self (e x)
    dist_comm x y := PseudoMetricSpace.dist_comm (e x) (e y)
    dist_triangle x y z := PseudoMetricSpace.dist_triangle (e x) (e y) (e z)
  }

/-- Transfer a `MetricSpace` across an `Equiv` -/
protected abbrev metricSpace (e : α ≃ β) : ∀ [MetricSpace β], MetricSpace α := by
  intros
  let := e.pseudometricSpace
  exact {
    eq_of_dist_eq_zero {x} {y} hxy := by
      rw [← e.symm_apply_apply x, ← e.symm_apply_apply y, MetricSpace.eq_of_dist_eq_zero hxy]
  }

/-- Transfer a `SeminormedAddCommGroup` across an `Equiv` -/
protected abbrev seminormedAddCommGroup (e : α ≃ β) :
    ∀ [SeminormedAddCommGroup β], SeminormedAddCommGroup α := by
  intros
  let := e.addCommGroup
  let := e.pseudometricSpace
  exact {
    norm := fun x ↦ ‖e x‖
    dist_eq x y := by
      have aux := SeminormedAddCommGroup.dist_eq (e x) (e y)
      convert aux
      -- TODO: e is linear w.r.t. the addition and subtraction we put
      -- how to make this rigorous in the best way?
      sorry
  }

/-- Transfer a `NormedAddCommGroup` across an `Equiv` -/
protected abbrev normedAddCommGroup (e : α ≃ β) :
    ∀ [NormedAddCommGroup β], NormedAddCommGroup α := by
  intros
  let := e.addCommGroup
  let := e.metricSpace
  exact {
    norm := fun x ↦ ‖e x‖
    dist_eq x y := by
      have aux := NormedAddCommGroup.dist_eq (e x) (e y)
      convert aux
      sorry -- same issue as above
  }

/-- Transfer `NormedSpace` across an `Equiv` -/
protected abbrev normedSpace {𝕜 : Type*} [NormedField 𝕜] (e : α ≃ β) [SeminormedAddCommGroup β] :
    let _ := Equiv.seminormedAddCommGroup e
    ∀ [NormedSpace 𝕜 β], NormedSpace 𝕜 α := by
  intros
  let := e.seminormedAddCommGroup
  let := e.module 𝕜
  refine ⟨?_⟩
  intro r x
  have aux := NormedSpace.norm_smul_le r (e x)
  convert aux
  -- do I need additional facts about the transported module structure?
  sorry

end Equiv
