import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint

open ContinuousLinearMap

/--
A linear program is an optimization problem with object
-/

structure LinearProgram
  (V : Type _) [NormedOrderedAddGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (W : Type _) [NormedOrderedAddGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    where
  objective : V
  constraints : (V →L[ℝ]W) × W

namespace LinearProgram

variable {V : Type _} [NormedOrderedAddGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {W : Type _} [NormedOrderedAddGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
variable (lp : LinearProgram V W)

def value (v : V) := ⟪lp.objective, v⟫_ℝ

def is_feasible (lp : LinearProgram V W) (v : V) :=
  lp.constraints.1 v ≤ lp.constraints.2 ∧ 0 ≤ v

def is_optimal (lp : LinearProgram V W) (v : V) :=
  lp.is_feasible v ∧ ∀ w : V, lp.is_feasible w → lp.value w ≤ lp.value v

noncomputable def Dual (lp : LinearProgram V W) : LinearProgram W V where
  objective := - lp.constraints.2
  constraints := ⟨adjoint (lp.constraints.1), lp.objective⟩

theorem weak_duality {lp : LinearProgram V W} (v : V) (w : W)
    (hv : lp.is_optimal v) (hw : lp.Dual.is_optimal w) :
    lp.value v ≤ -lp.Dual.value w := by
  sorry

example (u v w : V) (hu : 0 ≤ u) (hvw : v ≤ w) : ⟪u, v⟫_ℝ ≤ ⟪u, w⟫_ℝ := by

  sorry



end LinearProgram
