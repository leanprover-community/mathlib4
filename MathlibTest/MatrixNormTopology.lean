import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Matrix

/-! # Regression tests: elementwise matrix norm vs the ambient matrix topology

The scoped elementwise matrix norm (`Matrix.seminormedAddCommGroup`, scope
`Matrix.Norms.Elementwise`) induces a topology that is definitionally equal to
the ambient `instTopologicalSpaceMatrix` (the `Pi` topology).  These tests pin
down that the agreement is visible to *instance resolution*: without the
`replaceTopology` anchor in `Matrix.seminormedAddCommGroup`, the `Norm`
synthesis below fails even though the `rfl` example succeeds.
-/

open scoped Matrix.Norms.Elementwise

variable {m n : Type*} [Fintype m] [Fintype n]

-- The norm-induced topology is definitionally the ambient (`Pi`) topology.
example :
    (instTopologicalSpaceMatrix : TopologicalSpace (Matrix m n ℝ)) =
      (Matrix.seminormedAddCommGroup :
        SeminormedAddCommGroup (Matrix m n ℝ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
  rfl

-- ... and the same for the `NormedAddCommGroup` instance.
example :
    (instTopologicalSpaceMatrix : TopologicalSpace (Matrix m n ℝ)) =
      (Matrix.normedAddCommGroup :
        NormedAddCommGroup (Matrix m n ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace :=
  rfl

-- Operator-norm synthesis for continuous linear maps between matrix types
-- (whose types are formed with the ambient topology).
noncomputable example : Norm (Matrix m n ℝ →L[ℝ] Matrix m n ℝ) := inferInstance

-- The operator norm is actually usable.
noncomputable example (f : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) : ℝ := ‖f‖

-- Smul-continuity over the norm-induced topology unifies with the ambient
-- `ContinuousConstSMul` instance from `Topology.Instances.Matrix`.
example : ContinuousConstSMul ℝ (Matrix m n ℝ) := inferInstance
