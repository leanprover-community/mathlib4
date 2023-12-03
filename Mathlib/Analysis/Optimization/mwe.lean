import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Cone.Pointed

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m]
variable (A : Matrix m n ℝ) (b : m → ℝ)

-- works
noncomputable def mulVec_convexCone : PointedCone ℝ (n → ℝ) where
  carrier := { x : n → ℝ | 0 ≤ mulVec A x }
  add_mem' := by
    rintro v w hv hw
    rw [Set.mem_setOf_eq, mulVec_add]
    exact add_nonneg hv hw
  zero_mem' := by simp
  smul_mem' := by
    rintro ⟨c, hc⟩ v hv
    dsimp only [Set.mem_setOf_eq, id_eq, eq_mpr_eq_cast, cast_eq, Nonneg.mk_smul] at *
    rw [mulVec_smul]
    exact smul_nonneg hc hv

-- fails
noncomputable def mulVec_convexCone' : PointedCone ℝ (EuclideanSpace ℝ n) where
  carrier := { x : EuclideanSpace ℝ n | 0 ≤ mulVec A x }
  add_mem' := by
    rintro v w hv hw
    rw [Set.mem_setOf_eq, mulVec_add] --error
    exact add_nonneg hv hw
  zero_mem' := by simp
  smul_mem' := by
    rintro ⟨c, hc⟩ v hv
    dsimp only [Set.mem_setOf_eq, id_eq, eq_mpr_eq_cast, cast_eq, Nonneg.mk_smul] at *
    rw [mulVec_smul]
    exact smul_nonneg hc hv
