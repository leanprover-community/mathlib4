import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2

open Matrix

example {n m : Type*} [Fintype n] [Fintype m] (A : Matrix m n ℝ) :
  IsClosedMap (mulVec A) := sorry
