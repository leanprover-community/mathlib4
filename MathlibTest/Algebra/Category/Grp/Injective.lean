import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Topology.Instances.AddCircle.Defs

open CategoryTheory

-- This instance used to have a specialized proof, but we can now find it with typeclass synthesis.
-- If this test fails, you should re-add this as a specialized instance.
instance AddCommGrp.injective_ratCircle : Injective <| of <| ULift.{u} <| AddCircle (1 : ℚ) :=
  inferInstance
  -- Proof should be: injective_of_divisible _
