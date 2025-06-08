import Mathlib.Analysis.Complex.Basic

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/defeq.20of.20.60NormedAddCommGroup.20.E2.84.82.60/near/422248635
example :
    (NonUnitalNormedRing.toNormedAddCommGroup : NormedAddCommGroup ℂ) =
      Complex.instNormedAddCommGroup := by
  with_reducible_and_instances rfl
