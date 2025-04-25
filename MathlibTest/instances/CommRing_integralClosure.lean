import Mathlib

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/category.20theory.20import.20breaks.20CommRing.20synthesis/near/449132250

variable (R : Type) (A : Type) [CommRing R] [CommRing A] [Algebra R A]

/-- info: (integralClosure R A).toCommRing -/
#guard_msgs in
#synth CommRing (integralClosure R A)
