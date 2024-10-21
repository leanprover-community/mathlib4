import Mathlib

-- https://github.com/leanprover-community/mathlib4/pull/17557#issuecomment-2426920648

variable (R : Type*) [Ring R] [IsSemisimpleRing R]

/-- info: isNoetherian_of_isNoetherianRing_of_finite R R -/
#guard_msgs in
#synth IsNoetherianRing R

/-- info: instIsArtinianOfIsSemisimpleModuleOfFinite -/
#guard_msgs in
#synth IsArtinianRing R
