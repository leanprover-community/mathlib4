import Mathlib

-- https://github.com/leanprover-community/mathlib4/pull/17557#issuecomment-2426920648

variable (R : Type*) [Ring R] [IsSemisimpleRing R]

example : IsNoetherianRing R := inferInstance
example : IsArtinianRing R := inferInstance
