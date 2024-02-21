import Mathlib.UniversalAlgebra.Init

@[lawvere]
class AA (X Y : Type*) where
  x : X → X → X
  y : X
  h : x y y = y

#print AA.OpType
--#eval lawvere_context% AA

#eval lawvere_context% AA
