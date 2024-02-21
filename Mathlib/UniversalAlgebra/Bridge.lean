import Mathlib.UniversalAlgebra.Init

@[lawvere]
class AA (X Y : Type*) where
  x : X
  y : X
  h : x = y

#check AA.SortType.Y
--#eval lawvere_context% AA

#eval lawvere_context% AA
