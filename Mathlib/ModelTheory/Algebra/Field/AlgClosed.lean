import Mathlib.ModelTheory.Algebra.Field.CharP
import Mathlib.ModelTheory.Algebra.Field.FreeCommRing
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FreeCommRing

namespace FirstOrder

namespace Language

open field FreeCommRing BigOperators

variable {K : Type _} [Field K]

def genMonicPoly (n : ℕ) : FreeCommRing (Fin (n + 1)) :=
  of 0 ^ n + ∑ i : Fin n, of i.castSucc * of 0 ^ (i : ℕ)

end Language

end FirstOrder
