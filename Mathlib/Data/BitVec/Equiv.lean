import Mathlib.Data.BitVec.Lemmas
import Mathlib.Algebra.BigOperators.Fin

namespace Std.BitVec

variable {w : ℕ}

def finEquiv : BitVec w ≃ Fin (2 ^ w) where
  toFun     := toFin
  invFun    := ofFin
  left_inv  := ofFin_toFin
  right_inv := toFin_ofFin

def finFunctionEquiv : BitVec w ≃ (Fin w → Bool) := calc
  BitVec w  ≃ (Fin (2 ^ w))     := finEquiv
  _         ≃ (Fin w -> Fin 2)  := finFunctionFinEquiv.symm
  _         ≃ (Fin w -> Bool)   := Equiv.arrowCongr (.refl _) finTwoEquiv

end Std.BitVec
