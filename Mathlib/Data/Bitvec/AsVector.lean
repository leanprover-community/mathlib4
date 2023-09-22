import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Vector

#check Vector.mapAccumr

/-!
  A `Bitvec n` is morally a sequence of `n` bits.
  This file establishes a way to shift to this perspective by proving the equivalence between
  `Bitvec n` and `Vector bool n`.
  Furthermore, we show how various (arithmetic) operations on bitvectors relate to a naive
  bit-by-bit implementation of those operations using the vector perspective.
-/

namespace BitVec

variable {n : Nat}

/-- Turn a bitvector into a vector of bools of the same length -/
def asVector : BitVec n → Vector Bool n :=
  sorry

/-- Turn a vector of bools into a bitvector of the same length -/
def ofVector : Vector Bool n → BitVec n :=
  sorry

def vectorEquiv : BitVec n ≃ Vector Bool n where
  toFun := asVector
  invFun := ofVector
  left_inv := sorry
  right_inv := sorry

variable {x y : BitVec n} {m : Nat}

/-!
  ## Bitwise
-/

theorem complement_asVector :
    (~~~x) = (ofVector <| Vector.map not x.asVector) := by
  sorry

theorem and_asVector :
    (x &&& y) = (ofVector <| Vector.map₂ and x.asVector y.asVector) := by
  sorry

theorem or_asVector :
    (x ||| y) = (ofVector <| Vector.map₂ or x.asVector y.asVector) := by
  sorry

theorem xor_asVector :
    (x ^^^ y) = (ofVector <| Vector.map₂ xor x.asVector y.asVector) := by
  sorry

/-
  TODO: `shiftLeft`, `shiftRight`, `rotateLeft`, `rotateRight`
-/

/-!
  ## Comparisons
-/

/-
  TODO: `lt`, `le`, `slt`, `sle`, `sgt`, `sge`
-/

/-!
  ## Arithmetic
-/

theorem add_asVector :
    x + y = (ofVector <| Prod.snd <|
      Vector.mapAccumr₂ (fun x y c => (_, _)) x.asVector y.asVector false
    ) := by
  sorry

theorem sub_asVector :
    x - y = (ofVector <| Prod.snd <|
      Vector.mapAccumr₂ (fun x y c => (_, _)) x.asVector y.asVector false
    ) := by
  sorry

/-
  TODO: `mul`, `div`, `mod`
  These operations cannot (easily) be defined in terms of `mapAccumr`.
  We could still formulate bitwise implementatoins, but the question is whether this is even useful
-/

end BitVec
