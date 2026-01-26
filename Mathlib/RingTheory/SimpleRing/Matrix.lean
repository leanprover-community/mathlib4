import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.SimpleRing.Defs

/-!
The matrix ring over a simple ring is simple
-/

@[expose] public section

namespace IsSimpleRing

variable (ι A : Type*) [Ring A] [Fintype ι] [Nonempty ι]

instance matrix [IsSimpleRing A] : IsSimpleRing (Matrix ι ι A) where
  simple := letI := Classical.decEq ι; TwoSidedIdeal.orderIsoMatrix |>.symm.isSimpleOrder

end IsSimpleRing
