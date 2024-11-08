/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.LinearAlgebra.Matrix.Ideal
import Mathlib.RingTheory.SimpleRing.Basic

/-!
Matrix ring over simple ring is simple
-/

namespace IsSimpleRing

variable (ι A : Type*) [Ring A] [Fintype ι] [Nonempty ι]

instance matrix [IsSimpleRing A] : IsSimpleRing (Matrix ι ι A) where
  simple := TwoSidedIdeal.orderIsoMatricesOver (Nonempty.some ‹_›) (Nonempty.some ‹_›)
    |>.symm.isSimpleOrder

end IsSimpleRing
