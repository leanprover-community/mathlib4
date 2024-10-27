/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Presentation.Basic

/-!

-/


namespace Module

namespace Presentation

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (M : Type*)
  [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
  {rB : Relations A} (pA : Presentation B rB)
  {rM : Relations B} (pM : Presentation M rM)

namespace RestrictScalarsData

end RestrictScalarsData

def restrictsScalars : Relations A where
  G := rM.G × rB.G
  R := Sum (rM.G × rB.R) (rM.R × rB.G)
  relation := sorry
  -- some extra data is needed for the second part

end Presentation

end Module
