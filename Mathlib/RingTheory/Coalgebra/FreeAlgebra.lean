/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.RingTheory.Bialgebra.FreeAlgebra

/-!
# Coalgebra structure on `FreeAlgebra R M`

In this file we implement the natural bialgebra structure on `FreeAlgebra R M`.
The comultiplication is the unique algebra map satisfying `comul (ι R x) = ι R x ⊗ 1 + 1 ⊗ ι R
x` for all `x : M`.
-/

@[expose] public section

namespace FreeAlgebra

variable (R X) [CommSemiring R]

instance instCoalgebra : Coalgebra R (FreeAlgebra R X) :=
  (FreeAlgebra.instBialgebra R X).toCoalgebra

end FreeAlgebra
