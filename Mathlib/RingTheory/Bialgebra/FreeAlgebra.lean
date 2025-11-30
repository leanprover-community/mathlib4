/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Bialgebra structure on `FreeAlgebra R M`

In this file we implement the natural bialgebra structure on `FreeAlgebra R M`.
The comultiplication is the unique algebra map satisfying `comul (ι R x) = ι R x ⊗ 1 + 1 ⊗ ι R
x` for all `x : M`, and `algebraMapInv` acts as the counit.
-/

@[expose] public section

open FreeAlgebra TensorProduct
open scoped TensorProduct

namespace FreeAlgebra

variable (R X) [CommSemiring R]

instance instBialgebra : Bialgebra R (FreeAlgebra R X) := Bialgebra.ofAlgHom
  (lift R <| fun (x : X) => ι R x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R x)
  algebraMapInv
  (by ext; simpa [tmul_add, add_tmul, Algebra.TensorProduct.one_def] using by abel)
  (by ext; simp)
  (by ext; simp)

end FreeAlgebra
