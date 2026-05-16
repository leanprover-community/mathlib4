/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Bialgebra structure on `TensorAlgebra R M`

In this file we implement the natural bialgebra structure on `TensorAlgebra R M`.
The comultiplication is the unique algebra map satisfying `comul (ι R x) = ι R x ⊗ 1 + 1 ⊗ ι R
x` for all `x : M`, and `algebraMapInv` acts as the counit.
-/

@[expose] public section

namespace TensorAlgebra

open scoped TensorProduct RingTheory.LinearMap
open TensorProduct

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/-- Comultiplication in `TensorAlgebra R M` as an algebra map.
It is induced by the linear map sending `(m : M)` to `ι R m ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R m`.
See `comul_apply`.
-/
def comul : TensorAlgebra R M →ₐ[R] TensorAlgebra R M ⊗[R] TensorAlgebra R M := lift R <|
  (ι R ⊗ₘ Algebra.linearMap R (TensorAlgebra R M)) ∘ₗ (TensorProduct.rid R M).symm +
  (Algebra.linearMap R (TensorAlgebra R M) ⊗ₘ ι R) ∘ₗ (TensorProduct.lid R M).symm

instance instBialgebra : Bialgebra R (TensorAlgebra R M) := Bialgebra.ofAlgHom comul algebraMapInv
    (by ext; simpa [comul, Algebra.TensorProduct.one_def, add_tmul, tmul_add] using by abel)
    (by ext; simp [comul])
    (by ext; simp [comul])

end TensorAlgebra
