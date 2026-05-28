/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.TensorAlgebra

/-!
# Hopf algebra structure on `SymmetricAlgebra R M`

When `R` is a commutative ring, `SymmetricAlgebra R M` inherits its `R`-Hopf algebra structure
from `TensorAlgebra R M` through the quotient by `SymRel`: the antipode of the tensor algebra
descends along the quotient, since it is an anti-homomorphism and the quotient is commutative.
The induced antipode is `S(ι x) = -ι x`.
-/

public noncomputable section

namespace SymmetricAlgebra

open HopfAlgebra
open TensorAlgebra (SymRel)

variable (R : Type*) [CommRing R] (M : Type*) [AddCommMonoid M] [Module R M]

/-- The tensor-algebra antipode descends along the quotient by `SymRel`: for `ι a * ι b ~ ι b * ι a`,
the antipode (an anti-homomorphism) sends the two sides to `ι b * ι a` and `ι a * ι b`, whose
images agree in the commutative quotient. -/
instance : IsHopfRel R (SymRel R M) where
  antipode_map_eq := by
    rintro _ _ ⟨a, b⟩
    rw [antipode_mul, antipode_mul, map_mul, map_mul, mul_comm]

@[simp]
theorem antipode_ι (x : M) :
    HopfAlgebra.antipode R (ι R M x) = -ι R M x := by
  have hp : IsPrimitiveElem R (TensorAlgebra.ι R x) := ⟨by simp, by simp⟩
  simp [ι, HopfAlgebra.Quotient.antipode_mkAlgHom, hp.antipode_eq_neg]

end SymmetricAlgebra
