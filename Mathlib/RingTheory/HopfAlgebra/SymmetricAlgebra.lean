/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Hopf algebra structure on `SymmetricAlgebra R M`

When `R` is a commutative ring, `SymmetricAlgebra R M` is the cocommutative
commutative `R`-Hopf algebra extending the bialgebra structure with antipode
`S(ι x) = -ι x` for `x : M`, extended multiplicatively.
-/

public noncomputable section

namespace SymmetricAlgebra

variable (R : Type*) [CommRing R] (M : Type*) [AddCommMonoid M] [Module R M]

instance instHopfAlgebra : HopfAlgebra R (SymmetricAlgebra R M) := by
  refine .ofAlgHom (lift (-ι R M)) ?_ ?_ <;> ext x <;> simp

@[simp]
theorem antipode_ι (x : M) :
    HopfAlgebra.antipode R (ι R M x) = -ι R M x :=
  lift_ι_apply _ x

end SymmetricAlgebra
