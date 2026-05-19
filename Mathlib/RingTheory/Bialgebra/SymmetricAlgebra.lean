/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Coalgebra.SymmetricAlgebra
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Bialgebra structure on `SymmetricAlgebra R M`

`SymmetricAlgebra R M` is the cocommutative commutative `R`-bialgebra on `M`
in which each generator `ι x` is primitive: `Δ(ι x) = ι x ⊗ 1 + 1 ⊗ ι x` and
`ε(ι x) = 0`. The coalgebra structure is in
`Mathlib/RingTheory/Coalgebra/SymmetricAlgebra.lean`.
-/

public section

namespace SymmetricAlgebra

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]

noncomputable instance instBialgebra : Bialgebra R (SymmetricAlgebra R M) :=
  .mk' R (SymmetricAlgebra R M)
    (map_one (algebraMapInv (R := R) (M := M)))
    (fun {a b} => map_mul (algebraMapInv (R := R) (M := M)) a b)
    (map_one (SymmetricAlgebra.comulAlgHom R M))
    (fun {a b} => map_mul (SymmetricAlgebra.comulAlgHom R M) a b)

@[simp]
theorem counitAlgHom_eq :
    Bialgebra.counitAlgHom R (SymmetricAlgebra R M) = algebraMapInv := rfl

@[simp]
theorem comulAlgHom_eq :
    Bialgebra.comulAlgHom R (SymmetricAlgebra R M) = SymmetricAlgebra.comulAlgHom R M := rfl

end SymmetricAlgebra
