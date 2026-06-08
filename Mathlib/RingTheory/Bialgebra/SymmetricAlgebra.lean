/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.Quotient
public import Mathlib.RingTheory.Bialgebra.TensorAlgebra

/-!
# Bialgebra structure on `SymmetricAlgebra R M`

`SymmetricAlgebra R M` is the quotient of `TensorAlgebra R M` by `SymRel`. The counit and
comultiplication descend along this quotient, so it inherits the bialgebra structure of the
tensor algebra: the cocommutative commutative `R`-bialgebra on `M` in which each generator `ι x`
is primitive, `Δ(ι x) = ι x ⊗ 1 + 1 ⊗ ι x` and `ε(ι x) = 0`.
-/

public noncomputable section

namespace SymmetricAlgebra

open scoped TensorProduct
open Bialgebra Coalgebra
open TensorAlgebra (SymRel)

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]

/-- The counit and comultiplication of `TensorAlgebra R M` descend along the quotient by `SymRel`:
the counit lands in the commutative ring `R`, and the comultiplication in the commutative ring
`SymmetricAlgebra R M ⊗ SymmetricAlgebra R M`. -/
instance : IsBialgebraRel R (SymRel R M) where
  counit_rel := by
    rintro _ _ ⟨a, b⟩
    rw [counit_mul, counit_mul, mul_comm]
  comul_rel := by
    rintro _ _ ⟨a, b⟩
    rw [comul_mul, comul_mul, map_mul, map_mul, mul_comm]

@[simp]
theorem comul_ι (x : M) :
    Coalgebra.comul (R := R) (ι R M x) = ι R M x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R M x := by
  simp [ι, Bialgebra.Quotient.comul_mkAlgHom, TensorAlgebra.comul_ι]

@[simp]
theorem counit_ι (x : M) :
    Coalgebra.counit (R := R) (ι R M x) = 0 := by
  simp [ι, Bialgebra.Quotient.counit_mkAlgHom, TensorAlgebra.counit_ι]

instance instIsCocomm : Coalgebra.IsCocomm R (SymmetricAlgebra R M) where
  comm_comp_comul := by
    have h : (Algebra.TensorProduct.comm R (SymmetricAlgebra R M)
          (SymmetricAlgebra R M)).toAlgHom.comp (Bialgebra.comulAlgHom R _) =
        Bialgebra.comulAlgHom R (SymmetricAlgebra R M) := by
      ext x
      simp
      abel
    exact congr(($h).toLinearMap)

@[simp]
theorem counitAlgHom_eq :
    Bialgebra.counitAlgHom R (SymmetricAlgebra R M) = algebraMapInv := by
  ext x
  simp [algebraMapInv_ι]

end SymmetricAlgebra
