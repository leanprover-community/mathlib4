/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bialgebra structure on `SymmetricAlgebra R M`

`SymmetricAlgebra R M` is the cocommutative commutative `R`-bialgebra on `M`
in which each generator `ι x` is primitive: `Δ(ι x) = ι x ⊗ 1 + 1 ⊗ ι x` and
`ε(ι x) = 0`.
-/

public noncomputable section

namespace SymmetricAlgebra

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]

open scoped TensorProduct

instance instBialgebra : Bialgebra R (SymmetricAlgebra R M) :=
  .ofAlgHom
    (lift <| (TensorProduct.mk R _ _).flip 1 ∘ₗ ι R M + TensorProduct.mk R _ _ 1 ∘ₗ ι R M)
    algebraMapInv
    (by
      ext x
      simp [Algebra.TensorProduct.one_def, TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel)
    (by ext x; simp [algebraMapInv_ι])
    (by ext x; simp [algebraMapInv_ι])

@[simp]
theorem comul_ι (x : M) :
    Coalgebra.comul (R := R) (ι R M x) = ι R M x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R M x :=
  lift_ι_apply _ x

@[simp]
theorem counit_ι (x : M) :
    Coalgebra.counit (R := R) (ι R M x) = 0 :=
  algebraMapInv_ι x

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
    Bialgebra.counitAlgHom R (SymmetricAlgebra R M) = algebraMapInv := rfl

end SymmetricAlgebra
