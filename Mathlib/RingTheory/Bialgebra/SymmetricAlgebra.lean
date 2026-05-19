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

public section

namespace SymmetricAlgebra

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]

open scoped TensorProduct

noncomputable section

@[simp]
theorem algebraMapInv_ι (x : M) : algebraMapInv (R := R) (M := M) (ι R M x) = 0 := by
  simp [algebraMapInv]

/-- The comultiplication on `SymmetricAlgebra R M` as an algebra
homomorphism, lifted from `x ↦ ι x ⊗ 1 + 1 ⊗ ι x`. -/
protected def comulAlgHom : SymmetricAlgebra R M →ₐ[R]
    (SymmetricAlgebra R M ⊗[R] SymmetricAlgebra R M) :=
  lift <|
    (TensorProduct.mk R _ _).flip 1 ∘ₗ ι R M +
    TensorProduct.mk R _ _ 1 ∘ₗ ι R M

protected theorem comulAlgHom_ι (x : M) :
    SymmetricAlgebra.comulAlgHom R M (ι R M x) =
      ι R M x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R M x := by
  simp [SymmetricAlgebra.comulAlgHom, lift_ι_apply]

-- `Algebra.TensorProduct.assoc R R R A A A` is the form for `R = S = T`; see
-- `AlgebraTensorModule.assoc` for the general typeclass shape.
protected theorem comulAlgHom_coassoc :
    (Algebra.TensorProduct.assoc R R R
        (SymmetricAlgebra R M) (SymmetricAlgebra R M)
        (SymmetricAlgebra R M)).toAlgHom.comp
      ((Algebra.TensorProduct.map (SymmetricAlgebra.comulAlgHom R M)
          (.id R (SymmetricAlgebra R M))).comp (SymmetricAlgebra.comulAlgHom R M)) =
    (Algebra.TensorProduct.map (.id R (SymmetricAlgebra R M))
        (SymmetricAlgebra.comulAlgHom R M)).comp (SymmetricAlgebra.comulAlgHom R M) := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_coe, AlgHom.comp_apply,
    SymmetricAlgebra.comulAlgHom_ι, map_add, Algebra.TensorProduct.map_tmul,
    AlgHom.coe_id, id_eq, map_one, TensorProduct.add_tmul, TensorProduct.tmul_add,
    Algebra.TensorProduct.one_def]
  abel

protected theorem comulAlgHom_rTensor_counit_comp :
    (Algebra.TensorProduct.map (algebraMapInv (R := R) (M := M))
        (.id R (SymmetricAlgebra R M))).comp (SymmetricAlgebra.comulAlgHom R M) =
      (Algebra.TensorProduct.lid R (SymmetricAlgebra R M)).symm.toAlgHom := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_coe, AlgHom.comp_apply,
    AlgEquiv.coe_algHom, SymmetricAlgebra.comulAlgHom_ι, map_add,
    Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, algebraMapInv_ι, map_one,
    Algebra.TensorProduct.lid_symm_apply, TensorProduct.zero_tmul, zero_add]

protected theorem comulAlgHom_lTensor_counit_comp :
    (Algebra.TensorProduct.map (.id R (SymmetricAlgebra R M))
        (algebraMapInv (R := R) (M := M))).comp (SymmetricAlgebra.comulAlgHom R M) =
      (Algebra.TensorProduct.rid R R (SymmetricAlgebra R M)).symm.toAlgHom := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_coe, AlgHom.comp_apply,
    AlgEquiv.coe_algHom, SymmetricAlgebra.comulAlgHom_ι, map_add,
    Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, algebraMapInv_ι, map_one,
    Algebra.TensorProduct.rid_symm_apply, TensorProduct.tmul_zero, add_zero]

instance instBialgebra : Bialgebra R (SymmetricAlgebra R M) :=
  .ofAlgHom (SymmetricAlgebra.comulAlgHom R M) (algebraMapInv (R := R) (M := M))
    (SymmetricAlgebra.comulAlgHom_coassoc R M)
    (SymmetricAlgebra.comulAlgHom_rTensor_counit_comp R M)
    (SymmetricAlgebra.comulAlgHom_lTensor_counit_comp R M)

@[simp]
theorem comul_ι (x : M) :
    Coalgebra.comul (R := R) (ι R M x) = ι R M x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R M x :=
  SymmetricAlgebra.comulAlgHom_ι R M x

@[simp]
theorem counit_ι (x : M) :
    Coalgebra.counit (R := R) (ι R M x) = 0 :=
  algebraMapInv_ι R M x

protected theorem comulAlgHom_comm :
    (Algebra.TensorProduct.comm R (SymmetricAlgebra R M)
        (SymmetricAlgebra R M)).toAlgHom.comp (SymmetricAlgebra.comulAlgHom R M) =
      SymmetricAlgebra.comulAlgHom R M := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_coe, AlgHom.comp_apply,
    AlgEquiv.coe_algHom, SymmetricAlgebra.comulAlgHom_ι, map_add,
    Algebra.TensorProduct.comm_tmul]
  abel

end

instance instIsCocomm : Coalgebra.IsCocomm R (SymmetricAlgebra R M) where
  comm_comp_comul := congr(($(SymmetricAlgebra.comulAlgHom_comm R M)).toLinearMap)

@[simp]
theorem counitAlgHom_eq :
    Bialgebra.counitAlgHom R (SymmetricAlgebra R M) = algebraMapInv := rfl

@[simp]
theorem comulAlgHom_eq :
    Bialgebra.comulAlgHom R (SymmetricAlgebra R M) = SymmetricAlgebra.comulAlgHom R M := rfl

end SymmetricAlgebra
