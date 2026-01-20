/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Finite-dimensional inner product space with a (co)algebra structure

This file proves that a finite-dimensional inner product space has a
colagebra structure if it has an algebra structure, where
the comultiplication and counit maps are given by taking adjoints of the
multiplication and algebra linear maps, respectively.
This is implemented by providing a linear equivalence between the inner product space
and a normed algebra.

And similarly, a finite-dimensional inner product space has an algebra
structure if it has a coalgebra structure, where `x * y = (adjoint comul) (x ⊗ₜ y)`,
`(1 : A) = (adjoint counit) (1 : 𝕜)` and `algebraMap = adjoint counit`.

This is useful for when we have a finite-dimensional C⋆-algebra with a faithful and
positive linear functional (so that it induces an inner product structure), and want the coalgebra
structure to be the _adjoint_ of the algebra structure.
This comes up in non-commutative graph theory for example.
-/

@[expose] public section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

open TensorProduct LinearMap LinearIsometryEquiv Coalgebra

namespace InnerProductSpace

section coalgebraOfAlgebra
variable {A : Type*} [NormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]

/- TODO: This does not require submultiplicativity of the norm. When we unbundle the algebra
and analysis hierachies, we should generalise this from `NormedRing` to `Ring`
and `NormedAddCommGroup`.
PR#24040 addresses this. -/
/-- A finite-dimensional inner product space with an algebra structure induces
a coalgebra, where comultiplication is given by the adjoint of multiplication
and the counit is given by the adjoint of the algebra map.

This is implemented by providing a linear equivalence between the inner product
space and a normed algebra.

See note [reducible non-instances]. -/
noncomputable abbrev coalgebraOfAlgebra (e : E ≃ₗ[𝕜] A) : Coalgebra 𝕜 E where
  comul := adjoint (e.symm.toLinearMap ∘ₗ mul' 𝕜 A ∘ₗ map e.toLinearMap e.toLinearMap)
  counit := innerₛₗ 𝕜 (e.symm 1)
  coassoc := by
    rw [← adjoint_lTensor, ← adjoint_rTensor, ← toLinearEquiv_assocIsometry,
      ← (assocIsometry 𝕜 _ _ _).symm_symm, ← adjoint_toLinearMap_eq_symm]
    simp_rw [← adjoint_comp]
    congr 1; ext; simp [mul_assoc]
  rTensor_counit_comp_comul := by
    rw [← adjoint_toSpanSingleton, ← adjoint_rTensor, ← adjoint_comp, ← toLinearMap_symm_lid,
      ← toLinearEquiv_lidIsometry, ← toLinearEquiv_symm, ← adjoint_toLinearMap_eq_symm]
    congr 1; ext; simp
  lTensor_counit_comp_comul := by
    rw [← adjoint_toSpanSingleton, ← adjoint_lTensor, ← adjoint_comp, ← toLinearMap_symm_rid,
      ← comm_trans_lid, ← toLinearEquiv_commIsometry, ← toLinearEquiv_lidIsometry,
      ← toLinearEquiv_trans, ← toLinearEquiv_symm, ← adjoint_toLinearMap_eq_symm]
    congr 1; ext; simp

end coalgebraOfAlgebra

section algebraOfCoalgebra
variable [Coalgebra 𝕜 E]

/-- The multiplication on a finite-dimensional inner product space with a coalgebra structure
given by `x * y = (adjoint comul) (x ⊗ₜ y)`.

See note [reducible non-instances]. -/
noncomputable abbrev mulOfCoalgebra :
    Mul E where mul x y := adjoint (comul (R := 𝕜) (A := E)) (x ⊗ₜ y)

attribute [local instance] InnerProductSpace.mulOfCoalgebra in
lemma AlgebraOfCoalgebra.mul_def (x y : E) :
    x * y = adjoint (comul (R := 𝕜) (A := E)) (x ⊗ₜ y) := rfl

attribute [local simp] AlgebraOfCoalgebra.mul_def

attribute [local instance] InnerProductSpace.mulOfCoalgebra in
/-- A finite-dimensional inner product space with a coalgebra structure induces a ring structure,
where multiplication is given by `x * y = (adjoint comul) (x ⊗ₜ y)` and
`1 = (adjoint counit) (1 : 𝕜)`.

See note [reducible non-instances]. -/
noncomputable abbrev ringOfCoalgebra :
    Ring E where
  left_distrib x y z := by simp [tmul_add]
  right_distrib x y z := by simp [add_tmul]
  zero_mul x := by simp
  mul_zero x := by simp
  mul_assoc x y z := by
    simp_rw [AlgebraOfCoalgebra.mul_def, ← rTensor_tmul, ← comp_apply, ← adjoint_rTensor,
      ← adjoint_comp, ← coassoc_symm, adjoint_comp, adjoint_lTensor, comp_apply,
      ← toLinearEquiv_assocIsometry, ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    rfl
  one := adjoint (counit (R := 𝕜) (A := E)) 1
  one_mul x := by
    dsimp [OfNat.ofNat]
    rw [← rTensor_tmul, ← comp_apply, ← adjoint_rTensor, ← adjoint_comp, rTensor_counit_comp_comul,
      ← toLinearMap_symm_lid, ← toLinearEquiv_lidIsometry, ← toLinearEquiv_symm,
      adjoint_toLinearMap_eq_symm]
    exact one_smul _ _
  mul_one x := by
    dsimp [OfNat.ofNat]
    rw [← lTensor_tmul, ← comp_apply, ← adjoint_lTensor, ← adjoint_comp, lTensor_counit_comp_comul,
      ← toLinearMap_symm_rid, ← comm_trans_lid, ← toLinearEquiv_commIsometry,
      ← toLinearEquiv_lidIsometry, ← toLinearEquiv_trans, ← toLinearEquiv_symm,
      adjoint_toLinearMap_eq_symm]
    exact one_smul _ _

attribute [local instance] InnerProductSpace.ringOfCoalgebra in
/-- A finite-dimensional inner product space with a coalgebra structure induces an algebra
structure, where `x * y = (adjoint comul) (x ⊗ₜ y)`, `1 = (adjoint counit) 1` and
`algebraMap = adjoint counit`.

See note [reducible non-instances]. -/
noncomputable abbrev algebraOfCoalgebra : Algebra 𝕜 E where
  algebraMap :=
    { toFun := adjoint (Coalgebra.counit (R := 𝕜) (A := E))
      map_one' := rfl
      map_mul' x y := by
        simp_rw [AlgebraOfCoalgebra.mul_def, ← map_tmul, ← adjoint_map, ← comp_apply,
          ← adjoint_comp, ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul,
          adjoint_comp, ← toLinearMap_symm_lid, ← toLinearEquiv_lidIsometry, ← toLinearEquiv_symm,
          adjoint_toLinearMap_eq_symm]
        simp only [LinearIsometryEquiv.symm_symm, toLinearEquiv_lidIsometry, adjoint_lTensor,
          coe_comp, LinearEquiv.coe_coe, Function.comp_apply, lTensor_tmul, lid_tmul]
        rw [← smul_eq_mul, ← _root_.map_smul]
      map_zero' := map_zero _
      map_add' := map_add _ }
  commutes' r x := by
    dsimp
    simp_rw [← rTensor_tmul, ← lTensor_tmul, ← adjoint_lTensor, ← adjoint_rTensor,
      ← comp_apply, ← adjoint_comp, rTensor_counit_comp_comul, lTensor_counit_comp_comul,
      ← toLinearMap_symm_rid, ← toLinearMap_symm_lid, ← comm_trans_lid,
      ← toLinearEquiv_commIsometry, ← toLinearEquiv_lidIsometry, ← toLinearEquiv_trans,
      ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    rfl
  smul_def' r x := by
    dsimp
    simp_rw [← rTensor_tmul, ← adjoint_rTensor, ← comp_apply, ← adjoint_comp,
      rTensor_counit_comp_comul, ← toLinearMap_symm_lid, ← toLinearEquiv_lidIsometry,
      ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    rfl

end algebraOfCoalgebra
end InnerProductSpace
