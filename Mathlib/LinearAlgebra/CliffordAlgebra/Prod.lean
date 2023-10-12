/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.TensorProduct.Graded
import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Clifford algebras of a direct sum of two vector spaces

We show that the clifford algebra of a direct sum is the super tensor product of the clifford
algebras, as `CliffordAlgebra.equivProd`.

-/

suppress_compilation

variable {R M₁ M₂  : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]

variable (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)

open scoped TensorProduct

namespace CliffordAlgebra

/-- The forward direction of `CliffordAlgebra.prodEquiv`. -/
def ofProd : CliffordAlgebra (Q₁.prod Q₂) →ₐ[R] (evenOdd Q₁ ⊗'[R] evenOdd Q₂) :=
  lift _ ⟨LinearMap.coprod
    ((SuperTensorProduct.includeLeft (evenOdd Q₁) (evenOdd Q₂)).toLinearMap ∘ₗ ι Q₁)
    ((SuperTensorProduct.includeRight (evenOdd Q₁) (evenOdd Q₂)).toLinearMap ∘ₗ ι Q₂), fun m => by
      dsimp only [LinearMap.coprod_apply, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        QuadraticForm.prod_apply]
      simp only [map_add, add_mul, mul_add, SuperTensorProduct.algebraMap_def, ←map_mul,
        ι_sq_scalar, AlgHom.commutes]
      simp_rw [add_assoc]
      congr 1
      simp_rw [←add_assoc, add_left_eq_self]
      dsimp
      sorry⟩

@[simp]
lemma ofProd_ι_mk (m₁ : M₁) (m₂ : M₂) :
    ofProd Q₁ Q₂ (ι _ (m₁, m₂)) = ι Q₁ m₁ ⊗ₜ' 1 + 1 ⊗ₜ' ι Q₂ m₂ := by
  rw [ofProd, lift_ι_apply]
  rfl

/-- The reverse direction of `CliffordAlgebra.prodEquiv`. -/
def toProd : evenOdd Q₁ ⊗'[R] evenOdd Q₂ →ₐ[R] CliffordAlgebra (Q₁.prod Q₂) :=
  SuperTensorProduct.lift _ _
    (CliffordAlgebra.map <| QuadraticForm.Isometry.inl _ _)
    (CliffordAlgebra.map <| QuadraticForm.Isometry.inr _ _)
    fun i₁ i₂ m₁ m₂ => by
      dsimp
      sorry

@[simp]
lemma toProd_ι_tmul_one (m₁ : M₁) : toProd Q₁ Q₂ (ι _ m₁ ⊗ₜ' 1) = ι _ (m₁, 0) := by
  rw [toProd, SuperTensorProduct.lift_tmul, map_one, mul_one, map_apply_ι,
    QuadraticForm.Isometry.inl_apply]

@[simp]
lemma toProd_one_tmul_ι (m₂ : M₂) : toProd Q₁ Q₂ (1 ⊗ₜ' ι _ m₂) = ι _ (0, m₂) := by
  rw [toProd, SuperTensorProduct.lift_tmul, map_one, one_mul, map_apply_ι,
    QuadraticForm.Isometry.inr_apply]

set_option maxHeartbeats 400000 in
lemma toProd_comp_ofProd : (toProd Q₁ Q₂).comp (ofProd Q₁ Q₂) = AlgHom.id _ _ := by
  ext m₁ <;> dsimp
  · rw [ofProd_ι_mk, map_add, toProd_one_tmul_ι, toProd_ι_tmul_one, ← Prod.zero_eq_mk]
    dsimp only
    rw [@LinearMap.map_zero _ _ _ _ _ _ _ _ (_) (_), add_zero]
  · rw [ofProd_ι_mk, map_add, toProd_one_tmul_ι, toProd_ι_tmul_one, ← Prod.zero_eq_mk]
    dsimp only
    rw [@LinearMap.map_zero _ _ _ _ _ _ _ _ (_) (_), zero_add]

lemma ofProd_comp_toProd : (ofProd Q₁ Q₂).comp (toProd Q₁ Q₂) = AlgHom.id _ _ := by
  ext <;> (dsimp; simp)

/-- The clifford algebra over an orthogonal direct sum of quadratic vector spaces is isomorphic
as an algebra to the graded tensor product of the clifford algebras of each space.

This is `CliffordAlgebra.toProd` and `CliffordAlgebra.ofProd` as an equivalence. -/
@[simps!]
def prodEquiv : CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] (evenOdd Q₁ ⊗'[R] evenOdd Q₂) :=
  AlgEquiv.ofAlgHom
    (ofProd Q₁ Q₂)
    (toProd Q₁ Q₂)
    (ofProd_comp_toProd _ _)
    (toProd_comp_ofProd _ _)

end CliffordAlgebra
