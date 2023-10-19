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

variable {R M₁ M₂ : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]

variable (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)

open scoped TensorProduct

namespace CliffordAlgebra

@[simp] theorem ι_inl_mul_ι_inr_add_swap (m₁ : M₁) (m₂ : M₂) :
    ι (Q₁.prod Q₂) (m₁, 0) * ι (Q₁.prod Q₂) (0, m₂)
      + ι (Q₁.prod Q₂) (0, m₂) * ι (Q₁.prod Q₂) (m₁, 0) = 0 := by
  rw [ι_mul_ι_add_swap, QuadraticForm.polar_prod]
  simp

theorem ι_inl_mul_ι_inr (m₁ : M₁) (m₂ : M₂) :
    ι (Q₁.prod Q₂) (m₁, 0) * ι (Q₁.prod Q₂) (0, m₂) =
      -(ι (Q₁.prod Q₂) (0, m₂) * ι (Q₁.prod Q₂) (m₁, 0)) :=
  eq_neg_of_add_eq_zero_left <| ι_inl_mul_ι_inr_add_swap _ _ _ _

theorem ι_inr_mul_ι_inl (m₂ : M₂) (m₁ : M₁) :
    ι (Q₁.prod Q₂) (0, m₂) * ι (Q₁.prod Q₂) (m₁, 0) =
      -(ι (Q₁.prod Q₂) (m₁, 0) * ι (Q₁.prod Q₂) (0, m₂)) :=
  neg_eq_iff_eq_neg.mp (ι_inl_mul_ι_inr Q₁ Q₂ m₁ m₂).symm

theorem ι_inl_mul_ι_inr_right (x : CliffordAlgebra (Q₁.prod Q₂)) (m₁ : M₁) (m₂ : M₂) :
    x * ι (Q₁.prod Q₂) (m₁, 0) * ι (Q₁.prod Q₂) (0, m₂) =
      -(x * ι (Q₁.prod Q₂) (0, m₂) * ι (Q₁.prod Q₂) (m₁, 0)) := by
  rw [mul_assoc, ι_inl_mul_ι_inr, mul_neg, mul_assoc]

theorem ι_inr_mul_ι_inl_right (x : CliffordAlgebra (Q₁.prod Q₂)) (m₂ : M₂) (m₁ : M₁) :
    x * ι (Q₁.prod Q₂) (0, m₂) * ι (Q₁.prod Q₂) (m₁, 0) =
      -(x * ι (Q₁.prod Q₂) (m₁, 0) * ι (Q₁.prod Q₂) (0, m₂)) := by
  rw [mul_assoc, ι_inr_mul_ι_inl, mul_neg, mul_assoc]

open QuadraticForm.Isometry in
theorem map_inl_mul_map_inr_of_mem_evenOdd {i₁ i₂ : ZMod 2}
    (m₁ : CliffordAlgebra Q₁) (hm₁ : m₁ ∈ evenOdd Q₁ i₁)
    (m₂ : CliffordAlgebra Q₂) (hm₂ : m₂ ∈ evenOdd Q₂ i₂) :
    map (inl Q₁ Q₂) m₁ * map (inr Q₁ Q₂) m₂ =
      (-1 : ℤˣ) ^ (i₂ * i₁) • (map (inr Q₁ Q₂) m₂ * map (inl Q₁ Q₂) m₁) := by
  -- the strategy; for each variable, induct on powers of `ι`, then on the exponent of each
  -- power.
  induction hm₁ using Submodule.iSup_induction' with
  | hp i₁' m₁' hm₁ =>
    clear m₁
    obtain ⟨i₁n, rfl⟩ := i₁'
    dsimp only at *
    induction hm₁ using Submodule.pow_induction_on_left' with
    | hr =>
      rw [AlgHom.commutes, Nat.cast_zero, mul_zero, z₂pow_zero, one_smul, Algebra.commutes]
    | hadd _ _ _ _ _ ihx ihy =>
      rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]
    | hmul m₁ hm₁ i x₁ _hx₁ ih₁ =>
      obtain ⟨v₁, rfl⟩ := hm₁
      -- this is the first interesting goal
      rw [map_mul, mul_assoc, ih₁, mul_smul_comm, map_apply_ι, Nat.cast_succ, mul_add_one,
        z₂pow_add, mul_smul, ←mul_assoc, ←mul_assoc, ←smul_mul_assoc ((-1) ^ i₂), inl_apply]
      clear ih₁
      congr 2
      induction hm₂ using Submodule.iSup_induction' with
      | hp i₂' m₂' hm₂ =>
        clear m₂
        obtain ⟨i₂n, rfl⟩ := i₂'
        dsimp only at *
        induction hm₂ using Submodule.pow_induction_on_left' with
        | hr =>
          rw [AlgHom.commutes, Nat.cast_zero, z₂pow_zero, one_smul, Algebra.commutes]
        | hadd _ _ _ _ _ ihx ihy =>
          rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]
        | hmul m₂ hm₂ i x₂ _hx₂ ih₂ =>
          obtain ⟨v₂, rfl⟩ := hm₂
          -- this is the second interesting goal
          rw [map_mul, map_apply_ι, inr_apply, Nat.cast_succ, ←mul_assoc, ι_inl_mul_ι_inr,
            neg_mul, mul_assoc, ih₂, mul_smul_comm, ←mul_assoc, ←Units.neg_smul, z₂pow_add,
            z₂pow_one, mul_neg_one]
      | h0 => rw [map_zero, zero_mul, mul_zero, smul_zero]
      | hadd _ _ _ _ ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]
  | h0 => rw [map_zero, zero_mul, mul_zero, smul_zero]
  | hadd _ _ _ _ ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]


/-- The forward direction of `CliffordAlgebra.prodEquiv`. -/
def ofProd : CliffordAlgebra (Q₁.prod Q₂) →ₐ[R] (evenOdd Q₁ ⊗'[R] evenOdd Q₂) :=
  lift _ ⟨
    LinearMap.coprod
      ((SuperTensorProduct.includeLeft (evenOdd Q₁) (evenOdd Q₂)).toLinearMap
          ∘ₗ Submodule.subtype (evenOdd Q₁ 1) ∘ₗ (ι Q₁).codRestrict _ (ι_mem_evenOdd_one Q₁))
      ((SuperTensorProduct.includeRight (evenOdd Q₁) (evenOdd Q₂)).toLinearMap
          ∘ₗ Submodule.subtype (evenOdd Q₂ 1) ∘ₗ (ι Q₂).codRestrict _ (ι_mem_evenOdd_one Q₂)),
    fun m => by
      dsimp only [LinearMap.coprod_apply, LinearMap.coe_comp, Function.comp_apply,
        AlgHom.toLinearMap_apply, QuadraticForm.prod_apply, Submodule.coeSubtype,
        SuperTensorProduct.includeLeft_apply, SuperTensorProduct.includeRight_apply]
      simp only [map_add, add_mul, mul_add, SuperTensorProduct.algebraMap_def]
      rw [SuperTensorProduct.tmul_one_mul_one_tmul, SuperTensorProduct.tmul_one_mul_coe_tmul,
        SuperTensorProduct.tmul_coe_mul_one_tmul, SuperTensorProduct.tmul_coe_mul_coe_tmul]
      dsimp
      simp_rw [one_mul, z₂pow_one, Units.neg_smul, one_smul]
      rw [ι_sq_scalar, ι_sq_scalar, mul_one, one_mul]
      simp_rw [←SuperTensorProduct.algebraMap_def, ←SuperTensorProduct.algebraMap_def']
      abel⟩

@[simp]
lemma ofProd_ι_mk (m₁ : M₁) (m₂ : M₂) :
    ofProd Q₁ Q₂ (ι _ (m₁, m₂)) = ι Q₁ m₁ ⊗ₜ' 1 + 1 ⊗ₜ' ι Q₂ m₂ := by
  rw [ofProd, lift_ι_apply]
  rfl

open QuadraticForm.Isometry in
/-- The reverse direction of `CliffordAlgebra.prodEquiv`. -/
def toProd : evenOdd Q₁ ⊗'[R] evenOdd Q₂ →ₐ[R] CliffordAlgebra (Q₁.prod Q₂) :=
  SuperTensorProduct.lift _ _
    (CliffordAlgebra.map <| QuadraticForm.Isometry.inl _ _)
    (CliffordAlgebra.map <| QuadraticForm.Isometry.inr _ _)
    fun _i₁ _i₂ x₁ x₂ => map_inl_mul_map_inr_of_mem_evenOdd _ _ _ x₁.prop _ x₂.prop

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
