/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies
-/
module
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.RingTheory.Coalgebra.SimpAttr

/-!
# Tactic to reassociate comultiplication in a coalgebra

`coassoc_simps` is a simp set useful to prove tautologies on coalgebras.

Note: It is not confluent with `(ε ⊗ₘ id) ∘ₗ δ = λ⁻¹`.
It is often useful to `trans` (or `calc`) with a term containing `(ε ⊗ₘ _) ∘ₗ δ` or `(_ ⊗ₘ ε) ∘ₗ δ`,
and use one of `map_counit_comp_comul_left` `map_counit_comp_comul_right`
`map_counit_comp_comul_left_assoc` `map_counit_comp_comul_right_assoc` to continue.

-/

open TensorProduct

open LinearMap (id)

namespace Coalgebra

variable {R A M N P M' N' P' Q Q' : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
    [Coalgebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    [AddCommMonoid P'] [Module R P'] [AddCommMonoid Q] [Module R Q] [AddCommMonoid Q'] [Module R Q']
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R N₁] [Module R N₂] [Module R N₃]

local notation3 "α" => (TensorProduct.assoc R _ _ _).toLinearMap
local notation3 "α⁻¹" => (TensorProduct.assoc R _ _ _).symm.toLinearMap
local notation3 "λ" => (TensorProduct.lid R _).toLinearMap
local notation3 "λ⁻¹" => (TensorProduct.lid R _).symm.toLinearMap
local notation3 "ρ" => (TensorProduct.rid R _).toLinearMap
local notation3 "ρ⁻¹" => (TensorProduct.rid R _).symm.toLinearMap
local notation3 "β" => (TensorProduct.comm R _ _).toLinearMap
local infix:90 " ⊗ₘ " => TensorProduct.map
local notation3 "δ" => comul (R := R)
local notation3 "ε" => counit (R := R)

attribute [coassoc_simps] LinearMap.comp_id LinearMap.id_comp TensorProduct.map_id
  LinearMap.lTensor_def LinearMap.rTensor_def LinearMap.comp_assoc
  LinearEquiv.coe_trans LinearEquiv.trans_symm
  LinearEquiv.refl_toLinearMap TensorProduct.toLinearMap_congr
  LinearEquiv.comp_symm LinearEquiv.symm_comp LinearEquiv.symm_symm
  LinearEquiv.coe_lTensor LinearEquiv.coe_lTensor_symm
  LinearEquiv.coe_rTensor LinearEquiv.coe_rTensor_symm
  IsCocomm.comm_comp_comul TensorProduct.AlgebraTensorModule.map_eq
  TensorProduct.AlgebraTensorModule.assoc_eq TensorProduct.AlgebraTensorModule.rightComm_eq
  TensorProduct.tensorTensorTensorComm TensorProduct.AlgebraTensorModule.tensorTensorTensorComm

attribute [coassoc_simps← ] TensorProduct.map_comp TensorProduct.map_map_comp_assoc_eq
  TensorProduct.map_map_comp_assoc_symm_eq

-- move me
@[coassoc_simps]
lemma TensorProduct.AlgebraTensorModule.congr_eq {R M N P Q : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid Q] [Module R Q] (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    AlgebraTensorModule.congr f g = congr f g := rfl

-- move me
@[coassoc_simps]
lemma TensorProduct.map_comp_assoc {R₀ R R₂ R₃ : Type*} [CommSemiring R₀] [CommSemiring R]
    [CommSemiring R₂] [CommSemiring R₃] {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
    {M₀ M N M₂ M₃ N₂ N₃ : Type*} [AddCommMonoid M₀] [Module R₀ M₀]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid M₃]
    [AddCommMonoid N₃] [Module R M] [Module R N] [Module R₂ M₂] [Module R₂ N₂] [Module R₃ M₃]
    [Module R₃ N₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
    (f₂ : M₂ →ₛₗ[σ₂₃] M₃) (g₂ : N₂ →ₛₗ[σ₂₃] N₃) (f₁ : M →ₛₗ[σ₁₂] M₂) (g₁ : N →ₛₗ[σ₁₂] N₂)
    {σ₃ : R₀ →+* R₃} {σ₂ : R₀ →+* R₂} {σ₁ : R₀ →+* R}
    [RingHomCompTriple σ₂ σ₂₃ σ₃] [RingHomCompTriple σ₁ σ₁₂ σ₂] [RingHomCompTriple σ₁ σ₁₃ σ₃]
    (f : M₀ →ₛₗ[σ₁] M ⊗[R] N) :
    map f₂ g₂ ∘ₛₗ map f₁ g₁ ∘ₛₗ f = map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁) ∘ₛₗ f := by
  rw [← LinearMap.comp_assoc, TensorProduct.map_comp]

-- move me
@[coassoc_simps]
lemma LinearEquiv.comp_symm_assoc {R S T M M₂ M' : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Semiring T] [AddCommMonoid M₂] [AddCommMonoid M']
    {module_M : Module R M} {module_S_M₂ : Module S M₂} {_ : Module T M'} {σ : R →+* S}
    {σ' : S →+* R} {re₁ : RingHomInvPair σ σ'} {re₂ : RingHomInvPair σ' σ} (e : M ≃ₛₗ[σ] M₂)
    {σ'' : T →+* S} {σ''' : T →+* R} [RingHomCompTriple σ'' σ' σ''']
    [RingHomCompTriple σ''' σ σ'']
    (f : M' →ₛₗ[σ''] M₂) :
  e.toLinearMap ∘ₛₗ e.symm.toLinearMap ∘ₛₗ f = f := by ext; simp

-- move me
@[coassoc_simps]
lemma LinearEquiv.symm_comp_assoc {R S T M M₂ M' : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Semiring T] [AddCommMonoid M₂] [AddCommMonoid M']
    {module_M : Module R M} {module_S_M₂ : Module S M₂} {_ : Module T M'} {σ : R →+* S}
    {σ' : S →+* R} {re₁ : RingHomInvPair σ σ'} {re₂ : RingHomInvPair σ' σ} (e : M ≃ₛₗ[σ] M₂)
    {σ'' : T →+* S} {σ''' : T →+* R} [RingHomCompTriple σ'' σ' σ''']
    [RingHomCompTriple σ''' σ σ'']
    (f : M' →ₛₗ[σ'''] M) :
  e.symm.toLinearMap ∘ₛₗ e.toLinearMap ∘ₛₗ f = f := by ext; simp

open scoped LinearMap

-- move me
@[coassoc_simps]
lemma TensorProduct.rightComm_def : rightComm R M N P =
    TensorProduct.assoc R _ _ _ ≪≫ₗ congr (.refl _ _) (TensorProduct.comm _ _ _) ≪≫ₗ
      (TensorProduct.assoc R _ _ _).symm := by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

-- move me
@[coassoc_simps]
lemma TensorProduct.leftComm_def : leftComm R M N P =
    (TensorProduct.assoc R _ _ _).symm ≪≫ₗ congr (TensorProduct.comm _ _ _) (.refl _ _) ≪≫ₗ
      (TensorProduct.assoc R _ _ _) := by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

-- move me, tag simp
@[coassoc_simps]
lemma TensorProduct.comm_symm : (TensorProduct.comm R M N).symm = TensorProduct.comm R N M := rfl

-- move me, tag simp
@[coassoc_simps]
lemma TensorProduct.comm_comp_comm :
    (TensorProduct.comm R N M).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap = .id :=
  (TensorProduct.comm R M N).symm_comp

-- move me, tag simp
@[coassoc_simps]
lemma TensorProduct.comm_comp_comm_assoc (f : P →ₗ[R] M ⊗[R] N) :
    (TensorProduct.comm R N M).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap ∘ₗ f = f := by
  rw [← LinearMap.comp_assoc, comm_comp_comm, LinearMap.id_comp]

-- move me
@[coassoc_simps← ]
lemma TensorProduct.map_map_comp_assoc_eq_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f : M →ₗ[R] M₁ ⊗[R] M₂ ⊗[R] M₃) :
    f₁ ⊗ₘ (f₂ ⊗ₘ f₃) ∘ₗ α ∘ₗ f = α ∘ₗ ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, TensorProduct.map_map_comp_assoc_eq]

-- move me
@[coassoc_simps← ]
lemma TensorProduct.map_map_comp_assoc_symm_eq_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f : M →ₗ[R] M₁ ⊗[R] (M₂ ⊗[R] M₃)) :
    (f₁ ⊗ₘ f₂) ⊗ₘ f₃ ∘ₗ α⁻¹ ∘ₗ f = α⁻¹ ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, TensorProduct.map_map_comp_assoc_symm_eq]

@[coassoc_simps]
lemma assoc_comp_map_map_comp
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) :
    α ∘ₗ (((f₁ ⊗ₘ f₂) ∘ₗ f₁₂) ⊗ₘ f₃) = (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ id) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_eq]
  ext
  rfl

@[coassoc_simps]
lemma assoc_comp_map_map_comp_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂)
    (f : M →ₗ[R] M ⊗[R] M₃) :
    α ∘ₗ (((f₁ ⊗ₘ f₂) ∘ₗ f₁₂) ⊗ₘ f₃) ∘ₗ f =
      (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ id) ∘ₗ f := by
  simp only [← LinearMap.comp_assoc, assoc_comp_map_map_comp]

-- loops. TODO: replace with simproc
lemma assoc_comp_map (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) :
    α ∘ₗ (f₁₂ ⊗ₘ f₃) = (id ⊗ₘ (id ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ id) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_eq]
  simp only [coassoc_simps]

-- loops. TODO: replace with simproc
lemma assoc_comp_map_assoc (f₃ : M₃ →ₗ[R] N₃)
    (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) (f : P →ₗ[R] M ⊗[R] M₃) :
    α ∘ₗ (f₁₂ ⊗ₘ f₃) ∘ₗ f = (id ⊗ₘ (id ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ id) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, assoc_comp_map]
  simp only [coassoc_simps]

@[coassoc_simps] -- TODO: remove once simproc lands
lemma assoc_comp_map_comp (f₃' : N →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) :
    α ∘ₗ (f₁₂ ⊗ₘ (f₃ ∘ₗ f₃')) = (id ⊗ₘ (id ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ f₃') := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_eq]
  simp only [coassoc_simps]

@[coassoc_simps] -- TODO: remove once simproc lands
lemma assoc_comp_map_comp_assoc (f₃' : N →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] N₃)
    (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) (f : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ (f₁₂ ⊗ₘ (f₃ ∘ₗ f₃')) ∘ₗ f = (id ⊗ₘ (id ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ f₃') ∘ₗ f := by
  rw [← LinearMap.comp_assoc, assoc_comp_map_comp]
  simp only [coassoc_simps]

@[coassoc_simps]
lemma assoc_symm_comp_map_map_comp
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃ ∘ₗ f₂₃)) = ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ α⁻¹ ∘ₗ (id ⊗ₘ f₂₃) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_symm_eq]
  ext
  rfl

@[coassoc_simps]
lemma assoc_symm_comp_map_map_comp_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃)
    (f : N →ₗ[R] M₁ ⊗[R] M) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃ ∘ₗ f₂₃)) ∘ₗ f = ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ α⁻¹ ∘ₗ (id ⊗ₘ f₂₃) ∘ₗ f := by
  simp only [← LinearMap.comp_assoc, assoc_symm_comp_map_map_comp]

@[coassoc_simps]
lemma assoc_symm_comp_map_comp
    (f₁ : M₁ →ₗ[R] N₁) (f₁' : N →ₗ[R] M₁) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) :
    α⁻¹ ∘ₗ ((f₁ ∘ₗ f₁') ⊗ₘ f₂₃) = ((f₁ ⊗ₘ id) ⊗ₘ id) ∘ₗ α⁻¹ ∘ₗ (f₁' ⊗ₘ f₂₃) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

@[coassoc_simps]
lemma assoc_symm_comp_map_comp_assoc (f₁ : M₁ →ₗ[R] N₁) (f₁' : N →ₗ[R] M₁)
    (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) (f : P →ₗ[R] N ⊗[R] M) :
    α⁻¹ ∘ₗ ((f₁ ∘ₗ f₁') ⊗ₘ f₂₃) ∘ₗ f = ((f₁ ⊗ₘ id) ⊗ₘ id) ∘ₗ α⁻¹ ∘ₗ (f₁' ⊗ₘ f₂₃) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, assoc_symm_comp_map_comp]
  simp only [coassoc_simps]

-- loops. TODO: replace with simproc
lemma assoc_symm_comp_map
    (f₁ : M₁ →ₗ[R] N₁) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ f₂₃) = ((f₁ ⊗ₘ id) ⊗ₘ id) ∘ₗ α⁻¹ ∘ₗ (id ⊗ₘ f₂₃) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

-- loops. TODO: replace with simproc
lemma assoc_symm_comp_map_assoc (f₁ : M₁ →ₗ[R] N₁)
    (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) (f : P →ₗ[R] M₁ ⊗[R] M) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ f₂₃) ∘ₗ f = ((f₁ ⊗ₘ id) ⊗ₘ id) ∘ₗ α⁻¹ ∘ₗ (id ⊗ₘ f₂₃) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, assoc_symm_comp_map]
  simp only [coassoc_simps]

@[coassoc_simps]
lemma assoc_symm_comp_lid_symm :
    (α⁻¹ ∘ₗ λ⁻¹ : M ⊗[R] N →ₗ[R] _) = λ⁻¹ ⊗ₘ id := rfl

@[coassoc_simps]
lemma assoc_symm_comp_lid_symm_assoc (f : P →ₗ[R] M ⊗[R] N) :
    α⁻¹ ∘ₗ λ⁻¹ ∘ₗ f = λ⁻¹ ⊗ₘ id ∘ₗ f := rfl

@[coassoc_simps]
lemma assoc_symm_comp_map_lid_symm (f : M →ₗ[R] M') :
    α⁻¹ ∘ₗ f ⊗ₘ λ⁻¹ = (f ⊗ₘ id ∘ₗ ρ⁻¹) ⊗ₘ id (M := N) := by
  ext; rfl

@[coassoc_simps]
lemma assoc_symm_comp_map_lid_symm_assoc (f : M →ₗ[R] M') (g : P →ₗ[R] M ⊗[R] N) :
    α⁻¹ ∘ₗ f ⊗ₘ λ⁻¹ ∘ₗ g = (f ⊗ₘ id ∘ₗ ρ⁻¹) ⊗ₘ id ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_lid_symm]

@[coassoc_simps]
lemma assoc_symm_comp_map_rid_symm (f : M →ₗ[R] M') :
    α⁻¹ ∘ₗ f ⊗ₘ ρ⁻¹ = (f ⊗ₘ id (M := N)) ⊗ₘ id ∘ₗ ρ⁻¹ := by
  ext; rfl

@[coassoc_simps]
lemma assoc_symm_comp_map_rid_symm_assoc (f : M →ₗ[R] M') (g : P →ₗ[R] M ⊗[R] N) :
    α⁻¹ ∘ₗ f ⊗ₘ ρ⁻¹ ∘ₗ g = (f ⊗ₘ id) ⊗ₘ id ∘ₗ ρ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_rid_symm]

@[coassoc_simps]
lemma assoc_comp_rid_symm :
    (α ∘ₗ ρ⁻¹ : M ⊗[R] N →ₗ[R] _) = id ⊗ₘ ρ⁻¹ := by ext; rfl

@[coassoc_simps]
lemma assoc_comp_rid_symm_assoc (f : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ ρ⁻¹ ∘ₗ f = id ⊗ₘ ρ⁻¹ ∘ₗ f := by
  simp_rw [← assoc_comp_rid_symm, LinearMap.comp_assoc]

@[coassoc_simps]
lemma assoc_comp_map_lid_symm (f : N →ₗ[R] N') :
    α ∘ₗ λ⁻¹ ⊗ₘ f = (id ⊗ₘ (id (M := M) ⊗ₘ f)) ∘ₗ λ⁻¹ := by
  ext; rfl

@[coassoc_simps]
lemma assoc_comp_map_lid_symm_assoc (f : N →ₗ[R] N') (g : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ λ⁻¹ ⊗ₘ f ∘ₗ g = (id ⊗ₘ (id ⊗ₘ f)) ∘ₗ λ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_lid_symm]

@[coassoc_simps]
lemma assoc_comp_map_rid_symm (f : N →ₗ[R] N') :
    α ∘ₗ ρ⁻¹ ⊗ₘ f = id (M := M) ⊗ₘ ((id ⊗ₘ f) ∘ₗ λ⁻¹) := by
  ext; rfl

@[coassoc_simps]
lemma assoc_comp_map_rid_symm_assoc (f : N →ₗ[R] N') (g : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ ρ⁻¹ ⊗ₘ f ∘ₗ g = id ⊗ₘ ((id ⊗ₘ f) ∘ₗ λ⁻¹) ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_rid_symm]

-- loops. TODO: replace with simproc
lemma lid_comp_map (f : M →ₗ[R] R) (g : N →ₗ[R] M') :
    λ ∘ₗ (f ⊗ₘ g) = g ∘ₗ λ ∘ₗ (f ⊗ₘ id) := by
  ext; simp

-- loops. TODO: replace with simproc
lemma lid_comp_map_assoc (f : M →ₗ[R] R) (g : N →ₗ[R] M') (h : P →ₗ[R] M ⊗[R] N) :
    λ ∘ₗ (f ⊗ₘ g) ∘ₗ h = g ∘ₗ λ ∘ₗ (f ⊗ₘ id) ∘ₗ h := by
  simp only [← LinearMap.comp_assoc, lid_comp_map _ g]

@[coassoc_simps] --TODO: remove once simproc lands
lemma lid_comp_map_id (g : N →ₗ[R] M') :
    λ ∘ₗ (id ⊗ₘ g) = g ∘ₗ λ := by
  ext; simp

@[coassoc_simps] --TODO: remove once simproc lands
lemma lid_comp_map_id_assoc (g : N →ₗ[R] M') (h : P →ₗ[R] R ⊗[R] N) :
    λ ∘ₗ (id ⊗ₘ g) ∘ₗ h =
      g ∘ₗ λ ∘ₗ h := by
  simp only [← LinearMap.comp_assoc, lid_comp_map_id]

@[coassoc_simps]
lemma lid_symm_comp (f : M →ₗ[R] M') :
    λ⁻¹ ∘ₗ f = (id ⊗ₘ f) ∘ₗ λ⁻¹ := by
  ext; rfl

@[coassoc_simps]
lemma rid_symm_comp (f : M →ₗ[R] M') :
    ρ⁻¹ ∘ₗ f = (f ⊗ₘ id) ∘ₗ ρ⁻¹ := by
  ext; rfl

@[coassoc_simps]
lemma symm_comp_lid_symm :
    (β ∘ₗ λ⁻¹ : M →ₗ[R] _) = ρ⁻¹ := rfl

@[coassoc_simps]
lemma symm_comp_lid_symm_assoc (f : M →ₗ[R] M') :
    β ∘ₗ λ⁻¹ ∘ₗ f = ρ⁻¹ ∘ₗ f := rfl

@[coassoc_simps]
lemma symm_comp_rid_symm :
    (β ∘ₗ ρ⁻¹ : M →ₗ[R] _) = λ⁻¹ := rfl

@[coassoc_simps]
lemma symm_comp_rid_symm_assoc (f : M →ₗ[R] M') :
    β ∘ₗ ρ⁻¹ ∘ₗ f = λ⁻¹ ∘ₗ f := rfl

@[coassoc_simps]
lemma symm_comp_map (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    β ∘ₗ (f ⊗ₘ g) = (g ⊗ₘ f) ∘ₗ β := by ext; rfl

@[coassoc_simps]
lemma symm_comp_map_assoc (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] M ⊗[R] N) :
    β ∘ₗ (f ⊗ₘ g) ∘ₗ h = (g ⊗ₘ f) ∘ₗ β ∘ₗ h := by
  simp only [← LinearMap.comp_assoc, symm_comp_map]

@[coassoc_simps]
lemma coassoc_left [Coalgebra R M] (f : M →ₗ[R] M') :
    α ∘ₗ (δ ⊗ₘ f) ∘ₗ δ = (id ⊗ₘ (id ⊗ₘ f)) ∘ₗ (id ⊗ₘ δ) ∘ₗ δ := by
  simp_rw [← LinearMap.lTensor_def, ← coassoc, ← LinearMap.comp_assoc, LinearMap.lTensor_def,
    map_map_comp_assoc_eq]
  simp only [coassoc_simps]

@[coassoc_simps]
lemma coassoc_left_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : N →ₗ[R] M) :
    α ∘ₗ (δ ⊗ₘ f) ∘ₗ δ ∘ₗ g = (id ⊗ₘ (id ⊗ₘ f)) ∘ₗ (id ⊗ₘ δ) ∘ₗ δ ∘ₗ g := by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

@[coassoc_simps]
lemma coassoc_right [Coalgebra R M] (f : M →ₗ[R] M') :
    α⁻¹ ∘ₗ (f ⊗ₘ δ) ∘ₗ δ = ((f ⊗ₘ id) ⊗ₘ id) ∘ₗ (δ ⊗ₘ id) ∘ₗ δ := by
  simp_rw [← LinearMap.rTensor_def, ← coassoc_symm, ← LinearMap.comp_assoc, LinearMap.rTensor_def,
    map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

@[coassoc_simps]
lemma coassoc_right_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : N →ₗ[R] M) :
    α⁻¹ ∘ₗ (f ⊗ₘ δ) ∘ₗ δ ∘ₗ g = ((f ⊗ₘ id) ⊗ₘ id) ∘ₗ (δ ⊗ₘ id) ∘ₗ δ ∘ₗ g := by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

lemma map_counit_comp_comul_left [Coalgebra R M] (f : M →ₗ[R] M') :
    (ε ⊗ₘ f) ∘ₗ δ = (id ⊗ₘ f) ∘ₗ λ⁻¹ := by
  rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc, Coalgebra.rTensor_counit_comp_comul]
  rfl

lemma map_counit_comp_comul_left_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : P →ₗ[R] M) :
    (ε ⊗ₘ f) ∘ₗ δ ∘ₗ g = (id ⊗ₘ f) ∘ₗ λ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_left]

lemma map_counit_comp_comul_right [Coalgebra R M] (f : M →ₗ[R] M') :
    (f ⊗ₘ ε) ∘ₗ δ = (f ⊗ₘ id) ∘ₗ ρ⁻¹ := by
  rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_assoc, Coalgebra.lTensor_counit_comp_comul]
  rfl

lemma map_counit_comp_comul_right_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : P →ₗ[R] M) :
    (f ⊗ₘ ε) ∘ₗ δ ∘ₗ g = (f ⊗ₘ id) ∘ₗ ρ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_right]

@[coassoc_simps]
lemma assoc_comp_map_comm_comp_comul_comp_comul [Coalgebra R M] (f : M →ₗ[R] N) :
    α ∘ₗ ((β ∘ₗ δ) ⊗ₘ f) ∘ₗ δ = (id ⊗ₘ ((id ⊗ₘ f) ∘ₗ β)) ∘ₗ α ∘ₗ δ ⊗ₘ id ∘ₗ β ∘ₗ δ := by
  rw [← symm_comp_map_assoc, ← LinearMap.lTensor_def, ← LinearMap.lTensor_def,
    ← LinearMap.lTensor_def, ← Coalgebra.coassoc, ← f.comp_id,
    TensorProduct.map_comp, ← LinearMap.rTensor_def]
  simp only [← LinearMap.comp_assoc]
  congr 2
  ext
  rfl

@[coassoc_simps]
lemma assoc_comp_map_comm_comp_comul_comp_comul_assoc
    [Coalgebra R M] (f : M →ₗ[R] N) (h : Q →ₗ[R] M) :
    α ∘ₗ ((β ∘ₗ δ) ⊗ₘ f) ∘ₗ δ ∘ₗ h = (id ⊗ₘ ((id ⊗ₘ f) ∘ₗ β)) ∘ₗ α ∘ₗ δ ⊗ₘ id ∘ₗ β ∘ₗ δ ∘ₗ h := by
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp only [LinearMap.comp_assoc, assoc_comp_map_comm_comp_comul_comp_comul]

end Coalgebra
