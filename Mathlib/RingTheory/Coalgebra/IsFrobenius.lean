/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic

import Mathlib.RingTheory.Coalgebra.CoassocSimps

/-!
# Frobenius equations

This file defines `Coalgebra.IsFrobenius` and shows some elementary results.

A coalgebra with an algebra structure is said to be Frobenius when the Frobenius equation
is satisfied:
`(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = comul ∘ mul = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`,
which in diagrams looks like
```
|    |            |            |    |
|    μ            μ            μ    |
|   / \          / \          / \   |
 \ /   |    =    \ /    =    |   \ /
  δ    |          δ          |    δ
  |    |          |          |    |
```
where `μ` stands for multiplication and `δ` for comultiplication.

This file shows that it suffices to have
`(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)` in order to have the
Frobenius equations. So we call this one the Frobenius equation too.

## Main definitions and results

* `Coalgebra.IsFrobenius`: the class for when a coalgebra satisfies the Frobenius equations
* `Coalgebra.IsFrobenius.lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul'`:
  the left Frobenius equation `(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = comul ∘ mul`
* `Coalgebra.IsFrobenius.rTensor_mul'_comp_assoc_symm_comp_lTensor_comul_eq_comul_comp_mul'`:
  the right Frobenius equation `(mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul) = comul ∘ mul`
* `Coalgebra.IsFrobenius.instFinite`: a coalgebra satisfying the Frobenius equations is finite
* `Bialgbera.algebraMap_bijective_of_isFrobenius`: when a bialgebra satisfies the Frobenius
  equations, `algebraMap R A` is bijective
-/

public section

open TensorProduct LinearMap Coalgebra
open scoped RingTheory.LinearMap

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Coalgebra R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

local notation3 "α" => (TensorProduct.assoc R _ _ _).toLinearMap
local notation3 "α⁻¹" => (TensorProduct.assoc R _ _ _).symm.toLinearMap
local notation3 "β" => (TensorProduct.lid R _).toLinearMap
local notation3 "β⁻¹" => (TensorProduct.lid R _).symm.toLinearMap
local notation "rT" => rTensor
local notation "lT" => lTensor

omit [Coalgebra R A] in
-- TODO: move earlier
lemma LinearMap.mul'_comp_map_lid_comp {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] R ⊗[R] A) (g : N →ₗ[R] _) :
    μ[R] ∘ₗ ((β ∘ₗ f) ⊗ₘ g) = β ∘ₗ lT R μ ∘ₗ α ∘ₗ (f ⊗ₘ g) := by
  trans μ[R] ∘ₗ (rT _ β) ∘ₗ (f ⊗ₘ g)
  · ext; simp
  simp only [← comp_assoc]
  congr 1; ext; simp

variable (R A) in
/-- A coalgebra with an algebra structure is said to be **Frobenius** when
the Frobenius equation is satisfied:

`(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`. -/
class Coalgebra.IsFrobenius : Prop where
  /-- The Frobenius equation. -/
  eq : lT A μ[R] ∘ₗ α ∘ₗ rT A δ = rT A μ[R] ∘ₗ α⁻¹ ∘ₗ lT A δ

lemma Coalgebra.isFrobenius_self : IsFrobenius R R where eq := by ext; simp

namespace Coalgebra.IsFrobenius
variable [IsFrobenius R A]

/-- The left Frobenius equation. -/
lemma lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul' :
    lT A μ[R] ∘ₗ α ∘ₗ rT A δ = δ ∘ₗ μ[R] := by
  have h := ‹IsFrobenius R A›.eq
  simp only [lTensor, rTensor] at h ⊢
  calc
    _ = rT A μ ∘ₗ α⁻¹ ∘ₗ ((β ∘ₗ rT A ε ∘ₗ δ) ⊗ₘ δ) := by
      simp only [h, CoassocSimps.map_counit_comp_comul_left, coassoc_simps]
    _ = β ∘ₗ rT (A ⊗[R] A) ε ∘ₗ α ∘ₗ rT A (rT A μ ∘ₗ α⁻¹ ∘ₗ lT A δ) ∘ₗ α⁻¹ ∘ₗ lT A δ := by
      simp only [rTensor, lTensor, ← h, lid_tensor]
      simp only [coassoc_simps, mul'_comp_map_lid_comp]
    _ = β ∘ₗ (ε ⊗ₘ δ) ∘ₗ lT A μ ∘ₗ α ∘ₗ rT A δ := by simp only [assoc_tensor, h, coassoc_simps]
    _ = β ∘ₗ lT R (δ ∘ₗ μ) ∘ₗ α ∘ₗ rT A (rT A ε ∘ₗ δ) := by simp only [coassoc_simps]
    _ = δ ∘ₗ μ := by simp only [coassoc_simps, CoassocSimps.map_counit_comp_comul_left]

/-- The right Frobenius equation. -/
lemma rTensor_mul'_comp_assoc_symm_comp_lTensor_comul_eq_comul_comp_mul' :
    rT A μ[R] ∘ₗ α⁻¹ ∘ₗ lT A δ = δ ∘ₗ μ[R] :=
  eq (R := R) (A := A) ▸ lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul'

/-- When a coalgebra with an algebra structure satisfies the Frobenius equations, it is finite. -/
instance instFinite {A : Type*} [NonAssocSemiring A] [Module R A] [Coalgebra R A]
    [SMulCommClass R A A] [IsScalarTower R A A] [IsFrobenius R A] : Module.Finite R A := by
  have ⟨S, hS⟩ := exists_finset (R := R) (δ (1 : A))
  classical
  refine Module.finite_def.mpr ⟨S.image Prod.snd, top_le_iff.mp fun a _ ↦ ?_⟩
  have := by simpa [hS, tmul_sum] using congr(β (rT A ε
    ($rTensor_mul'_comp_assoc_symm_comp_lTensor_comul_eq_comul_comp_mul' (a ⊗ₜ[R] 1))))
  exact this ▸ sum_mem fun _ _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (by grind))

section Algebra
variable {A : Type*} [Semiring A] [Algebra R A] [Coalgebra R A] [IsFrobenius R A]

/-- Composing the Frobenius equations with `Coalgebra.counit` and `Algebra.linearMap`.
See `lTensor_counit_comp_mul'_comp_assoc_comp_rTensor_comul_comp_algebraLinearMap` for when we
compose it on the other side of the tensor.

(This is sometimes known as the snake equation.) -/
lemma rTensor_counit_comp_mul'_assoc_symm_comp_lTensor_comul_comp_algebraLinearMap :
    rT A (ε ∘ₗ μ[R]) ∘ₗ α⁻¹ ∘ₗ lT A (δ ∘ₗ η[R]) = (TensorProduct.comm _ _ _).toLinearMap := by
  simp_rw [lTensor_comp, ← comp_assoc (lT A η), rTensor_comp, comp_assoc _ (rT _ _),
    rTensor_mul'_comp_assoc_symm_comp_lTensor_comul_eq_comul_comp_mul', ← comp_assoc,
    rTensor_counit_comp_comul]
  ext; simp

/-- Composing the Frobenius equations with `Coalgebra.counit` and `Algebra.linearMap`.
See `rTensor_counit_comp_mul'_assoc_symm_comp_lTensor_comul_comp_algebraLinearMap` for when we
compose it on the other side of the tensor.

(This is sometimes known as the snake equation.) -/
lemma lTensor_counit_comp_mul'_comp_assoc_comp_rTensor_comul_comp_algebraLinearMap :
    lT A (ε ∘ₗ μ[R]) ∘ₗ α ∘ₗ rT A (δ ∘ₗ η[R]) = (TensorProduct.comm _ _ _).toLinearMap := by
  simp_rw [rTensor_comp, ← comp_assoc (rT A η), lTensor_comp, comp_assoc _ (lT _ _),
    lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul', ← comp_assoc,
    lTensor_counit_comp_comul]
  ext; simp

end Algebra

end Coalgebra.IsFrobenius

/-! ## Bialgebras and the Frobenius equations

If a bialgebra `A` over `R` satisfies the Frobenius equations, then `A` is
isomorphic to the underlying ring `R` (see `algebraMap_bijective_of_isFrobenius`). -/

namespace Bialgebra
variable {A : Type*} [Semiring A] [Bialgebra R A] [IsFrobenius R A]

lemma comul_eq_of_isFrobenius : δ = (TensorProduct.mk R A A).flip 1 := calc
  .id ∘ₗ δ = (lT A μ ∘ₗ α ∘ₗ (TensorProduct.mk R _ _).flip 1) ∘ₗ δ := by congr; ext; simp
  _ = (lT A μ ∘ₗ α ∘ₗ rT A δ) ∘ₗ (TensorProduct.mk R A A).flip 1 := by ext; simp
  _ = _ := by ext; simp [IsFrobenius.eq, Algebra.TensorProduct.one_def]

@[simp] lemma algebraMap_counit_of_isFrobenius (a : A) : algebraMap R A (ε a) = a := by
  simpa [comul_eq_of_isFrobenius, Algebra.algebraMap_eq_smul_one] using
     congr(β ($rTensor_counit_comp_comul a))

lemma algebraMap_bijective_of_isFrobenius :
    Function.Bijective (algebraMap R A) := ⟨algebraMap_injective A, fun a ↦ ⟨ε a, by simp⟩⟩

end Bialgebra
