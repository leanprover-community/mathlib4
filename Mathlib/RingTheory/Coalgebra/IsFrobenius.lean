/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

import Mathlib.RingTheory.Coalgebra.CoassocSimps

/-!
# Frobenius equations

This file defines `Coalgebra.IsFrobenius` and shows some elementary results.

A coalgebra with an algebra structure is said to be Frobenius when the Frobenius equation
is satisfied:
`(id ⊗ mul') ∘ assoc ∘ (comul ⊗ id) = (mul' ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`,
which in diagrams looks like
```
|    |             |    |
|    μ             μ    |
|   / \           / \   |
 \ /   |    =    |   \ /
  δ    |         |    δ
  |    |         |    |
```
where `μ` stands for multiplication and `δ` for comultiplication.

When the Frobenius equations are satisfied, we actually get
`(id ⊗ mul') ∘ assoc ∘ (comul ⊗ id) = comul ∘ mul' = (mul' ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`,
which in diagrams looks like
```
|    |                           |    |
|    μ           |   |           μ    |
|   / \           \ /           / \   |
 \ /   |    =    δ ∘ μ    =    |   \ /
  δ    |          / \          |    δ
  |    |         |   |         |    |
```
In texts, this is what the Frobenius equations are usually referred to as.

## Main definitions and results

* `Coalgebra.IsFrobenius`: the class for when a coalgebra satisfies the Frobenius equations
* `Coalgebra.IsFrobenius.left_eq_comul_comp_mul'`:
  the left Frobenius equation `(id ⊗ mul') ∘ assoc ∘ (comul ⊗ id) = comul ∘ mul'`
* `Coalgebra.IsFrobenius.right_eq_comul_comp_mul'`:
  the right Frobenius equation `(mul' ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul) = comul ∘ mul'`
* `Coalgebra.IsFrobenius.instFinite`: a coalgebra satisfying the Frobenius equations is finite
* `Coalgebra.IsFrobenius.instProjective`: a coalgebra satisfying the Frobenius equations is
  projective
* `Bialgebra.nonempty_algEquiv_of_isFrobenius`: when a bialgebra satisfies the Frobenius
  equations, `R` is isomorphic to `A`
-/

public section

open TensorProduct LinearMap Coalgebra
open scoped RingTheory.LinearMap

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

local notation3 "α" => (TensorProduct.assoc R _ _ _).toLinearMap
local notation3 "α⁻¹" => (TensorProduct.assoc R _ _ _).symm.toLinearMap
local notation3 "β" => (TensorProduct.lid R _).toLinearMap
local notation3 "β⁻¹" => (TensorProduct.lid R _).symm.toLinearMap
local notation "rT" => rTensor
local notation "lT" => lTensor

-- TODO: move earlier
lemma LinearMap.mul'_comp_map_lid_comp {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] R ⊗[R] A) (g : N →ₗ[R] A) :
    μ[R] ∘ₗ ((β ∘ₗ f) ⊗ₘ g) = β ∘ₗ lT R μ ∘ₗ α ∘ₗ (f ⊗ₘ g) := by
  trans μ[R] ∘ₗ (rT _ β) ∘ₗ (f ⊗ₘ g)
  · ext; simp
  simp only [← comp_assoc]
  congr 1; ext; simp

/-! ### Definition and basic properties -/

section Defs
variable (R A)
variable [CoalgebraStruct R A]

/-- The left-hand side of the Frobenius equation: `(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id)`. -/
@[expose] def Coalgebra.IsFrobenius.left : A ⊗[R] A →ₗ[R] A ⊗[R] A := lT A μ[R] ∘ₗ α ∘ₗ rT A δ

lemma Coalgebra.IsFrobenius.left_def : left R A = lT A μ[R] ∘ₗ α ∘ₗ rT A δ := rfl

/-- The right-hand side of the Frobenius equation: `(mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`. -/
@[expose] def Coalgebra.IsFrobenius.right : A ⊗[R] A →ₗ[R] A ⊗[R] A := rT A μ[R] ∘ₗ α⁻¹ ∘ₗ lT A δ

lemma Coalgebra.IsFrobenius.right_def : right R A = rT A μ[R] ∘ₗ α⁻¹ ∘ₗ lT A δ := rfl

/-- A coalgebra with an algebra structure is said to be **Frobenius** when
the Frobenius equation is satisfied, i.e., `IsFrobenius.left` and `IsFrobenius.right` are equal,
in other words,

`(id ⊗ mul') ∘ assoc ∘ (comul ⊗ id) = (mul' ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`.

See `IsFrobenius.left_eq` and `IsFrobenius.right_eq` which refer to each side of the equality
being equal to `comul ∘ mul'`.

When the Frobenius equations are satisfied, the bilinear form `mul.compr₂ counit` is
nondegenerate and bijective (see `IsFrobenius.nondegenerate_compr₂_mul_counit` and
`IsFrobenius.bijective_compr₂_mul_counit`). -/
class Coalgebra.IsFrobenius : Prop where
  /-- The Frobenius equation. -/
  left_eq_right : IsFrobenius.left R A = IsFrobenius.right R A

end Defs

namespace Coalgebra.IsFrobenius
variable [Coalgebra R A] [IsFrobenius R A]

instance _root_.CommSemiring.toIsFrobenius : IsFrobenius R R where
  left_eq_right := by ext; simp [left_def, right_def]

lemma left_eq_comul_comp_mul' : left R A = δ ∘ₗ μ[R] := by
  have h := ‹IsFrobenius R A›.left_eq_right
  simp only [left_def, lTensor, rTensor, right_def] at h ⊢
  calc
    _ = rT A μ ∘ₗ α⁻¹ ∘ₗ ((β ∘ₗ rT A ε ∘ₗ δ) ⊗ₘ δ) := by
      simp only [h, CoassocSimps.map_counit_comp_comul_left, coassoc_simps]
    _ = β ∘ₗ rT (A ⊗[R] A) ε ∘ₗ α ∘ₗ rT A (rT A μ ∘ₗ α⁻¹ ∘ₗ lT A δ) ∘ₗ α⁻¹ ∘ₗ lT A δ := by
      simp only [rTensor, lTensor, ← h, lid_tensor]
      simp only [coassoc_simps, mul'_comp_map_lid_comp]
    _ = β ∘ₗ (ε ⊗ₘ δ) ∘ₗ lT A μ ∘ₗ α ∘ₗ rT A δ := by simp only [assoc_tensor, h, coassoc_simps]
    _ = β ∘ₗ lT R (δ ∘ₗ μ) ∘ₗ α ∘ₗ rT A (rT A ε ∘ₗ δ) := by simp only [coassoc_simps]
    _ = δ ∘ₗ μ := by simp only [coassoc_simps, CoassocSimps.map_counit_comp_comul_left]

lemma right_eq_comul_comp_mul' : right R A = δ ∘ₗ μ[R] := by
  rw [← left_eq_right, left_eq_comul_comp_mul']

-- TODO: show `IsFrobenius R (A ⊗ B)` and `IsFrobenius R (A × B)`
-- should be easy, but annoying

/-! ### Unital coalgebras

When our coalgebra is unital and satisfies the Frobenius equations, we get that the counit is
nondegenerate, and that it is finite and projective. -/

section nonAssoc
variable {A : Type*} [NonAssocSemiring A] [Module R A] [Coalgebra R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [IsFrobenius R A]

private lemma sum_counit_mul_left_smul_of_comul_one {S : Finset (A × A)}
    (hS : δ (1 : A) = ∑ i ∈ S, i.1 ⊗ₜ[R] i.2) (a : A) :
    ∑ x ∈ S, (ε : _ →ₗ[R] _) (a * x.1) • x.2 = a := by
  simpa [hS, tmul_sum, right_def] using congr(β (rT A ε ($right_eq_comul_comp_mul' (a ⊗ₜ[R] 1))))

private lemma sum_counit_mul_right_smul_of_comul_one {S : Finset (A × A)}
    (hS : δ (1 : A) = ∑ i ∈ S, i.1 ⊗ₜ[R] i.2) (a : A) :
    ∑ x ∈ S, (ε : _ →ₗ[R] _) (x.2 * a) • x.1 = a := by
  simpa [hS, sum_tmul, left_def] using
    congr(TensorProduct.rid R A (lT A ε ($left_eq_comul_comp_mul' (1 ⊗ₜ[R] a))))

instance instFinite : Module.Finite R A := by
  have ⟨S, hS⟩ := exists_finset (R := R) (δ (1 : A))
  classical refine Module.finite_def.mpr ⟨S.image Prod.snd, top_le_iff.mp fun a _ ↦ ?_⟩
  rw [← sum_counit_mul_left_smul_of_comul_one hS a]
  exact sum_mem fun _ _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (by grind))

instance instProjective : Module.Projective R A := by
  have ⟨S, hS⟩ := exists_finset (R := R) (δ (1 : A))
  refine Module.projective_def'.mpr ⟨∑ p ∈ S, (ε ∘ₗ mulRight R p.1).smulRight (.single p.2 1), ?_⟩
  ext; simp [sum_counit_mul_left_smul_of_comul_one hS]

/-- The bilinear form `(mul R A).compr₂ counit` is separating left.
This is the simplified version, see `nondegenerate_compr₂_mul_counit`. -/
lemma forall_counit_mul_left_eq_zero_iff {a : A} : (∀ b, (ε : _ →ₗ[R] _) (a * b) = 0) ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, fun h _ ↦ by simp [h]⟩
  have ⟨S, hS⟩ := exists_finset (R := R) (δ (1 : A))
  simpa [h] using (sum_counit_mul_left_smul_of_comul_one hS a).symm

/-- The bilinear form `(mul R A).compr₂ counit` is separating right.
This is the simplified version, see `nondegenerate_compr₂_mul_counit`. -/
lemma forall_counit_mul_right_eq_zero_iff {a : A} : (∀ b, (ε : _ →ₗ[R] _) (b * a) = 0) ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, fun h _ ↦ by simp [h]⟩
  have ⟨S, hS⟩ := exists_finset (R := R) (δ (1 : A))
  simpa [hS, sum_tmul, h] using (sum_counit_mul_right_smul_of_comul_one hS a).symm

/-- The bilinear form `mul.compr₂ counit` is nondegenerate. -/
lemma nondegenerate_compr₂_mul_counit : ((mul R A).compr₂ ε).Nondegenerate :=
  ⟨fun _ ↦ forall_counit_mul_left_eq_zero_iff.mp, fun _ ↦ forall_counit_mul_right_eq_zero_iff.mp⟩

/-- The bilinear form `mul.compr₂ counit` is bijective. -/
lemma bijective_compr₂_mul_counit : (⇑((mul R A).compr₂ ε)).Bijective := by
  have ⟨S, hS⟩ := exists_finset (R := R) (δ (1 : A))
  refine ⟨fun a b h ↦ ?_, fun f ↦ ⟨∑ x ∈ S, f x.1 • x.2, ext fun b ↦ ?_⟩⟩
  · rw [← sum_counit_mul_left_smul_of_comul_one hS b]
    simp only [LinearMap.ext_iff, compr₂_apply, mul_apply_apply] at h
    simp only [← h, sum_counit_mul_left_smul_of_comul_one hS]
  · calc _ = ∑ x ∈ S, ε (x.2 * b) * f x.1 := by simp [mul_comm (f _)]
      _ = ∑ x ∈ S, ε (x.2 * b) • f x.1 := by simp only [← smul_eq_mul]; rfl
      _ = _ := by simp only [← map_smul, ← map_sum, sum_counit_mul_right_smul_of_comul_one hS]

end nonAssoc

/-! ### The snake equations

Composing the Frobenius equations with the counit and algebra map gives the so called "snake"
equations. -/

section Algebra
variable {A : Type*} [Semiring A] [Algebra R A] [Coalgebra R A] [IsFrobenius R A]

/-- Composing the left Frobenius equation with `Coalgebra.counit` and `Algebra.linearMap`.
See `rTensor_counit_comp_right_comp_lTensor_algebraLinearMap` for the right Frobenius equation
version.

(This is sometimes known as the left snake equation.) -/
lemma lTensor_counit_comp_left_comp_rTensor_algebraLinearMap :
    lT A ε ∘ₗ left R A ∘ₗ rT A η[R] = (TensorProduct.comm _ _ _).toLinearMap := by
  ext; simp [left_eq_comul_comp_mul']

/-- Composing the right Frobenius equation with `Coalgebra.counit` and `Algebra.linearMap`.
See `lTensor_counit_comp_left_comp_rTensor_algebraLinearMap` for the left Frobenius equation
version.

(This is sometimes known as the right snake equation.) -/
lemma rTensor_counit_comp_right_comp_lTensor_algebraLinearMap :
    rT A ε ∘ₗ right R A ∘ₗ lT A η[R] = (TensorProduct.comm _ _ _).toLinearMap := by
  ext; simp [right_eq_comul_comp_mul']

end Algebra

end Coalgebra.IsFrobenius

/-! ### Bialgebras and the Frobenius equations

If a bialgebra `A` over `R` satisfies the Frobenius equations, then `A` is
isomorphic to the underlying ring `R`. -/

namespace Bialgebra
variable {A : Type*} [Semiring A] [Bialgebra R A] [IsFrobenius R A]

@[simp] lemma comul_apply_eq_of_isFrobenius (a : A) : δ a = a ⊗ₜ[R] 1 := by
  simpa [Algebra.TensorProduct.one_def, IsFrobenius.right_def] using
    congr($IsFrobenius.right_eq_comul_comp_mul' (a ⊗ₜ[R] 1)).symm

lemma comul_eq_of_isFrobenius : δ = (TensorProduct.mk R A A).flip 1 :=
  ext comul_apply_eq_of_isFrobenius

@[simp] lemma algebraMap_counit_of_isFrobenius (a : A) : algebraMap R A (ε a) = a := by
  simpa [Algebra.algebraMap_eq_smul_one] using congr(β ($rTensor_counit_comp_comul a))

lemma algebraMap_bijective_of_isFrobenius : Function.Bijective (algebraMap R A) :=
  ⟨algebraMap_injective A, fun a ↦ ⟨ε a, by simp⟩⟩

lemma counit_bijective_of_isFrobenius : Function.Bijective (ε : A →ₗ[R] R) :=
  ⟨Function.LeftInverse.injective algebraMap_counit_of_isFrobenius, counit_surjective⟩

/-- When a bialgebra satisfies the Frobenius equations, we get `R ≃ A`.
So if `R` and `A` are not isomorphic, then `A` cannot satisfy the Frobenius equations. -/
lemma nonempty_algEquiv_of_isFrobenius : Nonempty (R ≃ₐ[R] A) :=
  ⟨.ofBijective (Algebra.ofId R A) algebraMap_bijective_of_isFrobenius⟩

end Bialgebra
