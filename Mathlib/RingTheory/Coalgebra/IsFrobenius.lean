/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.Algebra.Module.Projective

import Mathlib.RingTheory.Coalgebra.CoassocSimps

/-!
# Frobenius equations

This file defines `Coalgebra.IsFrobenius` and shows some elementary results.

A coalgebra with an algebra structure is said to be Frobenius when the Frobenius equation
is satisfied:
`(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = comul ∘ mul = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`,
which in diagrams looks like
```
|    |                           |    |
|    μ          |   |            μ    |
|   / \          \ /            / \   |
 \ /   |    =   δ ∘ μ     =    |   \ /
  δ    |         / \           |    δ
  |    |        |   |          |    |
```
where `μ` stands for multiplication and `δ` for comultiplication.

This file shows that it suffices to have
`(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)` in order to have the
Frobenius equations. So we call this one the Frobenius equation too.

## Naming convention

We call the left part of the Frobenius equation "left" in lemma names, and the right part "right"
for simplicity.

## Main definitions and results

* `Coalgebra.IsFrobenius`: the class for when a coalgebra satisfies the Frobenius equations
* `Coalgebra.IsFrobenius.left_eq`:
  the left Frobenius equation `(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = comul ∘ mul`
* `Coalgebra.IsFrobenius.right_eq`:
  the right Frobenius equation `(mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul) = comul ∘ mul`
* `Coalgebra.IsFrobenius.instFinite`: a coalgebra satisfying the Frobenius equations is finite
* `Coalgebra.IsFrobenius.instProjective`: a coalgebra satisfying the Frobenius equations is
  projective
* `Bialgbera.nonempty_algEquiv_of_isFrobenius`: when a bialgebra satisfies the Frobenius
  equations, `R` is isomorphic to `A`
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

/-! ### Definition and basic properties -/

variable (R A) in
/-- A coalgebra with an algebra structure is said to be **Frobenius** when
the Frobenius equation is satisfied:

`(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`. -/
class Coalgebra.IsFrobenius : Prop where
  /-- The Frobenius equation. -/
  eq : lT A μ[R] ∘ₗ α ∘ₗ rT A δ = rT A μ[R] ∘ₗ α⁻¹ ∘ₗ lT A δ

instance CommSemiring.toIsFrobenius : IsFrobenius R R where eq := by ext; simp

namespace Coalgebra.IsFrobenius
variable [IsFrobenius R A]

/-- The left Frobenius equation. -/
lemma left_eq : lT A μ[R] ∘ₗ α ∘ₗ rT A δ = δ ∘ₗ μ[R] := by
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
lemma right_eq : rT A μ[R] ∘ₗ α⁻¹ ∘ₗ lT A δ = δ ∘ₗ μ[R] := eq (R := R) (A := A) ▸ left_eq

alias lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul' := left_eq
alias rTensor_mul'_comp_assoc_symm_comp_lTensor_comul_eq_comul_comp_mul' := right_eq

-- TODO: show `IsFrobenius R (A ⊗ B)` and `IsFrobenius R (A × B)`
-- should be easy, but annoying

/-! ### Unital coalgebras

When our coalgebra is unital and satisfies the Frobenius equations, we get that the counit is
nondegenerate, and that it is finite and projective. -/

section nonAssoc
variable {A : Type*} [NonAssocSemiring A] [Module R A] [Coalgebra R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [IsFrobenius R A]

private lemma sum_counit_mul_smul_of_comul_one {S : Finset (A × A)}
    (hS : δ (1 : A) = ∑ i ∈ S, i.1 ⊗ₜ[R] i.2) (a : A) :
    ∑ x ∈ S, (ε : _ →ₗ[R] _) (a * x.1) • x.2 = a := by
  simpa [hS, tmul_sum] using congr(β (rT A ε ($right_eq (a ⊗ₜ[R] 1))))

/-- If a coalgebra satisfies the Frobenius equations, then its counit is nondegenerate. -/
lemma forall_counit_mul_eq_zero_iff {a : A} :
    (∀ b, (ε : _ →ₗ[R] _) (a * b) = 0) ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, fun h _ ↦ by simp [h]⟩
  obtain ⟨S, hS⟩ := exists_finset (R := R) (δ (1 : A))
  simpa [h] using (sum_counit_mul_smul_of_comul_one hS a).symm

instance instFinite : Module.Finite R A := by
  have ⟨S, hS⟩ := exists_finset (R := R) (δ (1 : A))
  classical refine Module.finite_def.mpr ⟨S.image Prod.snd, top_le_iff.mp fun a _ ↦ ?_⟩
  rw [← sum_counit_mul_smul_of_comul_one hS a]
  exact sum_mem fun _ _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (by grind))

instance instProjective : Module.Projective R A := by
  obtain ⟨S, hS⟩ := exists_finset (R := R) (δ (1 : A))
  refine Module.projective_def'.mpr ⟨∑ p ∈ S, (ε ∘ₗ mulRight R p.1).smulRight (.single p.2 1), ?_⟩
  ext; simp [sum_counit_mul_smul_of_comul_one hS]

end nonAssoc

/-! ### The snake equations

Composing the Frobenius equations with the counit and algebra map gives the so called "snake"
equations. -/

section Algebra
variable {A : Type*} [Semiring A] [Algebra R A] [Coalgebra R A] [IsFrobenius R A]

/-- Composing the Frobenius equations with `Coalgebra.counit` and `Algebra.linearMap`.
See `rTensor_counit_comp_right_comp_lTensor_algebraLinearMap` for when we
compose it on the other side of the tensor.

(This is sometimes known as the left snake equation.) -/
lemma lTensor_counit_comp_left_comp_rTensor_algebraLinearMap :
    lT A (ε ∘ₗ μ[R]) ∘ₗ α ∘ₗ rT A (δ ∘ₗ η[R]) = (TensorProduct.comm _ _ _).toLinearMap := by
  simp_rw [rTensor_comp, ← comp_assoc (rT A η), lTensor_comp, comp_assoc _ (lT _ _),
    left_eq, ← comp_assoc, lTensor_counit_comp_comul]
  ext; simp

/-- Composing the Frobenius equations with `Coalgebra.counit` and `Algebra.linearMap`.
See `lTensor_counit_comp_left_comp_rTensor_algebraLinearMap` for when we
compose it on the other side of the tensor.

(This is sometimes known as the right snake equation.) -/
lemma rTensor_counit_comp_right_comp_lTensor_algebraLinearMap :
    rT A (ε ∘ₗ μ[R]) ∘ₗ α⁻¹ ∘ₗ lT A (δ ∘ₗ η[R]) = (TensorProduct.comm _ _ _).toLinearMap := by
  simp_rw [lTensor_comp, ← comp_assoc (lT A η), rTensor_comp, comp_assoc _ (rT _ _),
    right_eq, ← comp_assoc, rTensor_counit_comp_comul]
  ext; simp

alias rTensor_counit_comp_mul'_comp_assoc_symm_comp_lTensor_comul_comp_algebraLinearMap :=
  rTensor_counit_comp_right_comp_lTensor_algebraLinearMap
alias lTensor_counit_comp_mul'_comp_assoc_comp_rTensor_comul_comp_algebraLinearMap :=
  lTensor_counit_comp_left_comp_rTensor_algebraLinearMap

end Algebra

end Coalgebra.IsFrobenius

/-! ### Bialgebras and the Frobenius equations

If a bialgebra `A` over `R` satisfies the Frobenius equations, then `A` is
isomorphic to the underlying ring `R`. -/

namespace Bialgebra
variable {A : Type*} [Semiring A] [Bialgebra R A] [IsFrobenius R A]

@[simp] lemma comul_apply_eq_of_isFrobenius (a : A) : δ a = a ⊗ₜ[R] 1 := by
  simpa [Algebra.TensorProduct.one_def] using congr($IsFrobenius.right_eq (a ⊗ₜ[R] 1)).symm

lemma comul_eq_of_isFrobenius : δ = (TensorProduct.mk R A A).flip 1 :=
  ext comul_apply_eq_of_isFrobenius

@[simp] lemma algebraMap_counit_of_isFrobenius (a : A) : algebraMap R A (ε a) = a := by
  simpa [Algebra.algebraMap_eq_smul_one] using congr(β ($rTensor_counit_comp_comul a))

lemma algebraMap_bijective_of_isFrobenius : Function.Bijective (algebraMap R A) :=
  ⟨algebraMap_injective A, fun a ↦ ⟨ε a, by simp⟩⟩

lemma counit_bijective_of_isFrobenius : Function.Bijective (ε : A →ₗ[R] R) :=
  ⟨Function.LeftInverse.injective algebraMap_counit_of_isFrobenius, counit_surjective⟩

/-- When a bialgebra satisfies the Frobenius equations, we get `R ≃ A`.
So if `R` and `A` are not isomorphic, then it cannot satisfy the Frobenius equations. -/
lemma nonempty_algEquiv_of_isFrobenius : Nonempty (R ≃ₐ[R] A) :=
  ⟨.ofBijective (Algebra.ofId R A) algebraMap_bijective_of_isFrobenius⟩

end Bialgebra
