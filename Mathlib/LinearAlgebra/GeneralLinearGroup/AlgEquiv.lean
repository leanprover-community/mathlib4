/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Algebra automorphisms in `End R V` are inner

This file shows that given any algebra equivalence `f : End R V ≃ₐ End R V`,
there exists a linear equivalence `T : V ≃ₗ T` such that `f x = T * x * T.symm`.
In other words, the map `MulSemiringAction.toAlgEquiv` from `GeneralLinearGroup R V` to
`End R V ≃ₐ End R V` is surjective.
-/

namespace Module.End
variable {R K V : Type*} [CommSemiring R] [Field K] [AddCommGroup V] [Module R V] [Module K V]

open Module LinearMap End Free

/-- This takes in a linear map `f : End R V →ₗ End R V`, a dual `y : Dual R V`,
and an element `z : V`, and constructs a linear operator on `V` such that
`x ↦ f (smulRightₗ y x) z`. -/
private def auxLinear (f : End R V →ₗ[R] End R V) (y : Dual R V) (z : V) : End R V :=
  applyₗ z ∘ₗ f ∘ₗ smulRightₗ y

@[simp] private theorem auxLinear_apply (f : End R V →ₗ[R] End R V) (y : Dual R V) (x z : V) :
  auxLinear f y z x = f (smulRightₗ y x) z := rfl

private theorem auxLinear_map_apply (f : End R V →ₐ[R] End R V) (y : Dual R V)
    (z : V) (A : End R V) (x : V) :
    auxLinear f y z (A x) = f A (auxLinear f y z x) := by
  simp_rw [auxLinear_apply, coe_coe, ← mul_apply, ← map_mul]
  congr
  ext
  simp

private theorem auxLinear_comp (f : End R V →ₐ[R] End R V) (y : Dual R V) (z : V) (A : End R V) :
    auxLinear f y z ∘ₗ A = f A ∘ₗ auxLinear f y z :=
  LinearMap.ext <| auxLinear_map_apply f y z A

/-- Given an algebra automorphism `f` in `End K V`, there exists a linear isomorphism `T`
such that `f` is given by `x ↦ T * x * T⁻¹`. -/
theorem AlgEquiv.coe_eq_linearEquiv_conjugate (f : End K V ≃ₐ[K] End K V) :
    ∃ T : V ≃ₗ[K] V, ⇑f = fun x ↦ T ∘ₗ x ∘ₗ T.symm := by
  nontriviality V
  simp_rw [funext_iff, ← comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm]
  obtain ⟨u, v, huv⟩ : ∃ u : V, ∃ v : Dual K V, v u ≠ 0 := by
    obtain ⟨u, hu⟩ := nontrivial_iff_exists_ne 0 |>.mp ‹Nontrivial V›
    obtain ⟨v, hv⟩ := exists_linearMap_apply_ne_zero_of_ne_zero K hu
    exact ⟨u, v, hv⟩
  obtain ⟨z, hz⟩ : ∃ z : V, f (smulRightₗ v u) z ≠ 0 := by
    simp_rw [ne_eq, ← not_forall]
    suffices ¬ f (smulRightₗ v u) = 0 by rwa [LinearMap.ext_iff] at this
    simp only [EmbeddingLike.map_eq_zero_iff, LinearMap.ext_iff, smulRightₗ_apply,
      zero_apply, smul_eq_zero, not_forall, not_or, exists_and_right]
    exact ⟨⟨u, huv⟩, fun h ↦ by simp [h] at huv⟩
  let T := auxLinear f v z
  have this A : T ∘ₗ A = f A ∘ₗ T := auxLinear_comp f.toAlgHom v z A
  have this' A x : T (A x) = f A (T x) := auxLinear_map_apply f.toAlgHom v z A x
  have surj : Function.Surjective T := by
    intro w
    have : T u ≠ 0 := by simpa [T]
    obtain ⟨d, hd⟩ := exists_linearMap_apply_eq_one_of_ne_zero K this
    use f.symm (smulRightₗ d w) u
    have h : f (f.symm (smulRightₗ d w)) (T u) = w := by simp [hd]
    simp_rw [this', h]
  have inj : Function.Injective T := (injective_iff_map_eq_zero T).mpr fun x hx ↦ by
    have h_smul : smulRightₗ v x = 0 := by
      rw [← _root_.map_eq_zero_iff _ f.injective]
      ext y
      obtain ⟨w, rfl⟩ := surj y
      rw [← this', smulRightₗ_apply, map_smul, hx, smul_zero, zero_apply]
    simpa [huv] using congr((fun f ↦ f u) $h_smul)
  exact ⟨LinearEquiv.ofBijective T ⟨inj, surj⟩, fun A ↦ this A |>.symm⟩

/-- Alternate statement of `coe_eq_linearEquiv_conjugate`. -/
theorem mulSemiringActionToAlgEquiv_conjAct_surjective :
    Function.Surjective
      (MulSemiringAction.toAlgEquiv (G := ConjAct (GeneralLinearGroup K V)) K (End K V)) := by
  intro f
  obtain ⟨T, hT⟩ := f.coe_eq_linearEquiv_conjugate
  exact ⟨GeneralLinearGroup.ofLinearEquiv T, (DFunLike.coe_injective hT).symm⟩

end Module.End
