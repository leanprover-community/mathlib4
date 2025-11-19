/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup

/-!
# Algebra automorphisms in `End K V` are inner

This file shows that given any algebra equivalence `f : End K V ≃ₐ End K V`,
there exists a linear equivalence `T : V ≃ₗ V` such that `f x = T ∘ₗ x ∘ₗ T.symm`.
In other words, the map `MulSemiringAction.toAlgEquiv` from `GeneralLinearGroup K V` to
`End K V ≃ₐ End K V` is surjective.
-/

namespace Module.End
variable {R K V : Type*} [CommSemiring R] [Semifield K] [AddCommMonoid V] [Module R V] [Module K V]

open Module LinearMap End Free

/-- This takes in a linear map `f : End R V →ₗ End R V`, a dual `y : Dual R V`,
and an element `z : V`, and constructs a linear operator on `V` such that
`x ↦ f (smulRightₗ y x) z`. -/
private def auxLinear (f : End R V →ₗ[R] End R V) (y : Dual R V) (z : V) : End R V :=
  applyₗ z ∘ₗ f ∘ₗ smulRightₗ y

@[simp] private theorem auxLinear_apply (f : End R V →ₗ[R] End R V) (y : Dual R V) (x z : V) :
  auxLinear f y z x = f (smulRight y x) z := rfl

private theorem auxLinear_map_apply (f : End R V →ₐ[R] End R V) (y : Dual R V)
    (z : V) (A : End R V) (x : V) :
    auxLinear f y z (A x) = f A (auxLinear f y z x) := by
  simp_rw [auxLinear_apply, coe_coe, ← mul_apply, ← map_mul]
  congr; ext; simp

/-- Given an algebra automorphism `f` in `End K V`, there exists a linear isomorphism `T`
such that `f` is given by `x ↦ T ∘ₗ x ∘ₗ T.symm`. -/
theorem AlgEquiv.coe_eq_linearEquiv_conj [Free K V] (f : End K V ≃ₐ[K] End K V) :
    ∃ T : V ≃ₗ[K] V, ⇑f = T.conj := by
  nontriviality V
  simp_rw [funext_iff, LinearEquiv.conj_apply, LinearEquiv.eq_comp_toLinearMap_symm]
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  obtain ⟨v, huv⟩ := exists_dual_ne_zero K hu
  obtain ⟨z, hz⟩ : ∃ z : V, ¬ f (smulRight v u) z = (0 : End K V) z := by
    rw [← not_forall, ← LinearMap.ext_iff, EmbeddingLike.map_eq_zero_iff, LinearMap.ext_iff]
    exact not_forall.mpr ⟨u, huv.isUnit.smul_eq_zero.not.mpr hu⟩
  set T := auxLinear f v z
  have this A x : T (A x) = f A (T x) := auxLinear_map_apply f.toAlgHom v z A x
  have surj : Function.Surjective T := fun w ↦ by
    obtain ⟨d, hd⟩ := exists_dual_eq_one K hz
    exact ⟨f.symm (smulRightₗ d w) u, by simp [T, this, hd]⟩
  have inj : Function.Injective T := fun x y hxy ↦ by
    have h_smul : smulRightₗ v x = smulRightₗ v y := by
      apply f.injective <| ext fun z ↦ ?_
      obtain ⟨w, rfl⟩ := surj z
      simp_rw [← this, smulRightₗ_apply, map_smul, hxy]
    simpa [huv.isUnit.smul_left_cancel] using congr((fun f ↦ f u) $h_smul)
  exact ⟨.ofBijective T ⟨inj, surj⟩, fun A ↦ (ext <| auxLinear_map_apply f v z A).symm⟩

/-- Alternate statement of `coe_eq_linearEquiv_conj`. -/
theorem mulSemiringActionToAlgEquiv_conjAct_surjective [Free K V] :
    Function.Surjective
      (MulSemiringAction.toAlgEquiv (G := ConjAct (GeneralLinearGroup K V)) K (End K V)) := by
  intro f
  obtain ⟨T, hT⟩ := f.coe_eq_linearEquiv_conj
  exact ⟨.ofLinearEquiv T, (DFunLike.coe_injective hT).symm⟩

end Module.End
