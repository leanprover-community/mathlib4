/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.Projective

/-!
# Algebra isomorphisms between endomorphisms of projective modules are inner

This file shows that given any algebra equivalence `f : End K V ≃ₐ[K] End K W`,
there exists a linear equivalence `T : V ≃ₗ[K] W` such that `f x = T ∘ₗ x ∘ₗ T.symm`.
In other words, for `V = W`, the map `MulSemiringAction.toAlgEquiv` from
`GeneralLinearGroup K V` to `End K V ≃ₐ[K] End K V` is surjective.

For the continuous versions, see `Mathlib/Analysis/Normed/Operator/ContinuousAlgEquiv.lean`.
-/

open Module LinearMap LinearEquiv

variable {K V W : Type*} [Semifield K] [AddCommMonoid V] [Module K V] [Projective K V]
  [AddCommMonoid W] [Module K W] [Projective K W]

/-- Given an algebra isomorphism `f : End K V ≃ₐ[K] End K W`, there exists a linear isomorphism `T`
such that `f` is given by `x ↦ T ∘ₗ x ∘ₗ T.symm`. -/
public theorem AlgEquiv.eq_linearEquivConjAlgEquiv (f : End K V ≃ₐ[K] End K W) :
    ∃ T : V ≃ₗ[K] W, f = T.conjAlgEquiv K := by
  by_cases! hV : Subsingleton V
  · nontriviality W
    simpa using congr(f $(Subsingleton.allEq 0 1))
  simp_rw [AlgEquiv.ext_iff, conjAlgEquiv_apply, ← comp_assoc, eq_comp_toLinearMap_symm]
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  obtain ⟨v, huv⟩ := Projective.exists_dual_ne_zero K hu
  obtain ⟨z, hz⟩ : ∃ z : W, ¬ f (smulRight v u) z = (0 : End K W) z := by
    rw [← not_forall, ← LinearMap.ext_iff, EmbeddingLike.map_eq_zero_iff, LinearMap.ext_iff]
    exact not_forall.mpr ⟨u, huv.isUnit.smul_eq_zero.not.mpr hu⟩
  set T := applyₗ z ∘ₗ f.toLinearMap ∘ₗ smulRightₗ v
  have hT x : T x = f (smulRight v x) z := rfl
  have this A x : T (A x) = f A (T x) := by
    simp only [hT, ← End.mul_apply, ← map_mul]
    congr; ext; simp
  have surj : Function.Surjective T := fun w ↦ by
    obtain ⟨d, hd⟩ := Projective.exists_dual_eq_one K hz
    exact ⟨f.symm (smulRight d w) u, by simp [T, this, hd]⟩
  have inj : Function.Injective T := fun x y hxy ↦ by
    have h_smul : smulRightₗ v x = smulRightₗ v y := by
      apply f.injective <| LinearMap.ext fun z ↦ ?_
      obtain ⟨w, rfl⟩ := surj z
      simp_rw [← this, smulRightₗ_apply_apply, _root_.map_smul, hxy]
    simpa [huv.isUnit.smul_left_cancel] using congr((fun f ↦ f u) $h_smul)
  exact ⟨.ofBijective T ⟨inj, surj⟩, fun A ↦ (LinearMap.ext <| this A).symm⟩

variable (K V W) in
public theorem LinearEquiv.conjAlgEquiv_surjective :
    Function.Surjective (conjAlgEquiv K (S := K) (M₁ := V) (M₂ := W)) :=
  fun f ↦ f.eq_linearEquivConjAlgEquiv.imp fun _ h ↦ h.symm

/-- Alternate statement of `AlgEquiv.eq_linearEquivConjAlgEquiv` for when `V = W`. -/
public theorem Module.End.mulSemiringActionToAlgEquiv_conjAct_surjective :
    Function.Surjective
      (MulSemiringAction.toAlgEquiv (G := ConjAct (GeneralLinearGroup K V)) K (End K V)) := by
  intro f
  have ⟨T, hT⟩ := f.eq_linearEquivConjAlgEquiv
  exact ⟨.ofLinearEquiv T, hT.symm⟩
