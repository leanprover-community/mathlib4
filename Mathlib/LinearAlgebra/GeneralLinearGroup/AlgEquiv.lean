/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Algebra automorphisms in `End K V` are inner

This file shows that given any algebra equivalence `f : End K V ≃ₐ[K] End K V`,
there exists a linear equivalence `T : V ≃ₗ[K] V` such that `f x = T ∘ₗ x ∘ₗ T.symm`.
In other words, the map `MulSemiringAction.toAlgEquiv` from `GeneralLinearGroup K V` to
`End K V ≃ₐ[K] End K V` is surjective.
-/

open Module LinearMap LinearEquiv

variable {K V : Type*} [Semifield K] [AddCommMonoid V] [Module K V] [Projective K V]

/-- Given an algebra automorphism `f` in `End K V`, there exists a linear isomorphism `T`
such that `f` is given by `x ↦ T ∘ₗ x ∘ₗ T.symm`. -/
public theorem AlgEquiv.eq_linearEquivConjAlgEquiv (f : End K V ≃ₐ[K] End K V) :
    ∃ T : V ≃ₗ[K] V, f = T.conjAlgEquiv K := by
  nontriviality V
  simp_rw [AlgEquiv.ext_iff, conjAlgEquiv_apply, ← comp_assoc, eq_comp_toLinearMap_symm]
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  obtain ⟨v, huv⟩ := Projective.exists_dual_ne_zero K hu
  obtain ⟨z, hz⟩ : ∃ z : V, ¬ f (smulRight v u) z = (0 : End K V) z := by
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

/-- Alternate statement of `eq_linearEquivAlgConj`. -/
public theorem Module.End.mulSemiringActionToAlgEquiv_conjAct_surjective :
    Function.Surjective
      (MulSemiringAction.toAlgEquiv (G := ConjAct (GeneralLinearGroup K V)) K (End K V)) := by
  intro f
  have ⟨T, hT⟩ := f.eq_linearEquivConjAlgEquiv
  exact ⟨.ofLinearEquiv T, hT.symm⟩
