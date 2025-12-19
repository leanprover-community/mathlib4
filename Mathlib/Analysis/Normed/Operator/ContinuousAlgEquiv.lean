/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Algebra.Equiv

/-!
# Continuous algebra equivalences between continuous endomorphisms are inner

This file shows that continuous algebra equivalences between continuous endomorphisms are inner.
See `Mathlib/LinearAlgebra/GeneralLinearGroup/AlgEquiv.lean` for the non-continuous version.
The proof is essentially the same as the non-continuous version.
-/

open ContinuousLinearMap

/-- This is the continuous version of `AlgEquiv.eq_linearEquivConjAlgEquiv`. -/
public theorem ContinuousAlgEquiv.coe_eq_continuousLinearEquiv_conjugate {𝕜 V W : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] [SeparatingDual 𝕜 V] [SeparatingDual 𝕜 W]
    [CompleteSpace V] [CompleteSpace W] (f : (V →L[𝕜] V) ≃A[𝕜] (W →L[𝕜] W)) :
    ∃ U : V ≃L[𝕜] W, ⇑f = fun x ↦ U ∘L x ∘L U.symm := by
  by_cases! hV : Subsingleton V
  · by_cases! hV : Subsingleton W
    · exact ⟨{ toLinearEquiv := 0 }, Subsingleton.allEq _ _⟩
    simpa using congr(f $(Subsingleton.allEq 0 1))
  simp_rw [funext_iff, ← comp_assoc, ContinuousLinearEquiv.eq_comp_toContinuousLinearMap_symm]
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  obtain ⟨v, huv⟩ := SeparatingDual.exists_ne_zero (R := 𝕜) hu
  obtain ⟨z, hz⟩ : ∃ z : W, ¬ f (smulRight v u) z = (0 : W →L[𝕜] W) z := by
    rw [← not_forall, ← ContinuousLinearMap.ext_iff, EmbeddingLike.map_eq_zero_iff,
      ContinuousLinearMap.ext_iff]
    exact not_forall.mpr ⟨u, huv.isUnit.smul_eq_zero.not.mpr hu⟩
  set T := apply' _ (.id 𝕜) z ∘L f.toContinuousAlgHom.toContinuousLinearMap ∘L smulRightL 𝕜 _ _ v
  have hT x : T x = f (smulRight v x) z := rfl
  have this A x : T (A x) = f A (T x) := by
    simp only [hT, ← mul_apply, ← map_mul]
    congr; ext; simp
  have surj : Function.Surjective T := fun w ↦ by
    obtain ⟨d, hd⟩ := SeparatingDual.exists_eq_one (R := 𝕜) hz
    exact ⟨f.symm (smulRight d w) u, by simp [T, this, hd]⟩
  have inj : Function.Injective T := fun x y hxy ↦ by
    have h_smul : smulRight v x = smulRight v y := by
      apply f.injective <| ContinuousLinearMap.ext fun z ↦ ?_
      obtain ⟨w, rfl⟩ := surj z
      simp [← this, hxy]
    simpa [huv.isUnit.smul_left_cancel] using congr((fun f ↦ f u) $h_smul)
  exact ⟨.ofBijective T ((LinearMapClass.ker_eq_bot _).mpr inj)
    (LinearMap.range_eq_top_of_surjective T surj), fun A ↦ (ContinuousLinearMap.ext <| this A).symm⟩
