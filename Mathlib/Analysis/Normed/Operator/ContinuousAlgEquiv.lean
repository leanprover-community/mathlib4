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
The proof follows the same idea as the non-continuous version.

# TODO:
- when `V = W`, we can state that the group homomorphism
  `(V →L[𝕜] V)ˣ →* ((V →L[𝕜] V) ≃A[𝕜] (V →L[𝕜] V))` is surjective,
  see `Module.End.mulSemiringActionToAlgEquiv_conjAct_surjective` for the non-continuous
  version of this.
-/

open ContinuousLinearMap ContinuousLinearEquiv

/-- This is the continuous version of `AlgEquiv.eq_linearEquivConjAlgEquiv`. -/
public theorem ContinuousAlgEquiv.eq_continuousLinearEquivConjContinuousAlgEquiv {𝕜 V W : Type*}
    [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup V] [SeminormedAddCommGroup W]
    [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] [SeparatingDual 𝕜 V] [SeparatingDual 𝕜 W]
    (f : (V →L[𝕜] V) ≃A[𝕜] (W →L[𝕜] W)) :
    ∃ U : V ≃L[𝕜] W, f = U.conjContinuousAlgEquiv := by
  /- The proof goes as follows:
    We want to show the existence of a continuous linear equivalence `U : V ≃L[𝕜] W` such that
    `f A (U x) = U (A x)` for all `A : V →L[𝕜] V` and `x : V`.
    Assume nontriviality of `V`, and let `(u : V) ≠ 0`. Let `v` be a strong dual on `V` such that
    `v u ≠ 0` (exists since it has a separating dual).
    Let `z : W` such that `f (smulRight v u) z ≠ 0`.
    Then we construct a bijective continuous linear map `T : V →L[𝕜] W`
    given by `x ↦ f (smulRight v x) z` and so satisfies `T (A x) = f A (T x)` for all
    `A : V →L[𝕜] V` and `x : V`. So it remains to show that this map has a continuous inverse.
    Let `d` be a strong dual on `W` such that `d ((f (smulRight v u)) z) = 1` (exists since it has
    a separating dual).
    We then construct a right-inverse continuous linear map `T' : W →L[𝕜] V` given by
    `x ↦ f.symm (smulRight d x) u`.
    And so it follows that `T` is also a continuous linear equivalence. -/
  by_cases! hV : Subsingleton V
  · by_cases! hV : Subsingleton W
    · exact ⟨{ toLinearEquiv := 0 }, ext <| Subsingleton.allEq _ _⟩
    simpa using congr(f $(Subsingleton.allEq 0 1))
  simp_rw [ContinuousAlgEquiv.ext_iff, funext_iff, conjContinuousAlgEquiv_apply, ← comp_assoc,
    eq_comp_toContinuousLinearMap_symm]
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  obtain ⟨v, huv⟩ := SeparatingDual.exists_ne_zero (R := 𝕜) hu
  obtain ⟨z, hz⟩ : ∃ z : W, ¬ f (smulRight v u) z = (0 : W →L[𝕜] W) z := by
    rw [← not_forall, ← ContinuousLinearMap.ext_iff, map_eq_zero_iff, ContinuousLinearMap.ext_iff]
    exact not_forall.mpr ⟨u, huv.isUnit.smul_eq_zero.not.mpr hu⟩
  set T := apply' _ (.id 𝕜) z ∘L f.toContinuousAlgHom.toContinuousLinearMap ∘L smulRightL 𝕜 _ _ v
  have hT x : T x = f (smulRight v x) z := rfl
  have this A x : T (A x) = f A (T x) := by
    simp only [hT, ← mul_apply, ← map_mul]
    congr; ext; simp
  have ⟨d, hd⟩ := SeparatingDual.exists_eq_one (R := 𝕜) hz
  have surj : Function.Surjective T := fun w ↦ ⟨f.symm (smulRight d w) u, by simp [T, this, hd]⟩
  have inj : Function.Injective T := fun x y hxy ↦ by
    have h_smul : smulRight v x = smulRight v y := by
      apply f.injective <| ContinuousLinearMap.ext fun z ↦ ?_
      obtain ⟨w, rfl⟩ := surj z
      simp [← this, hxy]
    simpa [huv.isUnit.smul_left_cancel] using congr((fun f ↦ f u) $h_smul)
  set Tₗ : V ≃ₗ[𝕜] W := .ofBijective T.toLinearMap ⟨inj, surj⟩
  set T' := apply' _ (.id 𝕜) u ∘L f.symm.toContinuousAlgHom.toContinuousLinearMap ∘L
    smulRightL 𝕜 _ _ d
  set TL : V ≃L[𝕜] W := { Tₗ with
    continuous_toFun := T.continuous
    continuous_invFun := by
      change Continuous Tₗ.symm.toLinearMap
      suffices T'.toLinearMap = Tₗ.symm from this ▸ T'.continuous
      simp [LinearMap.ext_iff, ← Tₗ.injective.eq_iff, T', this, hT, hd, Tₗ] }
  exact ⟨TL, fun A ↦ (ContinuousLinearMap.ext <| this A).symm⟩
