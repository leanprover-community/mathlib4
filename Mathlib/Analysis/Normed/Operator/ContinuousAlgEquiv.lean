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

# TODO:
- when `V = W`, we can state that the group homomorphism
  `(V →L[𝕜] V)ˣ →* ((V →L[𝕜] V) ≃A[𝕜] (V →L[𝕜] V))` is surjective,
  see `Module.End.mulSemiringActionToAlgEquiv_conjAct_surjective` for the non-continuous
  version of this.
-/

open ContinuousLinearMap ContinuousLinearEquiv

/-- This is the continuous version of `AlgEquiv.eq_linearEquivConjAlgEquiv`. -/
public theorem ContinuousAlgEquiv.eq_continuousLinearEquivConjContinuousAlgEquiv {𝕜 V W : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] [SeparatingDual 𝕜 V] [SeparatingDual 𝕜 W]
    (f : (V →L[𝕜] V) ≃A[𝕜] (W →L[𝕜] W)) :
    ∃ U : V ≃L[𝕜] W, f = U.conjContinuousAlgEquiv := by
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
    exact not_forall.mpr ⟨u, (by grind : v u ≠ 0).isUnit.smul_eq_zero.not.mpr hu⟩
  obtain ⟨d, hd⟩ := SeparatingDual.exists_eq_one (R := 𝕜) hz
  set T := apply' _ (.id 𝕜) z ∘L f.toContinuousAlgHom.toContinuousLinearMap ∘L smulRightL 𝕜 _ _ v
  set T' := apply' _ (.id 𝕜) u ∘L f.symm.toContinuousAlgHom.toContinuousLinearMap ∘L
    smulRightL 𝕜 _ _ d
  have hT x : T x = f (smulRight v x) z := rfl
  have hT' x : T' x = f.symm (smulRight d x) u := rfl
  have this A x : T (A x) = f A (T x) := by
    simp only [hT, ← mul_apply, ← map_mul]
    congr; ext; simp
  have this' A x : T' (A x) = f.symm A (T' x) := by
    simp only [hT', ← mul_apply, ← map_mul]
    congr; ext; simp
  have hTT' : T ∘L T' = .id _ _ := by ext; simp [T', this, hT, hd]
  have surj : Function.Surjective T := fun w ↦
    have ⟨d, hd⟩ := SeparatingDual.exists_eq_one (R := 𝕜) hz
    ⟨f.symm (smulRight d w) u, by simp [T, this, hd]⟩
  have inj : Function.Injective T := fun x y hxy ↦ by
    have h_smul : smulRight v x = smulRight v y := by
      apply f.injective <| ContinuousLinearMap.ext fun z ↦ ?_
      obtain ⟨w, rfl⟩ := surj z
      simp [← this, hxy]
    simpa [huv.isUnit.smul_left_cancel] using congr((fun f ↦ f u) $h_smul)
  let Tₗ : V ≃ₗ[𝕜] W := .ofBijective T.toLinearMap ⟨inj, surj⟩
  have h_T'_eq_symm : T'.toLinearMap = Tₗ.symm := by
    ext x
    apply Tₗ.injective
    simpa using congr($hTT' x)
  let TL : V ≃L[𝕜] W :=
    { __ := Tₗ
      continuous_toFun := T.continuous
      continuous_invFun := by
        change Continuous Tₗ.symm.toLinearMap
        exact h_T'_eq_symm ▸ T'.continuous }
  exact ⟨TL, fun A ↦ (ContinuousLinearMap.ext <| this A).symm⟩
