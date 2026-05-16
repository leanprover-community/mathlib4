/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-!
# `Module.Invertible` is a local property

In this file, we prove that `Module.Invertible` is a local property.

## Main results
* `Module.Invertible.of_isLocalized_maximal`: Let `M` be a finite `R`-module, then `M` is invertible
  if `Mₘ` is invertible for any maximal ideal `m` of `R`.
-/

public section

namespace Module

open scoped TensorProduct

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem FinitePresentation.of_finite_of_flat_of_rankAtStalk_constant [Module.Flat R M] (n : ℕ)
    (h : ∀ (p : Ideal R) [p.IsMaximal], rankAtStalk M ⟨p, inferInstance⟩ = n) :
    Module.FinitePresentation R M := by
  let s : Set R := {g | Module.Free (Localization.Away g) (LocalizedModule.Away g M)}
  have hs : Ideal.span s = ⊤ := by
    by_contra! hs
    obtain ⟨m, _, hsm⟩ := Ideal.exists_le_maximal _ hs
    obtain ⟨g, hgm, hfree⟩ :=
      Free.away_of_finite_of_flat_of_rankAtStalk_constant M m (fun p _ ↦ by simp [h p, h m])
    exact hgm (hsm (Submodule.mem_span_of_mem hfree))
  refine FinitePresentation.of_localizationSpan s hs (fun ⟨g, hg⟩ ↦ ?_)
  simp only [Set.mem_setOf_eq, s] at hg
  exact finitePresentation_of_projective (Localization.Away g) (LocalizedModule.Away g M)

open IsLocalizedModule IsLocalization

open scoped TensorProduct

theorem Invertible.of_isLocalized_maximal
    (Rₚ : ∀ (m : Ideal R) [m.IsMaximal], Type*)
    [∀ (m : Ideal R) [m.IsMaximal], CommRing (Rₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], Algebra R (Rₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], IsLocalization.AtPrime (Rₚ m) m]
    (Mₚ : ∀ (m : Ideal R) [m.IsMaximal], Type*)
    [∀ (m : Ideal R) [m.IsMaximal], AddCommGroup (Mₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], Module R (Mₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], Module (Rₚ m) (Mₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], IsScalarTower R (Rₚ m) (Mₚ m)]
    (f : ∀ (m : Ideal R) [m.IsMaximal], M →ₗ[R] Mₚ m)
    [∀ (m : Ideal R) [m.IsMaximal], IsLocalizedModule.AtPrime m (f m)]
    (h : ∀ (m : Ideal R) [m.IsMaximal], Module.Invertible (Rₚ m) (Mₚ m)) :
    Module.Invertible R M where
  bijective := by
    have : Flat R M := by
      refine flat_of_isLocalized_maximal R M Mₚ f (fun m _ ↦ ?_)
      have : Flat R (Rₚ m) := IsLocalization.flat (Rₚ m) m.primeCompl
      exact Flat.trans R (Rₚ m) (Mₚ m)
    have : Module.FinitePresentation R M := by
      refine Module.FinitePresentation.of_finite_of_flat_of_rankAtStalk_constant 1 (fun m _ ↦ ?_)
      have : IsLocalRing (Rₚ m) := IsLocalization.AtPrime.isLocalRing (Rₚ m) m
      have hfree : Module.Free (Rₚ m) (Mₚ m) := Module.free_of_flat_of_isLocalRing
      let e : LocalizedModule.AtPrime m M ≃ₗ[R] Localization.AtPrime m :=
        IsLocalizedModule.linearEquiv m.primeCompl (LocalizedModule.mkLinearMap _ M) (f m) ≪≫ₗ
          (Invertible.free_iff_linearEquiv.mp hfree).some.restrictScalars R ≪≫ₗ
            (algEquiv m.primeCompl (Localization.AtPrime m) (Rₚ m)).symm.toLinearEquiv
      exact (e.extendScalarsOfIsLocalization m.primeCompl (Localization.AtPrime m)).finrank_eq.trans
        (CommSemiring.finrank_self (Localization.AtPrime m))
    let ϕ (m : Ideal R) [m.IsMaximal] := TensorProduct.map
      (mapExtendScalars m.primeCompl (f m) (Algebra.linearMap R (Rₚ m)) (Rₚ m)) (f m)
    refine bijective_of_isLocalized_maximal _ ϕ Rₚ
      (fun m _ ↦ Algebra.linearMap R (Rₚ m)) (contractLeft R M) (fun m _ ↦ ?_)
    let ψ : Module.Dual (Rₚ m) (Mₚ m) ⊗[Rₚ m] Mₚ m ≃ₗ[R] Module.Dual (Rₚ m) (Mₚ m) ⊗[R] Mₚ m :=
      (moduleTensorEquiv m.primeCompl (Rₚ m) (Module.Dual (Rₚ m) (Mₚ m)) (Mₚ m)).restrictScalars R
    have hψ : (map m.primeCompl (ϕ m) (Algebra.linearMap R (Rₚ m))) (contractLeft R M) =
        (contractLeft (Rₚ m) (Mₚ m)).restrictScalars R ∘ₗ ψ.symm.toLinearMap := by
      apply IsLocalizedModule.ext m.primeCompl (ϕ m) (map_units (Algebra.linearMap R (Rₚ m)))
      ext α x
      simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
        TensorProduct.curry_apply, LinearMap.coe_comp, Function.comp_apply, map_apply]
      exact (IsLocalizedModule.map_apply m.primeCompl (f m) (Algebra.linearMap R (Rₚ m)) α x).symm
    simp [hψ, (h m).bijective.comp ψ.symm.bijective]

/-- Let `M` be a finite `R`-module, then `M` is invertible if `Mₘ` is invertible for any maximal
ideal `m` of `R`. -/
theorem Invertible.of_localized_maximal
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Invertible (Localization.AtPrime m) (LocalizedModule.AtPrime m M)) :
    Module.Invertible R M :=
  of_isLocalized_maximal (fun m _ ↦ Localization.AtPrime m) (fun m _ ↦ LocalizedModule.AtPrime m M)
    (fun m _ ↦ LocalizedModule.mkLinearMap m.primeCompl M) h

end Module
