/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.FreeKaehler
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Smooth and locally standard smooth
-/

suppress_compilation

universe u

namespace RingHom

def Smooth {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @Algebra.Smooth R _ S _ f.toAlgebra

end RingHom

namespace Module

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

lemma exists_of_bijective [Module.Finite R M] [Module.Finite R N] (f : M →ₗ[R] N)
    (p : Ideal R) [p.IsPrime] {Rₚ Mₚ Nₚ : Type*}
    [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [AddCommGroup Mₚ] [AddCommGroup Nₚ] [Module R Mₚ] [Module R Nₚ]
    (fM : M →ₗ[R] Mₚ) (fN : N →ₗ[R] Nₚ)
    [IsLocalizedModule p.primeCompl fM]
    [IsLocalizedModule p.primeCompl fN]
    (hf : Function.Bijective (IsLocalizedModule.map p.primeCompl fM fN f)) :
    ∃ (g : R), g ∉ p ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers g) f) :=
  sorry

end Module

namespace Algebra

variable {R S : Type u} [CommRing R] [CommRing S]

section

variable [Algebra R S]

variable (R) in
lemma isSmoothAt_of_smooth [Smooth R S] (p : Ideal S) [p.IsPrime] :
    IsSmoothAt R p := by
  have : smoothLocus R S = Set.univ := by
    rw [smoothLocus_eq_univ_iff]
    infer_instance
  show ⟨p, inferInstance⟩ ∈ smoothLocus R S
  rw [this]
  trivial

theorem exists_isStandardSmooth [Smooth R S] (p : Ideal S) [p.IsPrime] :
    ∃ (f : S), f ∉ p ∧ IsStandardSmooth R (Localization.Away f) := by
  have : FormallySmooth R (Localization.AtPrime p) := isSmoothAt_of_smooth R p
  have : Module.Projective (Localization.AtPrime p) (Ω[Localization.AtPrime p ⁄R]) :=
    inferInstance
  let v (s : S) : (Ω[Localization.AtPrime p ⁄R]) :=
    KaehlerDifferential.D _ _ (algebraMap _ _ s)
  have hv : Submodule.span (Localization.AtPrime p) (Set.range v) = ⊤ :=
    sorry
  have : Module.FinitePresentation (Localization.AtPrime p) (Ω[Localization.AtPrime p⁄R]) :=
    sorry
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat v hv
  let e : (κ →₀ S) →ₗ[S] (Ω[S ⁄R]) := sorry
  let a : (κ →₀ S) →ₗ[S] (κ →₀ Localization.AtPrime p) := sorry
  have : IsLocalizedModule p.primeCompl a := sorry
  let b : (Ω[S⁄R]) →ₗ[S] (Ω[Localization.AtPrime p⁄R]) := sorry
  have : IsLocalizedModule p.primeCompl b := sorry
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[S] (Ω[Localization.AtPrime p⁄R]) :=
    IsLocalizedModule.map p.primeCompl a b e
  have heₚ : Function.Bijective eₚ := sorry
  have : Finite κ := sorry
  obtain ⟨g, hg, h⟩ := Module.exists_of_bijective e p a b (Rₚ := Localization.AtPrime p) heₚ
  use g, hg
  have : Subsingleton (H1Cotangent R (Localization.Away g)) := sorry
  -- universe problem
  -- apply isStandardSmooth_of
  sorry

theorem exists_cover [Smooth R S] : ∃ (s : Set S) (hs : Ideal.span s = ⊤),
    ∀ x ∈ s, IsStandardSmooth.{0, 0} R (Localization.Away x) :=
  sorry

end

end Algebra

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem locally_isStandardSmooth_of_smooth (f : R →+* S)
    (hf : f.Smooth) : Locally IsStandardSmooth.{0, 0} f := by
  algebraize [f]
  have : Algebra.Smooth R S := hf
  obtain ⟨s, hs, h⟩ := Algebra.exists_cover (R := R) (S := S)
  use s, hs
  intro t ht
  suffices h : Algebra.IsStandardSmooth.{0, 0} R (Localization.Away t) by
    rw [RingHom.IsStandardSmooth]
    convert h
    ext
    rw [Algebra.smul_def]
    rfl
  convert h t ht

theorem smooth_iff_locally_isStandardSmooth (f : R →+* S) :
    Smooth f ↔ Locally IsStandardSmooth f :=
  sorry

end RingHom
