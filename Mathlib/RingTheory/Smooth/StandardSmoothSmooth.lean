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

section Upstream

instance _root_.Localization.Away.finitePresentation {R : Type*} [CommRing R] (r : R) :
    Algebra.FinitePresentation R (Localization.Away r) :=
  IsLocalization.Away.finitePresentation r

instance _root_.Localization.essFiniteType {R : Type*} [CommRing R] (S : Submonoid R) :
    Algebra.EssFiniteType R (Localization S) :=
  Algebra.EssFiniteType.of_isLocalization _ S

lemma IsLocalizedModule.subsingleton_of_subsingleton {R M M' : Type*} [CommRing R]
    (S : Submonoid R)
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M')
    [IsLocalizedModule S f] [Subsingleton M] :
    Subsingleton M' := by
  sorry

end Upstream

universe u

namespace RingHom

def Smooth {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @Algebra.Smooth R _ S _ f.toAlgebra

end RingHom

namespace Module

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

lemma exists_of_bijective' [Module.Finite R M] [Module.Finite R N] (f : M →ₗ[R] N)
    (p : Ideal R) [p.IsPrime] {Rₚ Mₚ Nₚ : Type*}
    [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [AddCommGroup Mₚ] [AddCommGroup Nₚ] [Module R Mₚ] [Module R Nₚ]
    (fM : M →ₗ[R] Mₚ) (fN : N →ₗ[R] Nₚ)
    [IsLocalizedModule p.primeCompl fM]
    [IsLocalizedModule p.primeCompl fN]
    {Mₜ Nₜ : R → Type*}
    [∀ r, AddCommGroup (Mₜ r)] [∀ r, Module R (Mₜ r)]
    [∀ r, AddCommGroup (Nₜ r)] [∀ r, Module R (Nₜ r)]
    (fₜ : ∀ r, M →ₗ[R] Mₜ r) [∀ r, IsLocalizedModule (Submonoid.powers r) (fₜ r)]
    (gₜ : ∀ r, N →ₗ[R] Nₜ r) [∀ r, IsLocalizedModule (Submonoid.powers r) (gₜ r)]
    (hf : Function.Bijective (IsLocalizedModule.map p.primeCompl fM fN f)) :
    ∃ (g : R), g ∉ p ∧
      Function.Bijective (IsLocalizedModule.map (Submonoid.powers g) (fₜ g) (gₜ g) f) :=
  sorry

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

open KaehlerDifferential

lemma _root_.KaehlerDifferential.span_range_map_derivation_of_isLocalization
    (R : Type u) {S : Type u} (T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] (M : Submonoid S) [IsLocalization M T] :
    Submodule.span T (Set.range <| fun s ↦ map R R S T (D R S s)) = ⊤ := by
  convert span_eq_top_of_isLocalizedModule T M (map R R S T) (v := Set.range <| D R S)
    (span_range_derivation R S)
  rw [← Set.range_comp, Function.comp_def]

theorem exists_isStandardSmooth [Smooth R S] (p : Ideal S) [p.IsPrime] :
    ∃ (f : S), f ∉ p ∧ IsStandardSmooth.{u, u} R (Localization.Away f) := by
  have : FormallySmooth R (Localization.AtPrime p) := isSmoothAt_of_smooth R p
  have : Module.Projective (Localization.AtPrime p) (Ω[Localization.AtPrime p ⁄R]) :=
    inferInstance
  let v (s : S) : (Ω[Localization.AtPrime p⁄R]) :=
    map R R S (Localization.AtPrime p) (D R S s)
  have hv : Submodule.span (Localization.AtPrime p) (Set.range v) = ⊤ :=
    span_range_map_derivation_of_isLocalization R (Localization.AtPrime p) p.primeCompl
  have : Algebra.EssFiniteType R (Localization.AtPrime p) :=
    Algebra.EssFiniteType.comp R S (Localization.AtPrime p)
  have : Module.FinitePresentation (Localization.AtPrime p) (Ω[Localization.AtPrime p⁄R]) :=
    Module.finitePresentation_of_projective (Localization.AtPrime p) (Ω[Localization.AtPrime p⁄R])
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat v hv
  let e : (κ →₀ S) →ₗ[S] (Ω[S ⁄R]) :=
    Finsupp.basisSingleOne.constr S (fun i : κ ↦ D R S (a i))
  let l₁ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (Localization.AtPrime p))
  have : IsLocalizedModule p.primeCompl l₁ := inferInstance
  let l₂ : (Ω[S⁄R]) →ₗ[S] (Ω[Localization.AtPrime p⁄R]) := map R R S (Localization.AtPrime p)
  have : IsLocalizedModule p.primeCompl l₂ := inferInstance
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] (Ω[Localization.AtPrime p⁄R]) :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have : eₚ = b.repr.symm := by
    apply Finsupp.basisSingleOne.ext
    intro i
    have : Finsupp.basisSingleOne i = l₁ (Finsupp.basisSingleOne i) := by simp [l₁]
    simp only [this, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply,
      Basis.constr_basis, map_D, Basis.coe_repr_symm, eₚ, l₂, e]
    simp [l₁, hb, v]
  have heₚ : Function.Bijective eₚ := by
    rw [this]
    exact b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  let l₁ₜ (s : S) : (κ →₀ S) →ₗ[S] (κ →₀ Localization.Away s) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ (s : S) : (Ω[S⁄R]) →ₗ[S] (Ω[Localization.Away s⁄R]) :=
    map R R S (Localization.Away s)
  obtain ⟨g, hg, h⟩ := Module.exists_of_bijective' e p l₁ l₂ (Rₚ := Localization.AtPrime p)
    l₁ₜ l₂ₜ heₚ
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] (Ω[Localization.Away g⁄R]) :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) (l₁ₜ g) (l₂ₜ g) (Localization.Away g) e
  use g, hg
  have : Subsingleton (H1Cotangent R (Localization.Away g)) :=
    IsLocalizedModule.subsingleton_of_subsingleton (Submonoid.powers g)
      (Algebra.H1Cotangent.map R R S (Localization.Away g))
  have : FinitePresentation R (Localization.Away g) :=
    FinitePresentation.trans R S (Localization.Away g)
  refine isStandardSmooth_of (I := κ) (Basis.ofRepr (LinearEquiv.ofBijective eₜ' h).symm) ?_
  rintro - ⟨i, rfl⟩
  simp only [Basis.coe_ofRepr, LinearEquiv.symm_symm, LinearEquiv.ofBijective_apply,
    IsLocalizedModule.mapExtendScalars_apply_apply, Set.mem_range, eₜ']
  use algebraMap S (Localization.Away g) (a i)
  have : Finsupp.single i 1 = (l₁ₜ g) (Finsupp.basisSingleOne i) := by simp [l₁ₜ]
  rw [this]
  simp [-Finsupp.coe_basisSingleOne, l₂ₜ, e]

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
