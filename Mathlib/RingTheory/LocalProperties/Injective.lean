/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!

# Being injective is a local property

# Main Results

* `Module.injective_of_isLocalizedModule` : For module `M` over Noetherian ring `R`,
  being injective is preserved under localization.

* `Module.injective_of_localization_maximal` : For module `M` over Noetherian ring `R`,
  being injective can be checked at localization at maximal ideals.

-/

universe u v

@[expose] public section

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (S : Submonoid R)

section

universe u' v'

set_option backward.isDefEq.respectTransparency false in
open IsLocalizedModule in
theorem Module.injective_of_isLocalizedModule [Small.{v} R] [IsNoetherianRing R] {Rₛ : Type u'}
    [Small.{v'} Rₛ] [CommRing Rₛ] [Algebra R Rₛ] {Mₛ : Type v'} [AddCommGroup Mₛ] [Module R Mₛ]
    [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ]
    [IsLocalizedModule S f] [Module.Injective R M] : Module.Injective Rₛ Mₛ := by
  have MB : Baer R M := Baer.of_injective ‹_›
  simp only [← Baer.iff_injective, Module.Baer.iff_surjective] at MB ⊢
  intro Iₛ g
  obtain ⟨I, rfl⟩ : ∃ I, .localized' Rₛ S (Algebra.linearMap R Rₛ) I = Iₛ :=
    ⟨Iₛ.comap (algebraMap R Rₛ), by simp [Ideal.localized'_eq_map, IsLocalization.map_comap S]⟩
  have : FinitePresentation R I := finitePresentation_of_finite R I
  obtain ⟨⟨g', a⟩, e : a.1 • g = _⟩ := surj S (mapExtendScalars S (I.toLocalized' _ _ _) f Rₛ) g
  obtain ⟨g', rfl⟩ := MB I g'
  refine ⟨IsLocalization.mk' Rₛ 1 a • mapExtendScalars S (Algebra.linearMap _ _) f _ g', ?_⟩
  apply ((Module.End.isUnit_iff _).mp ((IsLocalization.map_units Rₛ a).map
    (algebraMap _ (Module.End Rₛ _)))).1
  simp_rw [algebraMap_end_apply, map_smul, ← mul_smul, algebraMap_smul, IsLocalization.mk'_spec', e]
  apply LinearMap.restrictScalars_injective R
  refine IsLocalizedModule.linearMap_ext S (I.toLocalized' Rₛ S (Algebra.linearMap R Rₛ)) f ?_
  ext
  simp [-Algebra.linearMap_apply]

end

set_option backward.isDefEq.respectTransparency false in
theorem Module.injective_of_localization_maximal [Small.{v} R] [IsNoetherianRing R]
    (H : ∀ (I : Ideal R) (_ : I.IsMaximal),
      Module.Injective (Localization.AtPrime I) (LocalizedModule I.primeCompl M)) :
    Module.Injective R M := by
  rw [← Baer.iff_injective, Baer.iff_surjective]
  intro I
  let _ : FinitePresentation R I := finitePresentation_of_finite R I
  apply surjective_of_localized_maximal _ (fun m _ ↦ ?_)
  let Rₘ := Localization.AtPrime m
  let Mₘ := LocalizedModule m.primeCompl M
  let f := LocalizedModule.mkLinearMap m.primeCompl M
  let h : R →ₗ[R] Rₘ := Algebra.linearMap R Rₘ
  let Iₘ : Ideal Rₘ := Submodule.localized' Rₘ m.primeCompl h I
  let g : I →ₗ[R] Iₘ := I.toLocalized' Rₘ m.primeCompl h
  let gM := IsLocalizedModule.mapExtendScalars m.primeCompl g f Rₘ
  let hM := IsLocalizedModule.mapExtendScalars m.primeCompl h f Rₘ
  have eq'' : Iₘ.subtype.restrictScalars R = IsLocalizedModule.map m.primeCompl g h I.subtype :=
    IsLocalizedModule.ext m.primeCompl g (IsLocalizedModule.map_units h) (by ext; simp [g, h, Iₘ])
  have eq' : (Iₘ.subtype.lcomp Rₘ Mₘ).restrictScalars R =
    IsLocalizedModule.map m.primeCompl hM gM (I.subtype.lcomp R M) :=
    IsLocalizedModule.ext m.primeCompl hM (IsLocalizedModule.map_units gM) <| LinearMap.ext
      fun l ↦ LinearMap.restrictScalars_injective R (IsLocalizedModule.ext m.primeCompl g
        (IsLocalizedModule.map_units f) (by ext; simp +zetaDelta [-Algebra.linearMap_apply]))
  have eq : Iₘ.subtype.lcomp Rₘ Mₘ = IsLocalizedModule.mapExtendScalars m.primeCompl hM gM Rₘ
    (I.subtype.lcomp R M) := by
    simp [IsLocalizedModule.mapExtendScalars, ← eq']
  have MB : Baer Rₘ Mₘ := Baer.of_injective (H m ‹_›)
  have surj : Function.Surjective (LinearMap.lcomp Rₘ Mₘ (Submodule.subtype Iₘ)) :=
    Baer.iff_surjective.mp MB Iₘ
  rw [eq] at surj
  rw [← LinearMap.coe_restrictScalars (R := R),
    LocalizedModule.restrictScalars_map_eq m.primeCompl hM gM]
  simpa using surj

section

universe u' v'

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type u')
  [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Small.{v'} (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type v')
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [inst : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

attribute [local instance] RingHomInvPair.of_ringEquiv in
include f in
/--
A variant of `Module.injective_of_localization_maximal` that accepts `IsLocalizedModule`.
-/
theorem Module.injective_of_localization_maximal' [Small.{v} R] [IsNoetherianRing R]
    (H : ∀ (I : Ideal R) (_ : I.IsMaximal), Module.Injective (Rₚ I) (Mₚ I)) :
    Module.Injective R M := by
  apply Module.injective_of_localization_maximal
  intro P hP
  refine Module.Injective.of_ringEquiv (M := Mₚ P)
    (IsLocalization.algEquiv P.primeCompl (Rₚ P) (Localization.AtPrime P)).toRingEquiv
    { __ := IsLocalizedModule.linearEquiv P.primeCompl (f P)
        (LocalizedModule.mkLinearMap P.primeCompl M)
      map_smul' := ?_ }
  · intro r m
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl r
    apply ((Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap P.primeCompl M) s)).1
    dsimp
    simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul,
      IsLocalization.map_id_mk']

end
