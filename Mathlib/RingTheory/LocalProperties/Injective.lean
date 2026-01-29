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

lemma Module.Baer.iff_surjective : Module.Baer R M ↔
    ∀ (I : Ideal R), Function.Surjective (LinearMap.lcomp R M I.subtype) := by
  refine ⟨fun h I g ↦ ?_, fun h I g ↦ ?_⟩
  · rcases h I g with ⟨g', hg'⟩
    use g'
    ext x
    simp [hg']
  · rcases h I g with ⟨g', hg'⟩
    use g'
    intro x hx
    simp [← hg']

section

universe u' v'

theorem Module.injective_of_isLocalizedModule [Small.{v} R] [IsNoetherianRing R] {Rₛ : Type u'}
    [Small.{v'} Rₛ] [CommRing Rₛ] [Algebra R Rₛ] {Mₛ : Type v'} [AddCommGroup Mₛ] [Module R Mₛ]
    [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ]
    [IsLocalizedModule S f] [Module.Injective R M] : Module.Injective Rₛ Mₛ := by
  have MB : Baer R M := Baer.of_injective ‹_›
  rw [← Baer.iff_injective, Baer.iff_surjective]
  intro Iₛ
  let I := Iₛ.comap (algebraMap R Rₛ)
  let _ : FinitePresentation R I := finitePresentation_of_finite R I
  let h : R →ₗ[R] Rₛ := Algebra.linearMap R Rₛ
  let _ : IsLocalizedModule S h := inferInstance
  have eqloc : Submodule.localized' Rₛ S h I = Iₛ := by
    simp [h, Ideal.localized'_eq_map, I, IsLocalization.map_comap S]
  let g : I →ₗ[R] Iₛ :=
    ((LinearEquiv.ofEq _ _ eqloc).restrictScalars R).toLinearMap.comp (I.toLocalized' Rₛ S h)
  let _ : IsLocalizedModule S g :=
    IsLocalizedModule.of_linearEquiv S
    (I.toLocalized' Rₛ S h) ((LinearEquiv.ofEq _ _ eqloc).restrictScalars R)
  let gM := IsLocalizedModule.mapExtendScalars S g f Rₛ
  let _ : IsLocalizedModule S gM := FinitePresentation.isLocalizedModule_mapExtendScalars S g f Rₛ
  let hM := IsLocalizedModule.mapExtendScalars S h f Rₛ
  let _ : IsLocalizedModule S hM := FinitePresentation.isLocalizedModule_mapExtendScalars S h f Rₛ
  have eq'' : Iₛ.subtype.restrictScalars R = ((IsLocalizedModule.map S g h) I.subtype) := by
    simp only [IsLocalizedModule.map, LinearMap.coe_mk, AddHom.coe_mk]
    symm
    apply IsLocalizedModule.lift_unique _ _ _ _
    ext x
    simp [g, h]
  have eq' : Iₛ.subtype.lcomp Rₛ Mₛ = IsLocalizedModule.map S hM gM (I.subtype.lcomp R M) := by
    simp only [IsLocalizedModule.map, LinearMap.coe_mk, AddHom.coe_mk]
    symm
    apply (IsLocalizedModule.lift_unique _ _ _ _)
    ext x y
    simp only [hM, gM, IsLocalizedModule.mapExtendScalars, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.restrictScalars_apply, LinearMap.extendScalarsOfIsLocalizationEquiv_apply,
      LinearMap.lcomp_apply', Submodule.coe_subtype, LinearMap.extendScalarsOfIsLocalization_apply',
      IsLocalizedModule.map_comp' S g h f]
    congr 1
    simp [← eq'']
  have eq : (LinearMap.lcomp Rₛ Mₛ (Submodule.subtype Iₛ)) =
    IsLocalizedModule.mapExtendScalars S hM gM Rₛ (LinearMap.lcomp R M (Submodule.subtype I)) := by
    simp [IsLocalizedModule.mapExtendScalars, ← eq']
  rw [eq]
  exact IsLocalizedModule.map_surjective S hM gM _ (Baer.iff_surjective.mp MB I)

end

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
  let _ : IsLocalizedModule m.primeCompl h := inferInstance
  let Iₘ : Ideal Rₘ := Submodule.localized' Rₘ m.primeCompl h I
  let g : I →ₗ[R] Iₘ := (I.toLocalized' Rₘ m.primeCompl h)
  let _ : IsLocalizedModule m.primeCompl g := inferInstance
  let gM := IsLocalizedModule.mapExtendScalars m.primeCompl g f Rₘ
  let _ : IsLocalizedModule m.primeCompl gM :=
    FinitePresentation.isLocalizedModule_mapExtendScalars m.primeCompl g f Rₘ
  let hM := IsLocalizedModule.mapExtendScalars m.primeCompl h f Rₘ
  let _ : IsLocalizedModule m.primeCompl hM :=
    FinitePresentation.isLocalizedModule_mapExtendScalars m.primeCompl h f Rₘ
  have eq'' : Iₘ.subtype.restrictScalars R =
    ((IsLocalizedModule.map m.primeCompl g h) I.subtype) := by
    simp only [IsLocalizedModule.map, LinearMap.coe_mk, AddHom.coe_mk]
    symm
    apply (IsLocalizedModule.lift_unique _ _ _ _)
    ext x
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Submodule.coe_subtype,
      Function.comp_apply, Algebra.linearMap_apply, g, h]
    rw [Submodule.toLocalized'_apply_coe, Algebra.linearMap_apply]
  have eq' : (Iₘ.subtype.lcomp Rₘ Mₘ).restrictScalars R =
    IsLocalizedModule.map m.primeCompl hM gM (I.subtype.lcomp R M) := by
    simp only [IsLocalizedModule.map, LinearMap.coe_mk, AddHom.coe_mk]
    symm
    apply (IsLocalizedModule.lift_unique _ _ _ _)
    ext x y
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [LinearMap.restrictScalars_apply, LinearMap.lcomp_apply', LinearMap.comp_apply,
      LinearMap.lcomp_apply']
    simp only [IsLocalizedModule.mapExtendScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.restrictScalars_apply,
      LinearMap.extendScalarsOfIsLocalizationEquiv_apply, Submodule.subtype_apply,
      LinearMap.extendScalarsOfIsLocalization_apply', hM, gM]
    rw [IsLocalizedModule.map_comp' m.primeCompl g h f, LinearMap.comp_apply]
    change ((IsLocalizedModule.map m.primeCompl h f) x) y.1 = _
    congr 1
    simp [← eq'']
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

namespace Module

universe u' v'

attribute [local instance] RingHomInvPair.of_ringEquiv in
theorem Injective.of_ringEquiv {R : Type u} [Ring R] [Small.{v} R] {S : Type u'} [Ring S]
    {M : Type v} {N : Type v'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e₁ : R ≃+* S) (e₂ : M ≃ₛₗ[RingHomClass.toRingHom e₁] N)
    [inj : Injective R M] : Injective S N := by
  apply Baer.injective (fun I g ↦ ?_)
  let I' := I.comap e₁
  have {x : S} (h : x ∈ I) : e₁.symm x ∈ I' := by
    rw [← Ideal.mem_comap, Ideal.comap_symm]
    simpa [I', Ideal.map_comap_eq_self_of_equiv e₁ I] using h
  let e : I' ≃ₛₗ[RingHomClass.toRingHom e₁] I := {
    toFun x := ⟨e₁ x.1, x.2⟩
    map_add' x y := SetCoe.ext (by simp)
    map_smul' r x := SetCoe.ext (by simp)
    invFun x := ⟨e₁.symm x.1, this x.2⟩
    left_inv := by simp [Function.LeftInverse]
    right_inv := by simp [Function.RightInverse, Function.LeftInverse] }
  let f : I' →ₗ[R] M := e₂.symm.toLinearMap.comp (g.comp e.toLinearMap)
  have MB : Baer R M := Baer.of_injective ‹_›
  rcases MB I' f with ⟨f', hf'⟩
  use e₂.toLinearMap.comp (f'.comp e₁.toSemilinearEquiv.symm.toLinearMap)
  intro x hx
  change e₂ (f' (e₁.symm x)) = g ⟨x, hx⟩
  rw [hf' _ (this hx)]
  simp [f, e]

end Module

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
