/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib

/-!

# QC

-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{u}} (M : X.Modules)

namespace AlgebraicGeometry.Scheme.Modules

instance (priority := 100) [M.IsFree] : M.IsLocallyFree := SheafOfModules.IsFree.isLocallyFree M

lemma isQuasicoherent_restrict_iff {U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    (M.restrict f).IsQuasicoherent ↔ (M.over f.opensRange).IsQuasicoherent := sorry

variable (𝓤 : OpenCover.{u} X)

lemma _root_.AlgebraicGeometry.Scheme.OpenCover.coversTop : (Opens.grothendieckTopology X).CoversTop
    (fun i : 𝓤.I₀ => (𝓤.f i).opensRange) := by
  intro W x hx
  have hx' : x ∈ (⊤ : X.Opens) := trivial
  rw [← 𝓤.iSup_opensRange, TopologicalSpace.Opens.mem_iSup] at hx'
  obtain ⟨i, hi⟩ := hx'
  refine ⟨(𝓤.f i).opensRange ⊓ W, homOfLE inf_le_right, ?_, ⟨hi, hx⟩⟩
  rw [Sieve.mem_ofObjects_iff]
  exact ⟨i, ⟨homOfLE inf_le_left⟩⟩

theorem isQuasiCoherent_of_open_cover
    (h : ∀ i, (M.restrict (𝓤.f i)).IsQuasicoherent) : M.IsQuasicoherent :=
  have _ i : (M.over (𝓤.f i).opensRange).IsQuasicoherent := by
    rw [← isQuasicoherent_restrict_iff]
    exact h i
  SheafOfModules.IsQuasicoherent.of_coversTop M (fun i : 𝓤.I₀ => (𝓤.f i).opensRange) 𝓤.coversTop

def LocallyFreeLocusSet : Set X := {x | ∃ (U : Scheme.{u}) (f : U ⟶ X)
    (_ : IsOpenImmersion f), x ∈ f.opensRange ∧ (M.restrict f).IsLocallyFree}

lemma locallyFreeLocusSet_isOpen : IsOpen (LocallyFreeLocusSet M) := by
  rw [LocallyFreeLocusSet, isOpen_iff_forall_mem_open]
  intro x ⟨U, f, hf, hxU, hfree⟩
  exact ⟨f.opensRange, fun y hy => ⟨U, f, hf, hy, hfree⟩, f.opensRange.2, hxU⟩

def LocallyFreeLocus : X.Opens := ⟨LocallyFreeLocusSet M, locallyFreeLocusSet_isOpen M⟩

@[simp]
lemma locallyFreeLocus_def (x : X) :
    x ∈ M.LocallyFreeLocus ↔ ∃ (U : Scheme.{u}) (f : U ⟶ X)
      (_ : IsOpenImmersion f), x ∈ f.opensRange ∧ (M.restrict f).IsLocallyFree := by
  simp [LocallyFreeLocus, LocallyFreeLocusSet]

abbrev restrictRestrictCompIso {U Y : Scheme.{u}} (f : U ⟶ Y) [IsOpenImmersion f]
    (g : Y ⟶ X) [IsOpenImmersion g] : M.restrict (f ≫ g) ≅ (M.restrict g).restrict f :=
  (restrictFunctorComp f g).app M

instance restrict_isLocallyFree {U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] [M.IsLocallyFree] :
    (M.restrict f).IsLocallyFree := sorry

lemma locallyFreeLocus_restrict {U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    f ⁻¹ᵁ (LocallyFreeLocus M) = LocallyFreeLocus (M.restrict f) := by
  ext x
  constructor
  · intro h
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      locallyFreeLocus_def] at ⊢ h
    obtain ⟨V, ⟨g, ⟨_, ⟨hx₁, hx₂⟩⟩⟩⟩ := h
    use Limits.pullback f g, Limits.pullback.fst f g, inferInstance
    constructor
    · rwa [Scheme.Hom.opensRange_pullbackFst]
    sorry
  sorry

lemma locallyFreeLocus_eq_top_iff_isLocallyFree :
    LocallyFreeLocus M = ⊤ ↔ M.IsLocallyFree := sorry

lemma isLocallyFree_restrict_iff {U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    (M.restrict f).IsLocallyFree ↔ f.opensRange ≤ LocallyFreeLocus M := by
  rw [← locallyFreeLocus_eq_top_iff_isLocallyFree, ← locallyFreeLocus_restrict]
  sorry

section

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

-- REMOVE
-- REMOVE
set_option backward.isDefEq.respectTransparency false

lemma free_iff_isFree : Module.Free R M ↔ (tilde M).IsFree := by
  constructor
  · intro
    rw [SheafOfModules.IsFree.iso_free.{u}]
    exact ⟨_, ⟨(tilde.functor R).mapIso (Module.Free.chooseBasis R M).repr.toModuleIso ≪≫
      tildeFinsupp _⟩⟩
  intro h
  rw [SheafOfModules.IsFree.iso_free.{u}] at h
  obtain ⟨I, ⟨φ⟩⟩ := h
  let ψ := φ ≪≫ (tildeFinsupp (R := R) I).symm
  exact Module.Free.of_equiv (((tilde.functor R).preimageIso ψ).toLinearEquiv.symm)

instance [Module.Free R M] : (tilde M).IsFree := (free_iff_isFree M).mp inferInstance
variable (r : R)

def NatIsoTildeFunctorRestrictFunctor : (tilde.functor R) ⋙
    (restrictFunctor (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))) ≅
    ModuleCat.localizedModuleFunctor (.powers r) ⋙
    (tilde.functor (CommRingCat.of (Localization (.powers r)))) := sorry

abbrev fromLocalizationAway : Spec (CommRingCat.of (Localization.Away r)) ⟶ Spec R :=
  (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))

@[simp]
theorem fromLocalizationAway_opensRange :
    (fromLocalizationAway r).opensRange = PrimeSpectrum.basicOpen r :=
  TopologicalSpace.Opens.ext (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r)

lemma freeLocus_le_locallyFreeLocusSet [Module.FinitePresentation R M] :
    Module.freeLocus R M ≤ LocallyFreeLocusSet (tilde M) := by
  intro p h
  rw [Module.mem_freeLocus] at h
  obtain ⟨r, ⟨hr₁, ⟨hr₂, _⟩⟩⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (p.asIdeal.primeCompl)
    (LocalizedModule.mkLinearMap (p.asIdeal.primeCompl) M) (Localization.AtPrime p.asIdeal)
  let Rᵣ : CommRingCat.{u} := CommRingCat.of (Localization.Away r)
  let Mᵣ : ModuleCat.{u} Rᵣ := ModuleCat.of Rᵣ (M.localizedModule (.powers r))
  use Spec Rᵣ, fromLocalizationAway r, inferInstance
  refine ⟨by rw [fromLocalizationAway_opensRange, PrimeSpectrum.mem_basicOpen]; exact hr₁, ?_⟩
  let φ : (tilde M).restrict _ ≅ tilde Mᵣ := (NatIsoTildeFunctorRestrictFunctor r).app M
  let ψ : Mᵣ ≃ₗ[Rᵣ] (LocalizedModule (.powers r) M) :=
    Shrink.linearEquiv (Localization.Away r) (LocalizedModule (.powers r) M)
  have := Module.Free.of_equiv ψ.symm
  refine ObjectProperty.prop_of_iso SheafOfModules.IsLocallyFree.{u} φ.symm ?_
  infer_instance

lemma locallyFreeLocusSet_le_freeLocus : LocallyFreeLocusSet (tilde M) ≤ Module.freeLocus R M := by
  intro p h
  sorry

theorem locallyFreeLocusSet_eq_freeLocus [Module.FinitePresentation R M] :
    LocallyFreeLocusSet (tilde M) = Module.freeLocus R M :=
  le_antisymm (locallyFreeLocusSet_le_freeLocus M) (freeLocus_le_locallyFreeLocusSet M)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance [Module.Flat R M] [Module.FinitePresentation R M] : (tilde M).IsLocallyFree := by
  rw [← locallyFreeLocus_eq_top_iff_isLocallyFree]
  ext1
  dsimp [LocallyFreeLocus]
  rw [locallyFreeLocusSet_eq_freeLocus, Module.freeLocus_eq_univ]

end

end AlgebraicGeometry.Scheme.Modules
