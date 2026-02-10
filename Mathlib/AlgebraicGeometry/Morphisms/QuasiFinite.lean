/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Quasi-finite morphisms

We say that a morphism `f : X ⟶ Y` is locally quasi finite if `Γ(Y, U) ⟶ Γ(X, V)` is
quasi-finite (in the mathlib sense) for every pair of affine opens that `f` maps one into the other.

This is equivalent to all the fibers `f⁻¹(x)` having an open cover of `κ(x)`-finite schemes.
Note that this does not require `f` to be quasi-compact nor locally of finite type.

We prove that this is stable under composition and base change, and is right cancellative.

## Main results
- `AlgebraicGeometry.LocallyQuasiFinite` : The class of locally quasi-finite morphisms.
- `AlgebraicGeometry.Scheme.Hom.isDiscrete_preimage_singleton`:
  Locally quasi-finite morphisms have discrete fibers.
- `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton`:
  Quasi-finite morphisms have finite fibers.
- `AlgebraicGeometry.locallyQuasiFinite_iff_isFinite_fiber`: If `f` is quasi-compact,
  then `f` is locally quasi-finite iff all the fibers `f⁻¹(x)` are `κ(x)`-finite.
- `AlgebraicGeometry.locallyQuasiFinite_iff_isDiscrete_preimage_singleton`:
  If `f` is locally of finite type, then `f` is locally quasi-finite iff `f` has discrete fibers.
- `AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton`:
  If `f` is of finite type, then `f` is locally quasi-finite iff `f` has finite fibers.
-/

@[expose] public section

open CategoryTheory hiding IsDiscrete
open Limits

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open Scheme

/--
We say that a morphism `f : X ⟶ Y` is locally quasi finite if `Γ(Y, U) ⟶ Γ(X, V)` is
quasi-finite (in the mathlib sense) for every pair of affine opens that `f` maps one into the other.

Note that this does not require `f` to be quasi-compact nor locally of finite type.

Being locally quasi-finite implies that `f` has discrete and finite fibers
(via `f.isDiscrete_preimage_singleton` and `f.finite_preimage_singleton`).
The converse holds under various scenarios:

- `locallyQuasiFinite_iff_isDiscrete_preimage_singleton`:
  If `f` is quasi-compact, this is equivalent to `f ⁻¹ {x}` being `κ(x)`-finite for all `x`.
- `locallyQuasiFinite_iff_isDiscrete_preimage_singleton`:
  If `f` is locally of finite type, this is equivalent to `f` having discrete fibers.
- `locallyQuasiFinite_iff_isDiscrete_preimage_singleton`:
  If `f` is locally of finite type, this is equivalent to `f` having finite fibers.
-/
@[mk_iff]
class LocallyQuasiFinite : Prop where
  quasiFinite_appLE :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.QuasiFinite

instance : HasRingHomProperty @LocallyQuasiFinite RingHom.QuasiFinite where
  isLocal_ringHomProperty := RingHom.QuasiFinite.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    simp [locallyQuasiFinite_iff, affineLocally_iff_affineOpens_le, affineOpens]

instance : MorphismProperty.IsStableUnderComposition @LocallyQuasiFinite :=
  HasRingHomProperty.stableUnderComposition RingHom.QuasiFinite.stableUnderComposition

instance {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyQuasiFinite f] [LocallyQuasiFinite g] : LocallyQuasiFinite (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹_› ‹_›

instance (priority := low) [IsFinite f] : LocallyQuasiFinite f := by
  rw [HasAffineProperty.eq_targetAffineLocally @IsFinite] at ‹IsFinite f›
  rw [HasRingHomProperty.eq_affineLocally @LocallyQuasiFinite]
  refine ((targetAffineLocally_affineAnd_eq_affineLocally
    RingHom.QuasiFinite.propertyIsLocal).le f ?_).2
  exact targetAffineLocally_affineAnd_le (fun hf ↦ .of_finite hf) f ‹_›

instance (priority := low) [IsImmersion f] : LocallyQuasiFinite f := by
  rw [← f.liftCoborder_ι]
  have := HasRingHomProperty.of_isOpenImmersion (P := @LocallyQuasiFinite)
    RingHom.QuasiFinite.holdsForLocalizationAway.containsIdentities (f := f.coborderRange.ι)
  infer_instance

theorem LocallyQuasiFinite.of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyQuasiFinite (f ≫ g)] : LocallyQuasiFinite f :=
  HasRingHomProperty.of_comp (fun _ _ ↦ RingHom.QuasiFinite.of_comp) ‹_›

instance : MorphismProperty.IsMultiplicative @LocallyQuasiFinite where
  id_mem _ := inferInstance

instance : MorphismProperty.IsStableUnderBaseChange @LocallyQuasiFinite :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.QuasiFinite.isStableUnderBaseChange

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyQuasiFinite g] :
    LocallyQuasiFinite (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyQuasiFinite f] :
    LocallyQuasiFinite (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (V : Y.Opens) [LocallyQuasiFinite f] : LocallyQuasiFinite (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (U : X.Opens) (V : Y.Opens) (e) [LocallyQuasiFinite f] :
    LocallyQuasiFinite (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

nonrec lemma IsLocallyArtinian.of_locallyQuasiFinite [LocallyQuasiFinite f]
    [IsLocallyArtinian Y] : IsLocallyArtinian X := by
  change id _ -- avoid typeclass synthesis from getting stuck on the wlog hypothesis.
  wlog hY : ∃ R, Y = Spec R
  · exact (isLocallyArtinian_iff_openCover (Y.affineCover.pullback₁ f)).mpr fun i ↦
      this (pullback.snd _ _) ⟨_, rfl⟩
  wlog hX : ∃ S, X = Spec S
  · exact (isLocallyArtinian_iff_openCover X.affineCover).mpr fun i ↦
      this (X.affineCover.f i ≫ f) hY ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [isLocallyArtinianScheme_Spec, HasRingHomProperty.Spec_iff, id_eq] at *
  algebraize [φ.hom]
  have : Module.Finite R S := .of_quasiFinite
  exact .of_finite R S

instance [LocallyQuasiFinite f] (y : Y) : IsLocallyArtinian (f.fiber y) :=
  .of_locallyQuasiFinite (pullback.snd _ _)

lemma Scheme.Hom.isDiscrete_preimage_singleton [LocallyQuasiFinite f] (y : Y) :
    IsDiscrete (f ⁻¹' {y}) := by
  simpa [Scheme.Hom.range_fiberι] using
    (isDiscrete_univ_iff.mpr inferInstance).image (f.fiberι y).isEmbedding

lemma Scheme.Hom.isDiscrete_preimage [LocallyQuasiFinite f] {s : Set Y} (hs : IsDiscrete s) :
    IsDiscrete (f ⁻¹' s) :=
  hs.preimage' f.continuous.continuousOn f.isDiscrete_preimage_singleton

instance [LocallyQuasiFinite f] [QuasiCompact f] (y : Y) : IsArtinianScheme (f.fiber y) where

lemma Scheme.Hom.finite_preimage_singleton [LocallyQuasiFinite f] [QuasiCompact f] (y : Y) :
    (f ⁻¹' {y}).Finite := by
  simpa [Scheme.Hom.range_fiberι] using Set.finite_univ.image (f.fiberι y)

@[deprecated (since := "2026-02-05")]
alias IsFinite.finite_preimage_singleton := Scheme.Hom.finite_preimage_singleton

lemma Scheme.Hom.finite_preimage [LocallyQuasiFinite f] [QuasiCompact f]
    {s : Set Y} (hs : s.Finite) : (f ⁻¹' s).Finite :=
  hs.preimage' fun _ _ ↦ f.finite_preimage_singleton _

lemma Scheme.Hom.tendsto_cofinite_cofinite [LocallyQuasiFinite f] [QuasiCompact f] :
    Filter.Tendsto f .cofinite .cofinite :=
  .cofinite_of_finite_preimage_singleton f.finite_preimage_singleton

nonrec lemma IsFinite.of_locallyQuasiFinite (f : X ⟶ Y) [LocallyQuasiFinite f]
    [QuasiCompact f] [IsLocallyArtinian Y] : IsFinite f := by
  change id _ -- avoid typeclass synthesis from getting stuck on the wlog hypothesis.
  wlog hY : ∃ R, Y = Spec R
  · exact (IsZariskiLocalAtTarget.iff_of_openCover Y.affineCover).mpr fun i ↦
      this (pullback.snd _ _) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have inst : IsArtinianScheme X :=
      { toIsLocallyArtinian := .of_locallyQuasiFinite f,
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mp
      (this _ ((Scheme.isoSpec X).inv ≫ f) ⟨_, rfl⟩)
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [isLocallyArtinianScheme_Spec, HasRingHomProperty.Spec_iff, id_eq,
    IsFinite.SpecMap_iff] at *
  algebraize [φ.hom]
  exact .of_quasiFinite

instance (f : X ⟶ Y) [LocallyQuasiFinite f] [QuasiCompact f] (x : Y) :
    IsFinite (f.fiberToSpecResidueField x) :=
  .of_locallyQuasiFinite (pullback.snd _ _)

nonrec lemma LocallyQuasiFinite.of_isFinite_fiberToSpecResidueField
    (hf : ∀ x, IsFinite (f.fiberToSpecResidueField x)) : LocallyQuasiFinite f := by
  change id _ -- avoid typeclass synthesis from getting stuck on the wlog hypothesis.
  wlog hY : ∃ R, Y = Spec R
  · refine (IsZariskiLocalAtTarget.iff_of_openCover Y.affineCover).mpr fun i ↦
      this (f := pullback.snd _ _) (fun x ↦ ?_) ⟨_, rfl⟩
    have (x : Y) : IsLocallyArtinian (f.fiber x) :=
      .of_locallyQuasiFinite (f.fiberToSpecResidueField x)
    refine (MorphismProperty.cancel_right_of_respectsIso @IsFinite _
      (Spec.map ((Y.affineCover.f i).residueFieldMap _))).mp ?_
    let g : (pullback.snd f (Y.affineCover.f i)).fiber x ⟶ f.fiber (Y.affineCover.f i x) :=
      pullback.map _ _ _ _ (pullback.fst _ _) (Spec.map ((Y.affineCover.f i).residueFieldMap _))
        (Y.affineCover.f i) (by simp [pullback.condition]) (by simp)
    have : IsClosedImmersion g := .of_isPreimmersion _ (isClosed_discrete _)
    convert (inferInstanceAs (IsFinite <| g ≫ f.fiberToSpecResidueField _)) using 1
    simp [g, Hom.fiberToSpecResidueField]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · refine (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i ↦
      this _ _ (fun x ↦ ?_) ⟨_, rfl⟩
    have (x : _) : IsLocallyArtinian (f.fiber x) :=
      .of_locallyQuasiFinite (f.fiberToSpecResidueField x)
    let g : (X.affineCover.f i ≫ f).fiber x ⟶ f.fiber x :=
      pullback.map _ _ _ _ (X.affineCover.f i) (𝟙 _) (𝟙 _) (by simp) (by simp)
    have : IsClosedImmersion g := .of_isPreimmersion _ (isClosed_discrete _)
    convert (inferInstanceAs (IsFinite <| g ≫ f.fiberToSpecResidueField _)) using 1
    simp [g, Hom.fiberToSpecResidueField]
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  simp only [HasRingHomProperty.Spec_iff, id_eq]
  refine ⟨fun P hP ↦ ?_⟩
  suffices IsFinite (Spec.map <| CommRingCat.ofHom <| algebraMap P.ResidueField (P.Fiber S)) by
    simpa [IsFinite.SpecMap_iff] using this
  obtain ⟨x, rfl⟩ : ∃ x : Spec R, P = x.asIdeal := ⟨⟨P, hP⟩, rfl⟩
  refine (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk ?_ ?_ ?_)).mp (hf x)
  · refine asIso (pullback.map _ _ _ _ (𝟙 _) (Spec.map (Spec.residueFieldIso _ x).inv) (𝟙 _)
      ?_ ?_) ≪≫ pullbackSymmetry _ _ ≪≫ pullbackSpecIso ..
    · simp; rfl
    · simp [← Spec.map_comp, fromSpecResidueField, Spec.fromSpecStalk_eq]
  · exact asIso (Spec.map (Spec.residueFieldIso _ x).inv)
  · simp [Hom.fiberToSpecResidueField]

lemma locallyQuasiFinite_iff_isFinite_fiber {f : X ⟶ Y} [QuasiCompact f] :
    LocallyQuasiFinite f ↔ ∀ x, IsFinite (f.fiberToSpecResidueField x) :=
  ⟨fun _ ↦ inferInstance, .of_isFinite_fiberToSpecResidueField f⟩

nonrec lemma locallyQuasiFinite_iff_isDiscrete_preimage_singleton
    {f : X ⟶ Y} [LocallyOfFiniteType f] :
    LocallyQuasiFinite f ↔ ∀ x, IsDiscrete (f ⁻¹' {x}) := by
  refine ⟨fun _ ↦ f.isDiscrete_preimage_singleton, fun H ↦ ?_⟩
  change id _ -- avoid typeclass synthesis from getting stuck on the wlog hypothesis.
  wlog hY : ∃ R, Y = Spec R
  · refine (IsZariskiLocalAtTarget.iff_of_openCover Y.affineCover).mpr fun i ↦
      this (f := pullback.snd _ _) (fun x ↦ ?_) ⟨_, rfl⟩
    convert (H (Y.affineCover.f i x)).preimage ((pullback.fst f _).continuous.continuousOn)
      (pullback.fst f (Y.affineCover.f i)).isOpenEmbedding.injective
    ext
    simp [← (Y.affineCover.f i).isOpenEmbedding.injective.eq_iff, ← Scheme.Hom.comp_apply,
      -Hom.comp_base, pullback.condition]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · exact (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i ↦
      this _ (fun x ↦ (H x).preimage (X.affineCover.f _).continuous.continuousOn
      (X.affineCover.f _).isOpenEmbedding.injective) ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [HasRingHomProperty.Spec_iff, id_eq] at *
  algebraize [φ.hom]
  exact (Algebra.QuasiFinite.iff_finite_comap_preimage_singleton).mpr fun x ↦
    ((Spec.map φ).isCompact_preimage_singleton _).finite (H _)

nonrec lemma LocallyQuasiFinite.of_finite_preimage_singleton
    [LocallyOfFiniteType f] (hf : ∀ x, (f ⁻¹' {x}).Finite) : LocallyQuasiFinite f := by
  change id _ -- avoid typeclass synthesis from getting stuck on the wlog hypothesis.
  wlog hY : ∃ R, Y = Spec R
  · refine (IsZariskiLocalAtTarget.iff_of_openCover Y.affineCover).mpr fun i ↦
      this (f := pullback.snd _ _) (fun x ↦ ?_) ⟨_, rfl⟩
    convert (hf (Y.affineCover.f i x)).preimage
      (pullback.fst f (Y.affineCover.f i)).isOpenEmbedding.injective.injOn
    ext
    simp [← (Y.affineCover.f i).isOpenEmbedding.injective.eq_iff, ← Scheme.Hom.comp_apply,
      -Hom.comp_base, pullback.condition]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · exact (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i ↦ this _ _
      (fun x ↦ ((hf x).preimage (X.affineCover.f _).isOpenEmbedding.injective.injOn:)) ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [HasRingHomProperty.Spec_iff, id_eq] at *
  algebraize [φ.hom]
  exact (Algebra.QuasiFinite.iff_finite_comap_preimage_singleton).mpr hf

lemma locallyQuasiFinite_iff_finite_preimage_singleton
    {f : X ⟶ Y} [LocallyOfFiniteType f] [QuasiCompact f] :
    LocallyQuasiFinite f ↔ ∀ x, (f ⁻¹' {x}).Finite :=
  ⟨fun _ ↦ f.finite_preimage_singleton, .of_finite_preimage_singleton f⟩

/-- A morphism `f : X ⟶ Y` is quasi-finite at `x : X`
if the stalk map `𝒪_{X, x} ⟶ 𝒪_{Y, f x}` is quasi-finite. -/
def Scheme.Hom.QuasiFiniteAt (x : X) : Prop := (f.stalkMap x).hom.QuasiFinite

variable {f} in
lemma Scheme.Hom.QuasiFiniteAt.quasiFiniteAt
    {x : X} (hx : f.QuasiFiniteAt x) {V : X.Opens} (hV : IsAffineOpen V) {U : Y.Opens}
    (hU : IsAffineOpen U) (hVU : V ≤ f ⁻¹ᵁ U) (hxV : x ∈ V.1) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    Algebra.QuasiFiniteAt Γ(Y, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
  letI := (f.appLE U V hVU).hom.toAlgebra
  have H : (Y.presheaf.germ U _ (hVU hxV)).hom.QuasiFinite := by
    let := (Y.presheaf.germ U _ (hVU hxV)).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨f x, (hVU hxV)⟩
    rw [← (Y.presheaf.germ U _ (hVU hxV)).hom.algebraMap_toAlgebra,
      RingHom.quasiFinite_algebraMap]
    exact .of_isLocalization (hU.primeIdealOf ⟨_, hVU hxV⟩).asIdeal.primeCompl
  let := (X.presheaf.germ V x hxV).hom.toAlgebra
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  let e := IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (X.presheaf.stalk (⟨x, hxV⟩ : V.1)) (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
  rw [Algebra.QuasiFiniteAt, ← RingHom.quasiFinite_algebraMap]
  convert (RingHom.QuasiFinite.of_finite e.finite).comp (hx.comp H)
  rw [← CommRingCat.hom_comp, f.germ_stalkMap, ← X.presheaf.germ_res (homOfLE hVU) _ hxV,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc, CommRingCat.hom_comp, ← RingHom.comp_assoc,
    IsScalarTower.algebraMap_eq Γ(Y, U) Γ(X, V)]
  congr 1
  exact e.toAlgHom.comp_algebraMap.symm

lemma Scheme.Hom.quasiFiniteAt [LocallyQuasiFinite f] (x : X) :
    f.QuasiFiniteAt x := by
  refine HasRingHomProperty.stalkMap ?_ ‹_› x
  introv hf
  algebraize [f]
  refine .of_comp (g := algebraMap R _) ?_
  convert RingHom.quasiFinite_algebraMap.mpr (inferInstanceAs
    (Algebra.QuasiFinite R (Localization.AtPrime J)))
  ext; simp; rfl

end AlgebraicGeometry
