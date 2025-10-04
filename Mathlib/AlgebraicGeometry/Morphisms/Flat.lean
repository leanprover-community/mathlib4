/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Topology.Category.TopCat.EffectiveEpi

/-!
# Flat morphisms

A morphism of schemes `f : X ⟶ Y` is flat if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is flat. This is equivalent to
asking that all stalk maps are flat (see `AlgebraicGeometry.Flat.iff_flat_stalkMap`).

We show that this property is local, and are stable under compositions and base change.

-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is flat if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is flat. This is equivalent to
asking that all stalk maps are flat (see `AlgebraicGeometry.Flat.iff_flat_stalkMap`).
-/
@[mk_iff]
class Flat (f : X ⟶ Y) : Prop where
  flat_of_affine_subset :
    ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1), (f.appLE U V e).hom.Flat

namespace Flat

instance : HasRingHomProperty @Flat RingHom.Flat where
  isLocal_ringHomProperty := RingHom.Flat.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [flat_iff, affineLocally_iff_affineOpens_le]

instance (priority := 900) [IsOpenImmersion f] : Flat f :=
  HasRingHomProperty.of_isOpenImmersion
    RingHom.Flat.containsIdentities

instance : MorphismProperty.IsStableUnderComposition @Flat :=
  HasRingHomProperty.stableUnderComposition RingHom.Flat.stableUnderComposition

instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : Flat f] [hg : Flat g] : Flat (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

instance : MorphismProperty.IsMultiplicative @Flat where
  id_mem _ := inferInstance

instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Flat :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.Flat.isStableUnderBaseChange

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Flat g] : Flat (pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Flat f] : Flat (pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

lemma of_stalkMap (H : ∀ x, (f.stalkMap x).hom.Flat) : Flat f :=
  HasRingHomProperty.of_stalkMap RingHom.Flat.ofLocalizationPrime H

lemma stalkMap [Flat f] (x : X) : (f.stalkMap x).hom.Flat :=
  HasRingHomProperty.stalkMap (P := @Flat)
    (fun f hf J hJ ↦ hf.localRingHom J (J.comap f) rfl) ‹_› x

lemma iff_flat_stalkMap : Flat f ↔ ∀ x, (f.stalkMap x).hom.Flat :=
  ⟨fun _ ↦ stalkMap f, fun H ↦ of_stalkMap f H⟩

instance {X : Scheme.{u}} {ι : Type v} [Small.{u} ι] {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ X}
    [∀ i, Flat (f i)] : Flat (Sigma.desc f) :=
  IsLocalAtSource.sigmaDesc (fun _ ↦ inferInstance)

section FlatAndSurjective

/-- A surjective, quasi-compact, flat morphism is a quotient map. -/
@[stacks 02JY]
lemma isQuotientMap_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f]
    [Surjective f] : Topology.IsQuotientMap f.base := by
  rw [Topology.isQuotientMap_iff]
  refine ⟨f.surjective, fun s ↦ ⟨fun hs ↦ hs.preimage f.continuous, fun hs ↦ ?_⟩⟩
  wlog hY : ∃ R, Y = Spec R
  · let 𝒰 := Y.affineCover
    rw [𝒰.isOpenCover_opensRange.isOpen_iff_inter]
    intro i
    rw [Scheme.Hom.coe_opensRange, ← Set.image_preimage_eq_inter_range]
    apply (𝒰.f i).isOpenEmbedding.isOpenMap
    refine this (f := pullback.fst (𝒰.f i) f) _ ?_ ⟨_, rfl⟩
    rw [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.comp_base, pullback.condition,
      Scheme.comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact hs.preimage (Scheme.Hom.continuous _)
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    let 𝒰 := X.affineCover.finiteSubcover
    let p : ∐ (fun i : 𝒰.I₀ ↦ 𝒰.X i) ⟶ X := Sigma.desc (fun i ↦ 𝒰.f i)
    refine this (f := (∐ (fun i : 𝒰.I₀ ↦ 𝒰.X i)).isoSpec.inv ≫ p ≫ f) _ _ ?_ ⟨_, rfl⟩
    rw [← Category.assoc, Scheme.comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact hs.preimage (_ ≫ p).continuous
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  refine ((PrimeSpectrum.isQuotientMap_of_generalizingMap ?_ ?_).isOpen_preimage).mp hs
  · exact (surjective_iff (Spec.map φ)).mp inferInstance
  · apply RingHom.Flat.generalizingMap_comap
    rwa [← HasRingHomProperty.Spec_iff (P := @Flat)]

/-- A flat surjective morphism of schemes is an epimorphism in the category of schemes. -/
@[stacks 02VW]
lemma epi_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] : Epi f := by
  apply CategoryTheory.Functor.epi_of_epi_map (Scheme.forgetToLocallyRingedSpace)
  apply CategoryTheory.Functor.epi_of_epi_map (LocallyRingedSpace.forgetToSheafedSpace)
  apply SheafedSpace.epi_of_base_surjective_of_stalk_mono _ ‹Surjective f›.surj
  intro x
  apply ConcreteCategory.mono_of_injective
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f.base.hom x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

lemma flat_and_surjective_iff_of_faithfullyFlat_of_isAffine [IsAffine X] [IsAffine Y] :
    Flat f ∧ Surjective f ↔ f.appTop.hom.FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  constructor
  · intro ⟨hf, _⟩
    have : Surjective (Spec.map f.appTop) := Category.comp_id (Spec.map _) ▸
      Scheme.isoSpec_inv_toSpecΓ Y ▸ Scheme.isoSpec_inv_naturality_assoc f _ ▸ inferInstance
    exact ⟨HasRingHomProperty.iff_of_isAffine.mp hf, this.surj⟩
  · intro ⟨hf₁, hf₂⟩
    have : Flat (Spec.map (Scheme.Hom.appTop f)) := HasRingHomProperty.Spec_iff.mpr hf₁
    have : Surjective (Spec.map (Scheme.Hom.appTop f)) := ⟨hf₂⟩
    exact (Category.comp_id f ▸ Scheme.toSpecΓ_isoSpec_inv Y ▸
      Scheme.isoSpec_hom_naturality_assoc f _).symm ▸ ⟨inferInstance, inferInstance⟩

/-- An effective epimorphism structure on the continuous map underlying a flat surjective and
quasi-compact map of schemes. -/
noncomputable def effectiveEpisStructBase [Flat f] [Surjective f] [QuasiCompact f] :
    EffectiveEpiStruct f.base :=
  TopCat.effectiveEpiStructOfQuotientMap _ (isQuotientMap_of_surjective f)

variable {f} in
/-- A preparation lemma for `AlgebraicGeometry.Flat.base_factor`. -/
lemma base_factorization_type [Flat f] [Surjective f] [QuasiCompact f] {W : Scheme.{u}} {e : X ⟶ W}
    (h : pullback.fst f f ≫ e = pullback.snd f f ≫ e) :
    ∃ (g : ↥Y → ↥W), ⇑e.base.hom = g ∘ ⇑f.base.hom := by
  let : RegularEpi (Scheme.forget.map f) := by
    have := (isSplitEpi_iff_surjective (Scheme.forget.map f)).mpr ‹Surjective f›.surj
    exact regularEpiOfEffectiveEpi (Scheme.forget.map f)
  refine ⟨_, types_comp _ _ ▸ Cofork.IsColimit.π_desc' this.isColimit _ ?_|>.symm⟩
  change pullback.fst _ _ ≫ Scheme.forget.map e = pullback.snd _ _ ≫ Scheme.forget.map e
  apply ((epi_iff_surjective _).mpr
    (Scheme.Pullback.forget_comparison_surjective _ _)).left_cancellation
  simp only [← Category.assoc, pullbackComparison_comp_fst, ← Functor.map_comp, h,
    pullbackComparison_comp_snd]

variable {f} in
/-- For a flat surjective and quasi-compact morphism `f : X ⟶ Y` of schemes,
any morphism `e : X ⟶ W` of schemes satisfying `pullback.fst f f ≫ e = pullback.snd f f ≫ e`
factors through a unique *continuous map* on underlying topological spaces. -/
lemma base_factorization [Flat f] [Surjective f] [QuasiCompact f] {W : Scheme.{u}} {e : X ⟶ W}
    (h : pullback.fst f f ≫ e = pullback.snd f f ≫ e) :
    ∃! (g : Y.carrier ⟶ W.carrier), f.base ≫ g = e.base := by
  have : ∀ {Z : TopCat} (g₁ g₂ : Z ⟶ X.carrier), g₁ ≫ f.base = g₂ ≫ f.base →
      g₁ ≫ e.base = g₂ ≫ e.base := by
    intro _ _ _ hg
    apply TopCat.hom_ext
    apply ContinuousMap.coe_injective
    simp only [TopCat.hom_comp, ContinuousMap.coe_comp]
    rw [(base_factorization_type h).choose_spec, Function.comp_assoc]
    congr 1
    exact congrArg (fun g ↦ g.toFun) ((TopCat.hom_comp _ _).trans (congrArg (fun g ↦ g.hom) hg))
  exact ⟨(effectiveEpisStructBase f).desc e.base this, ⟨(effectiveEpisStructBase f).fac e.base this,
    fun g' hg' ↦ (effectiveEpisStructBase f).uniq e.base this g' hg'⟩⟩

end FlatAndSurjective

end Flat

end AlgebraicGeometry
