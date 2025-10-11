/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# Morphisms of finite type

A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.

A morphism of schemes is of finite type if it is both locally of finite type and quasi-compact.

We show that these properties are local, and are stable under compositions and base change.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.
-/
@[mk_iff]
class LocallyOfFiniteType (f : X ⟶ Y) : Prop where
  finiteType_of_affine_subset :
    ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1), (f.appLE U V e).hom.FiniteType

instance : HasRingHomProperty @LocallyOfFiniteType RingHom.FiniteType where
  isLocal_ringHomProperty := RingHom.finiteType_isLocal
  eq_affineLocally' := by
    ext X Y f
    rw [locallyOfFiniteType_iff, affineLocally_iff_affineOpens_le]

instance (priority := 900) locallyOfFiniteType_of_isOpenImmersion [IsOpenImmersion f] :
    LocallyOfFiniteType f :=
  HasRingHomProperty.of_isOpenImmersion
    RingHom.finiteType_holdsForLocalizationAway.containsIdentities

instance : MorphismProperty.IsStableUnderComposition @LocallyOfFiniteType :=
  HasRingHomProperty.stableUnderComposition RingHom.finiteType_stableUnderComposition

instance locallyOfFiniteType_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : LocallyOfFiniteType f] [hg : LocallyOfFiniteType g] : LocallyOfFiniteType (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

theorem locallyOfFiniteType_of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ g)] : LocallyOfFiniteType f :=
  HasRingHomProperty.of_comp (fun _ _ ↦ RingHom.FiniteType.of_comp_finiteType) ‹_›

instance : MorphismProperty.IsMultiplicative @LocallyOfFiniteType where
  id_mem _ := inferInstance

open scoped TensorProduct in
instance locallyOfFiniteType_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @LocallyOfFiniteType :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.finiteType_isStableUnderBaseChange

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType g] :
    LocallyOfFiniteType (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance {R} [CommRing R] [IsJacobsonRing R] : JacobsonSpace <| Spec <| .of R :=
  inferInstanceAs (JacobsonSpace (PrimeSpectrum R))

instance {R : CommRingCat} [IsJacobsonRing R] : JacobsonSpace (Spec R) :=
  inferInstanceAs (JacobsonSpace (PrimeSpectrum R))

nonrec lemma LocallyOfFiniteType.jacobsonSpace
    (f : X ⟶ Y) [LocallyOfFiniteType f] [JacobsonSpace Y] : JacobsonSpace X := by
  wlog hY : ∃ S, Y = Spec S
  · rw [(Scheme.OpenCover.isOpenCover_opensRange (Y.affineCover.pullback₁ f)).jacobsonSpace_iff]
    intro i
    have inst : LocallyOfFiniteType (Y.affineCover.pullbackHom f i) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have inst : JacobsonSpace Y := ‹_› -- TC gets stuck on the WLOG hypothesis without it.
    have inst : JacobsonSpace (Y.affineCover.X i) :=
      .of_isOpenEmbedding (Y.affineCover.f i).isOpenEmbedding
    let e := ((Y.affineCover.pullback₁ f).f i).isOpenEmbedding.isEmbedding.toHomeomorph
    have := this (Y.affineCover.pullbackHom f i) ⟨_, rfl⟩
    exact .of_isClosedEmbedding e.symm.isClosedEmbedding
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have inst : JacobsonSpace (Spec R) := ‹_› -- TC gets stuck on the WLOG hypothesis without it.
    rw [X.affineCover.isOpenCover_opensRange.jacobsonSpace_iff]
    intro i
    have := this _ (X.affineCover.f i ≫ f) ⟨_, rfl⟩
    let e := (X.affineCover.f i).isOpenEmbedding.isEmbedding.toHomeomorph
    exact .of_isClosedEmbedding e.symm.isClosedEmbedding
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl : Spec.map φ = f⟩ := Spec.homEquiv.symm.surjective f
  have : RingHom.FiniteType φ.hom := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom]
  have := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mpr ‹_›
  exact PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp (isJacobsonRing_of_finiteType (A := R))

end AlgebraicGeometry
