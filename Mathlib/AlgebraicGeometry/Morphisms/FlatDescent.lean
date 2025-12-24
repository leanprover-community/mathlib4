/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Properties of morphisms satisfying fpqc descent

In this file we show some global properties satisfy fpqc descent.

- universally closed
  (`AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`)
- universally open
  (`AlgebraicGeometry.descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact`)
- universally injective
  (`AlgebraicGeometry.descendsAlong_universallyInjective_surjective_inf_flat_inf_quasicompact`)
- being an isomorphism
  (`AlgebraicGeometry.descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`)
- being an open immersion
  (`AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact`)
-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

/-- Surjective satisfies fpqc descent. -/
instance Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @Surjective (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  .of_le (Q := @Surjective) (le_of_inf_eq' (by grind))

/-- Universally closed satisfies fpqc descent. -/
@[stacks 02KS]
instance descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @UniversallyClosed (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  refine fun {R} S Y φ g ⟨_, _⟩ hfst ↦ ⟨universally_mk' _ _ fun {T} f _ s hs ↦ ?_⟩
  let p := pullback.fst (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g)
  let r : pullback (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g) ⟶ pullback f g :=
    pullback.map _ _ _ _ (pullback.snd _ _) (pullback.snd _ _) (Spec.map φ) (pullback.condition ..)
      (pullback.condition ..)
  have : IsClosed ((pullback.snd (Spec.map φ) f).base ⁻¹' ((pullback.fst f g).base '' s)) := by
    rw [← Scheme.image_preimage_eq_of_isPullback (isPullback_map_snd_snd ..)]
    exact p.isClosedMap _ (hs.preimage r.continuous)
  rwa [(Flat.isQuotientMap_of_surjective _).isClosed_preimage] at this

/-- Universally open satisfies fpqc descent. -/
@[stacks 02KT]
instance descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @UniversallyOpen
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  refine fun {R} S Y φ g ⟨_, _⟩ hfst ↦ ⟨universally_mk' _ _ fun {T} f _ s hs ↦ ?_⟩
  let p := pullback.fst (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g)
  let r : pullback (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g) ⟶ pullback f g :=
    pullback.map _ _ _ _ (pullback.snd _ _) (pullback.snd _ _) (Spec.map φ) (pullback.condition ..)
      (pullback.condition ..)
  have : IsOpen ((pullback.snd (Spec.map φ) f).base ⁻¹' ((pullback.fst f g).base '' s)) := by
    rw [← Scheme.image_preimage_eq_of_isPullback (isPullback_map_snd_snd ..)]
    exact p.isOpenMap _ (hs.preimage r.continuous)
  rwa [(Flat.isQuotientMap_of_surjective _).isOpen_preimage] at this

/-- Universally injective satisfies fpqc descent. -/
@[stacks 02KW]
instance descendsAlong_universallyInjective_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @UniversallyInjective (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [universallyInjective_eq_diagonal]
  infer_instance

/-- Being an isomorphism satisfies fpqc descent. -/
@[stacks 02L4]
instance descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact :
    (isomorphisms Scheme.{u}).DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R S Y φ g h (hfst : IsIso _)
  have : IsAffine Y :=
    have : UniversallyInjective g :=
      of_pullback_fst_of_descendsAlong (P := @UniversallyInjective) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have : Surjective g :=
      of_pullback_fst_of_descendsAlong (P := @Surjective) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have hopen' : UniversallyOpen g :=
      of_pullback_fst_of_descendsAlong (P := @UniversallyOpen) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have : IsHomeomorph g.base := ⟨g.continuous, g.isOpenMap, g.injective, g.surjective⟩
    have : IsAffineHom g :=
      isAffineHom_of_isInducing g this.isInducing this.isClosedEmbedding.isClosed_range
    isAffine_of_isAffineHom g
  wlog hY : ∃ T, Y = Spec T generalizing Y
  · rw [← (isomorphisms Scheme).cancel_left_of_respectsIso Y.isoSpec.inv]
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
      pullback.map _ _ _ _ (𝟙 _) (Y.isoSpec.inv) (𝟙 _) (by simp) (by simp) ≫
        pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    change isomorphisms Scheme _
    rwa [heq, (isomorphisms Scheme).cancel_left_of_respectsIso]
  obtain ⟨T, rfl⟩ := hY
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  refine of_pullback_fst_Spec_of_codescendsAlong (P := isomorphisms Scheme.{u})
      (Q' := RingHom.FaithfullyFlat) (Q := fun f ↦ Function.Bijective f) (P' := @Surjective ⊓ @Flat)
      RingHom.FaithfullyFlat.codescendsAlong_bijective ?_ ?_ h hfst
  · intro _ _ f hf
    rwa [← flat_and_surjective_SpecMap_iff, and_comm]
  · simp_rw [← isIso_SpecMap_iff, isomorphisms.iff, implies_true]

/-- Being an open immersion satisfies fpqc descent. -/
@[stacks 02L3]
instance descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact' :
    IsOpenImmersion.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply DescendsAlong.mk'
  intro X Y Z f g _ hf hg
  have : UniversallyOpen g :=
    MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @UniversallyOpen) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f)
      hf inferInstance
  let U : Z.Opens := ⟨Set.range g.base, g.isOpenMap.isOpen_range⟩
  let f' := pullback.snd f U.ι
  let g' : Y ⟶ U := IsOpenImmersion.lift U.ι g (by simp [U])
  have : Surjective g' := ⟨fun ⟨x, ⟨y, hy⟩⟩ ↦
    ⟨y, by apply U.ι.injective; simp [← Scheme.Hom.comp_apply, g', hy]⟩⟩
  have : IsIso (pullback.fst f' g') := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨?_, inferInstance⟩
    have : IsOpenImmersion (pullback.fst f (g' ≫ U.ι)) := by
      rwa [AlgebraicGeometry.IsOpenImmersion.lift_fac]
    have : IsOpenImmersion (pullback.fst f' g' ≫ pullback.fst f U.ι) := by
      rw [← pullbackLeftPullbackSndIso_hom_fst]
      infer_instance
    exact .of_comp _ (pullback.fst _ _)
  have : IsIso g' := by
    apply MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := isomorphisms Scheme) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f') ?_ this
    exact MorphismProperty.pullback_snd _ _ hf
  rw [← IsOpenImmersion.lift_fac U.ι g (by simp [U])]
  infer_instance

end AlgebraicGeometry
