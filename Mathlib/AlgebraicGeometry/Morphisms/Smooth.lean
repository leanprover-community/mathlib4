/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.RingHom.StandardSmooth

/-!

# Smooth morphisms

A morphism of schemes `f : X ⟶ Y` is smooth (of relative dimension `n`) if for each `x : X` there
exists an affine open neighborhood `V` of `x` and an affine open neighborhood `U` of
`f.base x` with `V ≤ f ⁻¹ᵁ U` such that the induced map `Γ(Y, U) ⟶ Γ(X, V)` is
standard smooth (of relative dimension `n`).

In other words, smooth (resp. smooth of relative dimension `n`) for scheme morphisms is associated
to the property of ring homomorphisms `Locally IsStandardSmooth`
(resp. `Locally (IsStandardSmoothOfRelativeDimension n)`).

## Implementation details

- Our definition is equivalent to defining `IsSmooth` as the associated scheme morphism property of
the property of ring maps induced by `Algebra.Smooth`. The equivalence will follow from the
equivalence of `Locally IsStandardSmooth` and `Algebra.IsSmooth`, but the latter is a (hard) TODO.

The reason why we choose the definition via `IsStandardSmooth`, is because verifying that
`Algebra.IsSmooth` is local in the sense of `RingHom.PropertyIsLocal` is a (hard) TODO.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry" in
June 2024.

-/


noncomputable section

open CategoryTheory

universe t w v u

namespace AlgebraicGeometry

open RingHom

variable (n m : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A morphism of schemes `f : X ⟶ Y` is smooth if for each `x : X` there
exists an affine open neighborhood `V` of `x` and an affine open neighborhood `U` of
`f.base x` with `V ≤ f ⁻¹ᵁ U` such that the induced map `Γ(Y, U) ⟶ Γ(X, V)` is
standard smooth.
-/
@[mk_iff]
class IsSmooth : Prop where
  exists_isStandardSmooth : ∀ (x : X), ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1)
    (e : V.1 ≤ f ⁻¹ᵁ U.1), IsStandardSmooth (f.appLE U V e).hom

/-- The property of scheme morphisms `IsSmooth` is associated with the ring
homomorphism property `Locally IsStandardSmooth`. -/
instance : HasRingHomProperty @IsSmooth (Locally IsStandardSmooth) := by
  apply HasRingHomProperty.locally_of_iff
  · exact isStandardSmooth_localizationPreserves.away
  · exact isStandardSmooth_stableUnderCompositionWithLocalizationAway
  · intro X Y f
    rw [isSmooth_iff]

/-- Being smooth is stable under composition. -/
instance : MorphismProperty.IsStableUnderComposition @IsSmooth :=
  HasRingHomProperty.stableUnderComposition <| locally_stableUnderComposition
    isStandardSmooth_respectsIso isStandardSmooth_localizationPreserves
      isStandardSmooth_stableUnderComposition

/-- The composition of smooth morphisms is smooth. -/
instance isSmooth_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [IsSmooth f] [IsSmooth g] :
    IsSmooth (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹IsSmooth f› ‹IsSmooth g›

/-- Smooth of relative dimension `n` is stable under base change. -/
lemma isSmooth_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsSmooth :=
  HasRingHomProperty.isStableUnderBaseChange <| locally_isStableUnderBaseChange
    isStandardSmooth_respectsIso isStandardSmooth_isStableUnderBaseChange

/--
A morphism of schemes `f : X ⟶ Y` is smooth of relative dimension `n` if for each `x : X` there
exists an affine open neighborhood `V` of `x` and an affine open neighborhood `U` of
`f.base x` with `V ≤ f ⁻¹ᵁ U` such that the induced map `Γ(Y, U) ⟶ Γ(X, V)` is
standard smooth of relative dimension `n`.
-/
@[mk_iff]
class IsSmoothOfRelativeDimension : Prop where
  exists_isStandardSmoothOfRelativeDimension : ∀ (x : X), ∃ (U : Y.affineOpens)
    (V : X.affineOpens) (_ : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1),
    IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom

/-- If `f` is smooth of any relative dimension, it is smooth. -/
lemma IsSmoothOfRelativeDimension.isSmooth [IsSmoothOfRelativeDimension n f] : IsSmooth f where
  exists_isStandardSmooth x := by
    obtain ⟨U, V, hx, e, hf⟩ := exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
    exact ⟨U, V, hx, e, hf.isStandardSmooth⟩

/-- The property of scheme morphisms `IsSmoothOfRelativeDimension n` is associated with the ring
homomorphism property `Locally (IsStandardSmoothOfRelativeDimension n)`. -/
instance : HasRingHomProperty (@IsSmoothOfRelativeDimension n)
    (Locally (IsStandardSmoothOfRelativeDimension n)) := by
  apply HasRingHomProperty.locally_of_iff
  · exact (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
  · exact isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n
  · intro X Y f
    rw [isSmoothOfRelativeDimension_iff]

/-- Smooth of relative dimension `n` is stable under base change. -/
lemma isSmoothOfRelativeDimension_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@IsSmoothOfRelativeDimension n) :=
  HasRingHomProperty.isStableUnderBaseChange <| locally_isStableUnderBaseChange
    isStandardSmoothOfRelativeDimension_respectsIso
    (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n)

/-- Open immersions are smooth of relative dimension `0`. -/
instance (priority := 900) [IsOpenImmersion f] : IsSmoothOfRelativeDimension 0 f :=
  HasRingHomProperty.of_isOpenImmersion
    (locally_holdsForLocalizationAway <|
      isStandardSmoothOfRelativeDimension_holdsForLocalizationAway).containsIdentities

/-- Open immersions are smooth. -/
instance (priority := 900) [IsOpenImmersion f] : IsSmooth f :=
  IsSmoothOfRelativeDimension.isSmooth 0 f

/-- If `f` is smooth of relative dimension `n` and `g` is smooth of relative dimension
`m`, then `f ≫ g` is smooth of relative dimension `n + m`. -/
instance isSmoothOfRelativeDimension_comp {Z : Scheme.{u}} (g : Y ⟶ Z)
    [hf : IsSmoothOfRelativeDimension n f] [hg : IsSmoothOfRelativeDimension m g] :
    IsSmoothOfRelativeDimension (n + m) (f ≫ g) where
  exists_isStandardSmoothOfRelativeDimension x := by
    obtain ⟨U₂, V₂, hfx₂, e₂, hf₂⟩ := hg.exists_isStandardSmoothOfRelativeDimension (f.base x)
    obtain ⟨U₁', V₁', hx₁', e₁', hf₁'⟩ := hf.exists_isStandardSmoothOfRelativeDimension x
    obtain ⟨r, s, hx₁, e₁, hf₁⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
      (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
      (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
      x V₂ U₁' V₁' V₁' hx₁' hx₁' e₁' hf₁' hfx₂
    have e : X.basicOpen s ≤ (f ≫ g) ⁻¹ᵁ U₂ :=
      le_trans e₁ <| f.preimage_mono <| le_trans (Y.basicOpen_le r) e₂
    have heq : (f ≫ g).appLE U₂ (X.basicOpen s) e = g.appLE U₂ V₂ e₂ ≫
        CommRingCat.ofHom (algebraMap Γ(Y, V₂) Γ(Y, Y.basicOpen r)) ≫
          f.appLE (Y.basicOpen r) (X.basicOpen s) e₁ := by
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
        g.appLE_map_assoc, Scheme.Hom.appLE_comp_appLE]
    refine ⟨U₂, ⟨X.basicOpen s, V₁'.2.basicOpen s⟩, hx₁, e, heq ▸ ?_⟩
    apply IsStandardSmoothOfRelativeDimension.comp ?_ hf₂
    haveI : IsLocalization.Away r Γ(Y, Y.basicOpen r) := V₂.2.isLocalization_basicOpen r
    exact (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).left
      _ r _ hf₁

instance {Z : Scheme.{u}} (g : Y ⟶ Z) [IsSmoothOfRelativeDimension 0 f]
    [IsSmoothOfRelativeDimension 0 g] :
    IsSmoothOfRelativeDimension 0 (f ≫ g) :=
  inferInstanceAs <| IsSmoothOfRelativeDimension (0 + 0) (f ≫ g)

/-- Smooth of relative dimension `0` is multiplicative. -/
instance : MorphismProperty.IsMultiplicative (@IsSmoothOfRelativeDimension 0) where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance

/-- Smooth morphisms are locally of finite presentation. -/
instance (priority := 100) [hf : IsSmooth f] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation]
  rw [HasRingHomProperty.eq_affineLocally @IsSmooth] at hf
  refine affineLocally_le (fun hf ↦ ?_) f hf
  apply RingHom.locally_of_locally (Q := RingHom.FinitePresentation) at hf
  · rwa [RingHom.locally_iff_of_localizationSpanTarget finitePresentation_respectsIso
      finitePresentation_ofLocalizationSpanTarget] at hf
  · introv hf
    algebraize [f]
    -- TODO: why is `algebraize` not generating the following instance?
    haveI : Algebra.IsStandardSmooth R S := hf
    exact this.finitePresentation

end AlgebraicGeometry
