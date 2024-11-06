/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer

/-!

# Separated morphisms

A morphism of schemes is separated if its diagonal morphism is a closed immmersion.

## Main definitions
- `AlgebraicGeometry.IsSeparated`: The class of separated morphisms.
- `AlgebraicGeometry.Scheme.IsSeparated`: The class of separated schemes.
- `AlgebraicGeometry.IsSeparated.hasAffineProperty`:
  A morphism is separated iff the preimage of affine opens are separated schemes.
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {W X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism is separated if the diagonal map is a closed immersion. -/
@[mk_iff]
class IsSeparated : Prop where
  /-- A morphism is separated if the diagonal map is a closed immersion. -/
  diagonal_isClosedImmersion : IsClosedImmersion (pullback.diagonal f) := by infer_instance

namespace IsSeparated

attribute [instance] diagonal_isClosedImmersion

theorem isSeparated_eq_diagonal_isClosedImmersion :
    @IsSeparated = MorphismProperty.diagonal @IsClosedImmersion := by
  ext
  exact isSeparated_iff _

/-- Monomorphisms are separated. -/
instance (priority := 900) isSeparated_of_mono [Mono f] : IsSeparated f where

instance : MorphismProperty.RespectsIso @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

instance (priority := 900) [IsSeparated f] : QuasiSeparated f where

instance stableUnderComposition : MorphismProperty.IsStableUnderComposition @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  exact MorphismProperty.diagonal_isStableUnderComposition IsClosedImmersion.stableUnderBaseChange

instance [IsSeparated f] [IsSeparated g] : IsSeparated (f ≫ g) :=
  stableUnderComposition.comp_mem f g inferInstance inferInstance

instance : MorphismProperty.IsMultiplicative @IsSeparated where
  id_mem _ := inferInstance

lemma stableUnderBaseChange : MorphismProperty.StableUnderBaseChange @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  exact MorphismProperty.StableUnderBaseChange.diagonal IsClosedImmersion.stableUnderBaseChange

instance : IsLocalAtTarget @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

instance (R S : CommRingCat.{u}) (f : R ⟶ S) : IsSeparated (Spec.map f) := by
  constructor
  letI := f.toAlgebra
  show IsClosedImmersion (Limits.pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  rw [diagonal_Spec_map, MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]
  exact .spec_of_surjective _ fun x ↦ ⟨.tmul R 1 x,
    (Algebra.TensorProduct.lmul'_apply_tmul (R := R) (S := S) 1 x).trans (one_mul x)⟩

@[instance 100]
lemma of_isAffineHom [h : IsAffineHom f] : IsSeparated f := by
  wlog hY : IsAffine Y
  · rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H : IsAffineHom (f ∣_ U) := IsLocalAtTarget.restrict h U
    exact this _ U.2
  have : IsAffine X := HasAffineProperty.iff_of_isAffine.mp h
  rw [MorphismProperty.arrow_mk_iso_iff @IsSeparated (arrowIsoSpecΓOfIsAffine f)]
  infer_instance

instance {S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [IsSeparated i] :
    IsClosedImmersion (pullback.mapDesc f g i) :=
  IsClosedImmersion.stableUnderBaseChange (pullback_map_diagonal_isPullback f g i)
    inferInstance

/-- Given `f : X ⟶ Y` and `g : Y ⟶ Z` such that `g` is separated, the induced map
`X ⟶ X ×[Z] Y` is a closed immersion. -/
instance [IsSeparated g] :
    IsClosedImmersion (pullback.lift (𝟙 _) f (Category.id_comp (f ≫ g))) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (pullback.fst f (𝟙 Y))]
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (pullback.congrHom rfl (Category.id_comp g)).inv]
  convert (inferInstanceAs <| IsClosedImmersion (pullback.mapDesc f (𝟙 _) g)) using 1
  ext : 1 <;> simp [pullback.condition]

end IsSeparated

lemma IsClosedImmersion.of_comp [IsClosedImmersion (f ≫ g)] [IsSeparated g] :
    IsClosedImmersion f := by
  rw [← pullback.lift_snd (𝟙 _) f (Category.id_comp (f ≫ g))]
  have := IsClosedImmersion.stableUnderBaseChange.snd (f ≫ g) g inferInstance
  infer_instance

lemma IsSeparated.of_comp [IsSeparated (f ≫ g)] : IsSeparated f := by
  have := IsSeparated.diagonal_isClosedImmersion (f := f ≫ g)
  rw [pullback.diagonal_comp] at this
  exact ⟨@IsClosedImmersion.of_comp _ _ _ _ _ this inferInstance⟩

lemma IsSeparated.comp_iff [IsSeparated g] : IsSeparated (f ≫ g) ↔ IsSeparated f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩

@[stacks 01KM]
instance isClosedImmersion_equalizer_ι_left {S : Scheme} {X Y : Over S} [IsSeparated Y.hom]
    (f g : X ⟶ Y) : IsClosedImmersion (equalizer.ι f g).left := by
  refine IsClosedImmersion.stableUnderBaseChange
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert (inferInstanceAs (IsClosedImmersion (pullback.diagonal Y.hom)))
  ext1 <;> simp [← Over.comp_left]

/--
Suppose `X` is a reduced scheme and that `f g : X ⟶ Y` agree over some separated `Y ⟶ Z`.
Then `f = g` if `ι ≫ f = ι ≫ g` for some dominant `ι`.
-/
lemma ext_of_isDominant_of_isSeparated [IsReduced X] {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have : IsDominant (equalizer.ι f' g').left := by
    apply (config := { allowSynthFailures := true }) IsDominant.of_comp (equalizer.lift ι' ?_).left
    · rwa [← Over.comp_left, equalizer.lift_ι]
    · ext1; exact hU
  have : Surjective (equalizer.ι f' g').left :=
    surjective_of_isDominant_of_isClosed_range _ IsClosedImmersion.base_closed.2
  have := isIso_of_isClosedImmersion_of_surjective (Y := X) (equalizer.ι f' g').left
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

namespace Scheme

/-- A scheme `X` is separated if it is separated over `⊤_ Scheme`. -/
@[mk_iff]
protected class IsSeparated (X : Scheme.{u}) : Prop where
  isSeparated_terminal_from : IsSeparated (terminal.from X)

attribute [instance] IsSeparated.isSeparated_terminal_from

lemma isSeparated_iff_isClosedImmersion_prod_lift {X : Scheme.{u}} :
    X.IsSeparated ↔ IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rw [isSeparated_iff, AlgebraicGeometry.isSeparated_iff, iff_iff_eq,
    ← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ (prodIsoPullback X X).hom]
  congr
  ext : 1 <;> simp

instance [X.IsSeparated] : IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rwa [← isSeparated_iff_isClosedImmersion_prod_lift]

instance (priority := 900) {X : Scheme.{u}} [IsAffine X] : X.IsSeparated := ⟨inferInstance⟩

instance (priority := 900) [X.IsSeparated] : IsSeparated f := by
  apply (config := { allowSynthFailures := true }) @IsSeparated.of_comp (g := terminal.from Y)
  rw [terminal.comp_from]
  infer_instance

instance (f g : X ⟶ Y) [Y.IsSeparated] : IsClosedImmersion (Limits.equalizer.ι f g) :=
  IsClosedImmersion.stableUnderBaseChange (isPullback_equalizer_prod f g).flip inferInstance

end Scheme

instance IsSeparated.hasAffineProperty :
    HasAffineProperty @IsSeparated fun X _ _ _ ↦ X.IsSeparated := by
  convert HasAffineProperty.of_isLocalAtTarget @IsSeparated with X Y f hY
  rw [Scheme.isSeparated_iff, ← terminal.comp_from f, IsSeparated.comp_iff]
  rfl

/--
Suppose `f g : X ⟶ Y` where `X` is a reduced scheme and `Y` is a separated scheme.
Then `f = g` if `ι ≫ f = ι ≫ g` for some dominant `ι`.

Also see `ext_of_isDominant_of_isSeparated` for the general version over arbitrary bases.
-/
lemma ext_of_isDominant [IsReduced X] {f g : X ⟶ Y} [Y.IsSeparated]
    (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g :=
  ext_of_isDominant_of_isSeparated (Limits.terminal.from _) (Limits.terminal.hom_ext _ _) ι hU

end AlgebraicGeometry
