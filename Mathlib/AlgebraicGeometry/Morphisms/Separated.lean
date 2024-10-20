/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer

/-!

# Separated morphisms

A morphism of schemes is separated if its diagonal morphism is a closed immmersion.

## TODO

- Show affine morphisms are separated.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

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

instance {Z : Scheme.{u}} (g : Y ⟶ Z) [IsSeparated f] [IsSeparated g] : IsSeparated (f ≫ g) :=
  stableUnderComposition.comp_mem f g inferInstance inferInstance

instance : MorphismProperty.IsMultiplicative @IsSeparated where
  id_mem _ := inferInstance

lemma stableUnderBaseChange : MorphismProperty.StableUnderBaseChange @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  exact MorphismProperty.StableUnderBaseChange.diagonal IsClosedImmersion.stableUnderBaseChange

instance : IsLocalAtTarget @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

instance {S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [IsSeparated i] :
    IsClosedImmersion (pullback.mapDesc f g i) :=
  IsClosedImmersion.stableUnderBaseChange (pullback_map_diagonal_isPullback f g i)
    inferInstance

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

namespace Scheme

/-- A scheme `X` is separated if the diagonal map `X ⟶ X × X` is a closed immersion. -/
@[mk_iff]
protected class IsSeparated (X : Scheme.{u}) : Prop where
  isClosedImmersion_prod_lift : IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X))

attribute [instance] IsSeparated.isClosedImmersion_prod_lift

lemma isSeparated_iff_isSeparated_terminal {X : Scheme.{u}} :
    X.IsSeparated ↔ IsSeparated (terminal.from X) := by
  rw [isSeparated_iff, AlgebraicGeometry.isSeparated_iff, iff_iff_eq,
    ← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ (prodIsoPullback X X).hom]
  congr
  ext : 1 <;> simp

instance (f g : X ⟶ Y) [Y.IsSeparated] : IsClosedImmersion (Limits.equalizer.ι f g) :=
  IsClosedImmersion.stableUnderBaseChange (isPullback_equalizer_prod f g).flip inferInstance

end Scheme

end AlgebraicGeometry
