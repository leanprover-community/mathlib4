/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.LocalAtTarget
import Mathlib.AlgebraicGeometry.Morphisms.Basic

#align_import algebraic_geometry.morphisms.open_immersion from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!

# Open immersions

A morphism is an open immersion if the underlying map of spaces is an open embedding
`f : X ⟶ U ⊆ Y`, and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Most of the theories are developed in `AlgebraicGeometry/OpenImmersion`, and we provide the
remaining theorems analogous to other lemmas in `AlgebraicGeometry/Morphisms/*`.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem isOpenImmersion_iff_stalk {f : X ⟶ Y} : IsOpenImmersion f ↔
    OpenEmbedding f.1.base ∧ ∀ x, IsIso (PresheafedSpace.stalkMap f.1 x) := by
  constructor
  · intro h; exact ⟨h.1, inferInstance⟩
  · rintro ⟨h₁, h₂⟩; exact IsOpenImmersion.of_stalk_iso f h₁
#align algebraic_geometry.is_open_immersion_iff_stalk AlgebraicGeometry.isOpenImmersion_iff_stalk

instance isOpenImmersion_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @IsOpenImmersion where
  comp_mem f g _ _ := LocallyRingedSpace.IsOpenImmersion.comp f g
#align algebraic_geometry.is_open_immersion_stable_under_composition AlgebraicGeometry.isOpenImmersion_isStableUnderComposition

theorem isOpenImmersion_respectsIso : MorphismProperty.RespectsIso @IsOpenImmersion := by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro _ _ f (hf : IsIso f)
  have : IsIso f := hf
  infer_instance
#align algebraic_geometry.is_open_immersion_respects_iso AlgebraicGeometry.isOpenImmersion_respectsIso

theorem isOpenImmersion_isLocalAtTarget : PropertyIsLocalAtTarget @IsOpenImmersion := by
  constructor
  · exact isOpenImmersion_respectsIso
  · intros; infer_instance
  · intro X Y f 𝒰 H
    rw [isOpenImmersion_iff_stalk]
    constructor
    · apply (openEmbedding_iff_openEmbedding_of_iSup_eq_top 𝒰.iSup_opensRange f.1.base.2).mpr
      intro i
      have := ((isOpenImmersion_respectsIso.arrow_iso_iff
        (morphismRestrictOpensRange f (𝒰.map i))).mpr (H i)).1
      erw [Arrow.mk_hom, morphismRestrict_val_base] at this
      norm_cast
    · intro x
      have := Arrow.iso_w (morphismRestrictStalkMap
        f (Scheme.Hom.opensRange (𝒰.map <| 𝒰.f <| f.1.base x)) ⟨x, 𝒰.Covers _⟩)
      dsimp only [Arrow.mk_hom] at this
      rw [this]
      haveI : IsOpenImmersion (f ∣_ Scheme.Hom.opensRange (𝒰.map <| 𝒰.f <| f.1.base x)) :=
        (isOpenImmersion_respectsIso.arrow_iso_iff
          (morphismRestrictOpensRange f (𝒰.map _))).mpr (H _)
      infer_instance
#align algebraic_geometry.is_open_immersion_is_local_at_target AlgebraicGeometry.isOpenImmersion_isLocalAtTarget

theorem IsOpenImmersion.openCover_TFAE {X Y : Scheme.{u}} (f : X ⟶ Y) : List.TFAE
    [IsOpenImmersion f,
    ∃ 𝒰 : Scheme.OpenCover.{u} Y,
      ∀ i : 𝒰.J, IsOpenImmersion (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.OpenCover.{u} Y) (i : 𝒰.J),
      IsOpenImmersion (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
    ∀ U : Opens Y.carrier, IsOpenImmersion (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [IsOpenImmersion g],
      IsOpenImmersion (pullback.snd : pullback f g ⟶ _),
    ∃ (ι : Type u) (U : ι → Opens Y.carrier) (_ : iSup U = ⊤),
      ∀ i, IsOpenImmersion (f ∣_ U i)] :=
  isOpenImmersion_isLocalAtTarget.openCover_TFAE f
#align algebraic_geometry.is_open_immersion.open_cover_tfae AlgebraicGeometry.IsOpenImmersion.openCover_TFAE

theorem IsOpenImmersion.openCover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{u} Y)
    (f : X ⟶ Y) :
    IsOpenImmersion f ↔ ∀ i, IsOpenImmersion (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  isOpenImmersion_isLocalAtTarget.openCover_iff f 𝒰
#align algebraic_geometry.is_open_immersion.open_cover_iff AlgebraicGeometry.IsOpenImmersion.openCover_iff

theorem isOpenImmersion_stableUnderBaseChange :
    MorphismProperty.StableUnderBaseChange @IsOpenImmersion :=
  MorphismProperty.StableUnderBaseChange.mk isOpenImmersion_respectsIso <| by
    intro X Y Z f g H; infer_instance
#align algebraic_geometry.is_open_immersion_stable_under_base_change AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange

end AlgebraicGeometry
