/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.morphisms.open_immersion
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.LocalAtTarget
import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!

# Open immersions

A morphism is an open immersions if the underlying map of spaces is an open embedding
`f : X ⟶ U ⊆ Y`, and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Most of the theories are developed in `algebraic_geometry/open_immersion`, and we provide the
remaining theorems analogous to other lemmas in `algebraic_geometry/morphisms/*`.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem isOpenImmersionCat_iff_stalk {f : X ⟶ Y} :
    IsOpenImmersionCat f ↔ OpenEmbedding f.1.base ∧ ∀ x, IsIso (PresheafedSpace.stalkMap f.1 x) :=
  by
  constructor
  · intro h; exact ⟨h.1, inferInstance⟩
  · rintro ⟨h₁, h₂⟩; exact is_open_immersion.of_stalk_iso f h₁
#align algebraic_geometry.is_open_immersion_iff_stalk AlgebraicGeometry.isOpenImmersionCat_iff_stalk

theorem isOpenImmersionCat_stableUnderComposition :
    MorphismProperty.StableUnderComposition @IsOpenImmersionCat := by intro X Y Z f g h₁ h₂;
  infer_instance
#align algebraic_geometry.is_open_immersion_stable_under_composition AlgebraicGeometry.isOpenImmersionCat_stableUnderComposition

theorem isOpenImmersionCat_respectsIso : MorphismProperty.RespectsIso @IsOpenImmersionCat := by
  apply is_open_immersion_stable_under_composition.respects_iso
  intro _ _ _; infer_instance
#align algebraic_geometry.is_open_immersion_respects_iso AlgebraicGeometry.isOpenImmersionCat_respectsIso

theorem isOpenImmersionCat_is_local_at_target : PropertyIsLocalAtTarget @IsOpenImmersionCat := by
  constructor
  · exact is_open_immersion_respects_iso
  · intros; infer_instance
  · intro X Y f 𝒰 H
    rw [is_open_immersion_iff_stalk]
    constructor
    · apply (openEmbedding_iff_openEmbedding_of_iSup_eq_top 𝒰.supr_opens_range f.1.base.2).mpr
      intro i
      have :=
        ((is_open_immersion_respects_iso.arrow_iso_iff
                (morphism_restrict_opens_range f (𝒰.map i))).mpr
            (H i)).1
      rwa [arrow.mk_hom, morphism_restrict_val_base] at this 
    · intro x
      have :=
        arrow.iso_w
          (morphism_restrict_stalk_map f (𝒰.map <| 𝒰.f <| f.1 x).opensRange ⟨x, 𝒰.covers _⟩)
      dsimp only [arrow.mk_hom] at this 
      rw [this]
      haveI : is_open_immersion (f ∣_ (𝒰.map <| 𝒰.f <| f.1 x).opensRange) :=
        (is_open_immersion_respects_iso.arrow_iso_iff
              (morphism_restrict_opens_range f (𝒰.map _))).mpr
          (H _)
      infer_instance
#align algebraic_geometry.is_open_immersion_is_local_at_target AlgebraicGeometry.isOpenImmersionCat_is_local_at_target

theorem IsOpenImmersionCat.openCover_tFAE {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TFAE
      [IsOpenImmersionCat f,
        ∃ 𝒰 : Scheme.OpenCover.{u} Y,
          ∀ i : 𝒰.J, IsOpenImmersionCat (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ (𝒰 : Scheme.OpenCover.{u} Y) (i : 𝒰.J),
          IsOpenImmersionCat (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ U : Opens Y.carrier, IsOpenImmersionCat (f ∣_ U),
        ∀ {U : Scheme} (g : U ⟶ Y) [IsOpenImmersionCat g],
          IsOpenImmersionCat (pullback.snd : pullback f g ⟶ _),
        ∃ (ι : Type u) (U : ι → Opens Y.carrier) (hU : iSup U = ⊤),
          ∀ i, IsOpenImmersionCat (f ∣_ U i)] :=
  isOpenImmersionCat_is_local_at_target.openCover_TFAE f
#align algebraic_geometry.is_open_immersion.open_cover_tfae AlgebraicGeometry.IsOpenImmersionCat.openCover_tFAE

theorem IsOpenImmersionCat.openCover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{u} Y)
    (f : X ⟶ Y) :
    IsOpenImmersionCat f ↔ ∀ i, IsOpenImmersionCat (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  isOpenImmersionCat_is_local_at_target.openCover_iff f 𝒰
#align algebraic_geometry.is_open_immersion.open_cover_iff AlgebraicGeometry.IsOpenImmersionCat.openCover_iff

theorem isOpenImmersionCat_stableUnderBaseChange :
    MorphismProperty.StableUnderBaseChange @IsOpenImmersionCat :=
  MorphismProperty.StableUnderBaseChange.mk isOpenImmersionCat_respectsIso <| by intro X Y Z f g H;
    infer_instance
#align algebraic_geometry.is_open_immersion_stable_under_base_change AlgebraicGeometry.isOpenImmersionCat_stableUnderBaseChange

end AlgebraicGeometry

