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

instance isOpenImmersion_respectsIso : MorphismProperty.RespectsIso @IsOpenImmersion := by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro _ _ f (hf : IsIso f)
  have : IsIso f := hf
  infer_instance
#align algebraic_geometry.is_open_immersion_respects_iso AlgebraicGeometry.isOpenImmersion_respectsIso

instance isOpenImmersion_isLocalAtTarget : IsLocalAtTarget @IsOpenImmersion := by
  apply IsLocalAtTarget.mk'
  · intros; infer_instance
  · intro X Y f ι U hU H
    rw [isOpenImmersion_iff_stalk]
    constructor
    · apply (openEmbedding_iff_openEmbedding_of_iSup_eq_top hU f.1.base.2).mpr
      intro i
      have := (f ∣_ U i).openEmbedding
      rw [morphismRestrict_val_base] at this
      norm_cast
    · intro x
      obtain ⟨i, hi⟩ : ∃ i, f.1.base x ∈ U i := by
        simpa only [← SetLike.mem_coe, Opens.coe_iSup, Set.mem_iUnion, Opens.coe_top, Set.mem_univ,
          eq_iff_iff, iff_true] using congr(f.1.base x ∈ $hU)
      have := Arrow.iso_w (morphismRestrictStalkMap
        f (Scheme.ιOpens (U i)).opensRange ⟨x, ⟨_, hi⟩, rfl⟩)
      dsimp only [Arrow.mk_hom] at this
      rw [this]
      haveI : IsOpenImmersion (f ∣_ (Scheme.ιOpens (U i)).opensRange) := by
        rw [opensRange_ιOpens]
        infer_instance
      infer_instance
#align algebraic_geometry.is_open_immersion_is_local_at_target AlgebraicGeometry.isOpenImmersion_isLocalAtTarget

theorem isOpenImmersion_stableUnderBaseChange :
    MorphismProperty.StableUnderBaseChange @IsOpenImmersion :=
  MorphismProperty.StableUnderBaseChange.mk <| by
    intro X Y Z f g H; infer_instance
#align algebraic_geometry.is_open_immersion_stable_under_base_change AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange

lemma isomorphisms_isLocalAtTarget :
    PropertyIsLocalAtTarget (MorphismProperty.isomorphisms _) := by
  constructor
  · exact MorphismProperty.RespectsIso.isomorphisms _
  · rintro X Y f U h
    have : IsIso f := h
    delta morphismRestrict MorphismProperty.isomorphisms
    infer_instance
  · intros X Y f 𝒰 h
    simp only [MorphismProperty.isomorphisms] at h
    have h := h -- why?
    rw [MorphismProperty.isomorphisms, isIso_iff_isOpenImmersion,
      IsOpenImmersion.openCover_iff 𝒰, TopCat.epi_iff_surjective]
    refine ⟨fun _ ↦ inferInstance, fun x ↦ ?_⟩
    obtain ⟨y, e⟩ := 𝒰.covers x
    use (inv (Limits.pullback.snd (f := f) (g := 𝒰.map (𝒰.f x))) ≫ Limits.pullback.fst).1.base y
    rwa [← Scheme.comp_val_base_apply, Category.assoc, Limits.pullback.condition,
      IsIso.inv_hom_id_assoc]

end AlgebraicGeometry
