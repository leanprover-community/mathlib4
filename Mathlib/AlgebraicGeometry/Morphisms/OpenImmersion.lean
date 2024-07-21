/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

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

theorem isOpenImmersion_eq_inf :
    @IsOpenImmersion = (topologically OpenEmbedding) ⊓
      stalkwise (fun f ↦ Function.Bijective f) := by
  ext
  exact isOpenImmersion_iff_stalk.trans
    (and_congr Iff.rfl (forall_congr' fun x ↦ ConcreteCategory.isIso_iff_bijective _))

instance isOpenImmersion_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @IsOpenImmersion where
  comp_mem f g _ _ := LocallyRingedSpace.IsOpenImmersion.comp f g

instance isOpenImmersion_respectsIso : MorphismProperty.RespectsIso @IsOpenImmersion := by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro _ _ f (hf : IsIso f)
  have : IsIso f := hf
  infer_instance

instance : IsLocalAtTarget (stalkwise (fun f ↦ Function.Bijective f)) := by
  apply stalkwiseIsLocalAtTarget_of_respectsIso
  rw [RingHom.toMorphismProperty_respectsIso_iff]
  convert (inferInstanceAs (MorphismProperty.isomorphisms CommRingCat).RespectsIso)
  ext
  exact (ConcreteCategory.isIso_iff_bijective _).symm

instance isOpenImmersion_isLocalAtTarget : IsLocalAtTarget @IsOpenImmersion :=
  isOpenImmersion_eq_inf ▸ inferInstance

theorem isOpenImmersion_stableUnderBaseChange :
    MorphismProperty.StableUnderBaseChange @IsOpenImmersion :=
  MorphismProperty.StableUnderBaseChange.mk <| by
    intro X Y Z f g H; infer_instance

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
