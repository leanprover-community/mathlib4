/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.LocalAtTarget
import Mathlib.AlgebraicGeometry.Morphisms.Constructors

/-!

## Properties on the underlying functions of morphisms of schemes.

This file includes various results on properties of morphisms of schemes that come from properties
of the underlying map of topological spaces, including

- `Injective`
- `Surjective`
- `IsOpenMap`
- `IsClosedMap`
- `Embedding`
- `IsOpenEmbedding`
- `ClosedEmbedding`
- `DenseRange` (`Dominant`)

-/

open CategoryTheory

namespace AlgebraicGeometry

universe u

section Injective

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

instance : MorphismProperty.RespectsIso (topologically Function.Injective) :=
  topologically_respectsIso _ (fun e ↦ e.injective) (fun _ _ hf hg ↦ hg.comp hf)

instance injective_isLocalAtTarget : IsLocalAtTarget (topologically Function.Injective) := by
  refine topologically_isLocalAtTarget _ (fun _ s _ _ h ↦ h.restrictPreimage s)
    fun f ι U H _ hf x₁ x₂ e ↦ ?_
  obtain ⟨i, hxi⟩ : ∃ i, f x₁ ∈ U i := by simpa using congr(f x₁ ∈ $H)
  exact congr(($(@hf i ⟨x₁, hxi⟩ ⟨x₂, show f x₂ ∈ U i from e ▸ hxi⟩ (Subtype.ext e))).1)

end Injective

section Surjective

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes is surjective if the underlying map is. -/
@[mk_iff]
class Surjective : Prop where
  surj : Function.Surjective f.base

lemma surjective_eq_topologically :
    @Surjective = topologically Function.Surjective := by ext; exact surjective_iff _

lemma Scheme.Hom.surjective (f : X.Hom Y) [Surjective f] : Function.Surjective f.base :=
  Surjective.surj

instance (priority := 100) [IsIso f] : Surjective f := ⟨f.homeomorph.surjective⟩

instance [Surjective f] [Surjective g] : Surjective (f ≫ g) := ⟨g.surjective.comp f.surjective⟩

lemma Surjective.of_comp [Surjective (f ≫ g)] : Surjective g where
  surj := Function.Surjective.of_comp (g := f.base) (f ≫ g).surjective

lemma Surjective.comp_iff [Surjective f] : Surjective (f ≫ g) ↔ Surjective g :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

instance : MorphismProperty.RespectsIso @Surjective :=
  surjective_eq_topologically ▸ topologically_respectsIso _ (fun e ↦ e.surjective)
    (fun _ _ hf hg ↦ hg.comp hf)

instance surjective_isLocalAtTarget : IsLocalAtTarget @Surjective := by
  have : MorphismProperty.RespectsIso @Surjective := inferInstance
  rw [surjective_eq_topologically] at this ⊢
  refine topologically_isLocalAtTarget _ (fun _ s _ _ h ↦ h.restrictPreimage s) ?_
  intro α β _ _ f ι U H _ hf x
  obtain ⟨i, hxi⟩ : ∃ i, x ∈ U i := by simpa using congr(x ∈ $H)
  obtain ⟨⟨y, _⟩, hy⟩ := hf i ⟨x, hxi⟩
  exact ⟨y, congr(($hy).1)⟩

end Surjective

section IsOpenMap

instance : (topologically IsOpenMap).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isOpenMap) (fun _ _ hf hg ↦ hg.comp hf)

instance isOpenMap_isLocalAtTarget : IsLocalAtTarget (topologically IsOpenMap) :=
  topologically_isLocalAtTarget' _ fun _ _ _ hU _ ↦ isOpenMap_iff_isOpenMap_of_iSup_eq_top hU

end IsOpenMap

section IsClosedMap

instance : (topologically IsClosedMap).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isClosedMap) (fun _ _ hf hg ↦ hg.comp hf)

instance isClosedMap_isLocalAtTarget : IsLocalAtTarget (topologically IsClosedMap) :=
  topologically_isLocalAtTarget' _ fun _ _ _ hU _ ↦ isClosedMap_iff_isClosedMap_of_iSup_eq_top hU

end IsClosedMap

section Embedding

instance : (topologically Embedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.embedding) (fun _ _ hf hg ↦ hg.comp hf)

instance embedding_isLocalAtTarget : IsLocalAtTarget (topologically Embedding) :=
  topologically_isLocalAtTarget' _ fun _ _ _ ↦ embedding_iff_embedding_of_iSup_eq_top

end Embedding

section IsOpenEmbedding

instance : (topologically IsOpenEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isOpenEmbedding) (fun _ _ hf hg ↦ hg.comp hf)

instance isOpenEmbedding_isLocalAtTarget : IsLocalAtTarget (topologically IsOpenEmbedding) :=
  topologically_isLocalAtTarget' _ fun _ _ _ ↦ isOpenEmbedding_iff_isOpenEmbedding_of_iSup_eq_top

end IsOpenEmbedding

section ClosedEmbedding

instance : (topologically ClosedEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.closedEmbedding) (fun _ _ hf hg ↦ hg.comp hf)

instance closedEmbedding_isLocalAtTarget : IsLocalAtTarget (topologically ClosedEmbedding) :=
  topologically_isLocalAtTarget' _ fun _ _ _ ↦ closedEmbedding_iff_closedEmbedding_of_iSup_eq_top

end ClosedEmbedding

section Dominant

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes is dominant if the underlying map has dense range. -/
@[mk_iff]
class Dominant : Prop where
  denseRange : DenseRange f.base

lemma dominant_eq_topologically :
    @Dominant = topologically DenseRange := by ext; exact dominant_iff _

lemma Scheme.Hom.denseRange (f : X.Hom Y) [Dominant f] : DenseRange f.base :=
  Dominant.denseRange

instance (priority := 100) [Surjective f] : Dominant f := ⟨f.surjective.denseRange⟩

instance [Dominant f] [Dominant g] : Dominant (f ≫ g) := ⟨g.denseRange.comp f.denseRange g.base.2⟩

instance : MorphismProperty.IsStableUnderComposition @Dominant := ⟨fun _ _ _ _ ↦ inferInstance⟩

lemma Dominant.of_comp [H : Dominant (f ≫ g)] : Dominant g := by
  rw [dominant_iff, denseRange_iff_closure_range, ← Set.univ_subset_iff] at H ⊢
  exact H.trans (closure_mono (Set.range_comp_subset_range f.base g.base))

lemma Dominant.comp_iff [Dominant f] : Dominant (f ≫ g) ↔ Dominant g :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

instance : MorphismProperty.RespectsIso @Dominant :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦ inferInstance

instance Dominant.isLocalAtTarget : IsLocalAtTarget @Dominant :=
  have : MorphismProperty.RespectsIso (topologically DenseRange) :=
    dominant_eq_topologically ▸ instRespectsIsoSchemeDominant
  dominant_eq_topologically ▸ topologically_isLocalAtTarget' DenseRange
    fun _ _ _ hU _ ↦ denseRange_iff_denseRange_of_iSup_eq_top hU

end Dominant

end AlgebraicGeometry
