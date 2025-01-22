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
- `IsEmbedding`
- `IsOpenEmbedding`
- `IsClosedEmbedding`
- `DenseRange` (`IsDominant`)

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

section IsEmbedding

instance : (topologically IsEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isEmbedding) (fun _ _ hf hg ↦ hg.comp hf)

instance isEmbedding_isLocalAtTarget : IsLocalAtTarget (topologically IsEmbedding) :=
  topologically_isLocalAtTarget' _ fun _ _ _ ↦ isEmbedding_iff_of_iSup_eq_top

end IsEmbedding

section IsOpenEmbedding

instance : (topologically IsOpenEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isOpenEmbedding) (fun _ _ hf hg ↦ hg.comp hf)

instance isOpenEmbedding_isLocalAtTarget : IsLocalAtTarget (topologically IsOpenEmbedding) :=
  topologically_isLocalAtTarget' _ fun _ _ _ ↦ isOpenEmbedding_iff_isOpenEmbedding_of_iSup_eq_top

end IsOpenEmbedding

section IsClosedEmbedding

instance : (topologically IsClosedEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isClosedEmbedding) (fun _ _ hf hg ↦ hg.comp hf)

instance isClosedEmbedding_isLocalAtTarget : IsLocalAtTarget (topologically IsClosedEmbedding) :=
  topologically_isLocalAtTarget' _
    fun _ _ _ ↦ isClosedEmbedding_iff_isClosedEmbedding_of_iSup_eq_top

end IsClosedEmbedding

section IsDominant

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes is dominant if the underlying map has dense range. -/
@[mk_iff]
class IsDominant : Prop where
  denseRange : DenseRange f.base

lemma dominant_eq_topologically :
    @IsDominant = topologically DenseRange := by ext; exact isDominant_iff _

lemma Scheme.Hom.denseRange (f : X.Hom Y) [IsDominant f] : DenseRange f.base :=
  IsDominant.denseRange

instance (priority := 100) [Surjective f] : IsDominant f := ⟨f.surjective.denseRange⟩

instance [IsDominant f] [IsDominant g] : IsDominant (f ≫ g) :=
  ⟨g.denseRange.comp f.denseRange g.base.2⟩

instance : MorphismProperty.IsMultiplicative @IsDominant where
  id_mem := fun _ ↦ inferInstance
  comp_mem := fun _ _ _ _ ↦ inferInstance

lemma IsDominant.of_comp [H : IsDominant (f ≫ g)] : IsDominant g := by
  rw [isDominant_iff, denseRange_iff_closure_range, ← Set.univ_subset_iff] at H ⊢
  exact H.trans (closure_mono (Set.range_comp_subset_range f.base g.base))

lemma IsDominant.comp_iff [IsDominant f] : IsDominant (f ≫ g) ↔ IsDominant g :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

instance IsDominant.respectsIso : MorphismProperty.RespectsIso @IsDominant :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦ inferInstance

instance IsDominant.isLocalAtTarget : IsLocalAtTarget @IsDominant :=
  have : MorphismProperty.RespectsIso (topologically DenseRange) :=
    dominant_eq_topologically ▸ IsDominant.respectsIso
  dominant_eq_topologically ▸ topologically_isLocalAtTarget' DenseRange
    fun _ _ _ hU _ ↦ denseRange_iff_denseRange_of_iSup_eq_top hU

lemma surjective_of_isDominant_of_isClosed_range (f : X ⟶ Y) [IsDominant f]
    (hf : IsClosed (Set.range f.base)) :
    Surjective f :=
  ⟨by rw [← Set.range_iff_surjective, ← hf.closure_eq, f.denseRange.closure_range]⟩

lemma IsDominant.of_comp_of_isOpenImmersion
    (f : X ⟶ Y) (g : Y ⟶ Z) [H : IsDominant (f ≫ g)] [IsOpenImmersion g] :
    IsDominant f := by
  rw [isDominant_iff, DenseRange] at H ⊢
  simp only [Scheme.comp_coeBase, TopCat.coe_comp, Set.range_comp] at H
  convert H.preimage g.isOpenEmbedding.isOpenMap using 1
  rw [Set.preimage_image_eq _ g.isOpenEmbedding.inj]

end IsDominant

end AlgebraicGeometry
