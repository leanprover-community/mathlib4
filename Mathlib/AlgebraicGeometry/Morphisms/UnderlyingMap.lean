/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.LocalAtTarget
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors

/-!

## Properties on the underlying functions of morphisms of schemes.

This file includes various results on properties of morphisms of schemes that come from properties
of the underlying map of topological spaces, including

- `Injective`
- `Surjective`
- `IsOpenMap`
- `IsClosedMap`
- `GeneralizingMap`
- `IsEmbedding`
- `IsOpenEmbedding`
- `IsClosedEmbedding`
- `DenseRange` (`IsDominant`)

-/

@[expose] public section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u v

section Injective

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

instance : MorphismProperty.RespectsIso (topologically Function.Injective) :=
  topologically_respectsIso _ (fun e ↦ e.injective) (fun _ _ hf hg ↦ hg.comp hf)

instance injective_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically Function.Injective) := by
  refine topologically_isZariskiLocalAtTarget _ (fun _ s _ _ h ↦ h.restrictPreimage s)
    fun f ι U H _ hf x₁ x₂ e ↦ ?_
  obtain ⟨i, hxi⟩ : ∃ i, f x₁ ∈ U i := by simpa using congr(f x₁ ∈ $H)
  exact congr(($(@hf i ⟨x₁, hxi⟩ ⟨x₂, show f x₂ ∈ U i from e ▸ hxi⟩ (Subtype.ext e))).1)

end Injective

section Surjective

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes is surjective if the underlying map is. -/
@[mk_iff]
class Surjective : Prop where
  surj : Function.Surjective f

lemma surjective_eq_topologically :
    @Surjective = topologically Function.Surjective := by ext; exact surjective_iff _

lemma Scheme.Hom.surjective (f : X ⟶ Y) [Surjective f] : Function.Surjective f :=
  Surjective.surj

instance (priority := 100) [IsIso f] : Surjective f := ⟨f.homeomorph.surjective⟩

instance [Surjective f] [Surjective g] : Surjective (f ≫ g) := ⟨g.surjective.comp f.surjective⟩

lemma Surjective.of_comp [Surjective (f ≫ g)] : Surjective g where
  surj := Function.Surjective.of_comp (g := f) (f ≫ g).surjective

lemma Surjective.comp_iff [Surjective f] : Surjective (f ≫ g) ↔ Surjective g :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

instance : MorphismProperty.IsStableUnderComposition @Surjective.{u} where
  comp_mem _ _ hf hg := ⟨hg.1.comp hf.1⟩

instance : MorphismProperty.RespectsIso @Surjective :=
  surjective_eq_topologically ▸ topologically_respectsIso _ (fun e ↦ e.surjective)
    (fun _ _ hf hg ↦ hg.comp hf)

instance (P : MorphismProperty Scheme.{u}) :
    MorphismProperty.HasOfPrecompProperty @Surjective P where
  of_precomp f g _ _ := .of_comp f g

instance surjective_isZariskiLocalAtTarget : IsZariskiLocalAtTarget @Surjective := by
  have : MorphismProperty.RespectsIso @Surjective := inferInstance
  rw [surjective_eq_topologically] at this ⊢
  refine topologically_isZariskiLocalAtTarget _ (fun _ s _ _ h ↦ h.restrictPreimage s) ?_
  intro α β _ _ f ι U H _ hf x
  obtain ⟨i, hxi⟩ : ∃ i, x ∈ U i := by simpa using congr(x ∈ $H)
  obtain ⟨⟨y, _⟩, hy⟩ := hf i ⟨x, hxi⟩
  exact ⟨y, congr(($hy).1)⟩

@[simp]
lemma range_eq_univ [Surjective f] : Set.range f = Set.univ := by
  simpa [Set.range_eq_univ] using f.surjective

lemma range_eq_range_of_surjective {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : X ⟶ Y)
    [Surjective e] (hge : e ≫ g = f) : Set.range f = Set.range g := by
  rw [← hge]
  simp [Set.range_comp]

lemma mem_range_iff_of_surjective {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : X ⟶ Y)
    [Surjective e] (hge : e ≫ g = f) (s : S) : s ∈ Set.range f ↔ s ∈ Set.range g := by
  rw [range_eq_range_of_surjective f g e hge]

lemma Surjective.sigmaDesc_of_union_range_eq_univ {X : Scheme.{u}}
    {ι : Type v} [Small.{u} ι] {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ X}
    (H : ⋃ i, Set.range (f i) = Set.univ) : Surjective (Limits.Sigma.desc f) := by
  refine ⟨fun x ↦ ?_⟩
  simp_rw [Set.eq_univ_iff_forall, Set.mem_iUnion] at H
  obtain ⟨i, x, rfl⟩ := H x
  use Limits.Sigma.ι Y i x
  rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc]

instance {X : Scheme.{u}} {P : MorphismProperty Scheme.{u}} (𝒰 : X.Cover (Scheme.precoverage P)) :
    Surjective (Limits.Sigma.desc fun i ↦ 𝒰.f i) :=
  Surjective.sigmaDesc_of_union_range_eq_univ 𝒰.iUnion_range

/-- The single object covering by one surjective morphism satisfying `P`. -/
@[simps! I₀ X f]
def Scheme.Hom.cover {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f)
    [Surjective f] : Cover.{v} (precoverage P) S :=
  .singleton f <| by
    rw [singleton_mem_precoverage_iff]
    exact ⟨f.surjective, hf⟩

@[simp]
lemma Scheme.Hom.presieve₀_cover {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : P f) [Surjective f] : (f.cover hf).presieve₀ = Presieve.singleton f := by
  simp [cover]

instance {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f)
    [Surjective f] : Unique (Scheme.Hom.cover f hf).I₀ :=
  inferInstanceAs <| Unique PUnit

end Surjective

section Injective

instance injective_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (topologically (Function.Injective ·)) where
  comp_mem _ _ hf hg := hg.comp hf

end Injective

section IsOpenMap

instance : (topologically IsOpenMap).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isOpenMap) (fun _ _ hf hg ↦ hg.comp hf)

instance isOpenMap_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically IsOpenMap) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU _ ↦ hU.isOpenMap_iff_restrictPreimage

instance : IsZariskiLocalAtSource (topologically IsOpenMap) :=
  topologically_isZariskiLocalAtSource' (fun _ ↦ _) fun _ _ _ hU _ ↦ hU.isOpenMap_iff_comp

end IsOpenMap

section IsClosedMap

instance : (topologically IsClosedMap).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isClosedMap) (fun _ _ hf hg ↦ hg.comp hf)

instance isClosedMap_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically IsClosedMap) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU _ ↦ hU.isClosedMap_iff_restrictPreimage

end IsClosedMap

section IsEmbedding

instance : (topologically IsEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isEmbedding) (fun _ _ hf hg ↦ hg.comp hf)

instance isEmbedding_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically IsEmbedding) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU ↦ hU.isEmbedding_iff_restrictPreimage

end IsEmbedding

section IsOpenEmbedding

instance : (topologically IsOpenEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isOpenEmbedding) (fun _ _ hf hg ↦ hg.comp hf)

instance isOpenEmbedding_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically IsOpenEmbedding) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU ↦ hU.isOpenEmbedding_iff_restrictPreimage

end IsOpenEmbedding

section IsClosedEmbedding

instance : (topologically IsClosedEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isClosedEmbedding) (fun _ _ hf hg ↦ hg.comp hf)

instance isClosedEmbedding_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically IsClosedEmbedding) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU ↦ hU.isClosedEmbedding_iff_restrictPreimage

end IsClosedEmbedding

section IsDominant

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes is dominant if the underlying map has dense range. -/
@[mk_iff]
class IsDominant : Prop where
  denseRange : DenseRange f

lemma dominant_eq_topologically :
    @IsDominant = topologically DenseRange := by ext; exact isDominant_iff _

lemma Scheme.Hom.denseRange (f : X ⟶ Y) [IsDominant f] : DenseRange f :=
  IsDominant.denseRange

instance (priority := 100) [Surjective f] : IsDominant f := ⟨f.surjective.denseRange⟩

instance [IsDominant f] [IsDominant g] : IsDominant (f ≫ g) :=
  ⟨g.denseRange.comp f.denseRange g.continuous⟩

instance : MorphismProperty.IsMultiplicative @IsDominant where
  id_mem := fun _ ↦ inferInstance
  comp_mem := fun _ _ _ _ ↦ inferInstance

lemma IsDominant.of_comp [H : IsDominant (f ≫ g)] : IsDominant g := by
  rw [isDominant_iff, denseRange_iff_closure_range, ← Set.univ_subset_iff] at H ⊢
  exact H.trans (closure_mono (Set.range_comp_subset_range f g))

lemma IsDominant.comp_iff [IsDominant f] : IsDominant (f ≫ g) ↔ IsDominant g :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

instance IsDominant.respectsIso : MorphismProperty.RespectsIso @IsDominant :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦ inferInstance

instance IsDominant.isZariskiLocalAtTarget : IsZariskiLocalAtTarget @IsDominant :=
  have : MorphismProperty.RespectsIso (topologically DenseRange) :=
    dominant_eq_topologically ▸ IsDominant.respectsIso
  dominant_eq_topologically ▸ topologically_isZariskiLocalAtTarget' DenseRange
    fun _ _ _ hU _ ↦ hU.denseRange_iff_restrictPreimage

lemma surjective_of_isDominant_of_isClosed_range (f : X ⟶ Y) [IsDominant f]
    (hf : IsClosed (Set.range f)) :
    Surjective f :=
  ⟨by rw [← Set.range_eq_univ, ← hf.closure_eq, f.denseRange.closure_range]⟩

lemma IsDominant.of_comp_of_isOpenImmersion
    (f : X ⟶ Y) (g : Y ⟶ Z) [H : IsDominant (f ≫ g)] [IsOpenImmersion g] :
    IsDominant f := by
  rw [isDominant_iff, DenseRange] at H ⊢
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] at H
  convert H.preimage g.isOpenEmbedding.isOpenMap using 1
  rw [Set.preimage_image_eq _ g.isOpenEmbedding.injective]

end IsDominant

section SpecializingMap

open TopologicalSpace

instance specializingMap_respectsIso : (topologically @SpecializingMap).RespectsIso := by
  apply topologically_respectsIso
  · introv
    exact f.isClosedMap.specializingMap
  · introv hf hg
    exact hf.comp hg

instance specializingMap_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically @SpecializingMap) := by
  apply topologically_isZariskiLocalAtTarget
  · introv _ _ hf
    rw [specializingMap_iff_closure_singleton_subset] at hf ⊢
    intro ⟨x, hx⟩ ⟨y, hy⟩ hcl
    simp only [closure_subtype, Set.restrictPreimage_mk, Set.image_singleton] at hcl
    obtain ⟨a, ha, hay⟩ := hf x hcl
    rw [← specializes_iff_mem_closure] at hcl
    exact ⟨⟨a, by simp [hay, hy]⟩, by simpa [closure_subtype], by simpa⟩
  · introv hU _ hsp
    simp_rw [specializingMap_iff_closure_singleton_subset] at hsp ⊢
    intro x y hy
    have : ∃ i, y ∈ U i := Opens.mem_iSup.mp (hU ▸ Opens.mem_top _)
    obtain ⟨i, hi⟩ := this
    rw [← specializes_iff_mem_closure] at hy
    have hfx : f x ∈ U i := (U i).2.stableUnderGeneralization hy hi
    have hy : (⟨y, hi⟩ : U i) ∈ closure {⟨f x, hfx⟩} := by
      simp only [closure_subtype, Set.image_singleton]
      rwa [← specializes_iff_mem_closure]
    obtain ⟨a, ha, hay⟩ := hsp i ⟨x, hfx⟩ hy
    rw [closure_subtype] at ha
    simp only [Opens.carrier_eq_coe, Set.image_singleton] at ha
    apply_fun Subtype.val at hay
    simp only [Opens.carrier_eq_coe, Set.restrictPreimage_coe] at hay
    use a.val, ha, hay

end SpecializingMap

section GeneralizingMap

instance : (topologically GeneralizingMap).RespectsIso :=
  topologically_respectsIso _ (fun f ↦ f.isOpenEmbedding.generalizingMap
    f.isOpenEmbedding.isOpen_range.stableUnderGeneralization) (fun _ _ hf hg ↦ hf.comp hg)

instance : IsZariskiLocalAtSource (topologically GeneralizingMap) :=
  topologically_isZariskiLocalAtSource' (fun _ ↦ _) fun _ _ _ hU _ ↦ hU.generalizingMap_iff_comp

instance : IsZariskiLocalAtTarget (topologically GeneralizingMap) :=
  topologically_isZariskiLocalAtTarget' (fun _ ↦ _) fun _ _ _ hU _ ↦
    hU.generalizingMap_iff_restrictPreimage

end GeneralizingMap

end AlgebraicGeometry
