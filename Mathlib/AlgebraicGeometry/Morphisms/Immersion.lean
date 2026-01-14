/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!

# Immersions of schemes

A morphism of schemes `f : X ⟶ Y` is an immersion if the underlying map of topological spaces
is a locally closed embedding, and the induced morphisms of stalks are all surjective. This is true
if and only if it can be factored into a closed immersion followed by an open immersion.

# Main result
- `isImmersion_iff_exists`:
  A morphism is a (locally-closed) immersion if and only if it can be factored into
  a closed immersion followed by a (dominant) open immersion.

-/

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is an immersion if
1. the underlying map of topological spaces is an embedding
2. the range of the map is locally closed
3. the induced morphisms of stalks are all surjective. -/
@[mk_iff]
class IsImmersion (f : X ⟶ Y) : Prop extends IsPreimmersion f where
  isLocallyClosed_range : IsLocallyClosed (Set.range f.base)

lemma Scheme.Hom.isLocallyClosed_range (f : X.Hom Y) [IsImmersion f] :
    IsLocallyClosed (Set.range f.base) :=
  IsImmersion.isLocallyClosed_range

/--
Given an immersion `f : X ⟶ Y`, this is the biggest open set `U ⊆ Y` containing the image of `X`
such that `X` is closed in `U`.
-/
def Scheme.Hom.coborderRange (f : X.Hom Y) [IsImmersion f] : Y.Opens :=
  ⟨coborder (Set.range f.base), f.isLocallyClosed_range.isOpen_coborder⟩

/--
The first part of the factorization of an immersion `f : X ⟶ Y` to a closed immersion
`f.liftCoborder : X ⟶ f.coborderRange` and a dominant open immersion `f.coborderRange.ι`.
-/
noncomputable
def Scheme.Hom.liftCoborder (f : X.Hom Y) [IsImmersion f] : X ⟶ f.coborderRange :=
  IsOpenImmersion.lift f.coborderRange.ι f (by simpa using subset_coborder)

/--
Any (locally-closed) immersion can be factored into
a closed immersion followed by a (dominant) open immersion.
-/
@[reassoc (attr := simp)]
lemma Scheme.Hom.liftCoborder_ι (f : X.Hom Y) [IsImmersion f] :
    f.liftCoborder ≫ f.coborderRange.ι = f :=
  IsOpenImmersion.lift_fac _ _ _

instance [IsImmersion f] : IsClosedImmersion f.liftCoborder := by
  have : IsPreimmersion (f.liftCoborder ≫ f.coborderRange.ι) := by
    simp only [Scheme.Hom.liftCoborder_ι]; infer_instance
  have : IsPreimmersion f.liftCoborder := .of_comp f.liftCoborder f.coborderRange.ι
  refine .of_isPreimmersion _ ?_
  convert isClosed_preimage_val_coborder
  apply Set.image_injective.mpr f.coborderRange.ι.isEmbedding.injective
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.comp_base, f.liftCoborder_ι]
  exact (Set.image_preimage_eq_of_subset (by simpa using subset_coborder)).symm

instance [IsImmersion f] : IsDominant f.coborderRange.ι := by
  rw [isDominant_iff, DenseRange, Scheme.Opens.range_ι]
  exact dense_coborder

lemma isImmersion_eq_inf : @IsImmersion = (@IsPreimmersion ⊓
    topologically fun {_ _} _ _ f ↦ IsLocallyClosed (Set.range f) : MorphismProperty Scheme) := by
  ext; exact isImmersion_iff _

namespace IsImmersion

instance : IsLocalAtTarget @IsImmersion := by
  suffices IsLocalAtTarget (topologically fun {X Y} _ _ f ↦ IsLocallyClosed (Set.range f)) from
    isImmersion_eq_inf ▸ inferInstance
  apply (config := { allowSynthFailures := true }) topologically_isLocalAtTarget'
  · refine { precomp := ?_, postcomp := ?_ }
    · intro X Y Z i hi f hf
      change IsIso i at hi
      change IsLocallyClosed _
      simpa only [Scheme.comp_coeBase, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr i.surjective, Set.image_univ]
    · intro X Y Z i hi f hf
      change IsIso i at hi
      change IsLocallyClosed _
      simp only [Scheme.comp_coeBase, TopCat.coe_comp, Set.range_comp]
      refine hf.image i.homeomorph.isInducing ?_
      rw [Set.range_eq_univ.mpr i.surjective]
      exact isOpen_univ.isLocallyClosed
  · simp_rw [Set.range_restrictPreimage]
    exact fun _ _ _ hU _ ↦ hU.isLocallyClosed_iff_coe_preimage

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] : IsImmersion f where
  isLocallyClosed_range := f.isOpenEmbedding.2.isLocallyClosed

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] : IsImmersion f where
  isLocallyClosed_range := f.isClosedEmbedding.2.isLocallyClosed

instance : MorphismProperty.IsMultiplicative @IsImmersion where
  id_mem _ := inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine { __ := inferInstanceAs (IsPreimmersion (f ≫ g)), isLocallyClosed_range := ?_ }
    simp only [Scheme.comp_coeBase, TopCat.coe_comp, Set.range_comp]
    exact f.isLocallyClosed_range.image g.isEmbedding.isInducing g.isLocallyClosed_range

instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion f]
    [IsImmersion g] : IsImmersion (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

variable {f} in
/--
A morphism is a (locally-closed) immersion if and only if it can be factored into
a closed immersion followed by an open immersion.
-/
lemma isImmersion_iff_exists : IsImmersion f ↔ ∃ (Z : Scheme) (g₁ : X ⟶ Z) (g₂ : Z ⟶ Y),
    IsClosedImmersion g₁ ∧ IsOpenImmersion g₂ ∧ g₁ ≫ g₂ = f :=
  ⟨fun _ ↦ ⟨_, f.liftCoborder, f.coborderRange.ι, inferInstance, inferInstance, f.liftCoborder_ι⟩,
    fun ⟨_, _, _, _, _, e⟩ ↦ e ▸ inferInstance⟩

theorem of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion g]
    [IsImmersion (f ≫ g)] : IsImmersion f where
  __ := IsPreimmersion.of_comp f g
  isLocallyClosed_range := by
    rw [← Set.preimage_image_eq (Set.range _) g.isEmbedding.injective]
    have := (f ≫ g).isLocallyClosed_range.preimage g.base.hom.2
    simpa only [Scheme.comp_coeBase, TopCat.coe_comp, Set.range_comp] using this

theorem comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion g] :
    IsImmersion (f ≫ g) ↔ IsImmersion f :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsImmersion where
  of_isPullback := by
    intros X Y Y' S f g f' g' H hg
    let Z := Limits.pullback f g.coborderRange.ι
    let e : Y' ⟶ Z := Limits.pullback.lift g' (f' ≫ g.liftCoborder) (by simpa using H.w.symm)
    have : IsClosedImmersion e := by
      have := (IsPullback.paste_horiz_iff (.of_hasPullback f g.coborderRange.ι)
        (show e ≫ Limits.pullback.snd _ _ = _ from Limits.pullback.lift_snd _ _ _)).mp ?_
      · exact MorphismProperty.of_isPullback this.flip inferInstance
      · simpa [e] using H.flip
    rw [← Limits.pullback.lift_fst (f := f) (g := g.coborderRange.ι) g' (f' ≫ g.liftCoborder)
      (by simpa using H.w.symm)]
    infer_instance

open Limits Scheme.Pullback in
/-- The diagonal morphism is always an immersion. -/
@[stacks 01KJ]
instance : IsImmersion (pullback.diagonal f) := by
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.map i)).affineCover
  have H : pullback.diagonal f ⁻¹ᵁ diagonalCoverDiagonalRange f 𝒰 𝒱 = ⊤ :=
    top_le_iff.mp fun _ _ ↦ range_diagonal_subset_diagonalCoverDiagonalRange _ _ _ ⟨_, rfl⟩
  have := isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange f 𝒰 𝒱
  have : IsImmersion ((pullback.diagonal f ∣_
    diagonalCoverDiagonalRange f 𝒰 𝒱) ≫ Scheme.Opens.ι _) := inferInstance
  rwa [morphismRestrict_ι, H, ← Scheme.topIso_hom,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsImmersion)] at this

instance : IsImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _ (prodIsoPullback X X).hom]
  convert inferInstanceAs (IsImmersion (pullback.diagonal (terminal.from X)))
  ext : 1 <;> simp

instance (f g : X ⟶ Y) : IsImmersion (equalizer.ι f g) :=
  MorphismProperty.of_isPullback (P := @IsImmersion)
    (isPullback_equalizer_prod f g).flip inferInstance

end IsImmersion

end AlgebraicGeometry
