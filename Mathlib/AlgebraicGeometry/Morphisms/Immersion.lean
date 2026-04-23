/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.StacksAttribute
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Sheaves.Init

/-!

# Immersions of schemes

A morphism of schemes `f : X ⟶ Y` is an immersion if the underlying map of topological spaces
is a locally closed embedding, and the induced morphisms of stalks are all surjective. This is true
if and only if it can be factored into a closed immersion followed by an open immersion.

## Main results
- `isImmersion_iff_exists`:
  A morphism is a (locally-closed) immersion if and only if it can be factored into
  a closed immersion followed by a (dominant) open immersion.
- `isImmersion_iff_exists_of_quasiCompact`:
  A quasicompact morphism is a (locally-closed) immersion if and only if it can be factored into
  an open immersion followed by a closed immersion.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is an immersion if
1. the underlying map of topological spaces is an embedding
2. the range of the map is locally closed
3. the induced morphisms of stalks are all surjective. -/
@[mk_iff]
class IsImmersion (f : X ⟶ Y) : Prop extends IsPreimmersion f where
  isLocallyClosed_range : IsLocallyClosed (Set.range f)

lemma Scheme.Hom.isLocallyClosed_range (f : X ⟶ Y) [IsImmersion f] :
    IsLocallyClosed (Set.range f) :=
  IsImmersion.isLocallyClosed_range

/--
Given an immersion `f : X ⟶ Y`, this is the biggest open set `U ⊆ Y` containing the image of `X`
such that `X` is closed in `U`.
-/
def Scheme.Hom.coborderRange (f : X ⟶ Y) [IsImmersion f] : Y.Opens :=
  ⟨coborder (Set.range f), f.isLocallyClosed_range.isOpen_coborder⟩

/--
The first part of the factorization of an immersion `f : X ⟶ Y` to a closed immersion
`f.liftCoborder : X ⟶ f.coborderRange` and a dominant open immersion `f.coborderRange.ι`.
-/
noncomputable
def Scheme.Hom.liftCoborder (f : X ⟶ Y) [IsImmersion f] : X ⟶ f.coborderRange :=
  IsOpenImmersion.lift f.coborderRange.ι f (by simpa using subset_coborder)

/--
Any (locally-closed) immersion can be factored into
a closed immersion followed by a (dominant) open immersion.
-/
@[reassoc (attr := simp)]
lemma Scheme.Hom.liftCoborder_ι (f : X ⟶ Y) [IsImmersion f] :
    f.liftCoborder ≫ f.coborderRange.ι = f :=
  IsOpenImmersion.lift_fac _ _ _

lemma Scheme.Hom.liftCoborder_preimage [IsImmersion f] (U : f.coborderRange.toScheme.Opens) :
    f.liftCoborder ⁻¹ᵁ U = f ⁻¹ᵁ f.coborderRange.ι ''ᵁ U := by
  conv_rhs => enter [1]; rw [← f.liftCoborder_ι]
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]

set_option backward.isDefEq.respectTransparency false in
lemma liftCoborder_app [IsImmersion f] (U : f.coborderRange.toScheme.Opens) :
    f.liftCoborder.app U = f.app (f.coborderRange.ι ''ᵁ U) ≫
      X.presheaf.map (eqToHom <| f.liftCoborder_preimage U).op := by
  rw [Scheme.Hom.congr_app (f.liftCoborder_ι).symm (f.coborderRange.ι ''ᵁ U)]
  simp [Scheme.Hom.app_eq f.liftCoborder (f.coborderRange.ι.preimage_image_eq U),
    ← Functor.map_comp_assoc, -Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

set_option backward.isDefEq.respectTransparency false in
instance [IsImmersion f] : IsClosedImmersion f.liftCoborder := by
  have : IsPreimmersion (f.liftCoborder ≫ f.coborderRange.ι) := by
    simp only [Scheme.Hom.liftCoborder_ι]; infer_instance
  have : IsPreimmersion f.liftCoborder := .of_comp f.liftCoborder f.coborderRange.ι
  refine .of_isPreimmersion _ ?_
  convert isClosed_preimage_val_coborder
  apply Set.image_injective.mpr f.coborderRange.ι.isEmbedding.injective
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, f.liftCoborder_ι]
  exact (Set.image_preimage_eq_of_subset (by simpa using subset_coborder)).symm

instance [IsImmersion f] : IsDominant f.coborderRange.ι := by
  rw [isDominant_iff, DenseRange, Scheme.Opens.range_ι]
  exact dense_coborder

lemma isImmersion_eq_inf : @IsImmersion = (@IsPreimmersion ⊓
    topologically fun {_ _} _ _ f ↦ IsLocallyClosed (Set.range f) : MorphismProperty Scheme) := by
  ext; exact isImmersion_iff _

namespace IsImmersion

instance : IsZariskiLocalAtTarget @IsImmersion := by
  suffices IsZariskiLocalAtTarget
      (topologically fun {X Y} _ _ f ↦ IsLocallyClosed (Set.range f)) from
    isImmersion_eq_inf ▸ inferInstance
  apply +allowSynthFailures topologically_isZariskiLocalAtTarget'
  · refine { precomp := ?_, postcomp := ?_ }
    · intro X Y Z i hi f hf
      change IsIso i at hi
      change IsLocallyClosed _
      simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr i.surjective, Set.image_univ]
    · intro X Y Z i hi f hf
      change IsIso i at hi
      change IsLocallyClosed _
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      refine hf.image i.homeomorph.isInducing ?_
      rw [Set.range_eq_univ.mpr i.surjective]
      exact isOpen_univ.isLocallyClosed
  · simp_rw [Set.range_restrictPreimage]
    exact fun _ _ _ hU _ ↦ hU.isLocallyClosed_iff_coe_preimage

instance (priority := 900) (f : X ⟶ Y) [IsOpenImmersion f] : IsImmersion f where
  isLocallyClosed_range := f.isOpenEmbedding.2.isLocallyClosed

instance (priority := 900) (f : X ⟶ Y) [IsClosedImmersion f] : IsImmersion f where
  isLocallyClosed_range := f.isClosedEmbedding.2.isLocallyClosed

instance : MorphismProperty.IsMultiplicative @IsImmersion where
  id_mem _ := inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine { __ := (inferInstance : IsPreimmersion (f ≫ g)), isLocallyClosed_range := ?_ }
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
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

set_option backward.isDefEq.respectTransparency false in
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsImmersion where
  of_isPullback := by
    intro X Y Y' S f g f' g' H hg
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

instance (f : X ⟶ Z) (g : Y ⟶ Z) [IsImmersion g] : IsImmersion (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ ‹_›

instance (f : X ⟶ Z) (g : Y ⟶ Z) [IsImmersion f] : IsImmersion (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ ‹_›

instance (f : X ⟶ Y) (V : Y.Opens) [IsImmersion f] : IsImmersion (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [IsImmersion f] :
    IsImmersion (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

instance (priority := 900) (f : X ⟶ Y) [IsImmersion f] : LocallyOfFiniteType f := by
  rw [← f.liftCoborder_ι]
  infer_instance

open Limits Scheme.Pullback in
/-- The diagonal morphism is always an immersion. -/
@[stacks 01KJ]
instance : IsImmersion (pullback.diagonal f) := by
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.f i)).affineCover
  have H : pullback.diagonal f ⁻¹ᵁ diagonalCoverDiagonalRange f 𝒰 𝒱 = ⊤ :=
    top_le_iff.mp fun _ _ ↦ range_diagonal_subset_diagonalCoverDiagonalRange _ _ _ ⟨_, rfl⟩
  have := isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange f 𝒰 𝒱
  have : IsImmersion ((pullback.diagonal f ∣_
    diagonalCoverDiagonalRange f 𝒰 𝒱) ≫ Scheme.Opens.ι _) := inferInstance
  rwa [morphismRestrict_ι, H, ← Scheme.topIso_hom,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsImmersion)] at this

/-- The map `X ×[S] Y ⟶ X ×[T] Y` induced by any `S ⟶ T` is always an immersion. -/
instance {S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) :
    IsImmersion (pullback.mapDesc f g i) :=
  MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback f g i) inferInstance

instance : MorphismProperty.HasOfPostcompProperty @IsImmersion ⊤ :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (IsImmersion _)

lemma of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion (f ≫ g)] :
    IsImmersion f :=
  MorphismProperty.HasOfPostcompProperty.of_postcomp (W' := ⊤) _ g trivial ‹_›

theorem comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion g] :
    IsImmersion (f ≫ g) ↔ IsImmersion f :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
instance : IsImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _ (prodIsoPullback X X).hom]
  convert (inferInstance : IsImmersion (pullback.diagonal (terminal.from X)))
  ext : 1 <;> simp

instance (f g : X ⟶ Y) : IsImmersion (equalizer.ι f g) :=
  MorphismProperty.of_isPullback (P := @IsImmersion)
    (isPullback_equalizer_prod f g).flip inferInstance

instance [IsImmersion f] : IsImmersion f.toImage :=
  have : IsImmersion (f.toImage ≫ f.imageι) := by simpa
  IsImmersion.of_comp f.toImage f.imageι

set_option backward.isDefEq.respectTransparency false in
open Scheme in
/--
If `f : X ⟶ Y` is a quasi-compact immersion, then `X` is the pullback of the
closed immersion `im f ⟶ Y` and an open immersion `U ⟶ Y`.
-/
lemma isPullback_toImage_liftCoborder [IsImmersion f] [QuasiCompact f] :
    IsPullback f.toImage f.liftCoborder f.imageι f.coborderRange.ι := by
  refine (isPullback_of_isClosedImmersion _ _ _ _ (by simp) ?_).flip
  rw [Hom.imageι, IdealSheafData.ker_subschemeι]
  ext U : 2
  simp only [IdealSheafData.ideal_comap_of_isOpenImmersion, Opens.ι_appIso, Iso.refl_inv,
    Hom.ker_apply, RingHom.comap_ker, ← CommRingCat.hom_comp]
  dsimp [Opens.toScheme_presheaf_obj]
  rw [RingHomCompTriple.comp_eq, liftCoborder_app,
    CommRingCat.hom_comp, RingHom.ker_comp_of_injective]
  rw [← ConcreteCategory.mono_iff_injective_of_preservesPullback]
  infer_instance

instance [IsImmersion f] [QuasiCompact f] : IsOpenImmersion f.toImage :=
  MorphismProperty.of_isPullback (IsImmersion.isPullback_toImage_liftCoborder f).flip inferInstance

variable {f} in
/--
A quasi-compact morphism is a (locally-closed) immersion if and only if it can be factored into
an open immersion followed by a closed immersion.
-/
lemma isImmersion_iff_exists_of_quasiCompact [QuasiCompact f] :
    IsImmersion f ↔ ∃ (Z : Scheme) (g₁ : X ⟶ Z) (g₂ : Z ⟶ Y),
      IsOpenImmersion g₁ ∧ IsClosedImmersion g₂ ∧ g₁ ≫ g₂ = f :=
  ⟨fun _ ↦ ⟨_, f.toImage, f.imageι, inferInstance, inferInstance, f.toImage_imageι⟩,
    fun ⟨_, _, _, _, _, e⟩ ↦ e ▸ inferInstance⟩

end IsImmersion

end AlgebraicGeometry
