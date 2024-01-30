/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.Topology.Category.Stonean.Basic
import Mathlib.Topology.Category.CompHaus.Limits
/-!
# Explicit (co)limits in the category of Stonean spaces

This file describes some explicit (co)limits in `Stonean`

## Overview

We define explicit finite coproducts in `Stonean` as sigma types (disjoint unions) and explicit
pullbacks where one of the maps is an open embedding

-/

set_option autoImplicit true

open CategoryTheory

namespace Stonean

/-!
This section defines the finite Coproduct of a finite family
of profinite spaces `X : α → Stonean.{u}`

Notes: The content is mainly copied from
`Mathlib/Topology/Category/CompHaus/Limits.lean`
-/
section FiniteCoproducts

open Limits

variable {α : Type} [Fintype α] {B : Stonean.{u}}
  (X : α → Stonean.{u})

/--
The coproduct of a finite family of objects in `Stonean`, constructed as the disjoint
union with its usual topology.
-/
def finiteCoproduct : Stonean := Stonean.of <| Σ (a : α), X a

/-- The inclusion of one of the factors into the explicit finite coproduct. -/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X where
  toFun := fun x => ⟨a,x⟩
  continuous_toFun := continuous_sigmaMk (σ := fun a => X a)

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def finiteCoproduct.desc {B : Stonean.{u}} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a,x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a; exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : Stonean.{u}} (e : (a : α) → (X a ⟶ B)) (a : α) :
    finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : Stonean.{u}} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a, x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

/-- The coproduct cocone associated to the explicit finite coproduct. -/
@[simps]
def finiteCoproduct.cocone (F : Discrete α ⥤ Stonean) :
    Cocone F where
  pt := finiteCoproduct (F.obj ∘ Discrete.mk)
  ι := Discrete.natTrans fun a => finiteCoproduct.ι (F.obj ∘ Discrete.mk) a.as

/-- The explicit finite coproduct cocone is a colimit cocone. -/
@[simps]
def finiteCoproduct.isColimit (F : Discrete α ⥤ Stonean) :
    IsColimit (finiteCoproduct.cocone F) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (fun q => q t) at hm
    exact hm

/-- The category of extremally disconnected spaces has finite coproducts.
-/
instance hasFiniteCoproducts : HasFiniteCoproducts Stonean.{u} where
  out _ := {
    has_colimit := fun F => {
      exists_colimit := ⟨{
        cocone := finiteCoproduct.cocone F
        isColimit := finiteCoproduct.isColimit F }⟩ } }

/--
A coproduct cocone associated to the explicit finite coproduct with cone point `finiteCoproduct X`.
-/
@[simps]
def finiteCoproduct.explicitCocone : Limits.Cocone (Discrete.functor X) where
  pt := finiteCoproduct X
  ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι X a

/--
The more explicit finite coproduct cocone is a colimit cocone.
-/
@[simps]
def finiteCoproduct.isColimit' : Limits.IsColimit (finiteCoproduct.explicitCocone X) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (fun q => q t) at hm
    exact hm

/-- The isomorphism from the explicit finite coproducts to the abstract coproduct. -/
noncomputable
def coproductIsoCoproduct : finiteCoproduct X ≅ ∐ X :=
Limits.IsColimit.coconePointUniqueUpToIso
  (finiteCoproduct.isColimit' X) (Limits.colimit.isColimit _)

/-- The inclusion maps into the explicit finite coproduct are open embeddings. -/
lemma finiteCoproduct.openEmbedding_ι {α : Type} [Fintype α] (Z : α → Stonean.{u}) (a : α) :
    OpenEmbedding (finiteCoproduct.ι Z a) :=
  openEmbedding_sigmaMk (σ := fun a => (Z a))

/-- The inclusion maps into the abstract finite coproduct are open embeddings. -/
lemma Sigma.openEmbedding_ι {α : Type} [Fintype α] (Z : α → Stonean.{u}) (a : α) :
    OpenEmbedding (Sigma.ι Z a) := by
  refine' OpenEmbedding.of_comp _ (homeoOfIso (coproductIsoCoproduct Z).symm).openEmbedding _
  convert finiteCoproduct.openEmbedding_ι Z a
  ext x
  change ((Sigma.ι Z a) ≫ (coproductIsoCoproduct Z).inv) x = _
  simp only [coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv,
    finiteCoproduct.explicitCocone_pt, finiteCoproduct.explicitCocone_ι, Discrete.natTrans_app]

instance : PreservesFiniteCoproducts Stonean.toCompHaus := by
  refine ⟨fun J hJ ↦ ⟨fun {F} ↦ ?_⟩⟩
  suffices : PreservesColimit (Discrete.functor (F.obj ∘ Discrete.mk)) Stonean.toCompHaus
  · exact preservesColimitOfIsoDiagram _ Discrete.natIsoFunctor.symm
  apply preservesColimitOfPreservesColimitCocone (Stonean.finiteCoproduct.isColimit _)
  exact CompHaus.finiteCoproduct.isColimit _

end FiniteCoproducts

end Stonean

section Pullback

open CategoryTheory Limits

namespace Stonean

variable {X Y Z : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)

/--
The pullback of a morphism `f` and an open embedding `i` in `Stonean`, constructed explicitly as
the preimage under `f`of the image of `i` with the subspace topology.
-/
def pullback : Stonean where
  compHaus := {
    toTop := TopCat.of (f ⁻¹' (Set.range i))
    is_compact := by
      dsimp [TopCat.of]
      rw [← isCompact_iff_compactSpace]
      refine IsClosed.isCompact (IsClosed.preimage f.continuous (IsCompact.isClosed ?_))
      simp only [← Set.image_univ]
      exact IsCompact.image isCompact_univ i.continuous
    is_hausdorff := by
      dsimp [TopCat.of]
      exact inferInstance }
  extrDisc := by
    constructor
    intro U hU
    dsimp at U
    have h : IsClopen (f ⁻¹' (Set.range i))
    · constructor
      · exact IsOpen.preimage f.continuous hi.open_range
      · refine' IsClosed.preimage f.continuous _
        apply IsCompact.isClosed
        simp only [← Set.image_univ]
        exact IsCompact.image isCompact_univ i.continuous
    have hU' : IsOpen (Subtype.val '' U) := h.1.openEmbedding_subtype_val.isOpenMap U hU
    have := ExtremallyDisconnected.open_closure _ hU'
    rw [h.2.closedEmbedding_subtype_val.closure_image_eq U] at this
    suffices hhU : closure U = Subtype.val ⁻¹' (Subtype.val '' (closure U))
    · rw [hhU]
      exact isOpen_induced this
    exact ((closure U).preimage_image_eq Subtype.coe_injective).symm

/-- The projection from the pullback to the first component. -/
def pullback.fst : pullback f hi ⟶ X :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The projection from the pullback to the second component. -/
noncomputable
def pullback.snd : pullback f hi ⟶ Y :=
  ⟨(Homeomorph.ofEmbedding i hi.toEmbedding).symm ∘
    Set.MapsTo.restrict f _ _ (Set.mapsTo_preimage f (Set.range i)),
    (Homeomorph.ofEmbedding i hi.toEmbedding).symm.continuous.comp (Continuous.restrict
    (Set.mapsTo_preimage f (Set.range i)) f.continuous)⟩

/--
Construct a morphism to the explicit pullback given morphisms to the factors
which are compatible with the maps to the base.
This is essentially the universal property of the pullback.
-/
def pullback.lift {X Y Z W : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)
    (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ i) :
    W ⟶ pullback f hi where
  toFun := fun z => ⟨a z, by
    simp only [Set.mem_preimage]
    use (b z)
    exact congr_fun (DFunLike.ext'_iff.mp w.symm) z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact a.continuous

lemma pullback.condition {X Y Z : Stonean.{u}} (f : X ⟶ Z) {i : Y ⟶ Z}
    (hi : OpenEmbedding i) : pullback.fst f hi ≫ f = pullback.snd f hi ≫ i := by
  ext ⟨x, h⟩
  simp only [Set.mem_preimage] at h
  obtain ⟨y, hy⟩ := h
  simp only [fst, snd, comp_apply]
  change f x = _
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [← hy, @ContinuousMap.coe_mk _ _ (Stonean.instTopologicalSpace (pullback f hi)) _ _ _]
  congr
  apply_fun (Homeomorph.ofEmbedding i hi.toEmbedding)
  simpa only [Homeomorph.ofEmbedding, Homeomorph.homeomorph_mk_coe, Equiv.ofInjective_apply,
    Homeomorph.homeomorph_mk_coe_symm, Set.MapsTo.restrict, Subtype.map, Function.comp_apply,
    Equiv.apply_symm_apply, Subtype.mk.injEq]

@[reassoc (attr := simp)]
lemma pullback.lift_fst {W : Stonean} (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ i) :
    pullback.lift f hi a b w ≫ pullback.fst f hi = a := rfl

@[reassoc (attr := simp)]
lemma pullback.lift_snd {X Y Z W : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)
    (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ i) :
    pullback.lift f hi a b w ≫ Stonean.pullback.snd f hi = b := by
  congr
  ext z
  have := congr_fun (DFunLike.ext'_iff.mp w.symm) z
  have h : i (b z) = f (a z) := this
  suffices : b z = (Homeomorph.ofEmbedding i hi.toEmbedding).symm (⟨f (a z), by rw [← h]; simp⟩)
  · exact this.symm
  apply_fun (Homeomorph.ofEmbedding i hi.toEmbedding)
  simpa only [Homeomorph.ofEmbedding, Homeomorph.homeomorph_mk_coe, Equiv.ofInjective_apply,
    Homeomorph.homeomorph_mk_coe_symm, Equiv.apply_symm_apply, Subtype.mk.injEq]

/-- The pullback cone whose cone point is the explicit pullback. -/
@[simps! pt π]
noncomputable
def pullback.cone : Limits.PullbackCone f i :=
  Limits.PullbackCone.mk (pullback.fst f hi) (pullback.snd f hi) (pullback.condition f hi)

lemma pullback.hom_ext {X Y Z W : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)
    (a : W ⟶ (pullback.cone f hi).pt) (b : W ⟶ (pullback.cone f hi).pt)
    (hfst : a ≫ pullback.fst f hi = b ≫ pullback.fst f hi) : a = b := by
  ext z
  apply_fun (fun q => q z) at hfst
  apply Subtype.ext
  exact hfst

/-- The explicit pullback cone is a limit cone. -/
def pullback.isLimit  : IsLimit (pullback.cone f hi) :=
  Limits.PullbackCone.isLimitAux _
    (fun s => pullback.lift f hi s.fst s.snd s.condition)
    (fun _ => pullback.lift_fst _ _ _ _ _)
    (fun _ => pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm => pullback.hom_ext _ _ _ _ (hm .left))

lemma HasPullbackOpenEmbedding : HasPullback f i :=
  ⟨pullback.cone f hi, pullback.isLimit f hi⟩

section Isos

/-- The isomorphism from the explicit pullback to the abstract pullback. -/
@[simps]
noncomputable
def pullbackIsoPullback : Stonean.pullback f hi ≅
    @Limits.pullback _ _ _ _ _ f i (HasPullbackOpenEmbedding f hi) :=
  haveI : HasPullback f i := HasPullbackOpenEmbedding f hi
  { hom :=
      Limits.pullback.lift (pullback.fst _ hi) (pullback.snd _ hi) (pullback.condition f hi)
    inv :=
      pullback.lift f hi Limits.pullback.fst Limits.pullback.snd Limits.pullback.condition
    hom_inv_id :=
      pullback.hom_ext f hi _ _ (by simp only [pullback.cone_pt, Category.assoc, pullback.lift_fst,
        limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.id_comp])
    inv_hom_id := by
      refine' Limits.pullback.hom_ext (k := (pullback.lift f hi Limits.pullback.fst
        Limits.pullback.snd Limits.pullback.condition ≫ Limits.pullback.lift
        (pullback.fst _ hi) (pullback.snd _ hi) (pullback.condition f hi))) _ _
      · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          pullback.lift_fst, Category.id_comp]
      · rw [Category.id_comp, Category.assoc, Limits.pullback.lift_snd, pullback.lift_snd] }

end Isos

/-- The forgetful from `Stonean` to `TopCat` creates pullbacks along open embeddings -/
noncomputable
def createsPullbacksOfOpenEmbedding :
    CreatesLimit (cospan f i) (Stonean.toCompHaus ⋙ compHausToTop) :=
  createsLimitOfFullyFaithfulOfIso (Stonean.pullback f hi) (by
    refine (@TopCat.isoOfHomeo (TopCat.of _) (TopCat.of _)
      (TopCat.pullbackHomeoPreimage f f.2 i hi.toEmbedding)).symm ≪≫ ?_
    refine ?_ ≪≫ Limits.lim.mapIso (diagramIsoCospan _).symm
    exact (TopCat.pullbackConeIsLimit f i).conePointUniqueUpToIso (limit.isLimit _))

instance : HasPullbacksOfInclusions Stonean where
  hasPullbackInl f := by
    apply (config := { allowSynthFailures := true }) hasPullback_symmetry
    apply Stonean.HasPullbackOpenEmbedding
    apply Stonean.Sigma.openEmbedding_ι

noncomputable
instance : PreservesPullbacksOfInclusions Stonean.toCompHaus.{u} where
  preservesPullbackInl := by
    intros X Y Z f
    apply (config := { allowSynthFailures := true }) preservesPullbackSymmetry
    have : OpenEmbedding (coprod.inl : X ⟶ X ⨿ Y) := Stonean.Sigma.openEmbedding_ι _ _
    have := Stonean.createsPullbacksOfOpenEmbedding f this
    exact preservesLimitOfReflectsOfPreserves Stonean.toCompHaus compHausToTop

instance : FinitaryExtensive Stonean.{u} :=
  finitaryExtensive_of_preserves_and_reflects Stonean.toCompHaus

end Stonean

end Pullback
