/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.LocallyDirected
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
import Batteries.Tactic.Trans
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Category.TopCat.Adjunctions
import Mathlib.Topology.Sheaves.Init

/-!
# Gluing Schemes

Given a family of gluing data of schemes, we may glue them together.
Also see the section about "locally directed" gluing,
which is a special case where the conditions are easier to check.

## Main definitions

* `AlgebraicGeometry.Scheme.GlueData`: A structure containing the family of gluing data.
* `AlgebraicGeometry.Scheme.GlueData.glued`: The glued scheme.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `AlgebraicGeometry.Scheme.GlueData.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.
* `AlgebraicGeometry.Scheme.GlueData.isoCarrier`: The isomorphism between the underlying space
  of the glued scheme and the gluing of the underlying topological spaces.
* `AlgebraicGeometry.Scheme.OpenCover.gluedCover`: The glue data associated with an open cover.
* `AlgebraicGeometry.Scheme.OpenCover.fromGlued`: The canonical morphism
  `𝒰.gluedCover.glued ⟶ X`. This has an `is_iso` instance.
* `AlgebraicGeometry.Scheme.OpenCover.glueMorphisms`: We may glue a family of compatible
  morphisms defined on an open cover of a scheme.

## Main results

* `AlgebraicGeometry.Scheme.GlueData.ι_isOpenImmersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.
* `AlgebraicGeometry.Scheme.GlueData.ι_jointly_surjective` : The underlying maps of
  `ι i : U i ⟶ glued` are jointly surjective.
* `AlgebraicGeometry.Scheme.GlueData.vPullbackConeIsLimit` : `V i j` is the pullback
  (intersection) of `U i` and `U j` over the glued space.
* `AlgebraicGeometry.Scheme.GlueData.ι_eq_iff` : `ι i x = ι j y` if and only if they coincide
  when restricted to `V i i`.
* `AlgebraicGeometry.Scheme.GlueData.isOpen_iff` : A subset of the glued scheme is open iff
  all its preimages in `U i` are open.

## Implementation details

All the hard work is done in `Mathlib/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` where we
glue presheafed spaces, sheafed spaces, and locally ringed spaces.

-/

@[expose] public section


noncomputable section

universe v u

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpace

open CategoryTheory.GlueData

namespace AlgebraicGeometry

namespace Scheme

/-- A family of gluing data consists of
1. An index type `J`
2. A scheme `U i` for each `i : J`.
3. A scheme `V i j` for each `i j : J`.
  (Note that this is `J × J → Scheme` rather than `J → J → Scheme` to connect to the
  limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.

such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the schemes `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subschemes of the glued space.
-/
structure GlueData extends CategoryTheory.GlueData Scheme where
  f_open : ∀ i j, IsOpenImmersion (f i j)

attribute [instance] GlueData.f_open

namespace GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

/-- The glue data of locally ringed spaces associated to a family of glue data of schemes. -/
abbrev toLocallyRingedSpaceGlueData : LocallyRingedSpace.GlueData :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToLocallyRingedSpace }

instance (i j : 𝖣.J) :
    LocallyRingedSpace.IsOpenImmersion ((D.toLocallyRingedSpaceGlueData).toGlueData.f i j) := by
  apply GlueData.f_open

instance (i j : 𝖣.J) :
    SheafedSpace.IsOpenImmersion
      (D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toGlueData.f i j) := by
  apply GlueData.f_open

instance (i j : 𝖣.J) :
    PresheafedSpace.IsOpenImmersion
      (D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toGlueData.f
        i j) := by
  apply GlueData.f_open

instance (i : 𝖣.J) :
    LocallyRingedSpace.IsOpenImmersion ((D.toLocallyRingedSpaceGlueData).toGlueData.ι i) := by
  apply LocallyRingedSpace.GlueData.ι_isOpenImmersion

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation). The glued scheme of a glue data.
This should not be used outside this file. Use `AlgebraicGeometry.Scheme.GlueData.glued` instead. -/
def gluedScheme : Scheme := by
  apply LocallyRingedSpace.IsOpenImmersion.scheme
    D.toLocallyRingedSpaceGlueData.toGlueData.glued
  intro x
  obtain ⟨i, y, rfl⟩ := D.toLocallyRingedSpaceGlueData.ι_jointly_surjective x
  obtain ⟨j, z, hz⟩ := (D.U i).affineCover.exists_eq y
  refine ⟨_, ((D.U i).affineCover.f j).toLRSHom ≫
    D.toLocallyRingedSpaceGlueData.toGlueData.ι i, ?_⟩
  constructor
  · simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base,
      TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
    exact Set.mem_image_of_mem _ ⟨z, hz⟩
  · infer_instance

instance : CreatesColimit 𝖣.diagram.multispan forgetToLocallyRingedSpace :=
  createsColimitOfFullyFaithfulOfIso D.gluedScheme
    (HasColimit.isoOfNatIso (𝖣.diagramIso forgetToLocallyRingedSpace).symm)

instance : PreservesColimit (𝖣.diagram.multispan) forgetToTop :=
  inferInstanceAs (PreservesColimit (𝖣.diagram).multispan (forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat))

instance : PreservesColimit (𝖣.diagram.multispan) forget :=
  inferInstanceAs (PreservesColimit (𝖣.diagram).multispan (forgetToTop ⋙ CategoryTheory.forget _))

instance : HasMulticoequalizer 𝖣.diagram :=
  hasColimit_of_created _ forgetToLocallyRingedSpace

/-- The glued scheme of a glued space. -/
abbrev glued : Scheme :=
  𝖣.glued

/-- The immersion from `D.U i` into the glued space. -/
abbrev ι (i : D.J) : D.U i ⟶ D.glued :=
  𝖣.ι i

/-- The gluing as sheafed spaces is isomorphic to the gluing as presheafed spaces. -/
abbrev isoLocallyRingedSpace :
    D.glued.toLocallyRingedSpace ≅ D.toLocallyRingedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToLocallyRingedSpace

theorem ι_isoLocallyRingedSpace_inv (i : D.J) :
    D.toLocallyRingedSpaceGlueData.toGlueData.ι i ≫
      D.isoLocallyRingedSpace.inv = (𝖣.ι i).toLRSHom :=
  𝖣.ι_gluedIso_inv forgetToLocallyRingedSpace i

set_option backward.isDefEq.respectTransparency false in
instance ι_isOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  rw [IsOpenImmersion, ← D.ι_isoLocallyRingedSpace_inv]; infer_instance

theorem ι_jointly_surjective (x : 𝖣.glued.carrier) :
    ∃ (i : D.J) (y : (D.U i).carrier), D.ι i y = x :=
  𝖣.ι_jointly_surjective forget x

/-- Promoted to higher priority to short circuit simplifier. -/
@[simp (high), reassoc]
theorem glue_condition (i j : D.J) : D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i :=
  𝖣.glue_condition i j

/-- The pullback cone spanned by `V i j ⟶ U i` and `V i j ⟶ U j`.
This is a pullback diagram (`vPullbackConeIsLimit`). -/
def vPullbackCone (i j : D.J) : PullbackCone (D.ι i) (D.ι j) :=
  PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.
```
Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
```
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (D.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToLocallyRingedSpace i j
    (D.toLocallyRingedSpaceGlueData.vPullbackConeIsLimit _ _)

local notation "D_" => TopCat.GlueData.toGlueData <|
  D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData

/-- The underlying topological space of the glued scheme is isomorphic to the gluing of the
underlying spaces -/
def isoCarrier :
    D.glued.carrier ≅ (D_).glued := by
  refine (PresheafedSpace.forget _).mapIso ?_ ≪≫
    GlueData.gluedIso _ (PresheafedSpace.forget.{_, _, u} _)
  refine SheafedSpace.forgetToPresheafedSpace.mapIso ?_ ≪≫
    SheafedSpace.GlueData.isoPresheafedSpace _
  refine LocallyRingedSpace.forgetToSheafedSpace.mapIso ?_ ≪≫
    LocallyRingedSpace.GlueData.isoSheafedSpace _
  exact Scheme.GlueData.isoLocallyRingedSpace _

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem ι_isoCarrier_inv (i : D.J) :
    (D_).ι i ≫ D.isoCarrier.inv = (D.ι i).base := by
  delta isoCarrier
  rw [Iso.trans_inv, GlueData.ι_gluedIso_inv_assoc, Functor.mapIso_inv, Iso.trans_inv,
    Functor.mapIso_inv, Iso.trans_inv, SheafedSpace.forgetToPresheafedSpace_map,
    PresheafedSpace.forget_map,
    PresheafedSpace.forget_map, ← PresheafedSpace.comp_base, ← Category.assoc,
    D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.ι_isoPresheafedSpace_inv i]
  dsimp
  rw [← Category.assoc, ← PresheafedSpace.comp_base,
    ← InducedCategory.comp_hom, D.toLocallyRingedSpaceGlueData.ι_isoSheafedSpace_inv i,
    ← PresheafedSpace.comp_base]
  change (_ ≫ D.isoLocallyRingedSpace.inv).base = _
  rw [D.ι_isoLocallyRingedSpace_inv i]

/-- An equivalence relation on `Σ i, D.U i` that holds iff `𝖣.ι i x = 𝖣.ι j y`.
See `AlgebraicGeometry.Scheme.GlueData.ι_eq_iff`. -/
def Rel (a b : Σ i, ((D.U i).carrier : Type _)) : Prop :=
  ∃ x : (D.V (a.1, b.1)).carrier, D.f _ _ x = a.2 ∧ (D.t _ _ ≫ D.f _ _) x = b.2

theorem ι_eq_iff (i j : D.J) (x : (D.U i).carrier) (y : (D.U j).carrier) :
    𝖣.ι i x = 𝖣.ι j y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  refine Iff.trans ?_
    (TopCat.GlueData.ι_eq_iff_rel
      D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData
      i j x y)
  rw [← ((TopCat.mono_iff_injective D.isoCarrier.inv).mp _).eq_iff, ← ConcreteCategory.comp_apply]
  · simp_rw [← D.ι_isoCarrier_inv]
    rfl -- `rfl` was not needed before https://github.com/leanprover-community/mathlib4/pull/13170
  · infer_instance

theorem isOpen_iff (U : Set D.glued.carrier) : IsOpen U ↔ ∀ i, IsOpen (D.ι i ⁻¹' U) := by
  rw [← (TopCat.homeoOfIso D.isoCarrier.symm).isOpen_preimage, TopCat.GlueData.isOpen_iff]
  apply forall_congr'
  intro i
  rw [← Set.preimage_comp, ← ι_isoCarrier_inv]
  rfl

/-- The open cover of the glued space given by the glue data. -/
@[simps -isSimp]
def openCover (D : Scheme.GlueData) : OpenCover D.glued where
  I₀ := D.J
  X := D.U
  f := D.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    exact ⟨D.ι_jointly_surjective, inferInstance⟩

end GlueData

namespace Cover

variable {X : Scheme.{u}} (𝒰 : OpenCover.{u} X)

/-- (Implementation) the transition maps in the glue data associated with an open cover. -/
def gluedCoverT' (x y z : 𝒰.I₀) :
    pullback (pullback.fst (𝒰.f x) (𝒰.f y)) (pullback.fst (𝒰.f x) (𝒰.f z)) ⟶
      pullback (pullback.fst (𝒰.f y) (𝒰.f z)) (pullback.fst (𝒰.f y) (𝒰.f x)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_fst_fst (x y z : 𝒰.I₀) :
    𝒰.gluedCoverT' x y z ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_fst_snd (x y z : 𝒰.I₀) :
    gluedCoverT' 𝒰 x y z ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_snd_fst (x y z : 𝒰.I₀) :
    gluedCoverT' 𝒰 x y z ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_snd_snd (x y z : 𝒰.I₀) :
    gluedCoverT' 𝒰 x y z ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta gluedCoverT'; simp

theorem glued_cover_cocycle_fst (x y z : 𝒰.I₀) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  apply pullback.hom_ext <;> simp

theorem glued_cover_cocycle_snd (x y z : 𝒰.I₀) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  apply pullback.hom_ext <;> simp [pullback.condition]

theorem glued_cover_cocycle (x y z : 𝒰.I₀) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y = 𝟙 _ := by
  apply pullback.hom_ext <;> simp_rw [Category.id_comp, Category.assoc]
  · apply glued_cover_cocycle_fst
  · apply glued_cover_cocycle_snd

/-- The glue data associated with an open cover.
The canonical isomorphism `𝒰.gluedCover.glued ⟶ X` is provided by `𝒰.fromGlued`. -/
@[simps]
def gluedCover : Scheme.GlueData.{u} where
  J := 𝒰.I₀
  U := 𝒰.X
  V := fun ⟨x, y⟩ => pullback (𝒰.f x) (𝒰.f y)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id x := by simp
  t' x y z := gluedCoverT' 𝒰 x y z
  t_fac x y z := by apply pullback.hom_ext <;> simp
  -- The `cocycle` field could have been `by tidy` but lean timeouts.
  cocycle x y z := glued_cover_cocycle 𝒰 x y z
  f_open _ := inferInstance

/-- The canonical morphism from the gluing of an open cover of `X` into `X`.
This is an isomorphism, as witnessed by an `IsIso` instance. -/
def fromGlued : 𝒰.gluedCover.glued ⟶ X := by
  fapply Multicoequalizer.desc
  · exact fun x => 𝒰.f x
  rintro ⟨x, y⟩
  change pullback.fst _ _ ≫ _ = ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ _
  simpa using pullback.condition

@[simp, reassoc]
theorem ι_fromGlued (x : 𝒰.I₀) : 𝒰.gluedCover.ι x ≫ 𝒰.fromGlued = 𝒰.f x :=
  Multicoequalizer.π_desc _ _ _ _ _

theorem fromGlued_injective : Function.Injective 𝒰.fromGlued := by
  intro x y h
  obtain ⟨i, x, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective y
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply] at h
  simp_rw [← Scheme.Hom.comp_base] at h
  rw [ι_fromGlued, ι_fromGlued] at h
  let e :=
    (TopCat.pullbackConeIsLimit _ _).conePointUniqueUpToIso
      (isLimitOfHasPullbackOfPreservesLimit Scheme.forgetToTop (𝒰.f i) (𝒰.f j))
  rw [𝒰.gluedCover.ι_eq_iff]
  use e.hom ⟨⟨x, y⟩, h⟩
  constructor
  · erw [← ConcreteCategory.comp_apply e.hom,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left]
    rfl
  · erw [← ConcreteCategory.comp_apply e.hom, pullbackSymmetry_hom_comp_fst,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right]
    rfl

set_option backward.isDefEq.respectTransparency false in
instance (x : 𝒰.gluedCover.glued.carrier) :
    IsIso (𝒰.fromGlued.stalkMap x) := by
  obtain ⟨i, x, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective x
  have := Hom.stalkMap_congr_hom _ _ (𝒰.ι_fromGlued i) x
  rw [Hom.stalkMap_comp, ← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance

theorem isOpenMap_fromGlued : IsOpenMap 𝒰.fromGlued := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  rw [𝒰.gluedCover.isOpen_iff] at hU
  use 𝒰.fromGlued '' U ∩ Set.range (𝒰.f (𝒰.idx x))
  use Set.inter_subset_left
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply (𝒰.f (𝒰.idx x)).isOpenEmbedding.isOpenMap
    convert hU (𝒰.idx x) using 1
    simp only [← ι_fromGlued, gluedCover_U, Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
      Set.preimage_comp]
    congr! 1
    exact Set.preimage_image_eq _ 𝒰.fromGlued_injective
  · exact ⟨hx, 𝒰.covers x⟩

theorem isOpenEmbedding_fromGlued : IsOpenEmbedding 𝒰.fromGlued :=
  .of_continuous_injective_isOpenMap (by fun_prop) 𝒰.fromGlued_injective 𝒰.isOpenMap_fromGlued

instance : Epi 𝒰.fromGlued.base := by
  rw [TopCat.epi_iff_surjective]
  intro x
  obtain ⟨y, h⟩ := 𝒰.covers x
  use 𝒰.gluedCover.ι (𝒰.idx x) y
  rw [← ConcreteCategory.comp_apply]
  rw [← 𝒰.ι_fromGlued (𝒰.idx x)] at h
  exact h

instance : IsOpenImmersion 𝒰.fromGlued :=
  IsOpenImmersion.of_isIso_stalkMap _ 𝒰.isOpenEmbedding_fromGlued

instance : IsIso 𝒰.fromGlued :=
  let F := Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace
  have : IsIso (F.map (fromGlued 𝒰)) := by
    change IsIso 𝒰.fromGlued.toPshHom
    apply PresheafedSpace.IsOpenImmersion.to_iso
  isIso_of_reflects_iso _ F

/-- Given an open cover of `X`, and a morphism `𝒰.X x ⟶ Y` for each open subscheme in the cover,
such that these morphisms are compatible in the intersection (pullback), we may glue the morphisms
together into a morphism `X ⟶ Y`.

Note:
If `X` is exactly (defeq to) the gluing of `U i`, then using `Multicoequalizer.desc` suffices.
-/
def glueMorphisms (𝒰 : OpenCover.{v} X) {Y : Scheme.{u}} (f : ∀ x, 𝒰.X x ⟶ Y)
    (hf : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback.snd _ _ ≫ f y) :
    X ⟶ Y := by
  refine inv 𝒰.ulift.fromGlued ≫ ?_
  fapply Multicoequalizer.desc
  · exact fun i ↦ f _
  rintro ⟨i, j⟩
  dsimp
  change pullback.fst _ _ ≫ f _ = (_ ≫ _) ≫ f _
  simpa [pullbackSymmetry_hom_comp_fst] using hf _ _

set_option backward.isDefEq.respectTransparency false in
theorem hom_ext (𝒰 : OpenCover.{v} X) {Y : Scheme} (f₁ f₂ : X ⟶ Y)
    (h : ∀ x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂ := by
  rw [← cancel_epi 𝒰.ulift.fromGlued]
  apply Multicoequalizer.hom_ext
  intro x
  rw [fromGlued, Multicoequalizer.π_desc_assoc, Multicoequalizer.π_desc_assoc]
  exact h _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ι_glueMorphisms (𝒰 : OpenCover.{v} X) {Y : Scheme} (f : ∀ x, 𝒰.X x ⟶ Y)
    (hf : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback.snd _ _ ≫ f y)
    (x : 𝒰.I₀) : 𝒰.f x ≫ 𝒰.glueMorphisms f hf = f x := by
  refine Cover.hom_ext (𝒰.ulift.pullback₁ (𝒰.f x)) _ _ fun i ↦ ?_
  dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, ulift_X, ulift_f, PreZeroHypercover.pullback₁_f]
  simp_rw [pullback.condition_assoc, ← ulift_f, ← ι_fromGlued, Category.assoc, glueMorphisms,
    IsIso.hom_inv_id_assoc, ulift_f, hf]
  simp [CategoryTheory.GlueData.ι]

end Cover

lemma hom_ext_of_forall {X Y : Scheme} (f g : X ⟶ Y)
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g) : f = g := by
  choose U hxU hU using H
  let 𝒰 : X.OpenCover := {
    I₀ := X, X i := (U i), f i := (U i).ι,
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ⟨x, by simpa using hxU x⟩, inferInstance⟩ }
  exact 𝒰.hom_ext _ _ hU

set_option backward.isDefEq.respectTransparency false in
-- TODO: generalize to covers in subcanonical topologies
open pullback in
attribute [local simp] condition condition_assoc in
instance : (MorphismProperty.isomorphisms Scheme).IsLocalAtTarget zariskiPrecoverage :=
  .mk_of_isStableUnderBaseChange fun {X Y} f (𝒰 : Y.OpenCover) (H : ∀ i, IsIso _) ↦
    ⟨𝒰.glueMorphisms (fun i ↦ inv (snd f (𝒰.f i)) ≫ fst _ _) fun i j ↦ by
    rw [← cancel_epi ((pullbackRightPullbackFstIso _ _ _).hom ≫ map (fst f (𝒰.f i) ≫ f)
      (𝒰.f j) (𝒰.f i) (𝒰.f j) (snd _ _) (𝟙 _) (𝟙 _) (by simp) (by simp))]
    simp, Cover.hom_ext (𝒰.pullback₁ f) _ _ fun i ↦ by simp, Cover.hom_ext 𝒰 _ _ fun i ↦ by simp⟩

/-!

## Locally directed gluing

We say that a diagram of open immersions is "locally directed" if for any `V, W ⊆ U` in the diagram,
`V ∩ W` is a union of elements in the diagram. Equivalently, for every `x ∈ U` in the diagram,
the set of elements containing `x` is directed (and hence the name).

For such a diagram, we can glue them directly since the gluing conditions are always satisfied.
The intended usage is to provide the following instances:
- `∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)`
- `(F ⋙ forget).IsLocallyDirected`

and to directly use the `colimit` API.
Also see `AlgebraicGeometry.Scheme.IsLocallyDirected.openCover` for the open cover of the `colimit`.

-/
section IsLocallyDirected

open TopologicalSpace.Opens

universe w

variable {J : Type w} [Category.{v} J] (F : J ⥤ Scheme.{u})
variable [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]

namespace IsLocallyDirected

/-- (Implementation detail)
The intersection `V` in the glue data associated to a locally directed diagram. -/
noncomputable
def V (i j : J) : (F.obj i).Opens := ⨆ (k : Σ k, (k ⟶ i) × (k ⟶ j)), (F.map k.2.1).opensRange

lemma V_self (i) : V F i i = ⊤ :=
  top_le_iff.mp (le_iSup_of_le ⟨i, 𝟙 _, 𝟙 _⟩ (by simp [Scheme.Hom.opensRange_of_isIso]))

variable [(F ⋙ forget).IsLocallyDirected]

set_option backward.isDefEq.respectTransparency false in
lemma exists_of_pullback_V_V {i j k : J} (x : pullback (C := Scheme) (V F i j).ι (V F i k).ι) :
    ∃ (l : J) (fi : l ⟶ i) (fj : l ⟶ j) (fk : l ⟶ k)
      (α : F.obj l ⟶ pullback (V F i j).ι (V F i k).ι) (z : F.obj l),
      IsOpenImmersion α ∧
      α ≫ pullback.fst _ _ = (F.map fi).isoOpensRange.hom ≫
        (F.obj i).homOfLE (le_iSup_of_le ⟨l, _, fj⟩ le_rfl) ∧
      α ≫ pullback.snd _ _ = (F.map fi).isoOpensRange.hom ≫
        (F.obj i).homOfLE (le_iSup_of_le ⟨l, _, fk⟩ le_rfl) ∧
      α z = x := by
  obtain ⟨k₁, y₁, hy₁⟩ := mem_iSup.mp ((pullback.fst (C := Scheme) _ _) x).2
  obtain ⟨k₂, y₂, hy₂⟩ := mem_iSup.mp ((pullback.snd (C := Scheme) _ _) x).2
  obtain ⟨l, hli, hlk, z, rfl, rfl⟩ :=
    (F ⋙ forget).exists_map_eq_of_isLocallyDirected k₁.2.1 k₂.2.1 y₁ y₂
      (by simpa [hy₁, hy₂] using congr($(pullback.condition (f := (V F i j).ι)) x))
  let α : F.obj l ⟶ pullback (V F i j).ι (V F i k).ι :=
    pullback.lift
      ((F.map (hli ≫ k₁.2.1)).isoOpensRange.hom ≫ Scheme.homOfLE _
        (le_iSup_of_le ⟨l, hli ≫ k₁.2.1, hli ≫ k₁.2.2⟩ le_rfl))
      ((F.map (hli ≫ k₁.2.1)).isoOpensRange.hom ≫ Scheme.homOfLE _
        (le_iSup_of_le ⟨l, hli ≫ k₁.2.1, hlk ≫ k₂.2.2⟩ le_rfl))
      (by simp)
  have : IsOpenImmersion α := by
    apply +allowSynthFailures IsOpenImmersion.of_comp
    · exact (inferInstance : IsOpenImmersion (pullback.fst (V F i j).ι (V F i k).ι))
    · simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, α]
      infer_instance
  have : α z = x := by
    apply (pullback.fst (C := Scheme) _ _).isOpenEmbedding.injective
    apply (V F i j).ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    simpa using hy₁
  exact ⟨l, hli ≫ k₁.2.1, hli ≫ k₁.2.2, hlk ≫ k₂.2.2, α, z, ‹_›, by simp [α], by simp [α], ‹_›⟩

variable [Quiver.IsThin J]

set_option backward.isDefEq.respectTransparency false in
lemma fst_inv_eq_snd_inv
    {i j : J} (k₁ k₂ : (k : J) × (k ⟶ i) × (k ⟶ j)) {U : (F.obj i).Opens}
    (h₁ : (F.map k₁.2.1).opensRange ≤ U) (h₂ : (F.map k₂.2.1).opensRange ≤ U) :
    pullback.fst ((F.obj i).homOfLE h₁) ((F.obj i).homOfLE h₂) ≫
      (F.map k₁.2.1).isoOpensRange.inv ≫ F.map k₁.2.2 =
    pullback.snd ((F.obj i).homOfLE h₁) ((F.obj i).homOfLE h₂) ≫
      (F.map k₂.2.1).isoOpensRange.inv ≫ F.map k₂.2.2 := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨l, hli, hlj, y, hy₁, hy₂⟩ := (F ⋙ forget).exists_map_eq_of_isLocallyDirected k₁.2.1 k₂.2.1
    ((pullback.fst _ _ ≫ (F.map k₁.2.1).isoOpensRange.inv) x)
    ((pullback.snd _ _ ≫ (F.map k₂.2.1).isoOpensRange.inv) x) (by
      simp only [Functor.comp_obj, forget_obj, Functor.comp_map, forget_map,
        ConcreteCategory.hom_ofHom, Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply,
        TypeCat.Fun.coe_mk]
      simp only [← Hom.comp_apply]
      congr 5
      simpa using congr($(pullback.condition (f := (F.obj i).homOfLE h₁)
        (g := (F.obj i).homOfLE h₂)) ≫ Scheme.Opens.ι _))
  let α : F.obj l ⟶ pullback ((F.obj i).homOfLE h₁) ((F.obj i).homOfLE h₂) :=
    pullback.lift
      (F.map hli ≫ (F.map k₁.2.1).isoOpensRange.hom)
      (F.map hlj ≫ (F.map k₂.2.1).isoOpensRange.hom)
      (by simp [← cancel_mono (Scheme.Opens.ι _), ← Functor.map_comp,
        Subsingleton.elim (hli ≫ k₁.2.1) (hlj ≫ k₂.2.1)])
  have : IsOpenImmersion α := by
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by
      simp only [pullback.lift_fst, α]; infer_instance
    exact .of_comp _ (pullback.fst _ _)
  have : α y = x := by
    simp only [Functor.comp_obj, forget_obj, Functor.comp_map, forget_map, Hom.comp_base,
      TopCat.hom_comp, ContinuousMap.comp_apply] at hy₁
    apply (pullback.fst ((F.obj i).homOfLE h₁) _).isOpenEmbedding.injective
    simp only [← Scheme.Hom.comp_apply, α, pullback.lift_fst]
    simp_all
  refine ⟨α.opensRange, ⟨y, this⟩, ?_⟩
  rw [← cancel_epi α.isoOpensRange.hom]
  simp [α, ← Functor.map_comp, Subsingleton.elim (hli ≫ k₁.2.2) (hlj ≫ k₂.2.2)]

/-- (Implementation detail)
The inclusion map `V i j ⟶ F j` in the glue data associated to a locally directed diagram. -/
def tAux (i j : J) : (V F i j).toScheme ⟶ F.obj j :=
  (Scheme.Opens.iSupOpenCover _).glueMorphisms
    (fun k ↦ (F.map k.2.1).isoOpensRange.inv ≫ F.map k.2.2) fun k₁ k₂ ↦ by
      dsimp [Scheme.Opens.iSupOpenCover]
      apply fst_inv_eq_snd_inv F

@[reassoc]
lemma homOfLE_tAux (i j : J) {k : J} (fi : k ⟶ i) (fj : k ⟶ j) :
    (F.obj i).homOfLE (le_iSup_of_le ⟨k, fi, fj⟩ le_rfl) ≫
      tAux F i j = (F.map fi).isoOpensRange.inv ≫ F.map fj :=
  (Scheme.Opens.iSupOpenCover (J := Σ k, (k ⟶ i) × (k ⟶ j)) _).ι_glueMorphisms _ _ ⟨k, fi, fj⟩

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation detail)
The transition map `V i j ⟶ V j i` in the glue data associated to a locally directed diagram. -/
def t (i j : J) : (V F i j).toScheme ⟶ (V F j i).toScheme :=
  IsOpenImmersion.lift (V F j i).ι (tAux F i j) (by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, x, rfl⟩ := (Scheme.Opens.iSupOpenCover _).exists_eq x
    simp only [V, tAux, ← Scheme.Hom.comp_apply, Cover.ι_glueMorphisms]
    simp only [Opens.range_ι, iSup_mk, carrier_eq_coe, Hom.coe_opensRange, coe_mk, Hom.comp_base,
      TopCat.hom_comp, ContinuousMap.comp_apply]
    exact Set.mem_iUnion.mpr ⟨⟨l.1, l.2.2, l.2.1⟩, ⟨_, rfl⟩⟩)

lemma t_id (i : J) : t F i i = 𝟙 _ := by
  refine (Scheme.Opens.iSupOpenCover _).hom_ext _ _ fun k ↦ ?_
  simp only [Category.comp_id, ← cancel_mono (Scheme.Opens.ι _), Category.assoc,
    IsOpenImmersion.lift_fac, Scheme.Cover.ι_glueMorphisms, t, tAux, V]
  simp [Scheme.Opens.iSupOpenCover, Iso.inv_comp_eq, Subsingleton.elim k.2.1 k.2.2]

variable [Small.{u} J]

local notation3:max "↓"j:arg => Equiv.symm (equivShrink _) j

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation detail)
The glue data associated to a locally directed diagram.

One usually does not want to use this directly, and instead use the generic `colimit` API.
-/
def glueData : Scheme.GlueData where
  J := Shrink.{u} J
  U j := F.obj ↓j
  V ij := V F ↓ij.1 ↓ij.2
  f i j := Scheme.Opens.ι _
  f_id i := V_self F ↓i ▸ (Scheme.topIso _).isIso_hom
  f_hasPullback := inferInstance
  f_open := inferInstance
  t i j := t F ↓i ↓j
  t_id i := t_id F ↓i
  t' i j k := pullback.lift
    (IsOpenImmersion.lift (V F ↓j ↓k).ι (pullback.fst _ _ ≫ tAux F ↓i ↓j) (by
      rintro _ ⟨x, rfl⟩
      obtain ⟨l, fi, fj, fk, α, z, hα, hα₁, hα₂, rfl⟩ := exists_of_pullback_V_V F x
      rw [← Scheme.Hom.comp_apply, reassoc_of% hα₁, homOfLE_tAux F ↓i ↓j fi fj,
        Iso.hom_inv_id_assoc, Scheme.Opens.range_ι, SetLike.mem_coe]
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨l, fj, fk⟩, ⟨z, rfl⟩⟩))
      (pullback.fst _ _ ≫ t F _ _) (by simp [t])
  t_fac i j k := pullback.lift_snd _ _ _
  cocycle i j k := by
    refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
    have := exists_of_pullback_V_V F x
    obtain ⟨l, fi, fj, fk, α, z, hα, hα₁, hα₂, e⟩ := this -- doing them in the same step times out.
    refine ⟨α.opensRange, ⟨_, e⟩, ?_⟩
    rw [← cancel_mono (pullback.snd _ _), ← cancel_mono (Scheme.Opens.ι _)]
    simp only [t, Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      limit.lift_π_assoc, cospan_left, IsOpenImmersion.lift_fac, Category.id_comp]
    rw [IsOpenImmersion.comp_lift_assoc]
    simp only [limit.lift_π_assoc, PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app]
    rw [← cancel_epi α.isoOpensRange.hom]
    simp_rw [Scheme.Hom.isoOpensRange_hom_ι_assoc, IsOpenImmersion.comp_lift_assoc]
    simp only [reassoc_of% hα₁, homOfLE_tAux F _ _ fi fj, Iso.hom_inv_id_assoc, reassoc_of% hα₂]
    generalize_proofs _ h₁
    have : IsOpenImmersion.lift (V F ↓j ↓k).ι (F.map fj) h₁ = (F.map fj).isoOpensRange.hom ≫
        (F.obj ↓j).homOfLE (le_iSup_of_le ⟨l, fj, fk⟩ le_rfl) := by
      rw [← cancel_mono (Scheme.Opens.ι _), Category.assoc, IsOpenImmersion.lift_fac,
        ← Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_inv_comp]
      exact (Scheme.homOfLE_ι _ _).symm
    simp_rw [this, Category.assoc, homOfLE_tAux F _ _ fj fk, Iso.hom_inv_id_assoc]
    generalize_proofs h₂
    have : IsOpenImmersion.lift (V F ↓k ↓i).ι (F.map fk) h₂ = (F.map fk).isoOpensRange.hom ≫
        (F.obj ↓k).homOfLE (le_iSup_of_le ⟨l, fk, fi⟩ le_rfl) := by
      rw [← cancel_mono (Scheme.Opens.ι _), Category.assoc, IsOpenImmersion.lift_fac,
        ← Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_inv_comp]
      exact (Scheme.homOfLE_ι _ _).symm
    simp_rw [this, Category.assoc, homOfLE_tAux F _ _ fk fi, Iso.hom_inv_id_assoc,
      ← Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_inv_comp]
    exact (Scheme.homOfLE_ι _ _).symm

lemma glueDataι_naturality {i j : Shrink.{u} J} (f : ↓i ⟶ ↓j) :
    F.map f ≫ (glueData F).ι j = (glueData F).ι i := by
  have : IsIso (V F ↓i ↓j).ι := by
    have : V F ↓i ↓j = ⊤ :=
      top_le_iff.mp (le_iSup_of_le ⟨_, 𝟙 _, f⟩ (by simp [Scheme.Hom.opensRange_of_isIso]))
    exact this ▸ (topIso _).isIso_hom
  have : t F ↓i ↓j ≫ (V F ↓j ↓i).ι ≫ _ = (V F ↓i ↓j).ι ≫ _ :=
    (glueData F).glue_condition i j
  simp only [t, IsOpenImmersion.lift_fac_assoc] at this
  rw [← cancel_epi (V F ↓i ↓j).ι, ← this, ← Category.assoc,
    ← (Iso.eq_inv_comp _).mp (homOfLE_tAux F ↓i ↓j (𝟙 _) f),
    ← Category.assoc, ← Category.assoc, Category.assoc]
  convert Category.id_comp _
  simp [← cancel_mono (Opens.ι _), V]

/-- (Implementation detail)
The cocone associated to a locally directed diagram.

One usually does not want to use this directly, and instead use the generic `colimit` API.
-/
def cocone : Cocone F where
  pt := (glueData F).glued
  ι.app j := F.map (eqToHom (by simp)) ≫ (glueData F).ι (equivShrink _ j)
  ι.naturality {i j} f := by
    simp only [← IsIso.inv_comp_eq, ← Functor.map_inv, ← Functor.map_comp_assoc,
      glueDataι_naturality, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation detail)
The cocone associated to a locally directed diagram is a colimit.

One usually does not want to use this directly, and instead use the generic `colimit` API.
-/
noncomputable
def isColimit : IsColimit (cocone F) where
  desc s := Multicoequalizer.desc _ _ (fun i ↦ s.ι.app ↓i) (by
    rintro ⟨i, j⟩
    dsimp [glueData, GlueData.diagram]
    simp only [t, IsOpenImmersion.lift_fac]
    apply (Scheme.Opens.iSupOpenCover _).hom_ext _ _ fun k ↦ ?_
    simp only [Opens.iSupOpenCover, V, Scheme.homOfLE_ι_assoc]
    rw [homOfLE_tAux_assoc F ↓i ↓j k.2.1 k.2.2, Iso.eq_inv_comp]
    simp)
  fac s j := by
    refine (Category.assoc _ _ _).trans ?_
    conv_lhs => enter [2]; tactic => exact Multicoequalizer.π_desc _ _ _ _ _
    simp
  uniq s m hm := Multicoequalizer.hom_ext _ _ _ fun i ↦ by
    simp [← hm ↓i, cocone, reassoc_of% glueDataι_naturality]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation detail)
The cocone associated to a locally directed diagram is a colimit as locally ringed spaces.

One usually does not want to use this directly, and instead use the generic `colimit` API.
-/
noncomputable
def isColimitForgetToLocallyRingedSpace :
    IsColimit (Scheme.forgetToLocallyRingedSpace.mapCocone (cocone F)) where
  desc s := (glueData F).isoLocallyRingedSpace.hom ≫
    Multicoequalizer.desc _ _ (fun i ↦ s.ι.app ↓i) (by
      rintro ⟨i, j⟩
      dsimp [glueData, GlueData.diagram]
      simp only [t, IsOpenImmersion.lift_fac, ← Scheme.Hom.comp_toLRSHom]
      rw [← cancel_epi (Scheme.Opens.iSupOpenCover _).ulift.fromGlued.toLRSHom,
        ← cancel_epi (Scheme.Opens.iSupOpenCover _).ulift.gluedCover.isoLocallyRingedSpace.inv]
      refine Multicoequalizer.hom_ext _ _ _ fun ⟨k, hk⟩ ↦ ?_
      rw [← CategoryTheory.GlueData.ι, reassoc_of% GlueData.ι_isoLocallyRingedSpace_inv,
        reassoc_of% GlueData.ι_isoLocallyRingedSpace_inv,
        ← cancel_epi (Hom.isoOpensRange (F.map _)).hom.toLRSHom]
      simp +instances only [Opens.iSupOpenCover, Cover.ulift, V, ← Hom.comp_toLRSHom_assoc,
        Cover.ι_fromGlued_assoc, homOfLE_ι, Hom.isoOpensRange_hom_ι, Cover.idx]
      generalize_proofs _ _ h
      rw [homOfLE_tAux F ↓i ↓j h.choose.2.1 h.choose.2.2, Iso.hom_inv_id_assoc]
      exact (s.w h.choose.2.1).trans (s.w h.choose.2.2).symm)
  fac s j := by
    simp only [cocone, Functor.mapCocone_ι_app, Scheme.Hom.comp_toLRSHom,
      forgetToLocallyRingedSpace_map, ← GlueData.ι_isoLocallyRingedSpace_inv]
    simpa [CategoryTheory.GlueData.ι] using s.w _
  uniq s m hm := by
    rw [← Iso.inv_comp_eq]
    refine Multicoequalizer.hom_ext _ _ _ fun i ↦ ?_
    conv_lhs => rw [← ι.eq_def]
    dsimp
    simp [cocone, ← hm, glueDataι_naturality,
      ← GlueData.ι_isoLocallyRingedSpace_inv, -ι_gluedIso_inv_assoc, -ι_gluedIso_inv]

instance : HasColimit F := ⟨_, isColimit F⟩

instance : PreservesColimit F Scheme.forgetToLocallyRingedSpace :=
  preservesColimit_of_preserves_colimit_cocone (isColimit F) (isColimitForgetToLocallyRingedSpace F)

instance : CreatesColimit F Scheme.forgetToLocallyRingedSpace :=
  CategoryTheory.createsColimitOfReflectsIsomorphismsOfPreserves

set_option backward.isDefEq.respectTransparency false in
/-- The open cover of the colimit of a locally directed diagram by the components. -/
@[simps! I₀ X f]
def openCover : (colimit F).OpenCover :=
  Cover.copy ((coverOfIsIso ((isColimit F).coconePointUniqueUpToIso (colimit.isColimit F)).hom).bind
    fun i ↦ (glueData F).openCover) J F.obj (colimit.ι F)
    ((equivShrink J).trans <| (Equiv.uniqueSigma fun (_ : Unit) ↦ Shrink J).symm)
    (fun _ ↦ F.mapIso (eqToIso (by simp [GlueData.openCover, glueData]))) fun i ↦ by
  change colimit.ι F i = _ ≫ (glueData F).ι (equivShrink J i) ≫ _
  simp [← Category.assoc, ← Iso.comp_inv_eq, cocone]

instance (i) : IsOpenImmersion (colimit.ι F i) :=
  inferInstanceAs (IsOpenImmersion ((openCover F).f i))

set_option backward.isDefEq.respectTransparency false in
lemma ι_eq_ι_iff {i j : J} {xi : F.obj i} {xj : F.obj j} :
    colimit.ι F i xi = colimit.ι F j xj ↔
      ∃ k fi fj, ∃ (x : F.obj k), F.map fi x = xi ∧ F.map fj x = xj := by
  constructor; swap
  · rintro ⟨k, fi, fj, x, rfl, rfl⟩; simp only [← Scheme.Hom.comp_apply, colimit.w]
  obtain ⟨i, rfl⟩ := (equivShrink J).symm.surjective i
  obtain ⟨j, rfl⟩ := (equivShrink J).symm.surjective j
  rw [← ((isColimit F).coconePointUniqueUpToIso
    (colimit.isColimit F)).inv.isOpenEmbedding.injective.eq_iff]
  simp only [Limits.colimit, ← Scheme.Hom.comp_apply,
    colimit.comp_coconePointUniqueUpToIso_inv, cocone, glueDataι_naturality]
  refine ?_ ∘ ((glueData F).ι_eq_iff _ _ _ _).mp
  dsimp +instances only [GlueData.Rel]
  rintro ⟨x, rfl, rfl⟩
  obtain ⟨⟨k, ki, kj⟩, y, hy : F.map ki y = (glueData F).f i j x⟩ := mem_iSup.mp x.2
  refine ⟨k, ki, kj, y, hy, ?_⟩
  obtain ⟨k, rfl⟩ := (equivShrink J).symm.surjective k
  apply ((glueData F).ι _).isOpenEmbedding.injective
  simp only [← Scheme.Hom.comp_apply, Category.assoc, GlueData.glue_condition]
  trans (glueData F).ι k y
  · simp [← glueDataι_naturality F kj]; rfl
  · simp [← glueDataι_naturality F ki, ← hy]; rfl

set_option backward.isDefEq.respectTransparency false in
lemma ι_jointly_surjective (x : ↑(colimit F)) :
    ∃ (i : J) (xi : F.obj i), colimit.ι F i xi = x := by
  obtain ⟨i, xi, h⟩ :=
    (IsLocallyDirected.glueData F).ι_jointly_surjective
      (((IsLocallyDirected.isColimit F).coconePointUniqueUpToIso (colimit.isColimit _)).inv x)
  use (equivShrink J).symm i, xi
  apply ((isColimit F).coconePointUniqueUpToIso (colimit.isColimit F)).inv.isOpenEmbedding.injective
  simp_rw [← h, colimit.cocone_x, ← Scheme.Hom.comp_apply]
  congr 5
  have := eqToHom_naturality (fun j ↦ (glueData F).ι j)
    (show i = ((equivShrink J) ((equivShrink J).symm i)) by simp)
  simp [cocone, Functor.const_obj_obj, eqToHom_map, ← this]

instance (F : WidePushoutShape J ⥤ Scheme.{u}) [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)] :
    (F ⋙ forget).IsLocallyDirected :=
  have (i : _) : Mono ((F ⋙ forget).map (.init i)) :=
    (mono_iff_injective _).mpr (F.map _).isOpenEmbedding.injective
  inferInstance

end IsLocallyDirected

end IsLocallyDirected

end Scheme

end AlgebraicGeometry
