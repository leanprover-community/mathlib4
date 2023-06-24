/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.gluing
! leanprover-community/mathlib commit 533f62f4dd62a5aad24a04326e6e787c8f7e98b1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.PresheafedSpace.Gluing
import Mathbin.AlgebraicGeometry.OpenImmersion.Scheme

/-!
# Gluing Schemes

Given a family of gluing data of schemes, we may glue them together.

## Main definitions

* `algebraic_geometry.Scheme.glue_data`: A structure containing the family of gluing data.
* `algebraic_geometry.Scheme.glue_data.glued`: The glued scheme.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `algebraic_geometry.Scheme.glue_data.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.
* `algebraic_geometry.Scheme.glue_data.iso_carrier`: The isomorphism between the underlying space
  of the glued scheme and the gluing of the underlying topological spaces.
* `algebraic_geometry.Scheme.open_cover.glue_data`: The glue data associated with an open cover.
* `algebraic_geometry.Scheme.open_cover.from_glue_data`: The canonical morphism
  `𝒰.glue_data.glued ⟶ X`. This has an `is_iso` instance.
* `algebraic_geometry.Scheme.open_cover.glue_morphisms`: We may glue a family of compatible
  morphisms defined on an open cover of a scheme.

## Main results

* `algebraic_geometry.Scheme.glue_data.ι_is_open_immersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.
* `algebraic_geometry.Scheme.glue_data.ι_jointly_surjective` : The underlying maps of
  `ι i : U i ⟶ glued` are jointly surjective.
* `algebraic_geometry.Scheme.glue_data.V_pullback_cone_is_limit` : `V i j` is the pullback
  (intersection) of `U i` and `U j` over the glued space.
* `algebraic_geometry.Scheme.glue_data.ι_eq_iff_rel` : `ι i x = ι j y` if and only if they coincide
  when restricted to `V i i`.
* `algebraic_geometry.Scheme.glue_data.is_open_iff` : An subset of the glued scheme is open iff
  all its preimages in `U i` are open.

## Implementation details

All the hard work is done in `algebraic_geometry/presheafed_space/gluing.lean` where we glue
presheafed spaces, sheafed spaces, and locally ringed spaces.

-/


noncomputable section

universe u

open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpace

open CategoryTheory.GlueData

namespace AlgebraicGeometry

namespace Scheme

/-- A family of gluing data consists of
1. An index type `J`
2. An scheme `U i` for each `i : J`.
3. An scheme `V i j` for each `i j : J`.
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
@[nolint has_nonempty_instance]
structure GlueData extends CategoryTheory.GlueData Scheme where
  f_open : ∀ i j, IsOpenImmersionCat (f i j)
#align algebraic_geometry.Scheme.glue_data AlgebraicGeometry.Scheme.GlueData

attribute [instance] glue_data.f_open

namespace GlueData

variable (D : GlueData)

local notation "𝖣" => D.toGlueData

/-- The glue data of locally ringed spaces spaces associated to a family of glue data of schemes. -/
abbrev toLocallyRingedSpaceGlueData : LocallyRingedSpace.GlueData :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToLocallyRingedSpace }
#align algebraic_geometry.Scheme.glue_data.to_LocallyRingedSpace_glue_data AlgebraicGeometry.Scheme.GlueData.toLocallyRingedSpaceGlueData

/-- (Implementation). The glued scheme of a glue data.
This should not be used outside this file. Use `Scheme.glue_data.glued` instead. -/
def gluedScheme : Scheme :=
  by
  apply
    LocallyRingedSpace.is_open_immersion.Scheme D.to_LocallyRingedSpace_glue_data.to_glue_data.glued
  intro x
  obtain ⟨i, y, rfl⟩ := D.to_LocallyRingedSpace_glue_data.ι_jointly_surjective x
  refine' ⟨_, _ ≫ D.to_LocallyRingedSpace_glue_data.to_glue_data.ι i, _⟩
  swap; exact (D.U i).affineCover.map y
  constructor
  · dsimp [-Set.mem_range]
    rw [coe_comp, Set.range_comp]
    refine' Set.mem_image_of_mem _ _
    exact (D.U i).affineCover.Covers y
  · infer_instance
#align algebraic_geometry.Scheme.glue_data.glued_Scheme AlgebraicGeometry.Scheme.GlueData.gluedScheme

instance : CreatesColimit 𝖣.diagram.multispan forgetToLocallyRingedSpace :=
  createsColimitOfFullyFaithfulOfIso D.gluedScheme
    (HasColimit.isoOfNatIso (𝖣.diagramIso forgetToLocallyRingedSpace).symm)

instance : PreservesColimit 𝖣.diagram.multispan forgetToTop :=
  by
  delta forget_to_Top LocallyRingedSpace.forget_to_Top
  infer_instance

instance : HasMulticoequalizer 𝖣.diagram :=
  hasColimit_of_created _ forgetToLocallyRingedSpace

/-- The glued scheme of a glued space. -/
abbrev glued : Scheme :=
  𝖣.glued
#align algebraic_geometry.Scheme.glue_data.glued AlgebraicGeometry.Scheme.GlueData.glued

/-- The immersion from `D.U i` into the glued space. -/
abbrev ι (i : D.J) : D.U i ⟶ D.glued :=
  𝖣.ι i
#align algebraic_geometry.Scheme.glue_data.ι AlgebraicGeometry.Scheme.GlueData.ι

/-- The gluing as sheafed spaces is isomorphic to the gluing as presheafed spaces. -/
abbrev isoLocallyRingedSpace :
    D.glued.toLocallyRingedSpace ≅ D.toLocallyRingedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToLocallyRingedSpace
#align algebraic_geometry.Scheme.glue_data.iso_LocallyRingedSpace AlgebraicGeometry.Scheme.GlueData.isoLocallyRingedSpace

theorem ι_isoLocallyRingedSpace_inv (i : D.J) :
    D.toLocallyRingedSpaceGlueData.toGlueData.ι i ≫ D.isoLocallyRingedSpace.inv = 𝖣.ι i :=
  𝖣.ι_gluedIso_inv forgetToLocallyRingedSpace i
#align algebraic_geometry.Scheme.glue_data.ι_iso_LocallyRingedSpace_inv AlgebraicGeometry.Scheme.GlueData.ι_isoLocallyRingedSpace_inv

instance ι_isOpenImmersionCat (i : D.J) : IsOpenImmersionCat (𝖣.ι i) := by
  rw [← D.ι_iso_LocallyRingedSpace_inv]; infer_instance
#align algebraic_geometry.Scheme.glue_data.ι_is_open_immersion AlgebraicGeometry.Scheme.GlueData.ι_isOpenImmersionCat

theorem ι_jointly_surjective (x : 𝖣.glued.carrier) :
    ∃ (i : D.J) (y : (D.U i).carrier), (D.ι i).1.base y = x :=
  𝖣.ι_jointly_surjective (forgetToTop ⋙ forget TopCat) x
#align algebraic_geometry.Scheme.glue_data.ι_jointly_surjective AlgebraicGeometry.Scheme.GlueData.ι_jointly_surjective

@[simp, reassoc]
theorem glue_condition (i j : D.J) : D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i :=
  𝖣.glue_condition i j
#align algebraic_geometry.Scheme.glue_data.glue_condition AlgebraicGeometry.Scheme.GlueData.glue_condition

/-- The pullback cone spanned by `V i j ⟶ U i` and `V i j ⟶ U j`.
This is a pullback diagram (`V_pullback_cone_is_limit`). -/
def vPullbackCone (i j : D.J) : PullbackCone (D.ι i) (D.ι j) :=
  PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)
#align algebraic_geometry.Scheme.glue_data.V_pullback_cone AlgebraicGeometry.Scheme.GlueData.vPullbackCone

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.

Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (D.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToLocallyRingedSpace i j
    (D.toLocallyRingedSpaceGlueData.vPullbackConeIsLimit _ _)
#align algebraic_geometry.Scheme.glue_data.V_pullback_cone_is_limit AlgebraicGeometry.Scheme.GlueData.vPullbackConeIsLimit

/-- The underlying topological space of the glued scheme is isomorphic to the gluing of the
underlying spacess -/
def isoCarrier :
    D.glued.carrier ≅
      D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData.toGlueData.glued :=
  by
  refine' (PresheafedSpace.forget _).mapIso _ ≪≫ glue_data.glued_iso _ (PresheafedSpace.forget _)
  refine'
    SheafedSpace.forget_to_PresheafedSpace.map_iso _ ≪≫ SheafedSpace.glue_data.iso_PresheafedSpace _
  refine'
    LocallyRingedSpace.forget_to_SheafedSpace.map_iso _ ≪≫
      LocallyRingedSpace.glue_data.iso_SheafedSpace _
  exact Scheme.glue_data.iso_LocallyRingedSpace _
#align algebraic_geometry.Scheme.glue_data.iso_carrier AlgebraicGeometry.Scheme.GlueData.isoCarrier

@[simp]
theorem ι_isoCarrier_inv (i : D.J) :
    D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData.toGlueData.ι
          i ≫
        D.isoCarrier.inv =
      (D.ι i).1.base :=
  by
  delta iso_carrier
  simp only [functor.map_iso_inv, iso.trans_inv, iso.trans_assoc, glue_data.ι_glued_iso_inv_assoc,
    functor.map_iso_trans, category.assoc]
  iterate 3 erw [← comp_base]
  simp_rw [← category.assoc]
  rw [D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data.ι_iso_PresheafedSpace_inv i]
  erw [D.to_LocallyRingedSpace_glue_data.ι_iso_SheafedSpace_inv i]
  change (_ ≫ D.iso_LocallyRingedSpace.inv).1.base = _
  rw [D.ι_iso_LocallyRingedSpace_inv i]
#align algebraic_geometry.Scheme.glue_data.ι_iso_carrier_inv AlgebraicGeometry.Scheme.GlueData.ι_isoCarrier_inv

/-- An equivalence relation on `Σ i, D.U i` that holds iff `𝖣 .ι i x = 𝖣 .ι j y`.
See `Scheme.gluing_data.ι_eq_iff`. -/
def Rel (a b : Σ i, ((D.U i).carrier : Type _)) : Prop :=
  a = b ∨
    ∃ x : (D.V (a.1, b.1)).carrier, (D.f _ _).1.base x = a.2 ∧ (D.t _ _ ≫ D.f _ _).1.base x = b.2
#align algebraic_geometry.Scheme.glue_data.rel AlgebraicGeometry.Scheme.GlueData.Rel

theorem ι_eq_iff (i j : D.J) (x : (D.U i).carrier) (y : (D.U j).carrier) :
    (𝖣.ι i).1.base x = (𝖣.ι j).1.base y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩ :=
  by
  refine'
    Iff.trans _
      (D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data.toPresheafedSpaceGlueData.toTopGlueData.ι_eq_iff_rel
        i j x y)
  rw [← ((TopCat.mono_iff_injective D.iso_carrier.inv).mp inferInstance).eq_iff]
  simp_rw [← comp_apply, D.ι_iso_carrier_inv]
#align algebraic_geometry.Scheme.glue_data.ι_eq_iff AlgebraicGeometry.Scheme.GlueData.ι_eq_iff

theorem isOpen_iff (U : Set D.glued.carrier) : IsOpen U ↔ ∀ i, IsOpen ((D.ι i).1.base ⁻¹' U) :=
  by
  rw [← (TopCat.homeoOfIso D.iso_carrier.symm).isOpen_preimage]
  rw [TopCat.GlueData.isOpen_iff]
  apply forall_congr'
  intro i
  erw [← Set.preimage_comp, ← coe_comp, ι_iso_carrier_inv]
#align algebraic_geometry.Scheme.glue_data.is_open_iff AlgebraicGeometry.Scheme.GlueData.isOpen_iff

/-- The open cover of the glued space given by the glue data. -/
def openCover (D : Scheme.GlueData) : OpenCover D.glued
    where
  J := D.J
  obj := D.U
  map := D.ι
  f x := (D.ι_jointly_surjective x).some
  Covers x := ⟨_, (D.ι_jointly_surjective x).choose_spec.choose_spec⟩
#align algebraic_geometry.Scheme.glue_data.open_cover AlgebraicGeometry.Scheme.GlueData.openCover

end GlueData

namespace OpenCover

variable {X : Scheme.{u}} (𝒰 : OpenCover.{u} X)

/-- (Implementation) the transition maps in the glue data associated with an open cover. -/
def gluedCoverT' (x y z : 𝒰.J) :
    pullback (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _)
        (pullback.fst : pullback (𝒰.map x) (𝒰.map z) ⟶ _) ⟶
      pullback (pullback.fst : pullback (𝒰.map y) (𝒰.map z) ⟶ _)
        (pullback.fst : pullback (𝒰.map y) (𝒰.map x) ⟶ _) :=
  by
  refine' (pullback_right_pullback_fst_iso _ _ _).Hom ≫ _
  refine' _ ≫ (pullback_symmetry _ _).Hom
  refine' _ ≫ (pullback_right_pullback_fst_iso _ _ _).inv
  refine' pullback.map _ _ _ _ (pullback_symmetry _ _).Hom (𝟙 _) (𝟙 _) _ _
  · simp [pullback.condition]
  · simp
#align algebraic_geometry.Scheme.open_cover.glued_cover_t' AlgebraicGeometry.Scheme.OpenCover.gluedCoverT'

@[simp, reassoc]
theorem gluedCoverT'_fst_fst (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd := by
  delta glued_cover_t'; simp
#align algebraic_geometry.Scheme.open_cover.glued_cover_t'_fst_fst AlgebraicGeometry.Scheme.OpenCover.gluedCoverT'_fst_fst

@[simp, reassoc]
theorem gluedCoverT'_fst_snd (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  delta glued_cover_t'; simp
#align algebraic_geometry.Scheme.open_cover.glued_cover_t'_fst_snd AlgebraicGeometry.Scheme.OpenCover.gluedCoverT'_fst_snd

@[simp, reassoc]
theorem gluedCoverT'_snd_fst (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ pullback.snd := by
  delta glued_cover_t'; simp
#align algebraic_geometry.Scheme.open_cover.glued_cover_t'_snd_fst AlgebraicGeometry.Scheme.OpenCover.gluedCoverT'_snd_fst

@[simp, reassoc]
theorem gluedCoverT'_snd_snd (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst := by
  delta glued_cover_t'; simp
#align algebraic_geometry.Scheme.open_cover.glued_cover_t'_snd_snd AlgebraicGeometry.Scheme.OpenCover.gluedCoverT'_snd_snd

theorem glued_cover_cocycle_fst (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y ≫ pullback.fst =
      pullback.fst :=
  by apply pullback.hom_ext <;> simp
#align algebraic_geometry.Scheme.open_cover.glued_cover_cocycle_fst AlgebraicGeometry.Scheme.OpenCover.glued_cover_cocycle_fst

theorem glued_cover_cocycle_snd (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y ≫ pullback.snd =
      pullback.snd :=
  by apply pullback.hom_ext <;> simp [pullback.condition]
#align algebraic_geometry.Scheme.open_cover.glued_cover_cocycle_snd AlgebraicGeometry.Scheme.OpenCover.glued_cover_cocycle_snd

theorem glued_cover_cocycle (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y = 𝟙 _ :=
  by
  apply pullback.hom_ext <;> simp_rw [category.id_comp, category.assoc]
  apply glued_cover_cocycle_fst
  apply glued_cover_cocycle_snd
#align algebraic_geometry.Scheme.open_cover.glued_cover_cocycle AlgebraicGeometry.Scheme.OpenCover.glued_cover_cocycle

/-- The glue data associated with an open cover.
The canonical isomorphism `𝒰.glued_cover.glued ⟶ X` is provided by `𝒰.from_glued`. -/
@[simps]
def gluedCover : Scheme.GlueData.{u} where
  J := 𝒰.J
  U := 𝒰.obj
  V := fun ⟨x, y⟩ => pullback (𝒰.map x) (𝒰.map y)
  f x y := pullback.fst
  f_id x := inferInstance
  t x y := (pullbackSymmetry _ _).Hom
  t_id x := by simpa
  t' x y z := gluedCoverT' 𝒰 x y z
  t_fac x y z := by apply pullback.hom_ext <;> simp
  -- The `cocycle` field could have been `by tidy` but lean timeouts.
  cocycle x y z := glued_cover_cocycle 𝒰 x y z
  f_open x := inferInstance
#align algebraic_geometry.Scheme.open_cover.glued_cover AlgebraicGeometry.Scheme.OpenCover.gluedCover

/-- The canonical morphism from the gluing of an open cover of `X` into `X`.
This is an isomorphism, as witnessed by an `is_iso` instance. -/
def fromGlued : 𝒰.gluedCover.glued ⟶ X :=
  by
  fapply multicoequalizer.desc
  exact fun x => 𝒰.map x
  rintro ⟨x, y⟩
  change pullback.fst ≫ _ = ((pullback_symmetry _ _).Hom ≫ pullback.fst) ≫ _
  simpa using pullback.condition
#align algebraic_geometry.Scheme.open_cover.from_glued AlgebraicGeometry.Scheme.OpenCover.fromGlued

@[simp, reassoc]
theorem ι_fromGlued (x : 𝒰.J) : 𝒰.gluedCover.ι x ≫ 𝒰.fromGlued = 𝒰.map x :=
  Multicoequalizer.π_desc _ _ _ _ _
#align algebraic_geometry.Scheme.open_cover.ι_from_glued AlgebraicGeometry.Scheme.OpenCover.ι_fromGlued

theorem fromGlued_injective : Function.Injective 𝒰.fromGlued.1.base :=
  by
  intro x y h
  obtain ⟨i, x, rfl⟩ := 𝒰.glued_cover.ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := 𝒰.glued_cover.ι_jointly_surjective y
  simp_rw [← comp_apply, ← SheafedSpace.comp_base, ← LocallyRingedSpace.comp_val] at h 
  erw [ι_from_glued, ι_from_glued] at h 
  let e :=
    (TopCat.pullbackConeIsLimit _ _).conePointUniqueUpToIso
      (is_limit_of_has_pullback_of_preserves_limit Scheme.forget_to_Top (𝒰.map i) (𝒰.map j))
  rw [𝒰.glued_cover.ι_eq_iff]
  right
  use e.hom ⟨⟨x, y⟩, h⟩
  simp_rw [← comp_apply]
  constructor
  · erw [is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.left]; rfl
  · erw [pullback_symmetry_hom_comp_fst,
      is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right]
    rfl
#align algebraic_geometry.Scheme.open_cover.from_glued_injective AlgebraicGeometry.Scheme.OpenCover.fromGlued_injective

instance fromGlued_stalk_iso (x : 𝒰.gluedCover.glued.carrier) :
    IsIso (PresheafedSpace.stalkMap 𝒰.fromGlued.val x) :=
  by
  obtain ⟨i, x, rfl⟩ := 𝒰.glued_cover.ι_jointly_surjective x
  have :=
    PresheafedSpace.stalk_map.congr_hom _ _
      (congr_arg LocallyRingedSpace.hom.val <| 𝒰.ι_from_glued i) x
  erw [PresheafedSpace.stalk_map.comp] at this 
  rw [← is_iso.eq_comp_inv] at this 
  rw [this]
  infer_instance
#align algebraic_geometry.Scheme.open_cover.from_glued_stalk_iso AlgebraicGeometry.Scheme.OpenCover.fromGlued_stalk_iso

theorem fromGlued_open_map : IsOpenMap 𝒰.fromGlued.1.base :=
  by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  rw [𝒰.glued_cover.is_open_iff] at hU 
  use 𝒰.from_glued.val.base '' U ∩ Set.range (𝒰.map (𝒰.f x)).1.base
  use Set.inter_subset_left _ _
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply show is_open_immersion (𝒰.map (𝒰.f x)) by infer_instance.base_open.IsOpenMap
    convert hU (𝒰.f x) using 1
    rw [← ι_from_glued]; erw [coe_comp]; rw [Set.preimage_comp]
    congr 1
    refine' Set.preimage_image_eq _ 𝒰.from_glued_injective
  · exact ⟨hx, 𝒰.covers x⟩
#align algebraic_geometry.Scheme.open_cover.from_glued_open_map AlgebraicGeometry.Scheme.OpenCover.fromGlued_open_map

theorem fromGlued_openEmbedding : OpenEmbedding 𝒰.fromGlued.1.base :=
  openEmbedding_of_continuous_injective_open (by continuity) 𝒰.fromGlued_injective
    𝒰.fromGlued_open_map
#align algebraic_geometry.Scheme.open_cover.from_glued_open_embedding AlgebraicGeometry.Scheme.OpenCover.fromGlued_openEmbedding

instance : Epi 𝒰.fromGlued.val.base :=
  by
  rw [TopCat.epi_iff_surjective]
  intro x
  obtain ⟨y, h⟩ := 𝒰.covers x
  use (𝒰.glued_cover.ι (𝒰.f x)).1.base y
  rw [← comp_apply]
  rw [← 𝒰.ι_from_glued (𝒰.f x)] at h 
  exact h

instance fromGlued_open_immersion : IsOpenImmersionCat 𝒰.fromGlued :=
  SheafedSpace.IsOpenImmersion.of_stalk_iso _ 𝒰.fromGlued_openEmbedding
#align algebraic_geometry.Scheme.open_cover.from_glued_open_immersion AlgebraicGeometry.Scheme.OpenCover.fromGlued_open_immersion

instance : IsIso 𝒰.fromGlued :=
  by
  apply
    is_iso_of_reflects_iso _
      (Scheme.forget_to_LocallyRingedSpace ⋙
        LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace)
  change @is_iso (PresheafedSpace _) _ _ _ 𝒰.from_glued.val
  apply PresheafedSpace.is_open_immersion.to_iso

/-- Given an open cover of `X`, and a morphism `𝒰.obj x ⟶ Y` for each open subscheme in the cover,
such that these morphisms are compatible in the intersection (pullback), we may glue the morphisms
together into a morphism `X ⟶ Y`.

Note:
If `X` is exactly (defeq to) the gluing of `U i`, then using `multicoequalizer.desc` suffices.
-/
def glueMorphisms {Y : Scheme} (f : ∀ x, 𝒰.obj x ⟶ Y)
    (hf : ∀ x y, (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _) ≫ f x = pullback.snd ≫ f y) :
    X ⟶ Y := by
  refine' inv 𝒰.from_glued ≫ _
  fapply multicoequalizer.desc
  exact f
  rintro ⟨i, j⟩
  change pullback.fst ≫ f i = (_ ≫ _) ≫ f j
  erw [pullback_symmetry_hom_comp_fst]
  exact hf i j
#align algebraic_geometry.Scheme.open_cover.glue_morphisms AlgebraicGeometry.Scheme.OpenCover.glueMorphisms

@[simp, reassoc]
theorem ι_glueMorphisms {Y : Scheme} (f : ∀ x, 𝒰.obj x ⟶ Y)
    (hf : ∀ x y, (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _) ≫ f x = pullback.snd ≫ f y)
    (x : 𝒰.J) : 𝒰.map x ≫ 𝒰.glueMorphisms f hf = f x :=
  by
  rw [← ι_from_glued, category.assoc]
  erw [is_iso.hom_inv_id_assoc, multicoequalizer.π_desc]
#align algebraic_geometry.Scheme.open_cover.ι_glue_morphisms AlgebraicGeometry.Scheme.OpenCover.ι_glueMorphisms

theorem hom_ext {Y : Scheme} (f₁ f₂ : X ⟶ Y) (h : ∀ x, 𝒰.map x ≫ f₁ = 𝒰.map x ≫ f₂) : f₁ = f₂ :=
  by
  rw [← cancel_epi 𝒰.from_glued]
  apply multicoequalizer.hom_ext
  intro x
  erw [multicoequalizer.π_desc_assoc]
  erw [multicoequalizer.π_desc_assoc]
  exact h x
#align algebraic_geometry.Scheme.open_cover.hom_ext AlgebraicGeometry.Scheme.OpenCover.hom_ext

end OpenCover

end Scheme

end AlgebraicGeometry

