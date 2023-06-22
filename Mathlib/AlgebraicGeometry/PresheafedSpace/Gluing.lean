/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.presheafed_space.gluing
! leanprover-community/mathlib commit 533f62f4dd62a5aad24a04326e6e787c8f7e98b1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion.Basic
import Mathlib.AlgebraicGeometry.LocallyRingedSpace.HasColimits

/-!
# Gluing Structured spaces

Given a family of gluing data of structured spaces (presheafed spaces, sheafed spaces, or locally
ringed spaces), we may glue them together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `algebraic_geometry.PresheafedSpace.glue_data`: A structure containing the family of gluing data.
* `Category_theory.glue_data.glued`: The glued presheafed space.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `Category_theory.glue_data.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.

## Main results

* `algebraic_geometry.PresheafedSpace.glue_data.ι_IsOpenImmersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.
* `algebraic_geometry.PresheafedSpace.glue_data.ι_jointly_surjective` : The underlying maps of
  `ι i : U i ⟶ glued` are jointly surjective.
* `algebraic_geometry.PresheafedSpace.glue_data.V_pullback_cone_is_limit` : `V i j` is the pullback
  (intersection) of `U i` and `U j` over the glued space.

Analogous results are also provided for `SheafedSpace` and `LocallyRingedSpace`.

## Implementation details

Almost the whole file is dedicated to showing tht `ι i` is an open immersion. The fact that
this is an open embedding of topological spaces follows from `topology.gluing.lean`, and it remains
to construct `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, ι i '' U)` for each `U ⊆ U i`.
Since `Γ(𝒪_X, ι i '' U)` is the the limit of `diagram_over_open`, the components of the structure
sheafs of the spaces in the gluing diagram, we need to construct a map
`ι_inv_app_π_app : Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing diagram.

We will refer to ![this diagram](https://i.imgur.com/P0phrwr.png) in the following doc strings.
The `X` is the glued space, and the dotted arrow is a partial inverse guaranteed by the fact
that it is an open immersion. The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, _)` is given by the composition
of the red arrows, and the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{V_{jk}}, _)` is given by the composition of the
blue arrows. To lift this into a map from `Γ(𝒪_X, ι i '' U)`, we also need to show that these
commute with the maps in the diagram (the green arrows), which is just a lengthy diagram-chasing.

-/

set_option linter.uppercaseLean3 false

noncomputable section

open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpace

open CategoryTheory.GlueData

namespace AlgebraicGeometry

universe v u

variable (C : Type u) [Category.{v} C]

namespace PresheafedSpace

/-- A family of gluing data consists of
1. An index type `J`
2. A presheafed space `U i` for each `i : J`.
3. A presheafed space `V i j` for each `i j : J`.
  (Note that this is `J × J → PresheafedSpace C` rather than `J → J → PresheafedSpace C` to
  connect to the limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.
-/
-- Porting note : removed
-- @[nolint has_nonempty_instance]
structure GlueData extends GlueData (PresheafedSpace.{u, v, v} C) where
  f_open : ∀ i j, IsOpenImmersion (f i j)
#align algebraic_geometry.PresheafedSpace.glue_data AlgebraicGeometry.PresheafedSpace.GlueData

attribute [instance] GlueData.f_open

namespace GlueData

variable {C}
variable (D : GlueData.{v, u} C)

local notation "𝖣" => D.toGlueData

local notation "π₁ " i ", " j ", " k => @pullback.fst _ _ _ _ _ (D.f i j) (D.f i k) _

local notation "π₂ " i ", " j ", " k => @pullback.snd _ _ _ _ _ (D.f i j) (D.f i k) _

set_option quotPrecheck false
local notation "π₁⁻¹ " i ", " j ", " k =>
  (PresheafedSpace.IsOpenImmersion.pullbackFstOfRight (D.f i j) (D.f i k)).invApp

set_option quotPrecheck false
local notation "π₂⁻¹ " i ", " j ", " k =>
  (PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft (D.f i j) (D.f i k)).invApp

/-- The glue data of topological spaces associated to a family of glue data of PresheafedSpaces. -/
abbrev toTopGlueData : TopCat.GlueData :=
  { f_open := fun i j => (D.f_open i j).base_open
    toGlueData := 𝖣.mapGlueData (forget C) }
#align algebraic_geometry.PresheafedSpace.glue_data.to_Top_glue_data AlgebraicGeometry.PresheafedSpace.GlueData.toTopGlueData

theorem ι_openEmbedding [HasLimits C] (i : D.J) : OpenEmbedding (𝖣.ι i).base := by
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) _]
  -- Porting note : added this erewrite
  erw [coe_comp]
  refine
    OpenEmbedding.comp
      (TopCat.homeoOfIso (𝖣.gluedIso (PresheafedSpace.forget _)).symm).openEmbedding
      (D.toTopGlueData.ι_openEmbedding i)
#align algebraic_geometry.PresheafedSpace.glue_data.ι_open_embedding AlgebraicGeometry.PresheafedSpace.GlueData.ι_openEmbedding

theorem pullback_base (i j k : D.J) (S : Set (D.V (i, j)).carrier) :
    (π₂ i, j, k) '' ((π₁ i, j, k) ⁻¹' S) = D.f i k ⁻¹' (D.f i j '' S) := by
  have eq₁ : _ = (π₁ i, j, k).base := PreservesPullback.iso_hom_fst (forget C) _ _
  have eq₂ : _ = (π₂ i, j, k).base := PreservesPullback.iso_hom_snd (forget C) _ _
  rw [← eq₁, ← eq₂]
  -- Porting note : `rw` to `erw` on `coe_comp`
  erw [coe_comp]
  rw [Set.image_comp]
  -- Porting note : `rw` to `erw` on `coe_comp`
  erw [coe_comp]
  rw [Set.preimage_comp, Set.image_preimage_eq, TopCat.pullback_snd_image_fst_preimage]
  rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align algebraic_geometry.PresheafedSpace.glue_data.pullback_base AlgebraicGeometry.PresheafedSpace.GlueData.pullback_base

/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/0GiBUh6.png) commute. -/
@[simp, reassoc]
theorem f_invApp_f_app (i j k : D.J) (U : Opens (D.V (i, j)).carrier) :
    (D.f_open i j).invApp U ≫ (D.f i k).c.app _ =
      (π₁ i, j, k).c.app (op U) ≫
        (π₂⁻¹ i, j, k) (unop _) ≫
          (D.V _).presheaf.map
            (eqToHom
              (by
                delta IsOpenImmersion.openFunctor
                dsimp only [Functor.op, IsOpenMap.functor, Opens.map, unop_op]
                congr
                apply pullback_base)) := by
  have := PresheafedSpace.congr_app (@pullback.condition _ _ _ _ _ (D.f i j) (D.f i k) _)
  dsimp only [comp_c_app] at this
  rw [← cancel_epi (inv ((D.f_open i j).invApp U)), IsIso.inv_hom_id_assoc,
    IsOpenImmersion.inv_invApp]
  simp_rw [Category.assoc]
  erw [(π₁ i, j, k).c.naturality_assoc, reassoc_of% this, ← Functor.map_comp_assoc,
    IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_invApp_assoc, ←
    (D.V (i, k)).presheaf.map_comp, ← (D.V (i, k)).presheaf.map_comp]
  -- Porting note : need to provide an explicit argument, otherwise Lean does not know which
  -- category we are talking about
  convert (Category.comp_id ((f D.toGlueData i k).c.app _)).symm
  erw [(D.V (i, k)).presheaf.map_id]
  rfl
#align algebraic_geometry.PresheafedSpace.glue_data.f_inv_app_f_app AlgebraicGeometry.PresheafedSpace.GlueData.f_invApp_f_app

/-- We can prove the `eq` along with the lemma. Thus this is bundled together here, and the
lemma itself is separated below.
-/
theorem snd_invApp_t_app' (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier) :
    ∃ eq,
      (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ ≫ (D.V (k, i)).presheaf.map (eqToHom eq) =
        (D.t' k i j).c.app _ ≫ (π₁⁻¹ k, j, i) (unop _) := by
  fconstructor
  -- Porting note : I don't what the magic was in Lean3 proof, it just skipped the proof of `eq`
  . delta IsOpenImmersion.openFunctor
    dsimp only [Functor.op, Opens.map, IsOpenMap.functor, unop_op, Opens.coe_mk]
    congr
    have := (𝖣.t_fac k i j).symm
    rw [←IsIso.inv_comp_eq] at this
    replace this := (congr_arg ((PresheafedSpace.Hom.base .)) this).symm
    replace this := congr_arg (ContinuousMap.toFun .) this
    dsimp at this
    rw [coe_comp, coe_comp] at this
    rw [this, Set.image_comp, Set.image_comp, Set.preimage_image_eq]
    swap
    . refine Function.HasLeftInverse.injective ⟨(D.t i k).base, fun x => ?_⟩
      rw [←comp_apply, ←comp_base, D.t_inv, id_base, id_apply]
    refine congr_arg (_ '' .) ?_
    refine congr_fun ?_ _
    refine Set.image_eq_preimage_of_inverse ?_ ?_
    . intro x
      rw [←comp_apply, ←comp_base, IsIso.inv_hom_id, id_base, id_apply]
    . intro x
      rw [←comp_apply, ←comp_base, IsIso.hom_inv_id, id_base, id_apply]
  . rw [← IsIso.eq_inv_comp, IsOpenImmersion.inv_invApp, Category.assoc,
      (D.t' k i j).c.naturality_assoc]
    simp_rw [← Category.assoc]
    erw [← comp_c_app]
    rw [congr_app (D.t_fac k i j), comp_c_app]
    simp_rw [Category.assoc]
    erw [IsOpenImmersion.inv_naturality, IsOpenImmersion.inv_naturality_assoc,
      IsOpenImmersion.app_inv_app'_assoc]
    simp_rw [← (𝖣.V (k, i)).presheaf.map_comp, eqToHom_map (Functor.op _), eqToHom_op,
      eqToHom_trans]
    rintro x ⟨y, -, eq⟩
    replace eq := ConcreteCategory.congr_arg (𝖣.t i k).base eq
    change ((π₂ i, j, k) ≫ D.t i k).base y = (D.t k i ≫ D.t i k).base x at eq
    rw [𝖣.t_inv, id_base, TopCat.id_app] at eq
    subst eq
    use (inv (D.t' k i j)).base y
    change (inv (D.t' k i j) ≫ π₁ k, i, j).base y = _
    congr 2
    rw [IsIso.inv_comp_eq, 𝖣.t_fac_assoc, 𝖣.t_inv, Category.comp_id]
#align algebraic_geometry.PresheafedSpace.glue_data.snd_inv_app_t_app' AlgebraicGeometry.PresheafedSpace.GlueData.snd_invApp_t_app'

/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/q6X1GJ9.png) commute. -/
@[simp, reassoc]
theorem snd_invApp_t_app (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier) :
    (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ =
      (D.t' k i j).c.app _ ≫
        (π₁⁻¹ k, j, i) (unop _) ≫
          (D.V (k, i)).presheaf.map (eqToHom (D.snd_invApp_t_app' i j k U).choose.symm) := by
  have e := (D.snd_invApp_t_app' i j k U).choose_spec
  replace e := reassoc_of% e
  rw [← e]
  simp [eqToHom_map]
#align algebraic_geometry.PresheafedSpace.glue_data.snd_inv_app_t_app AlgebraicGeometry.PresheafedSpace.GlueData.snd_invApp_t_app

variable [HasLimits C]

theorem ι_image_preimage_eq (i j : D.J) (U : Opens (D.U i).carrier) :
    (Opens.map (𝖣.ι j).base).obj ((D.ι_openEmbedding i).isOpenMap.functor.obj U) =
      (D.f_open j i).openFunctor.obj
        ((Opens.map (𝖣.t j i).base).obj ((Opens.map (𝖣.f i j).base).obj U)) := by
  ext1
  dsimp only [Opens.map_coe, IsOpenMap.functor_obj_coe]
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) i, ←
    show _ = (𝖣.ι j).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) j]
  -- Porting note : change `rw` to `erw` on `coe_comp`
  erw [coe_comp, coe_comp, coe_comp]
  rw [Set.image_comp, Set.preimage_comp]
  erw [Set.preimage_image_eq]
  . refine' Eq.trans (D.toTopGlueData.preimage_image_eq_image' _ _ _) _
    dsimp
    rw [coe_comp, Set.image_comp]
    refine congr_arg (_ '' .) ?_
    rw [Set.eq_preimage_iff_image_eq, ← Set.image_comp]
    swap
    . apply CategoryTheory.ConcreteCategory.bijective_of_isIso
    change (D.t i j ≫ D.t j i).base '' _ = _
    rw [𝖣.t_inv]
    simp
  · rw [←coe_comp, ← TopCat.mono_iff_injective]
    infer_instance
#align algebraic_geometry.PresheafedSpace.glue_data.ι_image_preimage_eq AlgebraicGeometry.PresheafedSpace.GlueData.ι_image_preimage_eq

/-- (Implementation). The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, 𝖣.ι j ⁻¹' (𝖣.ι i '' U))` -/
def opensImagePreimageMap (i j : D.J) (U : Opens (D.U i).carrier) :
    (D.U i).presheaf.obj (op U) ⟶ (D.U j).presheaf.obj _ :=
  (D.f i j).c.app (op U) ≫
    (D.t j i).c.app _ ≫
      (D.f_open j i).invApp (unop _) ≫
        (𝖣.U j).presheaf.map (eqToHom (D.ι_image_preimage_eq i j U)).op
#align algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap

theorem opensImagePreimageMap_app' (i j k : D.J) (U : Opens (D.U i).carrier) :
    ∃ eq,
      D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ =
        ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
          (π₂⁻¹ j, i, k) (unop _) ≫ (D.V (j, k)).presheaf.map (eqToHom Eq) := by
  constructor
  delta opensImagePreimageMap
  simp_rw [Category.assoc]
  rw [(D.f j k).c.naturality, f_inv_app_f_app_assoc]
  erw [← (D.V (j, k)).presheaf.map_comp]
  simp_rw [← Category.assoc]
  erw [← comp_c_app, ← comp_c_app]
  simp_rw [Category.assoc]
  dsimp only [functor.op, unop_op, Quiver.Hom.unop_op]
  rw [eqToHom_map (opens.map _), eqToHom_op, eqToHom_trans]
  congr
#align algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map_app' AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app'

/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/mBzV1Rx.png) commute. -/
theorem opensImagePreimageMap_app (i j k : D.J) (U : Opens (D.U i).carrier) :
    D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ =
      ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
        (π₂⁻¹ j, i, k) (unop _) ≫
          (D.V (j, k)).presheaf.map (eqToHom (opensImagePreimageMap_app' D i j k U).some) :=
  (opensImagePreimageMap_app' D i j k U).choose_spec
#align algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map_app AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app

-- This is proved separately since `reassoc` somehow timeouts.
theorem opensImagePreimageMap_app_assoc (i j k : D.J) (U : Opens (D.U i).carrier) {X' : C}
    (f' : _ ⟶ X') :
    D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ ≫ f' =
      ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
        (π₂⁻¹ j, i, k) (unop _) ≫
          (D.V (j, k)).presheaf.map (eqToHom (opensImagePreimageMap_app' D i j k U).some) ≫ f' := by
  simpa only [Category.assoc] using
    congr_arg (fun g => g ≫ f') (opens_image_preimage_map_app D i j k U)
#align algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map_app_assoc AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app_assoc

/-- (Implementation) Given an open subset of one of the spaces `U ⊆ Uᵢ`, the sheaf component of
the image `ι '' U` in the glued space is the limit of this diagram. -/
abbrev diagramOverOpen {i : D.J} (U : Opens (D.U i).carrier) : (WalkingMultispan _ _)ᵒᵖ ⥤ C :=
  componentwiseDiagram 𝖣.diagram.multispan ((D.ι_openEmbedding i).isOpenMap.functor.obj U)
#align algebraic_geometry.PresheafedSpace.glue_data.diagram_over_open AlgebraicGeometry.PresheafedSpace.GlueData.diagramOverOpen

/-- (Implementation)
The projection from the limit of `diagram_over_open` to a component of `D.U j`. -/
abbrev diagramOverOpenπ {i : D.J} (U : Opens (D.U i).carrier) (j : D.J) :=
  limit.π (D.diagramOverOpen U) (op (WalkingMultispan.right j))
#align algebraic_geometry.PresheafedSpace.glue_data.diagram_over_open_π AlgebraicGeometry.PresheafedSpace.GlueData.diagramOverOpenπ

/-- (Implementation) We construct the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing
diagram. We will lift these maps into `ι_inv_app`. -/
def ιInvAppπApp {i : D.J} (U : Opens (D.U i).carrier) (j) :
    (𝖣.U i).presheaf.obj (op U) ⟶ (D.diagramOverOpen U).obj (op j) := by
  rcases j with (⟨j, k⟩ | j)
  · refine'
      D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom _)
    rw [functor.op_obj]
    congr 1; ext1
    dsimp only [functor.op_obj, opens.map_coe, unop_op, IsOpenMap.functor_obj_coe]
    rw [Set.preimage_preimage]
    change (D.f j k ≫ 𝖣.ι j).base ⁻¹' _ = _
    congr 3
    exact colimit.w 𝖣.diagram.multispan (walking_multispan.hom.fst (j, k))
  · exact D.opens_image_preimage_map i j U
#align algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app_π_app AlgebraicGeometry.PresheafedSpace.GlueData.ιInvAppπApp

/-- (Implementation) The natural map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, 𝖣.ι i '' U)`.
This forms the inverse of `(𝖣.ι i).c.app (op U)`. -/
def ιInvApp {i : D.J} (U : Opens (D.U i).carrier) :
    (D.U i).presheaf.obj (op U) ⟶ limit (D.diagramOverOpen U) :=
  limit.lift (D.diagramOverOpen U)
    { pt := (D.U i).presheaf.obj (op U)
      π :=
        { app := fun j => D.ιInvAppπApp U (unop j)
          naturality' := fun X Y f' => by
            induction X using Opposite.rec'
            induction Y using Opposite.rec'
            let f : Y ⟶ X := f'.unop; have : f' = f.op := rfl; clear_value f; subst this
            rcases f with (_ | ⟨j, k⟩ | ⟨j, k⟩)
            · erw [Category.id_comp, CategoryTheory.Functor.map_id]
              rw [Category.comp_id]
            · erw [Category.id_comp]; congr 1
            erw [Category.id_comp]
            -- It remains to show that the blue is equal to red + green in the original diagram.
            -- The proof strategy is illustrated in ![this diagram](https://i.imgur.com/mBzV1Rx.png)
            -- where we prove red = pink = light-blue = green = blue.
            change
              D.opens_image_preimage_map i j U ≫
                  (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom _) =
                D.opens_image_preimage_map _ _ _ ≫
                  ((D.f k j).c.app _ ≫ (D.t j k).c.app _) ≫ (D.V (j, k)).presheaf.map (eqToHom _)
            erw [opens_image_preimage_map_app_assoc]
            simp_rw [Category.assoc]
            erw [opens_image_preimage_map_app_assoc, (D.t j k).c.naturality_assoc]
            rw [snd_inv_app_t_app_assoc]
            erw [← PresheafedSpace.comp_c_app_assoc]
            -- light-blue = green is relatively easy since the part that differs does not involve
            -- partial inverses.
            have :
              D.t' j k i ≫ (π₁ k, i, j) ≫ D.t k i ≫ 𝖣.f i k =
                (pullback_symmetry _ _).Hom ≫ (π₁ j, i, k) ≫ D.t j i ≫ D.f i j := by
              rw [← 𝖣.t_fac_assoc, 𝖣.t'_comp_eq_pullbackSymmetry_assoc,
                pullback_symmetry_hom_comp_snd_assoc, pullback.condition, 𝖣.t_fac_assoc]
            rw [congr_app this]
            erw [PresheafedSpace.comp_c_app_assoc (pullback_symmetry _ _).Hom]
            simp_rw [Category.assoc]
            congr 1
            rw [← IsIso.eq_inv_comp]
            erw [IsOpenImmersion.inv_inv_app]
            simp_rw [Category.assoc]
            erw [nat_trans.naturality_assoc, ← PresheafedSpace.comp_c_app_assoc,
              congr_app (pullback_symmetry_hom_comp_snd _ _)]
            simp_rw [Category.assoc]
            erw [IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.inv_naturality_assoc,
              IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_inv_app_assoc]
            repeat' erw [← (D.V (j, k)).presheaf.map_comp]
            congr } }
#align algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app AlgebraicGeometry.PresheafedSpace.GlueData.ιInvApp

/-- `ι_inv_app` is the left inverse of `D.ι i` on `U`. -/
theorem ιInvApp_π {i : D.J} (U : Opens (D.U i).carrier) :
    ∃ eq, D.ιInvApp U ≫ D.diagramOverOpenπ U i = (D.U i).presheaf.map (eqToHom Eq) := by
  constructor
  delta ι_inv_app
  rw [limit.lift_π]
  change D.opens_image_preimage_map i i U = _
  dsimp [opens_image_preimage_map]
  rw [congr_app (D.t_id _), id_c_app, ← functor.map_comp]
  erw [IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_inv_app'_assoc]
  simp only [eqToHom_op, eqToHom_trans, eqToHom_map (functor.op _), ← functor.map_comp]
  rw [set.range_iff_surjective.mpr _]
  · simp
  · rw [← TopCat.epi_iff_surjective]
    infer_instance
#align algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app_π AlgebraicGeometry.PresheafedSpace.GlueData.ιInvApp_π

/-- The `eqToHom` given by `ι_inv_app_π`. -/
abbrev ιInvAppπEqMap {i : D.J} (U : Opens (D.U i).carrier) :=
  (D.U i).presheaf.map (eqToIso (D.ιInvApp_π U).some).inv
#align algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app_π_eq_map AlgebraicGeometry.PresheafedSpace.GlueData.ιInvAppπEqMap

/-- `ι_inv_app` is the right inverse of `D.ι i` on `U`. -/
theorem π_ιInvApp_π (i j : D.J) (U : Opens (D.U i).carrier) :
    D.diagramOverOpenπ U i ≫ D.ιInvAppπEqMap U ≫ D.ιInvApp U ≫ D.diagramOverOpenπ U j =
      D.diagramOverOpenπ U j := by
  rw [←
    cancel_mono
      ((componentwise_diagram 𝖣.diagram.multispan _).map
          (Quiver.Hom.op (walking_multispan.hom.snd (i, j))) ≫
        𝟙 _)]
  simp_rw [Category.assoc]
  rw [limit.w_assoc]
  erw [limit.lift_π_assoc]
  rw [Category.comp_id, Category.comp_id]
  change _ ≫ _ ≫ (_ ≫ _) ≫ _ = _
  rw [congr_app (D.t_id _), id_c_app]
  simp_rw [Category.assoc]
  rw [← functor.map_comp_assoc, IsOpenImmersion.inv_naturality_assoc]
  erw [IsOpenImmersion.app_inv_app_assoc]
  iterate 3 rw [← functor.map_comp_assoc]
  rw [nat_trans.naturality_assoc]
  erw [← (D.V (i, j)).presheaf.map_comp]
  convert
    limit.w (componentwise_diagram 𝖣.diagram.multispan _)
      (Quiver.Hom.op (walking_multispan.hom.fst (i, j)))
  · rw [Category.comp_id]
    apply (config := { instances := false }) mono_comp
    change mono ((_ ≫ D.f j i).c.app _)
    rw [comp_c_app]
    apply (config := { instances := false }) mono_comp
    erw [D.ι_image_preimage_eq i j U]
    all_goals infer_instance
#align algebraic_geometry.PresheafedSpace.glue_data.π_ι_inv_app_π AlgebraicGeometry.PresheafedSpace.GlueData.π_ιInvApp_π

/-- `ι_inv_app` is the inverse of `D.ι i` on `U`. -/
theorem π_ιInvApp_eq_id (i : D.J) (U : Opens (D.U i).carrier) :
    D.diagramOverOpenπ U i ≫ D.ιInvAppπEqMap U ≫ D.ιInvApp U = 𝟙 _ := by
  ext j
  induction j using Opposite.rec'
  rcases j with (⟨j, k⟩ | ⟨j⟩)
  · rw [←
      limit.w (componentwise_diagram 𝖣.diagram.multispan _)
        (Quiver.Hom.op (walking_multispan.hom.fst (j, k))),
      ← Category.assoc, Category.id_comp]
    congr 1
    simp_rw [Category.assoc]
    apply π_ι_inv_app_π
  · simp_rw [Category.assoc]
    rw [Category.id_comp]
    apply π_ι_inv_app_π
#align algebraic_geometry.PresheafedSpace.glue_data.π_ι_inv_app_eq_id AlgebraicGeometry.PresheafedSpace.GlueData.π_ιInvApp_eq_id

instance componentwise_diagram_π_isIso (i : D.J) (U : Opens (D.U i).carrier) :
    IsIso (D.diagramOverOpenπ U i) := by
  use D.ι_inv_app_π_eq_map U ≫ D.ι_inv_app U
  constructor
  · apply π_ι_inv_app_eq_id
  · rw [Category.assoc, (D.ι_inv_app_π _).choose_spec]
    exact iso.inv_hom_id ((D.to_glue_data.U i).presheaf.mapIso (eq_to_iso _))
#align algebraic_geometry.PresheafedSpace.glue_data.componentwise_diagram_π_IsIso AlgebraicGeometry.PresheafedSpace.GlueData.componentwise_diagram_π_isIso

instance ιIsOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) where
  base_open := D.ι_openEmbedding i
  c_iso U := by erw [← colimit_presheaf_obj_iso_componentwise_limit_hom_π]; infer_instance
#align algebraic_geometry.PresheafedSpace.glue_data.ι_IsOpenImmersion AlgebraicGeometry.PresheafedSpace.GlueData.ιIsOpenImmersion

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.

Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  PullbackCone.isLimitAux' _ fun s => by
    refine' ⟨_, _, _, _⟩
    · refine' PresheafedSpace.IsOpenImmersion.lift (D.f i j) s.fst _
      erw [← D.to_Top_glue_data.preimage_range j i]
      have :
        s.fst.base ≫ D.to_Top_glue_data.to_glue_data.ι i =
          s.snd.base ≫ D.to_Top_glue_data.to_glue_data.ι j := by
        rw [← 𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _, ←
          𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _]
        have := congr_arg PresheafedSpace.hom.base s.condition
        rw [comp_base, comp_base] at this
        reassoc! this
        exact this _
      rw [← Set.image_subset_iff, ← Set.image_univ, ← Set.image_comp, Set.image_univ, ← coe_comp,
        this, coe_comp, ← Set.image_univ, Set.image_comp]
      exact Set.image_subset_range _ _
    · apply IsOpenImmersion.lift_fac
    · rw [← cancel_mono (𝖣.ι j), Category.assoc, ← (𝖣.vPullbackCone i j).condition]
      conv_rhs => rw [← s.condition]
      erw [IsOpenImmersion.lift_fac_assoc]
    · intro m e₁ e₂; rw [← cancel_mono (D.f i j)]; erw [e₁]; rw [IsOpenImmersion.lift_fac]
#align algebraic_geometry.PresheafedSpace.glue_data.V_pullback_cone_is_limit AlgebraicGeometry.PresheafedSpace.GlueData.vPullbackConeIsLimit

theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : D.J) (y : D.U i), (𝖣.ι i).base y = x :=
  𝖣.ι_jointly_surjective (PresheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x
#align algebraic_geometry.PresheafedSpace.glue_data.ι_jointly_surjective AlgebraicGeometry.PresheafedSpace.GlueData.ι_jointly_surjective

end GlueData

end PresheafedSpace

namespace SheafedSpace

variable (C) [HasProducts.{v} C]

/-- A family of gluing data consists of
1. An index type `J`
2. A sheafed space `U i` for each `i : J`.
3. A sheafed space `V i j` for each `i j : J`.
  (Note that this is `J × J → SheafedSpace C` rather than `J → J → SheafedSpace C` to
  connect to the limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.
-/
@[nolint has_nonempty_instance]
structure GlueData extends GlueData (SheafedSpace.{v} C) where
  f_open : ∀ i j, SheafedSpace.IsOpenImmersion (f i j)
#align algebraic_geometry.SheafedSpace.glue_data AlgebraicGeometry.SheafedSpaceₓ.GlueData

attribute [instance] glue_data.f_open

namespace GlueData

variable {C} (D : GlueData C)

local notation "𝖣" => D.toGlueData

/-- The glue data of presheafed spaces associated to a family of glue data of sheafed spaces. -/
abbrev toPresheafedSpaceGlueData : PresheafedSpace.GlueData C :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToPresheafedSpace }
#align algebraic_geometry.SheafedSpace.glue_data.to_PresheafedSpace_glue_data AlgebraicGeometry.SheafedSpaceₓ.GlueData.toPresheafedSpaceGlueData

variable [HasLimits C]

/-- The gluing as sheafed spaces is isomorphic to the gluing as presheafed spaces. -/
abbrev isoPresheafedSpace :
    𝖣.glued.toPresheafedSpace ≅ D.toPresheafedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToPresheafedSpace
#align algebraic_geometry.SheafedSpace.glue_data.iso_PresheafedSpace AlgebraicGeometry.SheafedSpaceₓ.GlueData.isoPresheafedSpace

theorem ι_isoPresheafedSpace_inv (i : D.J) :
    D.toPresheafedSpaceGlueData.toGlueData.ι i ≫ D.isoPresheafedSpace.inv = 𝖣.ι i :=
  𝖣.ι_gluedIso_inv _ _
#align algebraic_geometry.SheafedSpace.glue_data.ι_iso_PresheafedSpace_inv AlgebraicGeometry.SheafedSpaceₓ.GlueData.ι_isoPresheafedSpace_inv

instance ιIsOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  rw [← D.ι_iso_PresheafedSpace_inv]; infer_instance
#align algebraic_geometry.SheafedSpace.glue_data.ι_IsOpenImmersion AlgebraicGeometry.SheafedSpaceₓ.GlueData.ιIsOpenImmersion

theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : D.J) (y : D.U i), (𝖣.ι i).base y = x :=
  𝖣.ι_jointly_surjective (SheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x
#align algebraic_geometry.SheafedSpace.glue_data.ι_jointly_surjective AlgebraicGeometry.SheafedSpaceₓ.GlueData.ι_jointly_surjective

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.

Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToPresheafedSpace i j
    (D.toPresheafedSpaceGlueData.vPullbackConeIsLimit _ _)
#align algebraic_geometry.SheafedSpace.glue_data.V_pullback_cone_is_limit AlgebraicGeometry.SheafedSpaceₓ.GlueData.vPullbackConeIsLimit

end GlueData

end SheafedSpace

namespace LocallyRingedSpace

/-- A family of gluing data consists of
1. An index type `J`
2. A locally ringed space `U i` for each `i : J`.
3. A locally ringed space `V i j` for each `i j : J`.
  (Note that this is `J × J → LocallyRingedSpace` rather than `J → J → LocallyRingedSpace` to
  connect to the limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.
-/
@[nolint has_nonempty_instance]
structure GlueData extends GlueData LocallyRingedSpace where
  f_open : ∀ i j, LocallyRingedSpace.IsOpenImmersion (f i j)
#align algebraic_geometry.LocallyRingedSpace.glue_data AlgebraicGeometry.LocallyRingedSpace.GlueData

attribute [instance] glue_data.f_open

namespace GlueData

variable (D : GlueData)

local notation "𝖣" => D.toGlueData

/-- The glue data of ringed spaces associated to a family of glue data of locally ringed spaces. -/
abbrev toSheafedSpaceGlueData : SheafedSpace.GlueData CommRingCat :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToSheafedSpace }
#align algebraic_geometry.LocallyRingedSpace.glue_data.to_SheafedSpace_glue_data AlgebraicGeometry.LocallyRingedSpace.GlueData.toSheafedSpaceGlueData

/-- The gluing as locally ringed spaces is isomorphic to the gluing as ringed spaces. -/
abbrev isoSheafedSpace : 𝖣.glued.toSheafedSpace ≅ D.toSheafedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToSheafedSpace
#align algebraic_geometry.LocallyRingedSpace.glue_data.iso_SheafedSpace AlgebraicGeometry.LocallyRingedSpace.GlueData.isoSheafedSpace

theorem ι_isoSheafedSpace_inv (i : D.J) :
    D.toSheafedSpaceGlueData.toGlueData.ι i ≫ D.isoSheafedSpace.inv = (𝖣.ι i).1 :=
  𝖣.ι_gluedIso_inv forgetToSheafedSpace i
#align algebraic_geometry.LocallyRingedSpace.glue_data.ι_iso_SheafedSpace_inv AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_isoSheafedSpace_inv

instance ι_isOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  delta IsOpenImmersion; rw [← D.ι_iso_SheafedSpace_inv]
  apply PresheafedSpace.IsOpenImmersion.comp
#align algebraic_geometry.LocallyRingedSpace.glue_data.ι_IsOpenImmersion AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_isOpenImmersion

instance (i j k : D.J) : PreservesLimit (cospan (𝖣.f i j) (𝖣.f i k)) forgetToSheafedSpace :=
  inferInstance

theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : D.J) (y : D.U i), (𝖣.ι i).1.base y = x :=
  𝖣.ι_jointly_surjective
    ((LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) ⋙ forget TopCat) x
#align algebraic_geometry.LocallyRingedSpace.glue_data.ι_jointly_surjective AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.

Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToSheafedSpace i j
    (D.toSheafedSpaceGlueData.vPullbackConeIsLimit _ _)
#align algebraic_geometry.LocallyRingedSpace.glue_data.V_pullback_cone_is_limit AlgebraicGeometry.LocallyRingedSpace.GlueData.vPullbackConeIsLimit

end GlueData

end LocallyRingedSpace

end AlgebraicGeometry
