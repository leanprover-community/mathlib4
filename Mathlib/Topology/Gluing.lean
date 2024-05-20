/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.GlueData
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Tactic.Generalize

#align_import topology.gluing from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!
# Gluing Topological spaces

Given a family of gluing data (see `Mathlib/CategoryTheory/GlueData.lean`), we can then glue them
together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `TopCat.GlueData`: A structure containing the family of gluing data.
* `CategoryTheory.GlueData.glued`: The glued topological space.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `CategoryTheory.GlueData.ι`: The immersion `ι i : U i ⟶ glued` for each `i : ι`.
* `TopCat.GlueData.Rel`: A relation on `Σ i, D.U i` defined by `⟨i, x⟩ ~ ⟨j, y⟩` iff
    `⟨i, x⟩ = ⟨j, y⟩` or `t i j x = y`. See `TopCat.GlueData.ι_eq_iff_rel`.
* `TopCat.GlueData.mk`: A constructor of `GlueData` whose conditions are stated in terms of
  elements rather than subobjects and pullbacks.
* `TopCat.GlueData.ofOpenSubsets`: Given a family of open sets, we may glue them into a new
  topological space. This new space embeds into the original space, and is homeomorphic to it if
  the given family is an open cover (`TopCat.GlueData.openCoverGlueHomeo`).

## Main results

* `TopCat.GlueData.isOpen_iff`: A set in `glued` is open iff its preimage along each `ι i` is
    open.
* `TopCat.GlueData.ι_jointly_surjective`: The `ι i`s are jointly surjective.
* `TopCat.GlueData.rel_equiv`: `Rel` is an equivalence relation.
* `TopCat.GlueData.ι_eq_iff_rel`: `ι i x = ι j y ↔ ⟨i, x⟩ ~ ⟨j, y⟩`.
* `TopCat.GlueData.image_inter`: The intersection of the images of `U i` and `U j` in `glued` is
    `V i j`.
* `TopCat.GlueData.preimage_range`: The preimage of the image of `U i` in `U j` is `V i j`.
* `TopCat.GlueData.preimage_image_eq_image`: The preimage of the image of some `U ⊆ U i` is
    given by XXX.
* `TopCat.GlueData.ι_openEmbedding`: Each of the `ι i`s are open embeddings.

-/

noncomputable section

open TopologicalSpace CategoryTheory

universe v u

open CategoryTheory.Limits

namespace TopCat

/-- A family of gluing data consists of
1. An index type `J`
2. An object `U i` for each `i : J`.
3. An object `V i j` for each `i j : J`.
  (Note that this is `J × J → TopCat` rather than `J → J → TopCat` to connect to the
  limits library easier.)
4. An open embedding `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
    (This merely means that `V i j ∩ V i k ⊆ t i j ⁻¹' (V j i ∩ V j k)`.)
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the topological spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.

Most of the times it would be easier to use the constructor `TopCat.GlueData.mk'` where the
conditions are stated in a less categorical way.
-/
-- porting note (#5171): removed @[nolint has_nonempty_instance]
structure GlueData extends GlueData TopCat where
  f_open : ∀ i j, OpenEmbedding (f i j)
  f_mono := fun i j => (TopCat.mono_iff_injective _).mpr (f_open i j).toEmbedding.inj
set_option linter.uppercaseLean3 false in
#align Top.glue_data TopCat.GlueData

namespace GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

theorem π_surjective : Function.Surjective 𝖣.π :=
  (TopCat.epi_iff_surjective 𝖣.π).mp inferInstance
set_option linter.uppercaseLean3 false in
#align Top.glue_data.π_surjective TopCat.GlueData.π_surjective

theorem isOpen_iff (U : Set 𝖣.glued) : IsOpen U ↔ ∀ i, IsOpen (𝖣.ι i ⁻¹' U) := by
  delta CategoryTheory.GlueData.ι
  simp_rw [← Multicoequalizer.ι_sigmaπ 𝖣.diagram]
  rw [← (homeoOfIso (Multicoequalizer.isoCoequalizer 𝖣.diagram).symm).isOpen_preimage]
  rw [coequalizer_isOpen_iff]
  dsimp only [GlueData.diagram_l, GlueData.diagram_left, GlueData.diagram_r, GlueData.diagram_right,
    parallelPair_obj_one]
  rw [colimit_isOpen_iff.{_,u}]  -- Porting note: changed `.{u}` to `.{_,u}`.  fun fact: the proof
                                 -- breaks down if this `rw` is merged with the `rw` above.
  constructor
  · intro h j; exact h ⟨j⟩
  · intro h j; cases j; apply h
set_option linter.uppercaseLean3 false in
#align Top.glue_data.is_open_iff TopCat.GlueData.isOpen_iff

theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : _) (y : D.U i), 𝖣.ι i y = x :=
  𝖣.ι_jointly_surjective (forget TopCat) x
set_option linter.uppercaseLean3 false in
#align Top.glue_data.ι_jointly_surjective TopCat.GlueData.ι_jointly_surjective

/-- An equivalence relation on `Σ i, D.U i` that holds iff `𝖣 .ι i x = 𝖣 .ι j y`.
See `TopCat.GlueData.ι_eq_iff_rel`.
-/
def Rel (a b : Σ i, ((D.U i : TopCat) : Type _)) : Prop :=
  a = b ∨ ∃ x : D.V (a.1, b.1), D.f _ _ x = a.2 ∧ D.f _ _ (D.t _ _ x) = b.2
set_option linter.uppercaseLean3 false in
#align Top.glue_data.rel TopCat.GlueData.Rel

theorem rel_equiv : Equivalence D.Rel :=
  ⟨fun x => Or.inl (refl x), by
    rintro a b (⟨⟨⟩⟩ | ⟨x, e₁, e₂⟩)
    exacts [Or.inl rfl, Or.inr ⟨D.t _ _ x, by simp [e₁, e₂]⟩], by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ (⟨⟨⟩⟩ | ⟨x, e₁, e₂⟩)
    · exact id
    rintro (⟨⟨⟩⟩ | ⟨y, e₃, e₄⟩)
    · exact Or.inr ⟨x, e₁, e₂⟩
    let z := (pullbackIsoProdSubtype (D.f j i) (D.f j k)).inv ⟨⟨_, _⟩, e₂.trans e₃.symm⟩
    have eq₁ : (D.t j i) ((pullback.fst : _ /-(D.f j k)-/ ⟶ D.V (j, i)) z) = x := by simp [z]
    have eq₂ : (pullback.snd : _ ⟶ D.V _) z = y := pullbackIsoProdSubtype_inv_snd_apply _ _ _
    clear_value z
    right
    use (pullback.fst : _ ⟶ D.V (i, k)) (D.t' _ _ _ z)
    dsimp only at *
    substs eq₁ eq₂ e₁ e₃ e₄
    have h₁ : D.t' j i k ≫ pullback.fst ≫ D.f i k = pullback.fst ≫ D.t j i ≫ D.f i j := by
      rw [← 𝖣.t_fac_assoc]; congr 1; exact pullback.condition
    have h₂ : D.t' j i k ≫ pullback.fst ≫ D.t i k ≫ D.f k i = pullback.snd ≫ D.t j k ≫ D.f k j := by
      rw [← 𝖣.t_fac_assoc]
      apply @Epi.left_cancellation _ _ _ _ (D.t' k j i)
      rw [𝖣.cocycle_assoc, 𝖣.t_fac_assoc, 𝖣.t_inv_assoc]
      exact pullback.condition.symm
    exact ⟨ContinuousMap.congr_fun h₁ z, ContinuousMap.congr_fun h₂ z⟩⟩
set_option linter.uppercaseLean3 false in
#align Top.glue_data.rel_equiv TopCat.GlueData.rel_equiv

open CategoryTheory.Limits.WalkingParallelPair

theorem eqvGen_of_π_eq
    -- Porting note: was `{x y : ∐ D.U} (h : 𝖣.π x = 𝖣.π y)`
    {x y : sigmaObj (β := D.toGlueData.J) (C := TopCat) D.toGlueData.U}
    (h : 𝖣.π x = 𝖣.π y) :
    EqvGen
      -- Porting note: was (Types.CoequalizerRel 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap)
      (Types.CoequalizerRel
        (X := sigmaObj (β := D.toGlueData.diagram.L) (C := TopCat) (D.toGlueData.diagram).left)
        (Y := sigmaObj (β := D.toGlueData.diagram.R) (C := TopCat) (D.toGlueData.diagram).right)
        𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap)
      x y := by
  delta GlueData.π Multicoequalizer.sigmaπ at h
  -- Porting note: inlined `inferInstance` instead of leaving as a side goal.
  replace h := (TopCat.mono_iff_injective (Multicoequalizer.isoCoequalizer 𝖣.diagram).inv).mp
    inferInstance h
  let diagram := parallelPair 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap ⋙ forget _
  have : colimit.ι diagram one x = colimit.ι diagram one y := by
    dsimp only [coequalizer.π, ContinuousMap.toFun_eq_coe] at h
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [← ι_preservesColimitsIso_hom, forget_map_eq_coe, types_comp_apply, h]
    simp
    rfl
  have :
    (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.isoColimitCocone _).hom) _ =
      (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.isoColimitCocone _).hom) _ :=
    (congr_arg
        (colim.map (diagramIsoParallelPair diagram).hom ≫
          (colimit.isoColimitCocone (Types.coequalizerColimit _ _)).hom)
        this :
      _)
  -- Porting note: was
  -- simp only [eqToHom_refl, types_comp_apply, colimit.ι_map_assoc,
  --   diagramIsoParallelPair_hom_app, colimit.isoColimitCocone_ι_hom, types_id_apply] at this
  -- See https://github.com/leanprover-community/mathlib4/issues/5026
  rw [colimit.ι_map_assoc, diagramIsoParallelPair_hom_app, eqToHom_refl,
    colimit.isoColimitCocone_ι_hom, types_comp_apply, types_id_apply, types_comp_apply,
    types_id_apply] at this
  exact Quot.eq.1 this
set_option linter.uppercaseLean3 false in
#align Top.glue_data.eqv_gen_of_π_eq TopCat.GlueData.eqvGen_of_π_eq

theorem ι_eq_iff_rel (i j : D.J) (x : D.U i) (y : D.U j) :
    𝖣.ι i x = 𝖣.ι j y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  constructor
  · delta GlueData.ι
    simp_rw [← Multicoequalizer.ι_sigmaπ]
    intro h
    rw [←
      show _ = Sigma.mk i x from ConcreteCategory.congr_hom (sigmaIsoSigma.{_, u} D.U).inv_hom_id _]
    rw [←
      show _ = Sigma.mk j y from ConcreteCategory.congr_hom (sigmaIsoSigma.{_, u} D.U).inv_hom_id _]
    change InvImage D.Rel (sigmaIsoSigma.{_, u} D.U).hom _ _
    rw [← (InvImage.equivalence _ _ D.rel_equiv).eqvGen_iff]
    refine' EqvGen.mono _ (D.eqvGen_of_π_eq h : _)
    rintro _ _ ⟨x⟩
    obtain ⟨⟨⟨i, j⟩, y⟩, rfl⟩ :=
      (ConcreteCategory.bijective_of_isIso (sigmaIsoSigma.{u, u} _).inv).2 x
    unfold InvImage MultispanIndex.fstSigmaMap MultispanIndex.sndSigmaMap
    simp only [forget_map_eq_coe, Opens.inclusion_apply, TopCat.comp_app, sigmaIsoSigma_inv_apply,
      Cofan.mk_ι_app]
    rw [← comp_apply, colimit.ι_desc, ← comp_apply, colimit.ι_desc]
    erw [sigmaIsoSigma_hom_ι_apply, sigmaIsoSigma_hom_ι_apply]
    exact Or.inr ⟨y, ⟨rfl, rfl⟩⟩
  · rintro (⟨⟨⟩⟩ | ⟨z, e₁, e₂⟩)
    · rfl
    dsimp only at *
    -- Porting note: there were `subst e₁` and `subst e₂`, instead of the `rw`
    rw [← e₁, ← e₂] at *
    simp
set_option linter.uppercaseLean3 false in
#align Top.glue_data.ι_eq_iff_rel TopCat.GlueData.ι_eq_iff_rel

theorem ι_injective (i : D.J) : Function.Injective (𝖣.ι i) := by
  intro x y h
  rcases (D.ι_eq_iff_rel _ _ _ _).mp h with (⟨⟨⟩⟩ | ⟨_, e₁, e₂⟩)
  · rfl
  · dsimp only at *
    -- Porting note: there were `cases e₁` and `cases e₂`, instead of the `rw`
    rw [← e₁, ← e₂]
    simp
set_option linter.uppercaseLean3 false in
#align Top.glue_data.ι_injective TopCat.GlueData.ι_injective

instance ι_mono (i : D.J) : Mono (𝖣.ι i) :=
  (TopCat.mono_iff_injective _).mpr (D.ι_injective _)
set_option linter.uppercaseLean3 false in
#align Top.glue_data.ι_mono TopCat.GlueData.ι_mono

theorem image_inter (i j : D.J) :
    Set.range (𝖣.ι i) ∩ Set.range (𝖣.ι j) = Set.range (D.f i j ≫ 𝖣.ι _) := by
  ext x
  constructor
  · rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩
    obtain ⟨⟨⟩⟩ | ⟨y, e₁, -⟩ := (D.ι_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm)
    · exact ⟨inv (D.f i i) x₁, by
        -- porting note (#10745): was `simp [eq₁]`
        -- See https://github.com/leanprover-community/mathlib4/issues/5026
        rw [TopCat.comp_app]
        erw [CategoryTheory.IsIso.inv_hom_id_apply]
        rw [eq₁]⟩
    · -- Porting note: was
      -- dsimp only at *; substs e₁ eq₁; exact ⟨y, by simp⟩
      dsimp only at *
      substs eq₁
      exact ⟨y, by simp [e₁]⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨D.f i j x, hx⟩, ⟨D.f j i (D.t _ _ x), by simp [← hx]⟩⟩
set_option linter.uppercaseLean3 false in
#align Top.glue_data.image_inter TopCat.GlueData.image_inter

theorem preimage_range (i j : D.J) : 𝖣.ι j ⁻¹' Set.range (𝖣.ι i) = Set.range (D.f j i) := by
  rw [← Set.preimage_image_eq (Set.range (D.f j i)) (D.ι_injective j), ← Set.image_univ, ←
    Set.image_univ, ← Set.image_comp, ← coe_comp, Set.image_univ, Set.image_univ, ← image_inter,
    Set.preimage_range_inter]
set_option linter.uppercaseLean3 false in
#align Top.glue_data.preimage_range TopCat.GlueData.preimage_range

theorem preimage_image_eq_image (i j : D.J) (U : Set (𝖣.U i)) :
    𝖣.ι j ⁻¹' (𝖣.ι i '' U) = D.f _ _ '' ((D.t j i ≫ D.f _ _) ⁻¹' U) := by
  have : D.f _ _ ⁻¹' (𝖣.ι j ⁻¹' (𝖣.ι i '' U)) = (D.t j i ≫ D.f _ _) ⁻¹' U := by
    ext x
    conv_rhs => rw [← Set.preimage_image_eq U (D.ι_injective _)]
    generalize 𝖣.ι i '' U = U'
    simp
  rw [← this, Set.image_preimage_eq_inter_range]
  symm
  apply Set.inter_eq_self_of_subset_left
  rw [← D.preimage_range i j]
  exact Set.preimage_mono (Set.image_subset_range _ _)
set_option linter.uppercaseLean3 false in
#align Top.glue_data.preimage_image_eq_image TopCat.GlueData.preimage_image_eq_image

theorem preimage_image_eq_image' (i j : D.J) (U : Set (𝖣.U i)) :
    𝖣.ι j ⁻¹' (𝖣.ι i '' U) = (D.t i j ≫ D.f _ _) '' (D.f _ _ ⁻¹' U) := by
  convert D.preimage_image_eq_image i j U using 1
  rw [coe_comp, coe_comp]
  -- Porting note: `show` was not needed, since `rw [← Set.image_image]` worked.
  show (fun x => ((forget TopCat).map _ ((forget TopCat).map _ x))) '' _ = _
  rw [← Set.image_image]
  -- Porting note: `congr 1` was here, instead of `congr_arg`, however, it did nothing.
  refine congr_arg ?_ ?_
  rw [← Set.eq_preimage_iff_image_eq, Set.preimage_preimage]
  · change _ = (D.t i j ≫ D.t j i ≫ _) ⁻¹' _
    rw [𝖣.t_inv_assoc]
  rw [← isIso_iff_bijective]
  apply (forget TopCat).map_isIso
set_option linter.uppercaseLean3 false in
#align Top.glue_data.preimage_image_eq_image' TopCat.GlueData.preimage_image_eq_image'

-- Porting note: the goal was simply `IsOpen (𝖣.ι i '' U)`.
-- I had to manually add the explicit type ascription.
theorem open_image_open (i : D.J) (U : Opens (𝖣.U i)) : IsOpen (𝖣.ι i '' (U : Set (D.U i))) := by
  rw [isOpen_iff]
  intro j
  rw [preimage_image_eq_image]
  apply (D.f_open _ _).isOpenMap
  apply (D.t j i ≫ D.f i j).continuous_toFun.isOpen_preimage
  exact U.isOpen
set_option linter.uppercaseLean3 false in
#align Top.glue_data.open_image_open TopCat.GlueData.open_image_open

theorem ι_openEmbedding (i : D.J) : OpenEmbedding (𝖣.ι i) :=
  openEmbedding_of_continuous_injective_open (𝖣.ι i).continuous_toFun (D.ι_injective i) fun U h =>
    D.open_image_open i ⟨U, h⟩
set_option linter.uppercaseLean3 false in
#align Top.glue_data.ι_open_embedding TopCat.GlueData.ι_openEmbedding

/-- A family of gluing data consists of
1. An index type `J`
2. A bundled topological space `U i` for each `i : J`.
3. An open set `V i j ⊆ U i` for each `i j : J`.
4. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `V i i = U i`.
7. `t i i` is the identity.
8. For each `x ∈ V i j ∩ V i k`, `t i j x ∈ V j k`.
9. `t j k (t i j x) = t i k x`.

We can then glue the topological spaces `U i` together by identifying `V i j` with `V j i`.
-/
-- Porting note(#5171): removed `@[nolint has_nonempty_instance]`
structure MkCore where
  {J : Type u}
  U : J → TopCat.{u}
  V : ∀ i, J → Opens (U i)
  t : ∀ i j, (Opens.toTopCat _).obj (V i j) ⟶ (Opens.toTopCat _).obj (V j i)
  V_id : ∀ i, V i i = ⊤
  t_id : ∀ i, ⇑(t i i) = id
  t_inter : ∀ ⦃i j⦄ (k) (x : V i j), ↑x ∈ V i k → (((↑) : (V j i) → (U j)) (t i j x)) ∈ V j k
  cocycle :
    ∀ (i j k) (x : V i j) (h : ↑x ∈ V i k),
      -- Porting note: the underscore in the next line was `↑(t i j x)`, but Lean type-mismatched
      (((↑) : (V k j) → (U k)) (t j k ⟨_, t_inter k x h⟩)) = ((↑) : (V k i) → (U k)) (t i k ⟨x, h⟩)
set_option linter.uppercaseLean3 false in
#align Top.glue_data.mk_core TopCat.GlueData.MkCore

theorem MkCore.t_inv (h : MkCore) (i j : h.J) (x : h.V j i) : h.t i j ((h.t j i) x) = x := by
  have := h.cocycle j i j x ?_
  · rw [h.t_id] at this
    · convert Subtype.eq this
    rw [h.V_id]
    trivial
set_option linter.uppercaseLean3 false in
#align Top.glue_data.mk_core.t_inv TopCat.GlueData.MkCore.t_inv

instance (h : MkCore.{u}) (i j : h.J) : IsIso (h.t i j) := by
  use h.t j i; constructor <;> ext1; exacts [h.t_inv _ _ _, h.t_inv _ _ _]

/-- (Implementation) the restricted transition map to be fed into `TopCat.GlueData`. -/
def MkCore.t' (h : MkCore.{u}) (i j k : h.J) :
    pullback (h.V i j).inclusion (h.V i k).inclusion ⟶
      pullback (h.V j k).inclusion (h.V j i).inclusion := by
  refine' (pullbackIsoProdSubtype _ _).hom ≫ ⟨_, _⟩ ≫ (pullbackIsoProdSubtype _ _).inv
  · intro x
    refine' ⟨⟨⟨(h.t i j x.1.1).1, _⟩, h.t i j x.1.1⟩, rfl⟩
    rcases x with ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    exact h.t_inter _ ⟨x, hx⟩ hx'
  -- Porting note: was `continuity`, see https://github.com/leanprover-community/mathlib4/issues/5030
  have : Continuous (h.t i j) := map_continuous (self := ContinuousMap.toContinuousMapClass) _
  set_option tactic.skipAssignedInstances false in
  exact ((Continuous.subtype_mk (by continuity) _).prod_mk (by continuity)).subtype_mk _

set_option linter.uppercaseLean3 false in
#align Top.glue_data.mk_core.t' TopCat.GlueData.MkCore.t'

/-- This is a constructor of `TopCat.GlueData` whose arguments are in terms of elements and
intersections rather than subobjects and pullbacks. Please refer to `TopCat.GlueData.MkCore` for
details. -/
def mk' (h : MkCore.{u}) : TopCat.GlueData where
  J := h.J
  U := h.U
  V i := (Opens.toTopCat _).obj (h.V i.1 i.2)
  f i j := (h.V i j).inclusion
  f_id i := by
    -- Porting note (#12129): additional beta reduction needed
    beta_reduce
    exact (h.V_id i).symm ▸ IsIso.of_iso (Opens.inclusionTopIso (h.U i))
  f_open := fun i j : h.J => (h.V i j).openEmbedding
  t := h.t
  t_id i := by ext; rw [h.t_id]; rfl
  t' := h.t'
  t_fac i j k := by
    delta MkCore.t'
    rw [Category.assoc, Category.assoc, pullbackIsoProdSubtype_inv_snd, ← Iso.eq_inv_comp,
      pullbackIsoProdSubtype_inv_fst_assoc]
    ext ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    rfl
  cocycle i j k := by
    delta MkCore.t'
    simp_rw [← Category.assoc]
    rw [Iso.comp_inv_eq]
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Category.id_comp]
    rw [← Iso.eq_inv_comp, Iso.inv_hom_id]
    ext1 ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    -- The next 9 tactics (up to `convert ...` were a single `rw` before leanprover/lean4#2644
    -- rw [comp_app, ContinuousMap.coe_mk, comp_app, id_app, ContinuousMap.coe_mk, Subtype.mk_eq_mk,
    --   Prod.mk.inj_iff, Subtype.mk_eq_mk, Subtype.ext_iff, and_self_iff]
    rw [comp_app] --, comp_app, id_app]
    -- erw [ContinuousMap.coe_mk]
    conv_lhs => erw [ContinuousMap.coe_mk]
    erw [id_app]
    rw [ContinuousMap.coe_mk]
    erw [Subtype.mk_eq_mk]
    rw [Prod.mk.inj_iff]
    erw [Subtype.mk_eq_mk]
    rw [Subtype.ext_iff]
    rw [and_self_iff]
    convert congr_arg Subtype.val (h.t_inv k i ⟨x, hx'⟩) using 3
    refine Subtype.ext ?_
    exact h.cocycle i j k ⟨x, hx⟩ hx'
  -- Porting note: was not necessary in mathlib3
  f_mono i j := (TopCat.mono_iff_injective _).mpr fun x y h => Subtype.ext h
set_option linter.uppercaseLean3 false in
#align Top.glue_data.mk' TopCat.GlueData.mk'

variable {α : Type u} [TopologicalSpace α] {J : Type u} (U : J → Opens α)

/-- We may construct a glue data from a family of open sets. -/
@[simps! toGlueData_J toGlueData_U toGlueData_V toGlueData_t toGlueData_f]
def ofOpenSubsets : TopCat.GlueData.{u} :=
  mk'.{u}
    { J
      U := fun i => (Opens.toTopCat <| TopCat.of α).obj (U i)
      V := fun i j => (Opens.map <| Opens.inclusion _).obj (U j)
      t := fun i j => ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, by
        -- Porting note: was `continuity`, see https://github.com/leanprover-community/mathlib4/issues/5030
        refine Continuous.subtype_mk ?_ ?_
        refine Continuous.subtype_mk ?_ ?_
        continuity⟩
      V_id := fun i => by
        ext
        -- Porting note: no longer needed `cases U i`!
        simp
      t_id := fun i => by ext; rfl
      t_inter := fun i j k x hx => hx
      cocycle := fun i j k x h => rfl }
set_option linter.uppercaseLean3 false in
#align Top.glue_data.of_open_subsets TopCat.GlueData.ofOpenSubsets

/-- The canonical map from the glue of a family of open subsets `α` into `α`.
This map is an open embedding (`fromOpenSubsetsGlue_openEmbedding`),
and its range is `⋃ i, (U i : Set α)` (`range_fromOpenSubsetsGlue`).
-/
def fromOpenSubsetsGlue : (ofOpenSubsets U).toGlueData.glued ⟶ TopCat.of α :=
  Multicoequalizer.desc _ _ (fun x => Opens.inclusion _) (by rintro ⟨i, j⟩; ext x; rfl)
set_option linter.uppercaseLean3 false in
#align Top.glue_data.from_open_subsets_glue TopCat.GlueData.fromOpenSubsetsGlue

-- Porting note: `elementwise` here produces a bad lemma,
-- where too much has been simplified, despite the `nosimp`.
@[simp, elementwise nosimp]
theorem ι_fromOpenSubsetsGlue (i : J) :
    (ofOpenSubsets U).toGlueData.ι i ≫ fromOpenSubsetsGlue U = Opens.inclusion _ :=
  Multicoequalizer.π_desc _ _ _ _ _
set_option linter.uppercaseLean3 false in
#align Top.glue_data.ι_from_open_subsets_glue TopCat.GlueData.ι_fromOpenSubsetsGlue

theorem fromOpenSubsetsGlue_injective : Function.Injective (fromOpenSubsetsGlue U) := by
  intro x y e
  obtain ⟨i, ⟨x, hx⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  obtain ⟨j, ⟨y, hy⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective y
  -- Porting note: now it is `erw`, it was `rw`
  -- see the porting note on `ι_fromOpenSubsetsGlue`
  erw [ι_fromOpenSubsetsGlue_apply, ι_fromOpenSubsetsGlue_apply] at e
  change x = y at e
  subst e
  rw [(ofOpenSubsets U).ι_eq_iff_rel]
  right
  exact ⟨⟨⟨x, hx⟩, hy⟩, rfl, rfl⟩
set_option linter.uppercaseLean3 false in
#align Top.glue_data.from_open_subsets_glue_injective TopCat.GlueData.fromOpenSubsetsGlue_injective

theorem fromOpenSubsetsGlue_isOpenMap : IsOpenMap (fromOpenSubsetsGlue U) := by
  intro s hs
  rw [(ofOpenSubsets U).isOpen_iff] at hs
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  use fromOpenSubsetsGlue U '' s ∩ Set.range (@Opens.inclusion (TopCat.of α) (U i))
  use Set.inter_subset_left _ _
  constructor
  · erw [← Set.image_preimage_eq_inter_range]
    apply (Opens.openEmbedding (X := TopCat.of α) (U i)).isOpenMap
    convert hs i using 1
    erw [← ι_fromOpenSubsetsGlue, coe_comp, Set.preimage_comp]
    --  porting note: `congr 1` did nothing, so I replaced it with `apply congr_arg`
    apply congr_arg
    exact Set.preimage_image_eq _ (fromOpenSubsetsGlue_injective U)
  · refine' ⟨Set.mem_image_of_mem _ hx, _⟩
    -- Porting note: another `rw ↦ erw`
    -- See above.
    erw [ι_fromOpenSubsetsGlue_apply]
    exact Set.mem_range_self _
set_option linter.uppercaseLean3 false in
#align Top.glue_data.from_open_subsets_glue_is_open_map TopCat.GlueData.fromOpenSubsetsGlue_isOpenMap

theorem fromOpenSubsetsGlue_openEmbedding : OpenEmbedding (fromOpenSubsetsGlue U) :=
  openEmbedding_of_continuous_injective_open (ContinuousMap.continuous_toFun _)
    (fromOpenSubsetsGlue_injective U) (fromOpenSubsetsGlue_isOpenMap U)
set_option linter.uppercaseLean3 false in
#align Top.glue_data.from_open_subsets_glue_open_embedding TopCat.GlueData.fromOpenSubsetsGlue_openEmbedding

theorem range_fromOpenSubsetsGlue : Set.range (fromOpenSubsetsGlue U) = ⋃ i, (U i : Set α) := by
  ext
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
    -- Porting note: another `rw ↦ erw`
    -- See above
    erw [ι_fromOpenSubsetsGlue_apply]
    exact Set.subset_iUnion _ i hx'
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    rename_i x
    exact ⟨(ofOpenSubsets U).toGlueData.ι i ⟨x, hx⟩, ι_fromOpenSubsetsGlue_apply _ _ _⟩
set_option linter.uppercaseLean3 false in
#align Top.glue_data.range_from_open_subsets_glue TopCat.GlueData.range_fromOpenSubsetsGlue

/-- The gluing of an open cover is homeomomorphic to the original space. -/
def openCoverGlueHomeo (h : ⋃ i, (U i : Set α) = Set.univ) :
    (ofOpenSubsets U).toGlueData.glued ≃ₜ α :=
  Equiv.ofBijective (fromOpenSubsetsGlue U) ⟨fromOpenSubsetsGlue_injective U,
      Set.range_iff_surjective.mp ((range_fromOpenSubsetsGlue U).symm ▸ h)⟩
    |>.toHomeomorphOfContinuousOpen (fromOpenSubsetsGlue U).2 (fromOpenSubsetsGlue_isOpenMap U)
set_option linter.uppercaseLean3 false in
#align Top.glue_data.open_cover_glue_homeo TopCat.GlueData.openCoverGlueHomeo

end GlueData

end TopCat
