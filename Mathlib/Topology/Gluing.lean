/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.GlueData
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Tactic.LibrarySearch

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
-- Porting note: removed @[nolint has_nonempty_instance]
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
  -- ⊢ IsOpen U ↔ ∀ (i : D.J), IsOpen (↑(Multicoequalizer.π (GlueData.diagram D.toG …
  simp_rw [← Multicoequalizer.ι_sigmaπ 𝖣.diagram]
  -- ⊢ IsOpen U ↔ ∀ (i : D.J), IsOpen (↑(Sigma.ι (GlueData.diagram D.toGlueData).ri …
  rw [← (homeoOfIso (Multicoequalizer.isoCoequalizer 𝖣.diagram).symm).isOpen_preimage]
  -- ⊢ IsOpen (↑(homeoOfIso (Multicoequalizer.isoCoequalizer (GlueData.diagram D.to …
  rw [coequalizer_isOpen_iff]
  -- ⊢ IsOpen (↑(colimit.ι (parallelPair (MultispanIndex.fstSigmaMap (GlueData.diag …
  dsimp only [GlueData.diagram_l, GlueData.diagram_left, GlueData.diagram_r, GlueData.diagram_right,
    parallelPair_obj_one]
  rw [colimit_isOpen_iff.{_,u}]  -- porting note: changed `.{u}` to `.{_,u}`.  fun fact: the proof
  -- ⊢ (∀ (j : Discrete D.J), IsOpen (↑(colimit.ι (Discrete.functor D.U) j) ⁻¹' (↑( …
                                 -- breaks down if this `rw` is merged with the `rw` above.
  constructor
  -- ⊢ (∀ (j : Discrete D.J), IsOpen (↑(colimit.ι (Discrete.functor D.U) j) ⁻¹' (↑( …
  · intro h j; exact h ⟨j⟩
    -- ⊢ IsOpen (↑(Sigma.ι D.U j ≫ Multicoequalizer.sigmaπ (GlueData.diagram D.toGlue …
               -- 🎉 no goals
  · intro h j; cases j; apply h
    -- ⊢ IsOpen (↑(colimit.ι (Discrete.functor D.U) j) ⁻¹' (↑(colimit.ι (parallelPair …
               -- ⊢ IsOpen (↑(colimit.ι (Discrete.functor D.U) { as := as✝ }) ⁻¹' (↑(colimit.ι ( …
                        -- 🎉 no goals
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
    -- ⊢ Rel D a a
    exacts [Or.inl rfl, Or.inr ⟨D.t _ _ x, by simp [e₁, e₂]⟩], by
    -- 🎉 no goals
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ (⟨⟨⟩⟩ | ⟨x, e₁, e₂⟩); exact id
    -- ⊢ Rel D { fst := i, snd := a } { fst := k, snd := c } → Rel D { fst := i, snd  …
                                                      -- ⊢ Rel D { fst := j, snd := b } { fst := k, snd := c } → Rel D { fst := i, snd  …
    rintro (⟨⟨⟩⟩ | ⟨y, e₃, e₄⟩); exact Or.inr ⟨x, e₁, e₂⟩
    -- ⊢ Rel D { fst := i, snd := a } { fst := j, snd := b }
                                 -- ⊢ Rel D { fst := i, snd := a } { fst := k, snd := c }
    let z := (pullbackIsoProdSubtype (D.f j i) (D.f j k)).inv ⟨⟨_, _⟩, e₂.trans e₃.symm⟩
    -- ⊢ Rel D { fst := i, snd := a } { fst := k, snd := c }
    have eq₁ : (D.t j i) ((pullback.fst : _ /-(D.f j k)-/ ⟶ D.V (j, i)) z) = x := by simp
    -- ⊢ Rel D { fst := i, snd := a } { fst := k, snd := c }
    have eq₂ : (pullback.snd : _ ⟶ D.V _) z = y := pullbackIsoProdSubtype_inv_snd_apply _ _ _
    -- ⊢ Rel D { fst := i, snd := a } { fst := k, snd := c }
    clear_value z
    -- ⊢ Rel D { fst := i, snd := a } { fst := k, snd := c }
    right
    -- ⊢ ∃ x, ↑(GlueData.f D.toGlueData { fst := i, snd := a }.fst { fst := k, snd := …
    use (pullback.fst : _ ⟶ D.V (i, k)) (D.t' _ _ _ z)
    -- ⊢ ↑(GlueData.f D.toGlueData { fst := i, snd := a }.fst { fst := k, snd := c }. …
    dsimp only at *
    -- ⊢ ↑(GlueData.f D.toGlueData i k) (↑pullback.fst (↑(GlueData.t' D.toGlueData j  …
    substs eq₁ eq₂ e₁ e₃ e₄
    -- ⊢ ↑(GlueData.f D.toGlueData i k) (↑pullback.fst (↑(GlueData.t' D.toGlueData j  …
    have h₁ : D.t' j i k ≫ pullback.fst ≫ D.f i k = pullback.fst ≫ D.t j i ≫ D.f i j := by
      rw [← 𝖣.t_fac_assoc]; congr 1; exact pullback.condition
    have h₂ : D.t' j i k ≫ pullback.fst ≫ D.t i k ≫ D.f k i = pullback.snd ≫ D.t j k ≫ D.f k j := by
      rw [← 𝖣.t_fac_assoc]
      apply @Epi.left_cancellation _ _ _ _ (D.t' k j i)
      rw [𝖣.cocycle_assoc, 𝖣.t_fac_assoc, 𝖣.t_inv_assoc]
      exact pullback.condition.symm
    exact ⟨ContinuousMap.congr_fun h₁ z, ContinuousMap.congr_fun h₂ z⟩⟩
    -- 🎉 no goals
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
  -- ⊢ EqvGen (Types.CoequalizerRel ↑(MultispanIndex.fstSigmaMap (GlueData.diagram  …
  -- Porting note: inlined `inferInstance` instead of leaving as a side goal.
  replace h := (TopCat.mono_iff_injective (Multicoequalizer.isoCoequalizer 𝖣.diagram).inv).mp
    inferInstance h
  let diagram := parallelPair 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap ⋙ forget _
  -- ⊢ EqvGen (Types.CoequalizerRel ↑(MultispanIndex.fstSigmaMap (GlueData.diagram  …
  have : colimit.ι diagram one x = colimit.ι diagram one y := by
    dsimp only [coequalizer.π, ContinuousMap.toFun_eq_coe] at h
    rw [← ι_preservesColimitsIso_hom, forget_map_eq_coe, types_comp_apply, h]
    simp
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
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.glue_data.eqv_gen_of_π_eq TopCat.GlueData.eqvGen_of_π_eq

theorem ι_eq_iff_rel (i j : D.J) (x : D.U i) (y : D.U j) :
    𝖣.ι i x = 𝖣.ι j y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  constructor
  -- ⊢ ↑(GlueData.ι D.toGlueData i) x = ↑(GlueData.ι D.toGlueData j) y → Rel D { fs …
  · delta GlueData.ι
    -- ⊢ ↑(Multicoequalizer.π (GlueData.diagram D.toGlueData) i) x = ↑(Multicoequaliz …
    simp_rw [← Multicoequalizer.ι_sigmaπ]
    -- ⊢ ↑(Sigma.ι (GlueData.diagram D.toGlueData).right i ≫ Multicoequalizer.sigmaπ  …
    intro h
    -- ⊢ Rel D { fst := i, snd := x } { fst := j, snd := y }
    rw [←
      show _ = Sigma.mk i x from ConcreteCategory.congr_hom (sigmaIsoSigma.{_, u} D.U).inv_hom_id _]
    rw [←
      show _ = Sigma.mk j y from ConcreteCategory.congr_hom (sigmaIsoSigma.{_, u} D.U).inv_hom_id _]
    change InvImage D.Rel (sigmaIsoSigma.{_, u} D.U).hom _ _
    -- ⊢ InvImage (Rel D) (↑(sigmaIsoSigma D.U).hom) (↑(sigmaIsoSigma D.U).inv { fst  …
    simp only [TopCat.sigmaIsoSigma_inv_apply]
    -- ⊢ InvImage (Rel D) (↑(sigmaIsoSigma D.U).hom) (↑(sigmaIsoSigma D.U).inv { fst  …
    rw [← (InvImage.equivalence _ _ D.rel_equiv).eqvGen_iff]
    -- ⊢ EqvGen (InvImage (Rel D) ↑(sigmaIsoSigma D.U).hom) (↑(sigmaIsoSigma D.U).inv …
    refine' EqvGen.mono _ (D.eqvGen_of_π_eq h : _)
    -- ⊢ ∀ (a b : (forget TopCat).obj (∐ D.U)), Types.CoequalizerRel (↑(MultispanInde …
    rintro _ _ ⟨x⟩
    -- ⊢ InvImage (Rel D) (↑(sigmaIsoSigma D.U).hom) (↑(MultispanIndex.fstSigmaMap (G …
    rw [←show (sigmaIsoSigma.{u, u} _).inv _ = x from
        ConcreteCategory.congr_hom (sigmaIsoSigma.{u, u} _).hom_inv_id x]
    generalize (sigmaIsoSigma.{u, u} D.V).hom x = x'
    -- ⊢ InvImage (Rel D) (↑(sigmaIsoSigma D.U).hom) (↑(MultispanIndex.fstSigmaMap (G …
    obtain ⟨⟨i, j⟩, y⟩ := x'
    -- ⊢ InvImage (Rel D) (↑(sigmaIsoSigma D.U).hom) (↑(MultispanIndex.fstSigmaMap (G …
    unfold InvImage MultispanIndex.fstSigmaMap MultispanIndex.sndSigmaMap
    -- ⊢ Rel D (↑(sigmaIsoSigma D.U).hom (↑(Sigma.desc fun b => MultispanIndex.fst (G …
    simp only [Opens.inclusion_apply, TopCat.comp_app, sigmaIsoSigma_inv_apply,
      Cofan.mk_ι_app]
    rw [←comp_apply, colimit.ι_desc, ←comp_apply, colimit.ι_desc]
    -- ⊢ Rel D (↑(sigmaIsoSigma D.U).hom (↑(NatTrans.app (Cofan.mk (∐ (GlueData.diagr …
    erw [sigmaIsoSigma_hom_ι_apply, sigmaIsoSigma_hom_ι_apply]
    -- ⊢ Rel D { fst := MultispanIndex.fstFrom (GlueData.diagram D.toGlueData) { as : …
    exact Or.inr ⟨y, by dsimp [GlueData.diagram]; simp only [true_and]; rfl⟩
    -- 🎉 no goals
  · rintro (⟨⟨⟩⟩ | ⟨z, e₁, e₂⟩)
    -- ⊢ ↑(GlueData.ι D.toGlueData i) x = ↑(GlueData.ι D.toGlueData i) x
    rfl
    -- ⊢ ↑(GlueData.ι D.toGlueData i) x = ↑(GlueData.ι D.toGlueData j) y
    dsimp only at *
    -- ⊢ ↑(GlueData.ι D.toGlueData i) x = ↑(GlueData.ι D.toGlueData j) y
    -- porting note: there were `subst e₁` and `subst e₂`, instead of the `rw`
    rw [← e₁, ← e₂] at *
    -- ⊢ ↑(GlueData.ι D.toGlueData i) (↑(GlueData.f D.toGlueData i j) z) = ↑(GlueData …
    simp
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.glue_data.ι_eq_iff_rel TopCat.GlueData.ι_eq_iff_rel

theorem ι_injective (i : D.J) : Function.Injective (𝖣.ι i) := by
  intro x y h
  -- ⊢ x = y
  rcases(D.ι_eq_iff_rel _ _ _ _).mp h with (⟨⟨⟩⟩ | ⟨_, e₁, e₂⟩)
  -- ⊢ x = x
  · rfl
    -- 🎉 no goals
  · dsimp only at *
    -- ⊢ x = y
    -- porting note: there were `cases e₁` and `cases e₂`, instead of the `rw`
    rw [← e₁, ← e₂]
    -- ⊢ ↑(GlueData.f D.toGlueData i i) w✝ = ↑(GlueData.f D.toGlueData i i) (↑(GlueDa …
    simp
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.glue_data.ι_injective TopCat.GlueData.ι_injective

instance ι_mono (i : D.J) : Mono (𝖣.ι i) :=
  (TopCat.mono_iff_injective _).mpr (D.ι_injective _)
set_option linter.uppercaseLean3 false in
#align Top.glue_data.ι_mono TopCat.GlueData.ι_mono

theorem image_inter (i j : D.J) :
    Set.range (𝖣.ι i) ∩ Set.range (𝖣.ι j) = Set.range (D.f i j ≫ 𝖣.ι _) := by
  ext x
  -- ⊢ x ∈ Set.range ↑(GlueData.ι D.toGlueData i) ∩ Set.range ↑(GlueData.ι D.toGlue …
  constructor
  -- ⊢ x ∈ Set.range ↑(GlueData.ι D.toGlueData i) ∩ Set.range ↑(GlueData.ι D.toGlue …
  · rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩
    -- ⊢ x ∈ Set.range ↑(GlueData.f D.toGlueData i j ≫ GlueData.ι D.toGlueData i)
    obtain ⟨⟨⟩⟩ | ⟨y, e₁, -⟩ := (D.ι_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm)
    -- ⊢ x ∈ Set.range ↑(GlueData.f D.toGlueData i i ≫ GlueData.ι D.toGlueData i)
    · exact ⟨inv (D.f i i) x₁, by
        -- Porting note: was `simp [eq₁]`
        -- See https://github.com/leanprover-community/mathlib4/issues/5026
        rw [TopCat.comp_app]
        erw [CategoryTheory.IsIso.inv_hom_id_apply]
        rw [eq₁]⟩
    · -- Porting note: was
      -- dsimp only at *; substs e₁ eq₁; exact ⟨y, by simp⟩
      dsimp only at *
      -- ⊢ x ∈ Set.range ↑(GlueData.f D.toGlueData i j ≫ GlueData.ι D.toGlueData i)
      substs eq₁
      -- ⊢ ↑(GlueData.ι D.toGlueData i) x₁ ∈ Set.range ↑(GlueData.f D.toGlueData i j ≫  …
      exact ⟨y, by simp [e₁]⟩
      -- 🎉 no goals
  · rintro ⟨x, hx⟩
    -- ⊢ x✝ ∈ Set.range ↑(GlueData.ι D.toGlueData i) ∩ Set.range ↑(GlueData.ι D.toGlu …
    exact ⟨⟨D.f i j x, hx⟩, ⟨D.f j i (D.t _ _ x), by simp [← hx]⟩⟩
    -- 🎉 no goals
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
  -- ⊢ ↑(GlueData.ι D.toGlueData j) ⁻¹' (↑(GlueData.ι D.toGlueData i) '' U) = ↑(Glu …
  symm
  -- ⊢ ↑(GlueData.ι D.toGlueData j) ⁻¹' (↑(GlueData.ι D.toGlueData i) '' U) ∩ Set.r …
  apply Set.inter_eq_self_of_subset_left
  -- ⊢ ↑(GlueData.ι D.toGlueData j) ⁻¹' (↑(GlueData.ι D.toGlueData i) '' U) ⊆ Set.r …
  rw [← D.preimage_range i j]
  -- ⊢ ↑(GlueData.ι D.toGlueData j) ⁻¹' (↑(GlueData.ι D.toGlueData i) '' U) ⊆ ↑(Glu …
  exact Set.preimage_mono (Set.image_subset_range _ _)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.glue_data.preimage_image_eq_image TopCat.GlueData.preimage_image_eq_image

theorem preimage_image_eq_image' (i j : D.J) (U : Set (𝖣.U i)) :
    𝖣.ι j ⁻¹' (𝖣.ι i '' U) = (D.t i j ≫ D.f _ _) '' (D.f _ _ ⁻¹' U) := by
  convert D.preimage_image_eq_image i j U using 1
  -- ⊢ ↑(GlueData.t D.toGlueData i j ≫ GlueData.f D.toGlueData j i) '' (↑(GlueData. …
  rw [coe_comp, coe_comp]
  -- ⊢ ↑(GlueData.f D.toGlueData j i) ∘ ↑(GlueData.t D.toGlueData i j) '' (↑(GlueDa …
  -- porting note: `show` was not needed, since `rw [← Set.image_image]` worked.
  show (fun x => ((forget TopCat).map _ ((forget TopCat).map _ x))) '' _ = _
  -- ⊢ (fun x => (forget TopCat).map (GlueData.f D.toGlueData j i) ((forget TopCat) …
  rw [← Set.image_image]
  -- ⊢ (forget TopCat).map (GlueData.f D.toGlueData j i) '' ((fun x => (forget TopC …
  -- porting note: `congr 1` was here, instead of `congr_arg`, however, it did nothing.
  refine congr_arg ?_ ?_
  -- ⊢ (fun x => (forget TopCat).map (GlueData.t D.toGlueData i j) x) '' (↑(GlueDat …
  rw [← Set.eq_preimage_iff_image_eq, Set.preimage_preimage]
  -- ⊢ ↑(GlueData.f D.toGlueData i j) ⁻¹' U = (fun x => (↑(GlueData.f D.toGlueData  …
  change _ = (D.t i j ≫ D.t j i ≫ _) ⁻¹' _
  -- ⊢ ↑(GlueData.f D.toGlueData i j) ⁻¹' U = ↑(GlueData.t D.toGlueData i j ≫ GlueD …
  rw [𝖣.t_inv_assoc]
  -- ⊢ Function.Bijective fun x => (forget TopCat).map (GlueData.t D.toGlueData i j …
  rw [← isIso_iff_bijective]
  -- ⊢ IsIso fun x => (forget TopCat).map (GlueData.t D.toGlueData i j) x
  apply (forget TopCat).map_isIso
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.glue_data.preimage_image_eq_image' TopCat.GlueData.preimage_image_eq_image'

-- porting note: the goal was simply `IsOpen (𝖣.ι i '' U)`.
-- I had to manually add the explicit type ascription.
theorem open_image_open (i : D.J) (U : Opens (𝖣.U i)) : IsOpen (𝖣.ι i '' (U : Set (D.U i))) := by
  rw [isOpen_iff]
  -- ⊢ ∀ (i_1 : D.J), IsOpen (↑(GlueData.ι D.toGlueData i_1) ⁻¹' (↑(GlueData.ι D.to …
  intro j
  -- ⊢ IsOpen (↑(GlueData.ι D.toGlueData j) ⁻¹' (↑(GlueData.ι D.toGlueData i) '' ↑U))
  rw [preimage_image_eq_image]
  -- ⊢ IsOpen (↑(GlueData.f D.toGlueData j i) '' (↑(GlueData.t D.toGlueData j i ≫ G …
  apply (D.f_open _ _).isOpenMap
  -- ⊢ IsOpen (↑(GlueData.t D.toGlueData j i ≫ GlueData.f D.toGlueData i j) ⁻¹' ↑U)
  apply (D.t j i ≫ D.f i j).continuous_toFun.isOpen_preimage
  -- ⊢ IsOpen ↑U
  exact U.isOpen
  -- 🎉 no goals
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
-- Porting note: removed `@[nolint has_nonempty_instance]`
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
      -- porting note: the underscore in the next line was `↑(t i j x)`, but Lean type-mismatched
      (((↑) : (V k j) → (U k)) (t j k ⟨_, t_inter k x h⟩)) = ((↑) : (V k i) → (U k)) (t i k ⟨x, h⟩)
set_option linter.uppercaseLean3 false in
#align Top.glue_data.mk_core TopCat.GlueData.MkCore

theorem MkCore.t_inv (h : MkCore) (i j : h.J) (x : h.V j i) : h.t i j ((h.t j i) x) = x := by
  have := h.cocycle j i j x ?_
  -- ⊢ ↑(t h i j) (↑(t h j i) x) = x
  rw [h.t_id] at this
  convert Subtype.eq this
  rw [h.V_id]
  -- ⊢ ↑x ∈ ⊤
  trivial
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.glue_data.mk_core.t_inv TopCat.GlueData.MkCore.t_inv

instance (h : MkCore.{u}) (i j : h.J) : IsIso (h.t i j) := by
  use h.t j i; constructor <;> ext1; exacts [h.t_inv _ _ _, h.t_inv _ _ _]
  -- ⊢ MkCore.t h i j ≫ MkCore.t h j i = 𝟙 ((Opens.toTopCat (MkCore.U h i)).obj (Mk …
               -- ⊢ MkCore.t h i j ≫ MkCore.t h j i = 𝟙 ((Opens.toTopCat (MkCore.U h i)).obj (Mk …
                               -- ⊢ ↑(MkCore.t h i j ≫ MkCore.t h j i) x✝ = ↑(𝟙 ((Opens.toTopCat (MkCore.U h i)) …
                               -- ⊢ ↑(MkCore.t h j i ≫ MkCore.t h i j) x✝ = ↑(𝟙 ((Opens.toTopCat (MkCore.U h j)) …
                                     -- 🎉 no goals

/-- (Implementation) the restricted transition map to be fed into `TopCat.GlueData`. -/
def MkCore.t' (h : MkCore.{u}) (i j k : h.J) :
    pullback (h.V i j).inclusion (h.V i k).inclusion ⟶
      pullback (h.V j k).inclusion (h.V j i).inclusion := by
  refine' (pullbackIsoProdSubtype _ _).hom ≫ ⟨_, _⟩ ≫ (pullbackIsoProdSubtype _ _).inv
  -- ⊢ ↑(of { p // ↑(Opens.inclusion (V h i j)) p.fst = ↑(Opens.inclusion (V h i k) …
  · intro x
    -- ⊢ ↑(of { p // ↑(Opens.inclusion (V h j k)) p.fst = ↑(Opens.inclusion (V h j i) …
    refine' ⟨⟨⟨(h.t i j x.1.1).1, _⟩, h.t i j x.1.1⟩, rfl⟩
    -- ⊢ ↑(↑(t h i j) (↑x).fst) ∈ V h j k
    rcases x with ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    -- ⊢ ↑(↑(t h i j) (↑{ val := ({ val := x, property := hx }, { val := x, property  …
    exact h.t_inter _ ⟨x, hx⟩ hx'
    -- 🎉 no goals
  -- Porting note: was `continuity`, see https://github.com/leanprover-community/mathlib4/issues/5030
  have : Continuous (h.t i j) := map_continuous (self := ContinuousMap.toContinuousMapClass) _
  -- ⊢ Continuous fun x => { val := ({ val := ↑(↑(t h i j) (↑x).fst), property := ( …
  exact ((Continuous.subtype_mk (by continuity) _).prod_mk (by continuity)).subtype_mk _
  -- 🎉 no goals

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
    -- Porting note: added `dsimp only`
    dsimp only
    -- ⊢ IsIso (Opens.inclusion (MkCore.V h i i))
    exact (h.V_id i).symm ▸ IsIso.of_iso (Opens.inclusionTopIso (h.U i))
    -- 🎉 no goals
  f_open := fun i j : h.J => (h.V i j).openEmbedding
  t := h.t
  t_id i := by ext; rw [h.t_id]; rfl
               -- ⊢ ↑(MkCore.t h i i) x✝ = ↑(𝟙 ((fun i => (Opens.toTopCat (MkCore.U h i.fst)).ob …
                    -- ⊢ id x✝ = ↑(𝟙 ((fun i => (Opens.toTopCat (MkCore.U h i.fst)).obj (MkCore.V h i …
                                 -- 🎉 no goals
  t' := h.t'
  t_fac i j k := by
    delta MkCore.t'
    -- ⊢ ((pullbackIsoProdSubtype (Opens.inclusion (MkCore.V h i j)) (Opens.inclusion …
    rw [Category.assoc, Category.assoc, pullbackIsoProdSubtype_inv_snd, ← Iso.eq_inv_comp,
      pullbackIsoProdSubtype_inv_fst_assoc]
    ext ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    -- ⊢ ↑((ContinuousMap.mk fun x => { val := ({ val := ↑(↑(MkCore.t h i j) (↑x).fst …
    rfl
    -- 🎉 no goals
  cocycle i j k := by
    delta MkCore.t'
    -- ⊢ ((pullbackIsoProdSubtype (Opens.inclusion (MkCore.V h i j)) (Opens.inclusion …
    simp_rw [← Category.assoc]
    -- ⊢ ((((((((pullbackIsoProdSubtype (Opens.inclusion (MkCore.V h i j)) (Opens.inc …
    rw [Iso.comp_inv_eq]
    -- ⊢ ((((((((pullbackIsoProdSubtype (Opens.inclusion (MkCore.V h i j)) (Opens.inc …
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Category.id_comp]
    -- ⊢ ((pullbackIsoProdSubtype (Opens.inclusion (MkCore.V h i j)) (Opens.inclusion …
    rw [← Iso.eq_inv_comp, Iso.inv_hom_id]
    -- ⊢ ((ContinuousMap.mk fun x => { val := ({ val := ↑(↑(MkCore.t h i j) (↑x).fst) …
    ext1 ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    -- ⊢ ↑((ContinuousMap.mk fun x => { val := ({ val := ↑(↑(MkCore.t h i j) (↑x).fst …
    rw [comp_app, ContinuousMap.coe_mk, comp_app, id_app, ContinuousMap.coe_mk, Subtype.mk_eq_mk,
      Prod.mk.inj_iff, Subtype.mk_eq_mk, Subtype.ext_iff, and_self_iff]
    convert congr_arg Subtype.val (h.t_inv k i ⟨x, hx'⟩) using 3
    -- ⊢ (↑(↑(ContinuousMap.mk fun x => { val := ({ val := ↑(↑(MkCore.t h j k) (↑x).f …
    refine Subtype.ext ?_
    -- ⊢ ↑(↑(↑(ContinuousMap.mk fun x => { val := ({ val := ↑(↑(MkCore.t h j k) (↑x). …
    exact h.cocycle i j k ⟨x, hx⟩ hx'
    -- 🎉 no goals
  -- Porting note : was not necessary in mathlib3
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
        -- ⊢ Continuous fun x => { val := ↑↑x, property := (_ : ↑x ∈ (fun i j => (Opens.m …
        refine Continuous.subtype_mk ?_ ?_
        -- ⊢ Continuous fun x => ↑↑x
        continuity⟩
        -- 🎉 no goals
      V_id := fun i => by
        ext
        -- ⊢ x✝ ∈ ↑((fun i j => (Opens.map (Opens.inclusion (U i))).obj (U j)) i i) ↔ x✝  …
        -- porting note: no longer needed `cases U i`!
        simp
        -- 🎉 no goals
      t_id := fun i => by ext; rfl
                          -- ⊢ ↑((fun i j => ContinuousMap.mk fun x => { val := { val := ↑↑x, property := ( …
                               -- 🎉 no goals
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
                                                             -- ⊢ MultispanIndex.fst (GlueData.diagram (ofOpenSubsets U).toGlueData) (i, j) ≫  …
                                                                            -- ⊢ ↑(MultispanIndex.fst (GlueData.diagram (ofOpenSubsets U).toGlueData) (i, j)  …
                                                                                   -- 🎉 no goals
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
  -- ⊢ x = y
  obtain ⟨i, ⟨x, hx⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  -- ⊢ ↑(GlueData.ι (ofOpenSubsets U).toGlueData i) { val := x, property := hx } = y
  obtain ⟨j, ⟨y, hy⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective y
  -- ⊢ ↑(GlueData.ι (ofOpenSubsets U).toGlueData i) { val := x, property := hx } =  …
  -- porting note: now it is `erw`, it was `rw`
  -- see the porting note on `ι_fromOpenSubsetsGlue`
  erw [ι_fromOpenSubsetsGlue_apply, ι_fromOpenSubsetsGlue_apply] at e
  -- ⊢ ↑(GlueData.ι (ofOpenSubsets U).toGlueData i) { val := x, property := hx } =  …
  change x = y at e
  -- ⊢ ↑(GlueData.ι (ofOpenSubsets U).toGlueData i) { val := x, property := hx } =  …
  subst e
  -- ⊢ ↑(GlueData.ι (ofOpenSubsets U).toGlueData i) { val := x, property := hx } =  …
  rw [(ofOpenSubsets U).ι_eq_iff_rel]
  -- ⊢ Rel (ofOpenSubsets U) { fst := i, snd := { val := x, property := hx } } { fs …
  right
  -- ⊢ ∃ x_1, ↑(GlueData.f (ofOpenSubsets U).toGlueData { fst := i, snd := { val := …
  exact ⟨⟨⟨x, hx⟩, hy⟩, rfl, rfl⟩
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.glue_data.from_open_subsets_glue_injective TopCat.GlueData.fromOpenSubsetsGlue_injective

theorem fromOpenSubsetsGlue_isOpenMap : IsOpenMap (fromOpenSubsetsGlue U) := by
  intro s hs
  -- ⊢ IsOpen (↑(fromOpenSubsetsGlue U) '' s)
  rw [(ofOpenSubsets U).isOpen_iff] at hs
  -- ⊢ IsOpen (↑(fromOpenSubsetsGlue U) '' s)
  rw [isOpen_iff_forall_mem_open]
  -- ⊢ ∀ (x : (forget TopCat).obj (of α)), x ∈ ↑(fromOpenSubsetsGlue U) '' s → ∃ t, …
  rintro _ ⟨x, hx, rfl⟩
  -- ⊢ ∃ t, t ⊆ ↑(fromOpenSubsetsGlue U) '' s ∧ IsOpen t ∧ ↑(fromOpenSubsetsGlue U) …
  obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  -- ⊢ ∃ t, t ⊆ ↑(fromOpenSubsetsGlue U) '' s ∧ IsOpen t ∧ ↑(fromOpenSubsetsGlue U) …
  use fromOpenSubsetsGlue U '' s ∩ Set.range (@Opens.inclusion (TopCat.of α) (U i))
  -- ⊢ ↑(fromOpenSubsetsGlue U) '' s ∩ Set.range ↑(Opens.inclusion (U i)) ⊆ ↑(fromO …
  use Set.inter_subset_left _ _
  -- ⊢ IsOpen (↑(fromOpenSubsetsGlue U) '' s ∩ Set.range ↑(Opens.inclusion (U i)))  …
  constructor
  -- ⊢ IsOpen (↑(fromOpenSubsetsGlue U) '' s ∩ Set.range ↑(Opens.inclusion (U i)))
  · erw [← Set.image_preimage_eq_inter_range]
    -- ⊢ IsOpen (↑(Opens.inclusion (U i)) '' (↑(Opens.inclusion (U i)) ⁻¹' (↑(fromOpe …
    apply (Opens.openEmbedding (X := TopCat.of α) (U i)).isOpenMap
    -- ⊢ IsOpen (↑(Opens.inclusion (U i)) ⁻¹' (↑(fromOpenSubsetsGlue U) '' s))
    convert hs i using 1
    -- ⊢ ↑(Opens.inclusion (U i)) ⁻¹' (↑(fromOpenSubsetsGlue U) '' s) = ↑(GlueData.ι  …
    erw [← ι_fromOpenSubsetsGlue, coe_comp, Set.preimage_comp]
    -- ⊢ ↑(GlueData.ι (ofOpenSubsets U).toGlueData i) ⁻¹' (↑(fromOpenSubsetsGlue U) ⁻ …
    --  porting note: `congr 1` did nothing, so I replaced it with `apply congr_arg`
    apply congr_arg
    -- ⊢ ↑(fromOpenSubsetsGlue U) ⁻¹' (↑(fromOpenSubsetsGlue U) '' s) = s
    refine' Set.preimage_image_eq _ (fromOpenSubsetsGlue_injective U)
    -- 🎉 no goals
  · refine' ⟨Set.mem_image_of_mem _ hx, _⟩
    -- ⊢ ↑(fromOpenSubsetsGlue U) (↑(GlueData.ι (ofOpenSubsets U).toGlueData i) { val …
    -- porting note: another `rw ↦ erw`
    -- See above.
    erw [ι_fromOpenSubsetsGlue_apply]
    -- ⊢ ↑(Opens.inclusion (U i)) { val := x, property := hx' } ∈ Set.range ↑(Opens.i …
    exact Set.mem_range_self _
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.glue_data.from_open_subsets_glue_is_open_map TopCat.GlueData.fromOpenSubsetsGlue_isOpenMap

theorem fromOpenSubsetsGlue_openEmbedding : OpenEmbedding (fromOpenSubsetsGlue U) :=
  openEmbedding_of_continuous_injective_open (ContinuousMap.continuous_toFun _)
    (fromOpenSubsetsGlue_injective U) (fromOpenSubsetsGlue_isOpenMap U)
set_option linter.uppercaseLean3 false in
#align Top.glue_data.from_open_subsets_glue_open_embedding TopCat.GlueData.fromOpenSubsetsGlue_openEmbedding

theorem range_fromOpenSubsetsGlue : Set.range (fromOpenSubsetsGlue U) = ⋃ i, (U i : Set α) := by
  ext
  -- ⊢ x✝ ∈ Set.range ↑(fromOpenSubsetsGlue U) ↔ x✝ ∈ ⋃ (i : J), ↑(U i)
  constructor
  -- ⊢ x✝ ∈ Set.range ↑(fromOpenSubsetsGlue U) → x✝ ∈ ⋃ (i : J), ↑(U i)
  · rintro ⟨x, rfl⟩
    -- ⊢ ↑(fromOpenSubsetsGlue U) x ∈ ⋃ (i : J), ↑(U i)
    obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
    -- ⊢ ↑(fromOpenSubsetsGlue U) (↑(GlueData.ι (ofOpenSubsets U).toGlueData i) { val …
    -- porting note: another `rw ↦ erw`
    -- See above
    erw [ι_fromOpenSubsetsGlue_apply]
    -- ⊢ ↑(Opens.inclusion (U i)) { val := x, property := hx' } ∈ ⋃ (i : J), ↑(U i)
    exact Set.subset_iUnion _ i hx'
    -- 🎉 no goals
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    -- ⊢ x✝ ∈ Set.range ↑(fromOpenSubsetsGlue U)
    rename_i x
    -- ⊢ x ∈ Set.range ↑(fromOpenSubsetsGlue U)
    refine' ⟨(ofOpenSubsets U).toGlueData.ι i ⟨x, hx⟩, ι_fromOpenSubsetsGlue_apply _ _ _⟩
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.glue_data.range_from_open_subsets_glue TopCat.GlueData.range_fromOpenSubsetsGlue

/-- The gluing of an open cover is homeomomorphic to the original space. -/
def openCoverGlueHomeo (h : ⋃ i, (U i : Set α) = Set.univ) :
    (ofOpenSubsets U).toGlueData.glued ≃ₜ α :=
  Homeomorph.homeomorphOfContinuousOpen
    (Equiv.ofBijective (fromOpenSubsetsGlue U)
      ⟨fromOpenSubsetsGlue_injective U,
        Set.range_iff_surjective.mp ((range_fromOpenSubsetsGlue U).symm ▸ h)⟩)
    (fromOpenSubsetsGlue U).2 (fromOpenSubsetsGlue_isOpenMap U)
set_option linter.uppercaseLean3 false in
#align Top.glue_data.open_cover_glue_homeo TopCat.GlueData.openCoverGlueHomeo

end GlueData

end TopCat
