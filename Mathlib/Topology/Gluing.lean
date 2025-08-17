/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.GlueData
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Tactic.Generalize
import Mathlib.CategoryTheory.Elementwise
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

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
* `TopCat.GlueData.ι_isOpenEmbedding`: Each of the `ι i`s are open embeddings.

-/

noncomputable section

open CategoryTheory TopologicalSpace Topology

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
structure GlueData extends CategoryTheory.GlueData TopCat where
  f_open : ∀ i j, IsOpenEmbedding (f i j)
  f_mono i j := (TopCat.mono_iff_injective _).mpr (f_open i j).isEmbedding.injective

namespace GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

theorem π_surjective : Function.Surjective 𝖣.π :=
  (TopCat.epi_iff_surjective 𝖣.π).mp inferInstance

theorem isOpen_iff (U : Set 𝖣.glued) : IsOpen U ↔ ∀ i, IsOpen (𝖣.ι i ⁻¹' U) := by
  delta CategoryTheory.GlueData.ι
  simp_rw [← Multicoequalizer.ι_sigmaπ 𝖣.diagram]
  rw [← (homeoOfIso (Multicoequalizer.isoCoequalizer 𝖣.diagram).symm).isOpen_preimage]
  rw [coequalizer_isOpen_iff, colimit_isOpen_iff.{u}]
  tauto

theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : _) (y : D.U i), 𝖣.ι i y = x :=
  𝖣.ι_jointly_surjective (forget TopCat) x

/-- An equivalence relation on `Σ i, D.U i` that holds iff `𝖣.ι i x = 𝖣.ι j y`.
See `TopCat.GlueData.ι_eq_iff_rel`.
-/
def Rel (a b : Σ i, ((D.U i : TopCat) : Type _)) : Prop :=
  ∃ x : D.V (a.1, b.1), D.f _ _ x = a.2 ∧ D.f _ _ (D.t _ _ x) = b.2

theorem rel_equiv : Equivalence D.Rel :=
  ⟨fun x => ⟨inv (D.f _ _) x.2, IsIso.inv_hom_id_apply (D.f x.fst x.fst) _,
    -- Use `elementwise_of%` elaborator instead of `IsIso.inv_hom_id_apply` to work around
    -- `ConcreteCategory`/`HasForget` mismatch:
    by simp [elementwise_of% IsIso.inv_hom_id (D.f x.fst x.fst)]⟩, by
    rintro a b ⟨x, e₁, e₂⟩
    exact ⟨D.t _ _ x, e₂, by rw [← e₁, D.t_inv_apply]⟩, by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ ⟨x, e₁, e₂⟩
    rintro ⟨y, e₃, e₄⟩
    let z := (pullbackIsoProdSubtype (D.f j i) (D.f j k)).inv ⟨⟨_, _⟩, e₂.trans e₃.symm⟩
    have eq₁ : (D.t j i) ((pullback.fst _ _ : _ /-(D.f j k)-/ ⟶ D.V (j, i)) z) = x := by
      dsimp only [coe_of, z]
      rw [pullbackIsoProdSubtype_inv_fst_apply, D.t_inv_apply]
    have eq₂ : (pullback.snd _ _ : _ ⟶ D.V _) z = y := pullbackIsoProdSubtype_inv_snd_apply _ _ _
    clear_value z
    use (pullback.fst _ _ : _ ⟶ D.V (i, k)) (D.t' _ _ _ z)
    dsimp only at *
    substs eq₁ eq₂ e₁ e₃ e₄
    have h₁ : D.t' j i k ≫ pullback.fst _ _ ≫ D.f i k = pullback.fst _ _ ≫ D.t j i ≫ D.f i j := by
      rw [← 𝖣.t_fac_assoc]; congr 1; exact pullback.condition
    have h₂ : D.t' j i k ≫ pullback.fst _ _ ≫ D.t i k ≫ D.f k i =
        pullback.snd _ _ ≫ D.t j k ≫ D.f k j := by
      rw [← 𝖣.t_fac_assoc]
      apply @Epi.left_cancellation _ _ _ _ (D.t' k j i)
      rw [𝖣.cocycle_assoc, 𝖣.t_fac_assoc, 𝖣.t_inv_assoc]
      exact pullback.condition.symm
    exact ⟨CategoryTheory.congr_fun h₁ z, CategoryTheory.congr_fun h₂ z⟩⟩

open CategoryTheory.Limits.WalkingParallelPair

theorem eqvGen_of_π_eq
    -- Porting note: was `{x y : ∐ D.U}`
    {x y : sigmaObj (β := D.toGlueData.J) (C := TopCat) D.toGlueData.U}
    (h : 𝖣.π x = 𝖣.π y) :
    Relation.EqvGen
      (Function.Coequalizer.Rel 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap) x y := by
  delta GlueData.π Multicoequalizer.sigmaπ at h
  replace h : coequalizer.π D.diagram.fstSigmaMap D.diagram.sndSigmaMap x =
      coequalizer.π D.diagram.fstSigmaMap D.diagram.sndSigmaMap y :=
    (TopCat.mono_iff_injective (Multicoequalizer.isoCoequalizer 𝖣.diagram).inv).mp
    inferInstance h
  let diagram := parallelPair 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap ⋙ forget _
  have : colimit.ι diagram one x = colimit.ι diagram one y := by
    dsimp only [coequalizer.π] at h
    rw [← ι_preservesColimitIso_hom, ConcreteCategory.forget_map_eq_coe, types_comp_apply]
    simp_all
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
    refine Relation.EqvGen.mono ?_ (D.eqvGen_of_π_eq h :)
    rintro _ _ ⟨x⟩
    obtain ⟨⟨⟨i, j⟩, y⟩, rfl⟩ :=
      (ConcreteCategory.bijective_of_isIso (sigmaIsoSigma.{u, u} _).inv).2 x
    unfold InvImage MultispanIndex.fstSigmaMap MultispanIndex.sndSigmaMap
    rw [sigmaIsoSigma_inv_apply]
    -- `rw [← ConcreteCategory.comp_apply]` succeeds but rewrites the wrong expression
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, colimit.ι_desc_assoc,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, colimit.ι_desc_assoc]
      -- previous line now `erw` after https://github.com/leanprover-community/mathlib4/pull/13170
    erw [sigmaIsoSigma_hom_ι_apply, sigmaIsoSigma_hom_ι_apply]
    exact ⟨y, ⟨rfl, rfl⟩⟩
  · rintro ⟨z, e₁, e₂⟩
    dsimp only at *
    -- Porting note: there were `subst e₁` and `subst e₂`, instead of the `rw`
    rw [← e₁, ← e₂] at *
    rw [D.glue_condition_apply]

theorem ι_injective (i : D.J) : Function.Injective (𝖣.ι i) := by
  intro x y h
  rcases (D.ι_eq_iff_rel _ _ _ _).mp h with ⟨_, e₁, e₂⟩
  · dsimp only at *
    -- Porting note: there were `cases e₁` and `cases e₂`, instead of the `rw`
    rw [← e₁, ← e₂]
    simp

instance ι_mono (i : D.J) : Mono (𝖣.ι i) :=
  (TopCat.mono_iff_injective _).mpr (D.ι_injective _)

theorem image_inter (i j : D.J) :
    Set.range (𝖣.ι i) ∩ Set.range (𝖣.ι j) = Set.range (D.f i j ≫ 𝖣.ι _) := by
  ext x
  constructor
  · rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩
    obtain ⟨y, e₁, -⟩ := (D.ι_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm)
    · substs eq₁
      exact ⟨y, by simp [e₁]⟩
  · rintro ⟨x, hx⟩
    refine ⟨⟨D.f i j x, hx⟩, ⟨D.f j i (D.t _ _ x), ?_⟩⟩
    rw [D.glue_condition_apply]
    exact hx

theorem preimage_range (i j : D.J) : 𝖣.ι j ⁻¹' Set.range (𝖣.ι i) = Set.range (D.f j i) := by
  rw [← Set.preimage_image_eq (Set.range (D.f j i)) (D.ι_injective j), ← Set.image_univ, ←
    Set.image_univ, ← Set.image_comp, ← coe_comp, Set.image_univ, Set.image_univ, ← image_inter,
    Set.preimage_range_inter]

theorem preimage_image_eq_image (i j : D.J) (U : Set (𝖣.U i)) :
    𝖣.ι j ⁻¹' (𝖣.ι i '' U) = D.f _ _ '' ((D.t j i ≫ D.f _ _) ⁻¹' U) := by
  have : D.f _ _ ⁻¹' (𝖣.ι j ⁻¹' (𝖣.ι i '' U)) = (D.t j i ≫ D.f _ _) ⁻¹' U := by
    ext x
    conv_rhs => rw [← Set.preimage_image_eq U (D.ι_injective _)]
    simp
  rw [← this, Set.image_preimage_eq_inter_range]
  symm
  apply Set.inter_eq_self_of_subset_left
  rw [← D.preimage_range i j]
  exact Set.preimage_mono (Set.image_subset_range _ _)

theorem preimage_image_eq_image' (i j : D.J) (U : Set (𝖣.U i)) :
    𝖣.ι j ⁻¹' (𝖣.ι i '' U) = (D.t i j ≫ D.f _ _) '' (D.f _ _ ⁻¹' U) := by
  convert D.preimage_image_eq_image i j U using 1
  rw [coe_comp, coe_comp, Set.image_comp]
  congr! 1
  rw [← Set.eq_preimage_iff_image_eq, Set.preimage_preimage]
  · change _ = (D.t i j ≫ D.t j i ≫ _) ⁻¹' _
    rw [𝖣.t_inv_assoc]
  rw [← isIso_iff_bijective]
  apply (forget TopCat).map_isIso

theorem open_image_open (i : D.J) (U : Opens (𝖣.U i)) : IsOpen (𝖣.ι i '' U) := by
  rw [isOpen_iff]
  intro j
  rw [preimage_image_eq_image]
  apply (D.f_open _ _).isOpenMap
  apply (D.t j i ≫ D.f i j).hom.continuous_toFun.isOpen_preimage
  exact U.isOpen

theorem ι_isOpenEmbedding (i : D.J) : IsOpenEmbedding (𝖣.ι i) :=
  .of_continuous_injective_isOpenMap (𝖣.ι i).hom.continuous_toFun (D.ι_injective i) fun U h =>
    D.open_image_open i ⟨U, h⟩

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
structure MkCore where
  /-- The index type `J` -/
  {J : Type u}
  /-- For each `i : J`, a bundled topological space `U i` -/
  U : J → TopCat.{u}
  /-- For each `i j : J`, an open set `V i j ⊆ U i` -/
  V : ∀ i, J → Opens (U i)
  /-- For each `i j : ι`, a transition map `t i j : V i j ⟶ V j i` -/
  t : ∀ i j, (Opens.toTopCat _).obj (V i j) ⟶ (Opens.toTopCat _).obj (V j i)
  V_id : ∀ i, V i i = ⊤
  t_id : ∀ i, ⇑(t i i) = id
  t_inter : ∀ ⦃i j⦄ (k) (x : V i j), ↑x ∈ V i k → (((↑) : (V j i) → (U j)) (t i j x)) ∈ V j k
  cocycle :
    ∀ (i j k) (x : V i j) (h : ↑x ∈ V i k),
      -- Porting note: the underscore in the next line was `↑(t i j x)`, but Lean type-mismatched
      (((↑) : (V k j) → (U k)) (t j k ⟨_, t_inter k x h⟩)) = ((↑) : (V k i) → (U k)) (t i k ⟨x, h⟩)

theorem MkCore.t_inv (h : MkCore) (i j : h.J) (x : h.V j i) : h.t i j ((h.t j i) x) = x := by
  have := h.cocycle j i j x ?_
  · rw [h.t_id] at this
    · convert Subtype.eq this
  rw [h.V_id]
  trivial

instance (h : MkCore.{u}) (i j : h.J) : IsIso (h.t i j) := by
  use h.t j i; constructor <;> ext1; exacts [h.t_inv _ _ _, h.t_inv _ _ _]

/-- (Implementation) the restricted transition map to be fed into `TopCat.GlueData`. -/
def MkCore.t' (h : MkCore.{u}) (i j k : h.J) :
    pullback (h.V i j).inclusion' (h.V i k).inclusion' ⟶
      pullback (h.V j k).inclusion' (h.V j i).inclusion' := by
  refine (pullbackIsoProdSubtype _ _).hom ≫ ofHom ⟨?_, ?_⟩ ≫ (pullbackIsoProdSubtype _ _).inv
  · intro x
    refine ⟨⟨⟨(h.t i j x.1.1).1, ?_⟩, h.t i j x.1.1⟩, rfl⟩
    rcases x with ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    exact h.t_inter _ ⟨x, hx⟩ hx'
  fun_prop

/-- This is a constructor of `TopCat.GlueData` whose arguments are in terms of elements and
intersections rather than subobjects and pullbacks. Please refer to `TopCat.GlueData.MkCore` for
details. -/
def mk' (h : MkCore.{u}) : TopCat.GlueData where
  J := h.J
  U := h.U
  V i := (Opens.toTopCat _).obj (h.V i.1 i.2)
  f i j := (h.V i j).inclusion'
  f_id i := (h.V_id i).symm ▸ (Opens.inclusionTopIso (h.U i)).isIso_hom
  f_open := fun i j : h.J => (h.V i j).isOpenEmbedding
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
    dsimp only [Opens.coe_inclusion', hom_comp, hom_ofHom, ContinuousMap.comp_assoc,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, hom_id, ContinuousMap.id_apply]
    rw [Subtype.mk_eq_mk, Prod.mk_inj, Subtype.mk_eq_mk, Subtype.ext_iff, and_self_iff]
    convert congr_arg Subtype.val (h.t_inv k i ⟨x, hx'⟩) using 3
    refine Subtype.ext ?_
    exact h.cocycle i j k ⟨x, hx⟩ hx'
  f_mono _ _ := (TopCat.mono_iff_injective _).mpr fun _ _ h => Subtype.ext h

variable {α : Type u} [TopologicalSpace α] {J : Type u} (U : J → Opens α)

/-- We may construct a glue data from a family of open sets. -/
@[simps! toGlueData_J toGlueData_U toGlueData_V toGlueData_t toGlueData_f]
def ofOpenSubsets : TopCat.GlueData.{u} :=
  mk'.{u}
    { J
      U := fun i => (Opens.toTopCat <| TopCat.of α).obj (U i)
      V := fun _ j => (Opens.map <| Opens.inclusion' _).obj (U j)
      t := fun i j => ofHom ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, by fun_prop⟩
      V_id := fun i => by ext; simp
      t_id := fun i => by ext; rfl
      t_inter := fun _ _ _ _ hx => hx
      cocycle := fun _ _ _ _ _ => rfl }

/-- The canonical map from the glue of a family of open subsets `α` into `α`.
This map is an open embedding (`fromOpenSubsetsGlue_isOpenEmbedding`),
and its range is `⋃ i, (U i : Set α)` (`range_fromOpenSubsetsGlue`).
-/
def fromOpenSubsetsGlue : (ofOpenSubsets U).toGlueData.glued ⟶ TopCat.of α :=
  Multicoequalizer.desc _ _ (fun _ => Opens.inclusion' _) (by rintro ⟨i, j⟩; ext x; rfl)

-- Porting note: `elementwise` here produces a bad lemma,
-- where too much has been simplified, despite the `nosimp`.
@[simp, elementwise nosimp]
theorem ι_fromOpenSubsetsGlue (i : J) :
    (ofOpenSubsets U).toGlueData.ι i ≫ fromOpenSubsetsGlue U = Opens.inclusion' _ :=
  Multicoequalizer.π_desc _ _ _ _ _

theorem fromOpenSubsetsGlue_injective : Function.Injective (fromOpenSubsetsGlue U) := by
  intro x y e
  obtain ⟨i, ⟨x, hx⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  obtain ⟨j, ⟨y, hy⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective y
  -- see the porting note on `ι_fromOpenSubsetsGlue`
  rw [ι_fromOpenSubsetsGlue_apply, ι_fromOpenSubsetsGlue_apply] at e
  change x = y at e
  subst e
  rw [(ofOpenSubsets U).ι_eq_iff_rel]
  exact ⟨⟨⟨x, hx⟩, hy⟩, rfl, rfl⟩

theorem fromOpenSubsetsGlue_isOpenMap : IsOpenMap (fromOpenSubsetsGlue U) := by
  intro s hs
  rw [(ofOpenSubsets U).isOpen_iff] at hs
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  use fromOpenSubsetsGlue U '' s ∩ Set.range (@Opens.inclusion' (TopCat.of α) (U i))
  use Set.inter_subset_left
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply (Opens.isOpenEmbedding (X := TopCat.of α) (U i)).isOpenMap
    convert hs i using 1
    rw [← ι_fromOpenSubsetsGlue, coe_comp, Set.preimage_comp]
    congr! 1
    exact Set.preimage_image_eq _ (fromOpenSubsetsGlue_injective U)
  · refine ⟨Set.mem_image_of_mem _ hx, ?_⟩
    rw [ι_fromOpenSubsetsGlue_apply]
    exact Set.mem_range_self (f := (Opens.inclusion' _).hom) ⟨x, hx'⟩

theorem fromOpenSubsetsGlue_isOpenEmbedding : IsOpenEmbedding (fromOpenSubsetsGlue U) :=
  .of_continuous_injective_isOpenMap (ContinuousMap.continuous_toFun _)
    (fromOpenSubsetsGlue_injective U) (fromOpenSubsetsGlue_isOpenMap U)

theorem range_fromOpenSubsetsGlue : Set.range (fromOpenSubsetsGlue U) = ⋃ i, (U i : Set α) := by
  ext
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
    rw [ι_fromOpenSubsetsGlue_apply]
    exact Set.subset_iUnion _ i hx'
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    rename_i x
    exact ⟨(ofOpenSubsets U).toGlueData.ι i ⟨x, hx⟩, ι_fromOpenSubsetsGlue_apply _ _ _⟩

/-- The gluing of an open cover is homeomomorphic to the original space. -/
def openCoverGlueHomeo (h : ⋃ i, (U i : Set α) = Set.univ) :
    (ofOpenSubsets U).toGlueData.glued ≃ₜ α :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (fromOpenSubsetsGlue U)
      ⟨fromOpenSubsetsGlue_injective U,
        Set.range_eq_univ.mp ((range_fromOpenSubsetsGlue U).symm ▸ h)⟩)
    (fromOpenSubsetsGlue U).hom.2 (fromOpenSubsetsGlue_isOpenMap U)

end GlueData

end TopCat
