/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang
-/
import Mathlib.Topology.Category.TopCat.Limits.Products

#align_import topology.category.Top.limits.pullbacks from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!
# Pullbacks and pushouts in the category of topological spaces
-/

-- Porting note: every ML3 decl has an uppercase letter
set_option linter.uppercaseLean3 false

open TopologicalSpace

open CategoryTheory

open CategoryTheory.Limits

universe v u w

noncomputable section

namespace TopCat

variable {J : Type v} [SmallCategory J]

section Pullback

variable {X Y Z : TopCat.{u}}

/-- The first projection from the pullback. -/
abbrev pullbackFst (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.of { p : X × Y // f p.1 = g p.2 } ⟶ X :=
  ⟨Prod.fst ∘ Subtype.val, by
    apply Continuous.comp <;> set_option tactic.skipAssignedInstances false in continuity⟩
#align Top.pullback_fst TopCat.pullbackFst

lemma pullbackFst_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x) : pullbackFst f g x = x.1.1 := rfl

/-- The second projection from the pullback. -/
abbrev pullbackSnd (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.of { p : X × Y // f p.1 = g p.2 } ⟶ Y :=
  ⟨Prod.snd ∘ Subtype.val, by
    apply Continuous.comp <;> set_option tactic.skipAssignedInstances false in continuity⟩
#align Top.pullback_snd TopCat.pullbackSnd

lemma pullbackSnd_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x) : pullbackSnd f g x = x.1.2 := rfl

/-- The explicit pullback cone of `X, Y` given by `{ p : X × Y // f p.1 = g p.2 }`. -/
def pullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) : PullbackCone f g :=
  PullbackCone.mk (pullbackFst f g) (pullbackSnd f g)
    (by
      dsimp [pullbackFst, pullbackSnd, Function.comp_def]
      ext ⟨x, h⟩
      -- Next 2 lines were
      -- `rw [comp_apply, ContinuousMap.coe_mk, comp_apply, ContinuousMap.coe_mk]`
      -- `exact h` before leanprover/lean4#2644
      rw [comp_apply, comp_apply]
      congr!)
#align Top.pullback_cone TopCat.pullbackCone

/-- The constructed cone is a limit. -/
def pullbackConeIsLimit (f : X ⟶ Z) (g : Y ⟶ Z) : IsLimit (pullbackCone f g) :=
  PullbackCone.isLimitAux' _
    (by
      intro S
      constructor; swap
      · exact
          { toFun := fun x =>
              ⟨⟨S.fst x, S.snd x⟩, by simpa using ConcreteCategory.congr_hom S.condition x⟩
            continuous_toFun := by
              apply Continuous.subtype_mk <| Continuous.prod_mk ?_ ?_
              · exact (PullbackCone.fst S)|>.continuous_toFun
              · exact (PullbackCone.snd S)|>.continuous_toFun
          }
      refine ⟨?_, ?_, ?_⟩
      · delta pullbackCone
        ext a
        -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
        erw [comp_apply, ContinuousMap.coe_mk]
      · delta pullbackCone
        ext a
        -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
        erw [comp_apply, ContinuousMap.coe_mk]
      · intro m h₁ h₂
        -- Porting note: used to be ext x
        apply ContinuousMap.ext; intro x
        apply Subtype.ext
        apply Prod.ext
        · simpa using ConcreteCategory.congr_hom h₁ x
        · simpa using ConcreteCategory.congr_hom h₂ x)
#align Top.pullback_cone_is_limit TopCat.pullbackConeIsLimit

/-- The pullback of two maps can be identified as a subspace of `X × Y`. -/
def pullbackIsoProdSubtype (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ≅ TopCat.of { p : X × Y // f p.1 = g p.2 } :=
  (limit.isLimit _).conePointUniqueUpToIso (pullbackConeIsLimit f g)
#align Top.pullback_iso_prod_subtype TopCat.pullbackIsoProdSubtype

@[reassoc (attr := simp)]
theorem pullbackIsoProdSubtype_inv_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).inv ≫ pullback.fst = pullbackFst f g := by
  simp [pullbackCone, pullbackIsoProdSubtype]
#align Top.pullback_iso_prod_subtype_inv_fst TopCat.pullbackIsoProdSubtype_inv_fst

theorem pullbackIsoProdSubtype_inv_fst_apply (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : { p : X × Y // f p.1 = g p.2 }) :
    (pullback.fst : pullback f g ⟶ _) ((pullbackIsoProdSubtype f g).inv x) = (x : X × Y).fst :=
  ConcreteCategory.congr_hom (pullbackIsoProdSubtype_inv_fst f g) x
#align Top.pullback_iso_prod_subtype_inv_fst_apply TopCat.pullbackIsoProdSubtype_inv_fst_apply

@[reassoc (attr := simp)]
theorem pullbackIsoProdSubtype_inv_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).inv ≫ pullback.snd = pullbackSnd f g := by
  simp [pullbackCone, pullbackIsoProdSubtype]
#align Top.pullback_iso_prod_subtype_inv_snd TopCat.pullbackIsoProdSubtype_inv_snd

theorem pullbackIsoProdSubtype_inv_snd_apply (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : { p : X × Y // f p.1 = g p.2 }) :
    (pullback.snd : pullback f g ⟶ _) ((pullbackIsoProdSubtype f g).inv x) = (x : X × Y).snd :=
  ConcreteCategory.congr_hom (pullbackIsoProdSubtype_inv_snd f g) x
#align Top.pullback_iso_prod_subtype_inv_snd_apply TopCat.pullbackIsoProdSubtype_inv_snd_apply

theorem pullbackIsoProdSubtype_hom_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).hom ≫ pullbackFst f g = pullback.fst := by
  rw [← Iso.eq_inv_comp, pullbackIsoProdSubtype_inv_fst]
#align Top.pullback_iso_prod_subtype_hom_fst TopCat.pullbackIsoProdSubtype_hom_fst

theorem pullbackIsoProdSubtype_hom_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).hom ≫ pullbackSnd f g = pullback.snd := by
  rw [← Iso.eq_inv_comp, pullbackIsoProdSubtype_inv_snd]
#align Top.pullback_iso_prod_subtype_hom_snd TopCat.pullbackIsoProdSubtype_hom_snd

-- Porting note: why do I need to tell Lean to coerce pullback to a type
theorem pullbackIsoProdSubtype_hom_apply {f : X ⟶ Z} {g : Y ⟶ Z}
    (x : ConcreteCategory.forget.obj (pullback f g)) :
    (pullbackIsoProdSubtype f g).hom x =
      ⟨⟨(pullback.fst : pullback f g ⟶ _) x, (pullback.snd : pullback f g ⟶ _) x⟩, by
        simpa using ConcreteCategory.congr_hom pullback.condition x⟩ := by
  apply Subtype.ext; apply Prod.ext
  exacts [ConcreteCategory.congr_hom (pullbackIsoProdSubtype_hom_fst f g) x,
    ConcreteCategory.congr_hom (pullbackIsoProdSubtype_hom_snd f g) x]
#align Top.pullback_iso_prod_subtype_hom_apply TopCat.pullbackIsoProdSubtype_hom_apply

theorem pullback_topology {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullback f g).str =
      induced (pullback.fst : pullback f g ⟶ _) X.str ⊓
        induced (pullback.snd : pullback f g ⟶ _) Y.str := by
  let homeo := homeoOfIso (pullbackIsoProdSubtype f g)
  refine homeo.inducing.induced.trans ?_
  change induced homeo (induced _ ( (induced Prod.fst X.str) ⊓ (induced Prod.snd Y.str))) = _
  simp only [induced_compose, induced_inf]
  congr
#align Top.pullback_topology TopCat.pullback_topology

theorem range_pullback_to_prod {X Y Z : TopCat} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Set.range (prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) =
      { x | (Limits.prod.fst ≫ f) x = (Limits.prod.snd ≫ g) x } := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (_ ≫ _ ≫ f) _ = (_ ≫ _ ≫ g) _ -- new `change` after #13170
    simp [pullback.condition]
  · rintro (h : f (_, _).1 = g (_, _).2)
    use (pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, h⟩
    change (forget TopCat).map _ _ = _ -- new `change` after #13170
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩ <;>
    erw [← comp_apply, ← comp_apply, limit.lift_π] <;> -- now `erw` after #13170
    -- This used to be `simp` before leanprover/lean4#2644
    aesop_cat
#align Top.range_pullback_to_prod TopCat.range_pullback_to_prod

/-- The pullback along an embedding is (isomorphic to) the preimage. -/
noncomputable
def pullbackHomeoPreimage
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Z) (hf : Continuous f) (g : Y → Z) (hg : Embedding g) :
    { p : X × Y // f p.1 = g p.2 } ≃ₜ f ⁻¹' Set.range g where
  toFun := fun x ↦ ⟨x.1.1, _, x.2.symm⟩
  invFun := fun x ↦ ⟨⟨x.1, Exists.choose x.2⟩, (Exists.choose_spec x.2).symm⟩
  left_inv := by
    intro x
    ext <;> dsimp
    apply hg.inj
    convert x.prop
    exact Exists.choose_spec (p := fun y ↦ g y = f (↑x : X × Y).1) _
  right_inv := fun x ↦ rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    refine continuous_prod_mk.mpr ⟨continuous_subtype_val, hg.toInducing.continuous_iff.mpr ?_⟩
    convert hf.comp continuous_subtype_val
    ext x
    exact Exists.choose_spec x.2

theorem inducing_pullback_to_prod {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Inducing <| ⇑(prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) :=
  ⟨by simp [topologicalSpace_coe, prod_topology, pullback_topology, induced_compose, ← coe_comp]⟩
#align Top.inducing_pullback_to_prod TopCat.inducing_pullback_to_prod

theorem embedding_pullback_to_prod {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Embedding <| ⇑(prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) :=
  ⟨inducing_pullback_to_prod f g, (TopCat.mono_iff_injective _).mp inferInstance⟩
#align Top.embedding_pullback_to_prod TopCat.embedding_pullback_to_prod

/-- If the map `S ⟶ T` is mono, then there is a description of the image of `W ×ₛ X ⟶ Y ×ₜ Z`. -/
theorem range_pullback_map {W X Y Z S T : TopCat} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) [H₃ : Mono i₃] (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    Set.range (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) =
      (pullback.fst : pullback g₁ g₂ ⟶ _) ⁻¹' Set.range i₁ ∩
        (pullback.snd : pullback g₁ g₂ ⟶ _) ⁻¹' Set.range i₂ := by
  ext
  constructor
  · rintro ⟨y, rfl⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_range]
    erw [← comp_apply, ← comp_apply] -- now `erw` after #13170
    simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, comp_apply]
    exact ⟨exists_apply_eq_apply _ _, exists_apply_eq_apply _ _⟩
  rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  have : f₁ x₁ = f₂ x₂ := by
    apply (TopCat.mono_iff_injective _).mp H₃
    erw [← comp_apply, eq₁, ← comp_apply, eq₂, -- now `erw` after #13170
      comp_apply, comp_apply, hx₁, hx₂, ← comp_apply, pullback.condition]
    rfl -- `rfl` was not needed before #13170
  use (pullbackIsoProdSubtype f₁ f₂).inv ⟨⟨x₁, x₂⟩, this⟩
  change (forget TopCat).map _ _ = _
  apply Concrete.limit_ext
  rintro (_ | _ | _) <;>
  erw [← comp_apply, ← comp_apply] -- now `erw` after #13170
  simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app_one]
  · simp only [cospan_one, pullbackIsoProdSubtype_inv_fst_assoc, comp_apply]
    erw [pullbackFst_apply, hx₁]
    rw [← limit.w _ WalkingCospan.Hom.inl, cospan_map_inl, comp_apply (g := g₁)]
    rfl -- `rfl` was not needed before #13170
  · simp only [cospan_left, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      pullbackIsoProdSubtype_inv_fst_assoc, comp_apply]
    erw [hx₁] -- now `erw` after #13170
    rfl -- `rfl` was not needed before #13170
  · simp only [cospan_right, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      pullbackIsoProdSubtype_inv_snd_assoc, comp_apply]
    erw [hx₂] -- now `erw` after #13170
    rfl -- `rfl` was not needed before #13170
#align Top.range_pullback_map TopCat.range_pullback_map

theorem pullback_fst_range {X Y S : TopCat} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.fst : pullback f g ⟶ _) = { x : X | ∃ y : Y, f x = g y } := by
  ext x
  constructor
  · rintro ⟨(y : (forget TopCat).obj _), rfl⟩
    use (pullback.snd : pullback f g ⟶ _) y
    exact ConcreteCategory.congr_hom pullback.condition y
  · rintro ⟨y, eq⟩
    use (TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨x, y⟩, eq⟩
    rw [pullbackIsoProdSubtype_inv_fst_apply]
#align Top.pullback_fst_range TopCat.pullback_fst_range

theorem pullback_snd_range {X Y S : TopCat} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.snd : pullback f g ⟶ _) = { y : Y | ∃ x : X, f x = g y } := by
  ext y
  constructor
  · rintro ⟨(x : (forget TopCat).obj _), rfl⟩
    use (pullback.fst : pullback f g ⟶ _) x
    exact ConcreteCategory.congr_hom pullback.condition x
  · rintro ⟨x, eq⟩
    use (TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨x, y⟩, eq⟩
    rw [pullbackIsoProdSubtype_inv_snd_apply]
#align Top.pullback_snd_range TopCat.pullback_snd_range

/-- If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are embeddings,
then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an embedding.

  W ⟶ Y
    ↘      ↘
      S ⟶ T
    ↗      ↗
  X ⟶ Z
-/
theorem pullback_map_embedding_of_embeddings {W X Y Z S T : TopCat.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S)
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z} (H₁ : Embedding i₁) (H₂ : Embedding i₂)
    (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    Embedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine
    embedding_of_embedding_compose (ContinuousMap.continuous_toFun _)
      (show Continuous (prod.lift pullback.fst pullback.snd : pullback g₁ g₂ ⟶ Y ⨯ Z) from
        ContinuousMap.continuous_toFun _)
      ?_
  suffices
    Embedding (prod.lift pullback.fst pullback.snd ≫ Limits.prod.map i₁ i₂ : pullback f₁ f₂ ⟶ _) by
    simpa [← coe_comp] using this
  rw [coe_comp]
  exact Embedding.comp (embedding_prod_map H₁ H₂) (embedding_pullback_to_prod _ _)
#align Top.pullback_map_embedding_of_embeddings TopCat.pullback_map_embedding_of_embeddings

/-- If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are open embeddings, and `S ⟶ T`
is mono, then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an open embedding.
  W ⟶ Y
    ↘      ↘
      S ⟶ T
    ↗       ↗
  X ⟶ Z
-/
theorem pullback_map_openEmbedding_of_open_embeddings {W X Y Z S T : TopCat.{u}} (f₁ : W ⟶ S)
    (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z} (H₁ : OpenEmbedding i₁)
    (H₂ : OpenEmbedding i₂) (i₃ : S ⟶ T) [H₃ : Mono i₃] (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : OpenEmbedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  constructor
  · apply
      pullback_map_embedding_of_embeddings f₁ f₂ g₁ g₂ H₁.toEmbedding H₂.toEmbedding i₃ eq₁ eq₂
  · rw [range_pullback_map]
    apply IsOpen.inter <;> apply Continuous.isOpen_preimage
    · apply ContinuousMap.continuous_toFun
    · exact H₁.isOpen_range
    · apply ContinuousMap.continuous_toFun
    · exact H₂.isOpen_range
#align Top.pullback_map_open_embedding_of_open_embeddings TopCat.pullback_map_openEmbedding_of_open_embeddings

theorem snd_embedding_of_left_embedding {X Y S : TopCat} {f : X ⟶ S} (H : Embedding f) (g : Y ⟶ S) :
    Embedding <| ⇑(pullback.snd : pullback f g ⟶ Y) := by
  convert (homeoOfIso (asIso (pullback.snd : pullback (𝟙 S) g ⟶ _))).embedding.comp
      (pullback_map_embedding_of_embeddings (i₂ := 𝟙 Y)
        f g (𝟙 S) g H (homeoOfIso (Iso.refl _)).embedding (𝟙 _) rfl (by simp))
  erw [← coe_comp]
  simp
#align Top.snd_embedding_of_left_embedding TopCat.snd_embedding_of_left_embedding

theorem fst_embedding_of_right_embedding {X Y S : TopCat} (f : X ⟶ S) {g : Y ⟶ S}
    (H : Embedding g) : Embedding <| ⇑(pullback.fst : pullback f g ⟶ X) := by
  convert (homeoOfIso (asIso (pullback.fst : pullback f (𝟙 S) ⟶ _))).embedding.comp
      (pullback_map_embedding_of_embeddings (i₁ := 𝟙 X)
        f g f (𝟙 _) (homeoOfIso (Iso.refl _)).embedding H (𝟙 _) rfl (by simp))
  erw [← coe_comp]
  simp
#align Top.fst_embedding_of_right_embedding TopCat.fst_embedding_of_right_embedding

theorem embedding_of_pullback_embeddings {X Y S : TopCat} {f : X ⟶ S} {g : Y ⟶ S} (H₁ : Embedding f)
    (H₂ : Embedding g) : Embedding (limit.π (cospan f g) WalkingCospan.one) := by
  convert H₂.comp (snd_embedding_of_left_embedding H₁ g)
  erw [← coe_comp]
  rw [← limit.w _ WalkingCospan.Hom.inr]
  rfl
#align Top.embedding_of_pullback_embeddings TopCat.embedding_of_pullback_embeddings

theorem snd_openEmbedding_of_left_openEmbedding {X Y S : TopCat} {f : X ⟶ S} (H : OpenEmbedding f)
    (g : Y ⟶ S) : OpenEmbedding <| ⇑(pullback.snd : pullback f g ⟶ Y) := by
  convert (homeoOfIso (asIso (pullback.snd : pullback (𝟙 S) g ⟶ _))).openEmbedding.comp
      (pullback_map_openEmbedding_of_open_embeddings (i₂ := 𝟙 Y) f g (𝟙 _) g H
        (homeoOfIso (Iso.refl _)).openEmbedding (𝟙 _) rfl (by simp))
  erw [← coe_comp]
  simp
#align Top.snd_open_embedding_of_left_open_embedding TopCat.snd_openEmbedding_of_left_openEmbedding

theorem fst_openEmbedding_of_right_openEmbedding {X Y S : TopCat} (f : X ⟶ S) {g : Y ⟶ S}
    (H : OpenEmbedding g) : OpenEmbedding <| ⇑(pullback.fst : pullback f g ⟶ X) := by
  convert (homeoOfIso (asIso (pullback.fst : pullback f (𝟙 S) ⟶ _))).openEmbedding.comp
      (pullback_map_openEmbedding_of_open_embeddings (i₁ := 𝟙 X) f g f (𝟙 _)
        (homeoOfIso (Iso.refl _)).openEmbedding H (𝟙 _) rfl (by simp))
  erw [← coe_comp]
  simp
#align Top.fst_open_embedding_of_right_open_embedding TopCat.fst_openEmbedding_of_right_openEmbedding

/-- If `X ⟶ S`, `Y ⟶ S` are open embeddings, then so is `X ×ₛ Y ⟶ S`. -/
theorem openEmbedding_of_pullback_open_embeddings {X Y S : TopCat} {f : X ⟶ S} {g : Y ⟶ S}
    (H₁ : OpenEmbedding f) (H₂ : OpenEmbedding g) :
    OpenEmbedding (limit.π (cospan f g) WalkingCospan.one) := by
  convert H₂.comp (snd_openEmbedding_of_left_openEmbedding H₁ g)
  erw [← coe_comp]
  rw [← limit.w _ WalkingCospan.Hom.inr]
  rfl
#align Top.open_embedding_of_pullback_open_embeddings TopCat.openEmbedding_of_pullback_open_embeddings

theorem fst_iso_of_right_embedding_range_subset {X Y S : TopCat} (f : X ⟶ S) {g : Y ⟶ S}
    (hg : Embedding g) (H : Set.range f ⊆ Set.range g) :
    IsIso (pullback.fst : pullback f g ⟶ X) := by
  let esto : (pullback f g : TopCat) ≃ₜ X :=
    (Homeomorph.ofEmbedding _ (fst_embedding_of_right_embedding f hg)).trans
      { toFun := Subtype.val
        invFun := fun x =>
          ⟨x, by
            rw [pullback_fst_range]
            exact ⟨_, (H (Set.mem_range_self x)).choose_spec.symm⟩⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun x => rfl }
  convert (isoOfHomeo esto).isIso_hom
#align Top.fst_iso_of_right_embedding_range_subset TopCat.fst_iso_of_right_embedding_range_subset

theorem snd_iso_of_left_embedding_range_subset {X Y S : TopCat} {f : X ⟶ S} (hf : Embedding f)
    (g : Y ⟶ S) (H : Set.range g ⊆ Set.range f) : IsIso (pullback.snd : pullback f g ⟶ Y) := by
  let esto : (pullback f g : TopCat) ≃ₜ Y :=
    (Homeomorph.ofEmbedding _ (snd_embedding_of_left_embedding hf g)).trans
      { toFun := Subtype.val
        invFun := fun x =>
          ⟨x, by
            rw [pullback_snd_range]
            exact ⟨_, (H (Set.mem_range_self x)).choose_spec⟩⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun x => rfl }
  convert (isoOfHomeo esto).isIso_hom
#align Top.snd_iso_of_left_embedding_range_subset TopCat.snd_iso_of_left_embedding_range_subset

theorem pullback_snd_image_fst_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set X) :
    (pullback.snd : pullback f g ⟶ _) '' ((pullback.fst : pullback f g ⟶ _) ⁻¹' U) =
      g ⁻¹' (f '' U) := by
  ext x
  constructor
  · rintro ⟨(y : (forget TopCat).obj _), hy, rfl⟩
    exact
      ⟨(pullback.fst : pullback f g ⟶ _) y, hy, ConcreteCategory.congr_hom pullback.condition y⟩
  · rintro ⟨y, hy, eq⟩
  -- next 5 lines were
  -- `exact ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq⟩, by simpa, by simp⟩` before #13170
    refine ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq⟩, ?_, ?_⟩
    · simp only [coe_of, Set.mem_preimage]
      convert hy
      erw [pullbackIsoProdSubtype_inv_fst_apply]
    · rw [pullbackIsoProdSubtype_inv_snd_apply]
#align Top.pullback_snd_image_fst_preimage TopCat.pullback_snd_image_fst_preimage

theorem pullback_fst_image_snd_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set Y) :
    (pullback.fst : pullback f g ⟶ _) '' ((pullback.snd : pullback f g ⟶ _) ⁻¹' U) =
      f ⁻¹' (g '' U) := by
  ext x
  constructor
  · rintro ⟨(y : (forget TopCat).obj _), hy, rfl⟩
    exact
      ⟨(pullback.snd : pullback f g ⟶ _) y, hy,
        (ConcreteCategory.congr_hom pullback.condition y).symm⟩
  · rintro ⟨y, hy, eq⟩
    -- next 5 lines were
    -- `exact ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq.symm⟩, by simpa, by simp⟩`
    -- before #13170
    refine ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq.symm⟩, ?_, ?_⟩
    · simp only [coe_of, Set.mem_preimage]
      convert hy
      erw [pullbackIsoProdSubtype_inv_snd_apply]
    · rw [pullbackIsoProdSubtype_inv_fst_apply]
#align Top.pullback_fst_image_snd_preimage TopCat.pullback_fst_image_snd_preimage

end Pullback

--TODO: Add analogous constructions for `pushout`.
theorem coinduced_of_isColimit {F : J ⥤ TopCat.{max v u}} (c : Cocone F) (hc : IsColimit c) :
    c.pt.str = ⨆ j, (F.obj j).str.coinduced (c.ι.app j) := by
  let homeo := homeoOfIso (hc.coconePointUniqueUpToIso (colimitCoconeIsColimit F))
  ext
  refine homeo.symm.isOpen_preimage.symm.trans (Iff.trans ?_ isOpen_iSup_iff.symm)
  exact isOpen_iSup_iff
#align Top.coinduced_of_is_colimit TopCat.coinduced_of_isColimit

theorem colimit_topology (F : J ⥤ TopCat.{max v u}) :
    (colimit F).str = ⨆ j, (F.obj j).str.coinduced (colimit.ι F j) :=
  coinduced_of_isColimit _ (colimit.isColimit F)
#align Top.colimit_topology TopCat.colimit_topology

theorem colimit_isOpen_iff (F : J ⥤ TopCat.{max v u}) (U : Set ((colimit F : _) : Type max v u)) :
    IsOpen U ↔ ∀ j, IsOpen (colimit.ι F j ⁻¹' U) := by
  dsimp [topologicalSpace_coe]
  conv_lhs => rw [colimit_topology F]
  exact isOpen_iSup_iff
#align Top.colimit_is_open_iff TopCat.colimit_isOpen_iff

theorem coequalizer_isOpen_iff (F : WalkingParallelPair ⥤ TopCat.{u})
    (U : Set ((colimit F : _) : Type u)) :
    IsOpen U ↔ IsOpen (colimit.ι F WalkingParallelPair.one ⁻¹' U) := by
  rw [colimit_isOpen_iff]
  constructor
  · intro H
    exact H _
  · intro H j
    cases j
    · rw [← colimit.w F WalkingParallelPairHom.left]
      exact (F.map WalkingParallelPairHom.left).continuous_toFun.isOpen_preimage _ H
    · exact H
#align Top.coequalizer_is_open_iff TopCat.coequalizer_isOpen_iff

end TopCat
