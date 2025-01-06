/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Mario Carneiro, Andrew Yang
-/
import Mathlib.Topology.Category.TopCat.Limits.Products

/-!
# Pullbacks and pushouts in the category of topological spaces
-/

open TopologicalSpace Topology

open CategoryTheory

open CategoryTheory.Limits

universe v u w

noncomputable section

namespace TopCat

variable {J : Type v} [Category.{w} J]

section Pullback

variable {X Y Z : TopCat.{u}}

/-- The first projection from the pullback. -/
abbrev pullbackFst (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.of { p : X × Y // f p.1 = g p.2 } ⟶ X :=
  ⟨Prod.fst ∘ Subtype.val, by
    apply Continuous.comp <;> set_option tactic.skipAssignedInstances false in continuity⟩

lemma pullbackFst_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x) : pullbackFst f g x = x.1.1 := rfl

/-- The second projection from the pullback. -/
abbrev pullbackSnd (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.of { p : X × Y // f p.1 = g p.2 } ⟶ Y :=
  ⟨Prod.snd ∘ Subtype.val, by
    apply Continuous.comp <;> set_option tactic.skipAssignedInstances false in continuity⟩

lemma pullbackSnd_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x) : pullbackSnd f g x = x.1.2 := rfl

/-- The explicit pullback cone of `X, Y` given by `{ p : X × Y // f p.1 = g p.2 }`. -/
def pullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) : PullbackCone f g :=
  PullbackCone.mk (pullbackFst f g) (pullbackSnd f g)
    (by
      dsimp [pullbackFst, pullbackSnd, Function.comp_def]
      ext ⟨x, h⟩
      -- Next 2 lines were
      -- `rw [comp_apply, ContinuousMap.coe_mk, comp_apply, ContinuousMap.coe_mk]`
      -- `exact h` before https://github.com/leanprover/lean4/pull/2644
      rw [comp_apply, comp_apply]
      congr!)

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
        -- This used to be `rw`, but we need `rw; rfl` after https://github.com/leanprover/lean4/pull/2644
        rw [comp_apply, ContinuousMap.coe_mk]
        rfl
      · delta pullbackCone
        ext a
        -- This used to be `rw`, but we need `rw; rfl` after https://github.com/leanprover/lean4/pull/2644
        rw [comp_apply, ContinuousMap.coe_mk]
        rfl
      · intro m h₁ h₂
        -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be `ext x`.
        apply ContinuousMap.ext; intro x
        apply Subtype.ext
        apply Prod.ext
        · simpa using ConcreteCategory.congr_hom h₁ x
        · simpa using ConcreteCategory.congr_hom h₂ x)

/-- The pullback of two maps can be identified as a subspace of `X × Y`. -/
def pullbackIsoProdSubtype (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ≅ TopCat.of { p : X × Y // f p.1 = g p.2 } :=
  (limit.isLimit _).conePointUniqueUpToIso (pullbackConeIsLimit f g)

@[reassoc (attr := simp)]
theorem pullbackIsoProdSubtype_inv_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).inv ≫ pullback.fst _ _ = pullbackFst f g := by
  simp [pullbackCone, pullbackIsoProdSubtype]

theorem pullbackIsoProdSubtype_inv_fst_apply (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : { p : X × Y // f p.1 = g p.2 }) :
    pullback.fst f g ((pullbackIsoProdSubtype f g).inv x) = (x : X × Y).fst :=
  ConcreteCategory.congr_hom (pullbackIsoProdSubtype_inv_fst f g) x

@[reassoc (attr := simp)]
theorem pullbackIsoProdSubtype_inv_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).inv ≫ pullback.snd _ _ = pullbackSnd f g := by
  simp [pullbackCone, pullbackIsoProdSubtype]

theorem pullbackIsoProdSubtype_inv_snd_apply (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : { p : X × Y // f p.1 = g p.2 }) :
    pullback.snd f g ((pullbackIsoProdSubtype f g).inv x) = (x : X × Y).snd :=
  ConcreteCategory.congr_hom (pullbackIsoProdSubtype_inv_snd f g) x

theorem pullbackIsoProdSubtype_hom_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).hom ≫ pullbackFst f g = pullback.fst _ _ := by
  rw [← Iso.eq_inv_comp, pullbackIsoProdSubtype_inv_fst]

theorem pullbackIsoProdSubtype_hom_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).hom ≫ pullbackSnd f g = pullback.snd _ _ := by
  rw [← Iso.eq_inv_comp, pullbackIsoProdSubtype_inv_snd]

-- Porting note: why do I need to tell Lean to coerce pullback to a type
theorem pullbackIsoProdSubtype_hom_apply {f : X ⟶ Z} {g : Y ⟶ Z}
    (x : ConcreteCategory.forget.obj (pullback f g)) :
    (pullbackIsoProdSubtype f g).hom x =
      ⟨⟨pullback.fst f g x, pullback.snd f g x⟩, by
        simpa using ConcreteCategory.congr_hom pullback.condition x⟩ := by
  apply Subtype.ext; apply Prod.ext
  exacts [ConcreteCategory.congr_hom (pullbackIsoProdSubtype_hom_fst f g) x,
    ConcreteCategory.congr_hom (pullbackIsoProdSubtype_hom_snd f g) x]

theorem pullback_topology {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullback f g).str =
      induced (pullback.fst f g) X.str ⊓
        induced (pullback.snd f g) Y.str := by
  let homeo := homeoOfIso (pullbackIsoProdSubtype f g)
  refine homeo.isInducing.eq_induced.trans ?_
  change induced homeo (induced _ ( (induced Prod.fst X.str) ⊓ (induced Prod.snd Y.str))) = _
  simp only [induced_compose, induced_inf]
  congr

theorem range_pullback_to_prod {X Y Z : TopCat} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Set.range (prod.lift (pullback.fst f g) (pullback.snd f g)) =
      { x | (Limits.prod.fst ≫ f) x = (Limits.prod.snd ≫ g) x } := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (_ ≫ _ ≫ f) _ = (_ ≫ _ ≫ g) _ -- new `change` after https://github.com/leanprover-community/mathlib4/pull/13170
    simp [pullback.condition]
  · rintro (h : f (_, _).1 = g (_, _).2)
    use (pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, h⟩
    change (forget TopCat).map _ _ = _ -- new `change` after https://github.com/leanprover-community/mathlib4/pull/13170
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩ <;>
    erw [← comp_apply, ← comp_apply, limit.lift_π] <;> -- now `erw` after https://github.com/leanprover-community/mathlib4/pull/13170
    -- This used to be `simp` before https://github.com/leanprover/lean4/pull/2644
    aesop_cat

/-- The pullback along an embedding is (isomorphic to) the preimage. -/
noncomputable
def pullbackHomeoPreimage
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Z) (hf : Continuous f) (g : Y → Z) (hg : IsEmbedding g) :
    { p : X × Y // f p.1 = g p.2 } ≃ₜ f ⁻¹' Set.range g where
  toFun := fun x ↦ ⟨x.1.1, _, x.2.symm⟩
  invFun := fun x ↦ ⟨⟨x.1, Exists.choose x.2⟩, (Exists.choose_spec x.2).symm⟩
  left_inv := by
    intro x
    ext <;> dsimp
    apply hg.injective
    convert x.prop
    exact Exists.choose_spec (p := fun y ↦ g y = f (↑x : X × Y).1) _
  right_inv := fun _ ↦ rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    refine continuous_prod_mk.mpr ⟨continuous_subtype_val, hg.isInducing.continuous_iff.mpr ?_⟩
    convert hf.comp continuous_subtype_val
    ext x
    exact Exists.choose_spec x.2

theorem isInducing_pullback_to_prod {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsInducing <| ⇑(prod.lift (pullback.fst f g) (pullback.snd f g)) :=
  ⟨by simp [topologicalSpace_coe, prod_topology, pullback_topology, induced_compose, ← coe_comp]⟩

@[deprecated (since := "2024-10-28")] alias inducing_pullback_to_prod := isInducing_pullback_to_prod

theorem isEmbedding_pullback_to_prod {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsEmbedding <| ⇑(prod.lift (pullback.fst f g) (pullback.snd f g)) :=
  ⟨isInducing_pullback_to_prod f g, (TopCat.mono_iff_injective _).mp inferInstance⟩

@[deprecated (since := "2024-10-26")]
alias embedding_pullback_to_prod := isEmbedding_pullback_to_prod

/-- If the map `S ⟶ T` is mono, then there is a description of the image of `W ×ₛ X ⟶ Y ×ₜ Z`. -/
theorem range_pullback_map {W X Y Z S T : TopCat} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) [H₃ : Mono i₃] (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    Set.range (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) =
      (pullback.fst g₁ g₂) ⁻¹' Set.range i₁ ∩ (pullback.snd g₁ g₂) ⁻¹' Set.range i₂ := by
  ext
  constructor
  · rintro ⟨y, rfl⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_range]
    rw [← comp_apply, ← comp_apply]
    simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, comp_apply]
    exact ⟨exists_apply_eq_apply _ _, exists_apply_eq_apply _ _⟩
  rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  have : f₁ x₁ = f₂ x₂ := by
    apply (TopCat.mono_iff_injective _).mp H₃
    rw [← comp_apply, eq₁, ← comp_apply, eq₂,
      comp_apply, comp_apply, hx₁, hx₂, ← comp_apply, pullback.condition]
    rfl -- `rfl` was not needed before https://github.com/leanprover-community/mathlib4/pull/13170
  use (pullbackIsoProdSubtype f₁ f₂).inv ⟨⟨x₁, x₂⟩, this⟩
  change (forget TopCat).map _ _ = _
  apply Concrete.limit_ext
  rintro (_ | _ | _) <;>
  erw [← comp_apply, ← comp_apply] -- now `erw` after https://github.com/leanprover-community/mathlib4/pull/13170
  · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app_one]
    simp only [cospan_one, pullbackIsoProdSubtype_inv_fst_assoc, comp_apply]
    rw [pullbackFst_apply, hx₁, ← limit.w _ WalkingCospan.Hom.inl, cospan_map_inl,
        comp_apply (g := g₁)]
  · simp only [cospan_left, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      pullbackIsoProdSubtype_inv_fst_assoc, comp_apply]
    erw [hx₁] -- now `erw` after https://github.com/leanprover-community/mathlib4/pull/13170
  · simp only [cospan_right, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      pullbackIsoProdSubtype_inv_snd_assoc, comp_apply]
    erw [hx₂] -- now `erw` after https://github.com/leanprover-community/mathlib4/pull/13170

theorem pullback_fst_range {X Y S : TopCat} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.fst f g) = { x : X | ∃ y : Y, f x = g y } := by
  ext x
  constructor
  · rintro ⟨(y : (forget TopCat).obj _), rfl⟩
    use (pullback.snd f g) y
    exact ConcreteCategory.congr_hom pullback.condition y
  · rintro ⟨y, eq⟩
    use (TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨x, y⟩, eq⟩
    rw [pullbackIsoProdSubtype_inv_fst_apply]

theorem pullback_snd_range {X Y S : TopCat} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.snd f g) = { y : Y | ∃ x : X, f x = g y } := by
  ext y
  constructor
  · rintro ⟨(x : (forget TopCat).obj _), rfl⟩
    use (pullback.fst f g) x
    exact ConcreteCategory.congr_hom pullback.condition x
  · rintro ⟨x, eq⟩
    use (TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨x, y⟩, eq⟩
    rw [pullbackIsoProdSubtype_inv_snd_apply]

/-- If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are embeddings,
then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an embedding.

```
W ⟶ Y
 ↘   ↘
  S ⟶ T
 ↗   ↗
X ⟶ Z
```
-/
theorem pullback_map_isEmbedding {W X Y Z S T : TopCat.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S)
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z} (H₁ : IsEmbedding i₁)
    (H₂ : IsEmbedding i₂) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    IsEmbedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine .of_comp (ContinuousMap.continuous_toFun _)
    (show Continuous (prod.lift (pullback.fst g₁ g₂) (pullback.snd g₁ g₂)) from
        ContinuousMap.continuous_toFun _)
      ?_
  suffices
    IsEmbedding (prod.lift (pullback.fst f₁ f₂) (pullback.snd f₁ f₂) ≫ Limits.prod.map i₁ i₂) by
    simpa [← coe_comp] using this
  rw [coe_comp]
  exact (isEmbedding_prodMap H₁ H₂).comp (isEmbedding_pullback_to_prod _ _)

@[deprecated (since := "2024-10-26")]
alias pullback_map_embedding_of_embeddings := pullback_map_isEmbedding

/-- If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are open embeddings, and `S ⟶ T`
is mono, then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an open embedding.

```
W ⟶ Y
 ↘   ↘
  S ⟶ T
 ↗   ↗
X ⟶ Z
```
-/
theorem pullback_map_isOpenEmbedding {W X Y Z S T : TopCat.{u}} (f₁ : W ⟶ S)
    (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z} (H₁ : IsOpenEmbedding i₁)
    (H₂ : IsOpenEmbedding i₂) (i₃ : S ⟶ T) [H₃ : Mono i₃] (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : IsOpenEmbedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  constructor
  · apply
      pullback_map_isEmbedding f₁ f₂ g₁ g₂ H₁.isEmbedding H₂.isEmbedding i₃ eq₁ eq₂
  · rw [range_pullback_map]
    apply IsOpen.inter <;> apply Continuous.isOpen_preimage
    · apply ContinuousMap.continuous_toFun
    · exact H₁.isOpen_range
    · apply ContinuousMap.continuous_toFun
    · exact H₂.isOpen_range

@[deprecated (since := "2024-10-18")]
alias pullback_map_openEmbedding_of_open_embeddings := pullback_map_isOpenEmbedding


lemma snd_isEmbedding_of_left {X Y S : TopCat} {f : X ⟶ S} (H : IsEmbedding f) (g : Y ⟶ S) :
    IsEmbedding <| ⇑(pullback.snd f g) := by
  convert (homeoOfIso (asIso (pullback.snd (𝟙 S) g))).isEmbedding.comp
      (pullback_map_isEmbedding (i₂ := 𝟙 Y)
        f g (𝟙 S) g H (homeoOfIso (Iso.refl _)).isEmbedding (𝟙 _) rfl (by simp))
  erw [← coe_comp]
  simp

@[deprecated (since := "2024-10-26")]
alias snd_embedding_of_left_embedding := snd_isEmbedding_of_left

theorem fst_isEmbedding_of_right {X Y S : TopCat} (f : X ⟶ S) {g : Y ⟶ S}
    (H : IsEmbedding g) : IsEmbedding <| ⇑(pullback.fst f g) := by
  convert (homeoOfIso (asIso (pullback.fst f (𝟙 S)))).isEmbedding.comp
      (pullback_map_isEmbedding (i₁ := 𝟙 X)
        f g f (𝟙 _) (homeoOfIso (Iso.refl _)).isEmbedding H (𝟙 _) rfl (by simp))
  erw [← coe_comp]
  simp

@[deprecated (since := "2024-10-26")]
alias fst_embedding_of_right_embedding := fst_isEmbedding_of_right

theorem isEmbedding_of_pullback {X Y S : TopCat} {f : X ⟶ S} {g : Y ⟶ S} (H₁ : IsEmbedding f)
    (H₂ : IsEmbedding g) : IsEmbedding (limit.π (cospan f g) WalkingCospan.one) := by
  convert H₂.comp (snd_isEmbedding_of_left H₁ g)
  rw [← coe_comp, ← limit.w _ WalkingCospan.Hom.inr]
  rfl

@[deprecated (since := "2024-10-26")]
alias embedding_of_pullback_embeddings := isEmbedding_of_pullback

theorem snd_isOpenEmbedding_of_left {X Y S : TopCat} {f : X ⟶ S} (H : IsOpenEmbedding f)
    (g : Y ⟶ S) : IsOpenEmbedding <| ⇑(pullback.snd f g) := by
  convert (homeoOfIso (asIso (pullback.snd (𝟙 S) g))).isOpenEmbedding.comp
      (pullback_map_isOpenEmbedding (i₂ := 𝟙 Y) f g (𝟙 _) g H
        (homeoOfIso (Iso.refl _)).isOpenEmbedding (𝟙 _) rfl (by simp))
  erw [← coe_comp]
  simp

@[deprecated (since := "2024-10-18")]
alias snd_openEmbedding_of_left_openEmbedding := snd_isOpenEmbedding_of_left

theorem fst_isOpenEmbedding_of_right {X Y S : TopCat} (f : X ⟶ S) {g : Y ⟶ S}
    (H : IsOpenEmbedding g) : IsOpenEmbedding <| ⇑(pullback.fst f g) := by
  convert (homeoOfIso (asIso (pullback.fst f (𝟙 S)))).isOpenEmbedding.comp
      (pullback_map_isOpenEmbedding (i₁ := 𝟙 X) f g f (𝟙 _)
        (homeoOfIso (Iso.refl _)).isOpenEmbedding H (𝟙 _) rfl (by simp))
  erw [← coe_comp]
  simp

@[deprecated (since := "2024-10-18")]
alias fst_openEmbedding_of_right_openEmbedding := fst_isOpenEmbedding_of_right

/-- If `X ⟶ S`, `Y ⟶ S` are open embeddings, then so is `X ×ₛ Y ⟶ S`. -/
theorem isOpenEmbedding_of_pullback {X Y S : TopCat} {f : X ⟶ S} {g : Y ⟶ S}
    (H₁ : IsOpenEmbedding f) (H₂ : IsOpenEmbedding g) :
    IsOpenEmbedding (limit.π (cospan f g) WalkingCospan.one) := by
  convert H₂.comp (snd_isOpenEmbedding_of_left H₁ g)
  rw [← coe_comp, ← limit.w _ WalkingCospan.Hom.inr]
  rfl

@[deprecated (since := "2024-10-30")]
alias isOpenEmbedding_of_pullback_open_embeddings := isOpenEmbedding_of_pullback

@[deprecated (since := "2024-10-18")]
alias openEmbedding_of_pullback_open_embeddings := isOpenEmbedding_of_pullback

theorem fst_iso_of_right_embedding_range_subset {X Y S : TopCat} (f : X ⟶ S) {g : Y ⟶ S}
    (hg : IsEmbedding g) (H : Set.range f ⊆ Set.range g) :
    IsIso (pullback.fst f g) := by
  let esto : (pullback f g : TopCat) ≃ₜ X :=
    (Homeomorph.ofIsEmbedding _ (fst_isEmbedding_of_right f hg)).trans
      { toFun := Subtype.val
        invFun := fun x =>
          ⟨x, by
            rw [pullback_fst_range]
            exact ⟨_, (H (Set.mem_range_self x)).choose_spec.symm⟩⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun x => rfl }
  convert (isoOfHomeo esto).isIso_hom

theorem snd_iso_of_left_embedding_range_subset {X Y S : TopCat} {f : X ⟶ S} (hf : IsEmbedding f)
    (g : Y ⟶ S) (H : Set.range g ⊆ Set.range f) : IsIso (pullback.snd f g) := by
  let esto : (pullback f g : TopCat) ≃ₜ Y :=
    (Homeomorph.ofIsEmbedding _ (snd_isEmbedding_of_left hf g)).trans
      { toFun := Subtype.val
        invFun := fun x =>
          ⟨x, by
            rw [pullback_snd_range]
            exact ⟨_, (H (Set.mem_range_self x)).choose_spec⟩⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun x => rfl }
  convert (isoOfHomeo esto).isIso_hom

theorem pullback_snd_image_fst_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set X) :
    (pullback.snd f g) '' ((pullback.fst f g) ⁻¹' U) =
      g ⁻¹' (f '' U) := by
  ext x
  constructor
  · rintro ⟨(y : (forget TopCat).obj _), hy, rfl⟩
    exact
      ⟨(pullback.fst f g) y, hy, ConcreteCategory.congr_hom pullback.condition y⟩
  · rintro ⟨y, hy, eq⟩
  -- next 5 lines were
  -- `exact ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq⟩, by simpa, by simp⟩` before https://github.com/leanprover-community/mathlib4/pull/13170
    refine ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq⟩, ?_, ?_⟩
    · simp only [coe_of, Set.mem_preimage]
      convert hy
      erw [pullbackIsoProdSubtype_inv_fst_apply]
    · rw [pullbackIsoProdSubtype_inv_snd_apply]

theorem pullback_fst_image_snd_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set Y) :
    (pullback.fst f g) '' ((pullback.snd f g) ⁻¹' U) =
      f ⁻¹' (g '' U) := by
  ext x
  constructor
  · rintro ⟨(y : (forget TopCat).obj _), hy, rfl⟩
    exact
      ⟨(pullback.snd f g) y, hy,
        (ConcreteCategory.congr_hom pullback.condition y).symm⟩
  · rintro ⟨y, hy, eq⟩
    -- next 5 lines were
    -- `exact ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq.symm⟩, by simpa, by simp⟩`
    -- before https://github.com/leanprover-community/mathlib4/pull/13170
    refine ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq.symm⟩, ?_, ?_⟩
    · simp only [coe_of, Set.mem_preimage]
      convert hy
      erw [pullbackIsoProdSubtype_inv_snd_apply]
    · rw [pullbackIsoProdSubtype_inv_fst_apply]

end Pullback

--TODO: Add analogous constructions for `pushout`.
theorem coinduced_of_isColimit {F : J ⥤ TopCat.{max v u}} (c : Cocone F) (hc : IsColimit c) :
    c.pt.str = ⨆ j, (F.obj j).str.coinduced (c.ι.app j) := by
  let homeo := homeoOfIso (hc.coconePointUniqueUpToIso (colimitCoconeIsColimit F))
  ext
  refine homeo.symm.isOpen_preimage.symm.trans (Iff.trans ?_ isOpen_iSup_iff.symm)
  exact isOpen_iSup_iff

theorem colimit_topology (F : J ⥤ TopCat.{max v u}) :
    (colimit F).str = ⨆ j, (F.obj j).str.coinduced (colimit.ι F j) :=
  coinduced_of_isColimit _ (colimit.isColimit F)

theorem colimit_isOpen_iff (F : J ⥤ TopCat.{max v u}) (U : Set ((colimit F : _) : Type max v u)) :
    IsOpen U ↔ ∀ j, IsOpen (colimit.ι F j ⁻¹' U) := by
  dsimp [topologicalSpace_coe]
  conv_lhs => rw [colimit_topology F]
  exact isOpen_iSup_iff

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

end TopCat
