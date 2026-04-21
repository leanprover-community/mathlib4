/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Mario Carneiro, Andrew Yang
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Products

/-!
# Pullbacks and pushouts in the category of topological spaces
-/

@[expose] public section

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
  ofHom ⟨Prod.fst ∘ Subtype.val, by fun_prop⟩

lemma pullbackFst_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x) : pullbackFst f g x = x.1.1 := rfl

/-- The second projection from the pullback. -/
abbrev pullbackSnd (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.of { p : X × Y // f p.1 = g p.2 } ⟶ Y :=
  ofHom ⟨Prod.snd ∘ Subtype.val, by fun_prop⟩

lemma pullbackSnd_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x) : pullbackSnd f g x = x.1.2 := rfl

/-- The explicit pullback cone of `X, Y` given by `{ p : X × Y // f p.1 = g p.2 }`. -/
def pullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) : PullbackCone f g :=
  PullbackCone.mk (pullbackFst f g) (pullbackSnd f g)
    (by
      dsimp [pullbackFst, pullbackSnd, Function.comp_def]
      ext ⟨x, h⟩
      simpa)

/-- The constructed cone is a limit. -/
def pullbackConeIsLimit (f : X ⟶ Z) (g : Y ⟶ Z) : IsLimit (pullbackCone f g) :=
  PullbackCone.isLimitAux' _
    (by
      intro S
      constructor; swap
      · exact ofHom
          { toFun := fun x =>
              ⟨⟨S.fst x, S.snd x⟩, by simpa using ConcreteCategory.congr_hom S.condition x⟩
            continuous_toFun := by fun_prop }
      refine ⟨?_, ?_, ?_⟩
      · delta pullbackCone
        ext a
        dsimp
      · delta pullbackCone
        ext a
        dsimp
      · intro m h₁ h₂
        ext x
        -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be `ext x`.
        apply Subtype.ext
        apply Prod.ext
        · simpa using ConcreteCategory.congr_hom h₁ x
        · simpa using ConcreteCategory.congr_hom h₂ x)

/-- The pullback of two maps can be identified as a subspace of `X × Y`. -/
def pullbackIsoProdSubtype (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ≅ TopCat.of { p : X × Y // f p.1 = g p.2 } :=
  (limit.isLimit _).conePointUniqueUpToIso (pullbackConeIsLimit f g)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackIsoProdSubtype_inv_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).inv ≫ pullback.fst _ _ = pullbackFst f g := by
  simp [pullbackCone, pullbackIsoProdSubtype]

theorem pullbackIsoProdSubtype_inv_fst_apply (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : { p : X × Y // f p.1 = g p.2 }) :
    pullback.fst f g ((pullbackIsoProdSubtype f g).inv x) = (x : X × Y).fst :=
  ConcreteCategory.congr_hom (pullbackIsoProdSubtype_inv_fst f g) x

set_option backward.isDefEq.respectTransparency false in
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

theorem pullbackIsoProdSubtype_hom_apply {f : X ⟶ Z} {g : Y ⟶ Z}
    (x : ↑(pullback f g)) :
    (pullbackIsoProdSubtype f g).hom x =
      ⟨⟨pullback.fst f g x, pullback.snd f g x⟩, by
        simpa using CategoryTheory.congr_fun pullback.condition x⟩ := rfl

theorem pullback_topology {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullback f g).str =
      induced (pullback.fst f g) X.str ⊓
        induced (pullback.snd f g) Y.str := by
  let homeo := homeoOfIso (pullbackIsoProdSubtype f g)
  refine homeo.isInducing.eq_induced.trans ?_
  change induced homeo (induced _ ((induced Prod.fst X.str) ⊓ (induced Prod.snd Y.str))) = _
  simp only [induced_compose, induced_inf]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem range_pullback_to_prod {X Y Z : TopCat} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Set.range (prod.lift (pullback.fst f g) (pullback.snd f g)) =
      { x | (Limits.prod.fst ≫ f) x = (Limits.prod.snd ≫ g) x } := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp only [← ConcreteCategory.comp_apply, Set.mem_setOf_eq]
    simp [pullback.condition]
  · rintro (h : f (_, _).1 = g (_, _).2)
    use (pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, h⟩
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩ <;>
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, limit.lift_π] <;>
      -- This used to be `simp` before https://github.com/leanprover/lean4/pull/2644
      cat_disch

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
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    refine continuous_subtype_val.prodMk <| hg.isInducing.continuous_iff.mpr ?_
    convert hf.comp continuous_subtype_val
    ext x
    exact Exists.choose_spec x.2

set_option backward.isDefEq.respectTransparency false in
theorem isInducing_pullback_to_prod {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsInducing <| ⇑(prod.lift (pullback.fst f g) (pullback.snd f g)) :=
  ⟨by simp [prod_topology, pullback_topology, induced_compose, ← coe_comp]⟩

theorem isEmbedding_pullback_to_prod {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsEmbedding <| ⇑(prod.lift (pullback.fst f g) (pullback.snd f g)) :=
  ⟨isInducing_pullback_to_prod f g, (TopCat.mono_iff_injective _).mp inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
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
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    exact ⟨exists_apply_eq_apply _ _, exists_apply_eq_apply _ _⟩
  rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  have : f₁ x₁ = f₂ x₂ := by
    apply (TopCat.mono_iff_injective _).mp H₃
    rw [← ConcreteCategory.comp_apply, eq₁, ← ConcreteCategory.comp_apply, eq₂,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hx₁, hx₂,
      ← ConcreteCategory.comp_apply, pullback.condition, ConcreteCategory.comp_apply]
  use (pullbackIsoProdSubtype f₁ f₂).inv ⟨⟨x₁, x₂⟩, this⟩
  apply Concrete.limit_ext
  rintro (_ | _ | _) <;>
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  · simp [hx₁, ← limit.w _ WalkingCospan.Hom.inl]
  · simp [hx₁]
  · simp [hx₂]

theorem pullback_fst_range {X Y S : TopCat} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.fst f g) = { x : X | ∃ y : Y, f x = g y } := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    use pullback.snd f g y
    exact CategoryTheory.congr_fun pullback.condition y
  · rintro ⟨y, eq⟩
    use (TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨x, y⟩, eq⟩
    rw [pullbackIsoProdSubtype_inv_fst_apply]

theorem pullback_snd_range {X Y S : TopCat} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.snd f g) = { y : Y | ∃ x : X, f x = g y } := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    use pullback.fst f g x
    exact CategoryTheory.congr_fun pullback.condition x
  · rintro ⟨x, eq⟩
    use (TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨x, y⟩, eq⟩
    rw [pullbackIsoProdSubtype_inv_snd_apply]

set_option backward.isDefEq.respectTransparency false in
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


set_option backward.isDefEq.respectTransparency false in
lemma snd_isEmbedding_of_left {X Y S : TopCat} {f : X ⟶ S} (H : IsEmbedding f) (g : Y ⟶ S) :
    IsEmbedding <| ⇑(pullback.snd f g) := by
  convert (homeoOfIso (asIso (pullback.snd (𝟙 S) g))).isEmbedding.comp
      (pullback_map_isEmbedding (i₂ := 𝟙 Y)
        f g (𝟙 S) g H (homeoOfIso (Iso.refl _)).isEmbedding (𝟙 _) rfl (by simp))
  simp [homeoOfIso, ← coe_comp]

set_option backward.isDefEq.respectTransparency false in
theorem fst_isEmbedding_of_right {X Y S : TopCat} (f : X ⟶ S) {g : Y ⟶ S}
    (H : IsEmbedding g) : IsEmbedding <| ⇑(pullback.fst f g) := by
  convert (homeoOfIso (asIso (pullback.fst f (𝟙 S)))).isEmbedding.comp
      (pullback_map_isEmbedding (i₁ := 𝟙 X)
        f g f (𝟙 _) (homeoOfIso (Iso.refl _)).isEmbedding H (𝟙 _) rfl (by simp))
  simp [homeoOfIso, ← coe_comp]

theorem isEmbedding_of_pullback {X Y S : TopCat} {f : X ⟶ S} {g : Y ⟶ S} (H₁ : IsEmbedding f)
    (H₂ : IsEmbedding g) : IsEmbedding (limit.π (cospan f g) WalkingCospan.one) := by
  convert H₂.comp (snd_isEmbedding_of_left H₁ g)
  rw [← coe_comp, ← limit.w _ WalkingCospan.Hom.inr]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem snd_isOpenEmbedding_of_left {X Y S : TopCat} {f : X ⟶ S} (H : IsOpenEmbedding f)
    (g : Y ⟶ S) : IsOpenEmbedding <| ⇑(pullback.snd f g) := by
  convert (homeoOfIso (asIso (pullback.snd (𝟙 S) g))).isOpenEmbedding.comp
      (pullback_map_isOpenEmbedding (i₂ := 𝟙 Y) f g (𝟙 _) g H
        (homeoOfIso (Iso.refl _)).isOpenEmbedding (𝟙 _) rfl (by simp))
  simp [homeoOfIso, ← coe_comp]

set_option backward.isDefEq.respectTransparency false in
theorem fst_isOpenEmbedding_of_right {X Y S : TopCat} (f : X ⟶ S) {g : Y ⟶ S}
    (H : IsOpenEmbedding g) : IsOpenEmbedding <| ⇑(pullback.fst f g) := by
  convert (homeoOfIso (asIso (pullback.fst f (𝟙 S)))).isOpenEmbedding.comp
      (pullback_map_isOpenEmbedding (i₁ := 𝟙 X) f g f (𝟙 _)
        (homeoOfIso (Iso.refl _)).isOpenEmbedding H (𝟙 _) rfl (by simp))
  simp [homeoOfIso, ← coe_comp]

/-- If `X ⟶ S`, `Y ⟶ S` are open embeddings, then so is `X ×ₛ Y ⟶ S`. -/
theorem isOpenEmbedding_of_pullback {X Y S : TopCat} {f : X ⟶ S} {g : Y ⟶ S}
    (H₁ : IsOpenEmbedding f) (H₂ : IsOpenEmbedding g) :
    IsOpenEmbedding (limit.π (cospan f g) WalkingCospan.one) := by
  convert H₂.comp (snd_isOpenEmbedding_of_left H₁ g)
  rw [← coe_comp, ← limit.w _ WalkingCospan.Hom.inr]
  rfl

theorem fst_iso_of_right_embedding_range_subset {X Y S : TopCat} (f : X ⟶ S) {g : Y ⟶ S}
    (hg : IsEmbedding g) (H : Set.range f ⊆ Set.range g) :
    IsIso (pullback.fst f g) := by
  let esto : (pullback f g : TopCat) ≃ₜ X :=
    (fst_isEmbedding_of_right f hg).toHomeomorph.trans
      { toFun := Subtype.val
        invFun := fun x =>
          ⟨x, by
            rw [pullback_fst_range]
            exact ⟨_, (H (Set.mem_range_self x)).choose_spec.symm⟩⟩ }
  convert (isoOfHomeo esto).isIso_hom

theorem snd_iso_of_left_embedding_range_subset {X Y S : TopCat} {f : X ⟶ S} (hf : IsEmbedding f)
    (g : Y ⟶ S) (H : Set.range g ⊆ Set.range f) : IsIso (pullback.snd f g) := by
  let esto : (pullback f g : TopCat) ≃ₜ Y :=
    (snd_isEmbedding_of_left hf g).toHomeomorph.trans
      { toFun := Subtype.val
        invFun := fun x =>
          ⟨x, by
            rw [pullback_snd_range]
            exact ⟨_, (H (Set.mem_range_self x)).choose_spec⟩⟩ }
  convert (isoOfHomeo esto).isIso_hom

theorem pullback_snd_image_fst_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set X) :
    (pullback.snd f g) '' ((pullback.fst f g) ⁻¹' U) =
      g ⁻¹' (f '' U) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact
      ⟨(pullback.fst f g) y, hy, CategoryTheory.congr_fun pullback.condition y⟩
  · rintro ⟨y, hy, eq⟩
  -- next 5 lines were
  -- `exact ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq⟩, by simpa, by simp⟩` before https://github.com/leanprover-community/mathlib4/pull/13170
    refine ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq⟩, ?_, ?_⟩
    · simp only [coe_of, Set.mem_preimage]
      convert hy
      rw [pullbackIsoProdSubtype_inv_fst_apply]
    · rw [pullbackIsoProdSubtype_inv_snd_apply]

theorem pullback_fst_image_snd_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set Y) :
    (pullback.fst f g) '' ((pullback.snd f g) ⁻¹' U) =
      f ⁻¹' (g '' U) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact
      ⟨(pullback.snd f g) y, hy,
        (CategoryTheory.congr_fun pullback.condition y).symm⟩
  · rintro ⟨y, hy, eq⟩
    -- next 5 lines were
    -- `exact ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq.symm⟩, by simpa, by simp⟩`
    -- before https://github.com/leanprover-community/mathlib4/pull/13170
    refine ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq.symm⟩, ?_, ?_⟩
    · simp only [coe_of, Set.mem_preimage]
      convert hy
      rw [pullbackIsoProdSubtype_inv_snd_apply]
    · rw [pullbackIsoProdSubtype_inv_fst_apply]

end Pullback

section

variable {X Y : TopCat.{u}} {f g : X ⟶ Y}

lemma isOpen_iff_of_isColimit_cofork (c : Cofork f g) (hc : IsColimit c) (U : Set c.pt) :
    IsOpen U ↔ IsOpen (c.π ⁻¹' U) := by
  rw [isOpen_iff_of_isColimit _ hc]
  constructor
  · intro h
    exact h .one
  · rintro h (_ | _)
    · rw [← c.w .left]
      exact Continuous.isOpen_preimage f.hom.continuous (c.π ⁻¹' U) h
    · exact h

lemma isQuotientMap_of_isColimit_cofork (c : Cofork f g) (hc : IsColimit c) :
    IsQuotientMap c.π := by
  rw [isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s ↦ ?_, ?_⟩
  · exact (isOpen_iff_of_isColimit_cofork c hc s).symm
  · simpa only [← epi_iff_surjective] using epi_of_isColimit_cofork hc

theorem coequalizer_isOpen_iff (U : Set ((coequalizer f g :) : Type u)) :
    IsOpen U ↔ IsOpen (coequalizer.π f g ⁻¹' U) :=
  isOpen_iff_of_isColimit_cofork _ (coequalizerIsCoequalizer f g) _

end

end TopCat
