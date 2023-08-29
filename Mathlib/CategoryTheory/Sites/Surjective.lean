/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Sites.CompatibleSheafification

#align_import category_theory.sites.surjective from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"
/-!

# Locally surjective morphisms

## Main definitions

- `IsLocallySurjective` : A morphism of presheaves valued in a concrete category is locally
  surjective with respect to a grothendieck topology if every section in the target is locally
  in the set-theoretic image, i.e. the image sheaf coincides with the target.

## Main results

- `toSheafify_isLocallySurjective` : `toSheafify` is locally surjective.

-/


universe v u w v' u' w'

open Opposite CategoryTheory CategoryTheory.GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.funLike

variable {A : Type u'} [Category.{v'} A] [ConcreteCategory.{w'} A]

/-- Given `f : F ⟶ G`, a morphism between presieves, and `s : G.obj (op U)`, this is the sieve
of `U` consisting of the `i : V ⟶ U` such that `s` restricted along `i` is in the image of `f`. -/
@[simps (config := .lemmasOnly)]
def imageSieve {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : G.obj (op U)) : Sieve U where
  arrows V i := ∃ t : F.obj (op V), f.app _ t = G.map i.op s
  downward_closed := by
    rintro V W i ⟨t, ht⟩ j
    -- ⊢ ∃ t, ↑(NatTrans.app f (op W)) t = ↑(G.map (j ≫ i).op) s
    refine' ⟨F.map j.op t, _⟩
    -- ⊢ ↑(NatTrans.app f (op W)) (↑(F.map j.op) t) = ↑(G.map (j ≫ i).op) s
    rw [op_comp, G.map_comp, comp_apply, ← ht, elementwise_of% f.naturality]
    -- 🎉 no goals
#align category_theory.image_sieve CategoryTheory.imageSieve

theorem imageSieve_eq_sieveOfSection {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : G.obj (op U)) :
    imageSieve f s = (imagePresheaf (whiskerRight f (forget A))).sieveOfSection s :=
  rfl
#align category_theory.image_sieve_eq_sieve_of_section CategoryTheory.imageSieve_eq_sieveOfSection

theorem imageSieve_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : G.obj (op U)) :
    imageSieve (whiskerRight f (forget A)) s = imageSieve f s :=
  rfl
#align category_theory.image_sieve_whisker_forget CategoryTheory.imageSieve_whisker_forget

theorem imageSieve_app {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : F.obj (op U)) :
    imageSieve f (f.app _ s) = ⊤ := by
  ext V i
  -- ⊢ (imageSieve f (↑(NatTrans.app f (op U)) s)).arrows i ↔ ⊤.arrows i
  simp only [Sieve.top_apply, iff_true_iff, imageSieve_apply]
  -- ⊢ ∃ t, ↑(NatTrans.app f (op V)) t = ↑(G.map i.op) (↑(NatTrans.app f (op U)) s)
  have := elementwise_of% (f.naturality i.op)
  -- ⊢ ∃ t, ↑(NatTrans.app f (op V)) t = ↑(G.map i.op) (↑(NatTrans.app f (op U)) s)
  exact ⟨F.map i.op s, this s⟩
  -- 🎉 no goals
#align category_theory.image_sieve_app CategoryTheory.imageSieve_app

/-- A morphism of presheaves `f : F ⟶ G` is locally surjective with respect to a grothendieck
topology if every section of `G` is locally in the image of `f`. -/
def IsLocallySurjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) : Prop :=
  ∀ (U : C) (s : G.obj (op U)), imageSieve f s ∈ J U
#align category_theory.is_locally_surjective CategoryTheory.IsLocallySurjective

theorem isLocallySurjective_iff_imagePresheaf_sheafify_eq_top {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) :
    IsLocallySurjective J f ↔ (imagePresheaf (whiskerRight f (forget A))).sheafify J = ⊤ := by
  simp only [Subpresheaf.ext_iff, Function.funext_iff, Set.ext_iff, top_subpresheaf_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true_iff]
  exact ⟨fun H U => H (unop U), fun H U => H (op U)⟩
  -- 🎉 no goals
#align category_theory.is_locally_surjective_iff_image_presheaf_sheafify_eq_top CategoryTheory.isLocallySurjective_iff_imagePresheaf_sheafify_eq_top

theorem isLocallySurjective_iff_imagePresheaf_sheafify_eq_top' {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) :
    IsLocallySurjective J f ↔ (imagePresheaf f).sheafify J = ⊤ := by
  simp only [Subpresheaf.ext_iff, Function.funext_iff, Set.ext_iff, top_subpresheaf_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true_iff]
  exact ⟨fun H U => H (unop U), fun H U => H (op U)⟩
  -- 🎉 no goals
#align category_theory.is_locally_surjective_iff_image_presheaf_sheafify_eq_top' CategoryTheory.isLocallySurjective_iff_imagePresheaf_sheafify_eq_top'

theorem isLocallySurjective_iff_isIso {F G : Sheaf J (Type w)} (f : F ⟶ G) :
    IsLocallySurjective J f.1 ↔ IsIso (imageSheafι f) := by
  rw [imageSheafι, isLocallySurjective_iff_imagePresheaf_sheafify_eq_top',
    Subpresheaf.eq_top_iff_isIso]
  exact
    ⟨fun h => @isIso_of_reflects_iso _ _ _ _ _ _ (imageSheafι f) (sheafToPresheaf J _) h _, fun h =>
      @Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf J _) _ h⟩
#align category_theory.is_locally_surjective_iff_is_iso CategoryTheory.isLocallySurjective_iff_isIso

theorem isLocallySurjective_iff_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) :
    IsLocallySurjective J f ↔ IsLocallySurjective J (whiskerRight f (forget A)) := by
  simp only [isLocallySurjective_iff_imagePresheaf_sheafify_eq_top]
  -- ⊢ Subpresheaf.sheafify J (imagePresheaf (whiskerRight f (forget A))) = ⊤ ↔ Sub …
  rfl
  -- 🎉 no goals
#align category_theory.is_locally_surjective_iff_whisker_forget CategoryTheory.isLocallySurjective_iff_whisker_forget

theorem isLocallySurjective_of_surjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
    (H : ∀ U, Function.Surjective (f.app U)) : IsLocallySurjective J f := by
  intro U s
  -- ⊢ imageSieve f s ∈ sieves J U
  obtain ⟨t, rfl⟩ := H _ s
  -- ⊢ imageSieve f (↑(NatTrans.app f (op U)) t) ∈ sieves J U
  rw [imageSieve_app]
  -- ⊢ ⊤ ∈ sieves J U
  exact J.top_mem _
  -- 🎉 no goals
#align category_theory.is_locally_surjective_of_surjective CategoryTheory.isLocallySurjective_of_surjective

theorem isLocallySurjective_of_iso {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsIso f] :
    IsLocallySurjective J f := by
  apply isLocallySurjective_of_surjective
  -- ⊢ ∀ (U : Cᵒᵖ), Function.Surjective ↑(NatTrans.app f U)
  intro U
  -- ⊢ Function.Surjective ↑(NatTrans.app f U)
  apply Function.Bijective.surjective
  -- ⊢ Function.Bijective ↑(NatTrans.app f U)
  rw [← isIso_iff_bijective, ←forget_map_eq_coe]
  -- ⊢ IsIso ((forget A).map (NatTrans.app f U))
  infer_instance
  -- 🎉 no goals
#align category_theory.is_locally_surjective_of_iso CategoryTheory.isLocallySurjective_of_iso

theorem IsLocallySurjective.comp {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃}
    (h₁ : IsLocallySurjective J f₁) (h₂ : IsLocallySurjective J f₂) :
    IsLocallySurjective J (f₁ ≫ f₂) := by
  intro U s
  -- ⊢ imageSieve (f₁ ≫ f₂) s ∈ sieves J U
  have : (Sieve.bind (imageSieve f₂ s) fun _ _ h => imageSieve f₁ h.choose) ≤
      imageSieve (f₁ ≫ f₂) s := by
    rintro V i ⟨W, i, j, H, ⟨t', ht'⟩, rfl⟩
    refine' ⟨t', _⟩
    rw [op_comp, F₃.map_comp, NatTrans.comp_app, comp_apply, comp_apply, ht',
      elementwise_of% f₂.naturality, H.choose_spec]
  apply J.superset_covering this
  -- ⊢ (Sieve.bind (imageSieve f₂ s).arrows fun x x_1 h => imageSieve f₁ (Exists.ch …
  apply J.bind_covering
  -- ⊢ imageSieve f₂ s ∈ sieves J U
  · apply h₂
    -- 🎉 no goals
  · intros; apply h₁
    -- ⊢ imageSieve f₁ (Exists.choose H✝) ∈ sieves J Y✝
            -- 🎉 no goals
#align category_theory.is_locally_surjective.comp CategoryTheory.IsLocallySurjective.comp

section

variable (F : Cᵒᵖ ⥤ Type max u v)

/-- The image of `F` in `J.sheafify F` is isomorphic to the sheafification. -/
noncomputable def sheafificationIsoImagePresheaf :
    J.sheafify F ≅ ((imagePresheaf (J.toSheafify F)).sheafify J).toPresheaf where
  hom :=
    J.sheafifyLift (toImagePresheafSheafify J _)
      ((isSheaf_iff_isSheaf_of_type J _).mpr <|
        Subpresheaf.sheafify_isSheaf _ <|
          (isSheaf_iff_isSheaf_of_type J _).mp <| sheafify_isSheaf J _)
  inv := Subpresheaf.ι _
  hom_inv_id :=
    J.sheafify_hom_ext _ _ (J.sheafify_isSheaf _) (by simp [toImagePresheafSheafify])
                                                      -- 🎉 no goals
  inv_hom_id := by
    rw [← cancel_mono (Subpresheaf.ι _), Category.id_comp, Category.assoc]
    -- ⊢ Subpresheaf.ι (Subpresheaf.sheafify J (imagePresheaf (toSheafify J F))) ≫ sh …
    refine' Eq.trans _ (Category.comp_id _)
    -- ⊢ Subpresheaf.ι (Subpresheaf.sheafify J (imagePresheaf (toSheafify J F))) ≫ sh …
    congr 1
    -- ⊢ sheafifyLift J (toImagePresheafSheafify J (toSheafify J F)) (_ : Presheaf.Is …
    exact J.sheafify_hom_ext _ _ (J.sheafify_isSheaf _) (by simp [toImagePresheafSheafify])
    -- 🎉 no goals
#align category_theory.sheafification_iso_image_presheaf CategoryTheory.sheafificationIsoImagePresheaf

-- We need to sheafify
variable {B : Type w} [Category.{max u v} B] [ConcreteCategory.{max u v} B]
  [∀ X : C, Limits.HasColimitsOfShape (J.Cover X)ᵒᵖ B]
  [∀ (P : Cᵒᵖ ⥤ B) (X : C) (S : J.Cover X), Limits.HasMultiequalizer (S.index P)]
  [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ B),
      Limits.PreservesLimit (W.index P).multicospan (forget B)]
  [∀ X : C, Limits.PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget B)]
  [∀ (α β : Type max u v) (fst snd : β → α),
      Limits.HasLimitsOfShape (Limits.WalkingMulticospan fst snd) B]

theorem toSheafify_isLocallySurjective (F : Cᵒᵖ ⥤ B) : IsLocallySurjective J (J.toSheafify F) := by
  rw [isLocallySurjective_iff_whisker_forget, ← toSheafify_comp_sheafifyCompIso_inv]
  -- ⊢ IsLocallySurjective J (toSheafify J (F ⋙ forget B) ≫ (sheafifyCompIso J (for …
  apply IsLocallySurjective.comp
  -- ⊢ IsLocallySurjective J (toSheafify J (F ⋙ forget B))
  · rw [isLocallySurjective_iff_imagePresheaf_sheafify_eq_top, Subpresheaf.eq_top_iff_isIso]
    -- ⊢ IsIso (Subpresheaf.ι (Subpresheaf.sheafify J (imagePresheaf (whiskerRight (t …
    exact IsIso.of_iso_inv (sheafificationIsoImagePresheaf J (F ⋙ forget B))
    -- 🎉 no goals
  · exact isLocallySurjective_of_iso _ _
    -- 🎉 no goals
#align category_theory.to_sheafify_is_locally_surjective CategoryTheory.toSheafify_isLocallySurjective

end

end CategoryTheory
