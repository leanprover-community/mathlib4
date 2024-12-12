/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Closed.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Monoidal category structure on categories of sheaves

-/

universe v v' u u'

namespace CategoryTheory

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {A : Type u} [Category.{v} A] [MonoidalCategory A]

open Opposite Limits MonoidalCategory MonoidalClosed Enriched.FunctorCategory

namespace Presieve

variable {P₁ : Cᵒᵖ ⥤ Type u} {P₂ : Cᵒᵖ ⥤ Type v}
  (e : ∀ (X : C), P₁.obj (op X) ≃ P₂.obj (op X))
  (he : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₁.obj (op Y)),
    e X (P₁.map f.op x) = P₂.map f.op (e Y x))

include he in
lemma isSheafFor_of_nat_equiv {X : C} {R : Presieve X} (hP₁ : IsSheafFor P₁ R) :
    IsSheafFor P₂ R := fun x₂ hx₂ ↦ by
  have he' : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₂.obj (op Y)),
    (e X).symm (P₂.map f.op x) = P₁.map f.op ((e Y).symm x) := fun X Y f x ↦
      (e _).injective (by simp only [Equiv.apply_symm_apply, he])
  let x₁ : FamilyOfElements P₁ R := fun Y f hf ↦ (e _).symm (x₂ f hf)
  have hx₁ : x₁.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac ↦ (e _).injective
    (by simp only [he, Equiv.apply_symm_apply, hx₂ g₁ g₂ h₁ h₂ fac, x₁])
  have : ∀ (t₂ : P₂.obj (op X)),
      x₂.IsAmalgamation t₂ ↔ x₁.IsAmalgamation ((e _).symm t₂) := fun t₂ ↦ by
    simp only [FamilyOfElements.IsAmalgamation, x₁,
      ← he', EmbeddingLike.apply_eq_iff_eq]
  refine ⟨e _ (hP₁.amalgamate x₁ hx₁), ?_, ?_⟩
  · dsimp
    simp only [this, Equiv.symm_apply_apply]
    exact IsSheafFor.isAmalgamation hP₁ hx₁
  · intro t₂ ht₂
    apply (e _).symm.injective
    simp only [Equiv.symm_apply_apply]
    exact hP₁.isSeparatedFor x₁ _ _ (by simpa only [this] using ht₂)
      (IsSheafFor.isAmalgamation hP₁ hx₁)

include he in
lemma isSheaf_of_nat_equiv (hP₁ : Presieve.IsSheaf J P₁) :
    Presieve.IsSheaf J P₂ := fun _ R hR ↦
  isSheafFor_of_nat_equiv e he (hP₁ R hR)

include he in
lemma isSheaf_iff_of_nat_equiv :
    Presieve.IsSheaf J P₁ ↔ Presieve.IsSheaf J P₂ :=
  ⟨fun hP₁ ↦ isSheaf_of_nat_equiv e he hP₁,
    fun hP₂ ↦ isSheaf_of_nat_equiv (fun X ↦ (e X).symm) (fun X Y f x ↦ by
      obtain ⟨y, rfl⟩ := (e _).surjective x
      apply (e _).injective
      simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, he]) hP₂⟩

end Presieve

namespace Presheaf

variable [MonoidalClosed A]

/-- Relation between `functorEnrichedHom` and `presheafHom`. -/
noncomputable def functorEnrichedHomCoyonedaObjEquiv (M : A) (F G : Cᵒᵖ ⥤ A)
    [HasFunctorEnrichedHom A F G] (X : C) :
    (functorEnrichedHom A F G ⋙ coyoneda.obj (op M)).obj (op X) ≃
    (presheafHom (F ⊗ (Functor.const _).obj M) G).obj (op X) where
  toFun f :=
    { app := fun j ↦
        MonoidalClosed.uncurry (f ≫ enrichedHomπ A _ _ (Under.mk j.unop.hom.op))
      naturality := sorry }
  invFun g := end_.lift (fun j ↦ MonoidalClosed.curry (g.app (op (Over.mk j.hom.unop)))) (by
    sorry)
  left_inv f := by
    dsimp
    ext j
    dsimp
    simp only [curry_uncurry, end_.lift_π]
    rfl
  right_inv g := by
    dsimp
    ext j
    dsimp
    simp only [uncurry_curry, end_.lift_π]
    rfl

lemma functorEnrichedHomCoyonedaObjEquiv_naturality
    {M : A} {F G : Cᵒᵖ ⥤ A} {X Y : C} (f : X ⟶ Y)
    [HasFunctorEnrichedHom A F G]
    (y : (functorEnrichedHom A F G ⋙ coyoneda.obj (op M)).obj (op Y)) :
  functorEnrichedHomCoyonedaObjEquiv M F G X
    (y ≫ precompEnrichedHom _ _ _ (Under.map f.op)) =
  (presheafHom (F ⊗ (Functor.const Cᵒᵖ).obj M) G).map f.op
    (functorEnrichedHomCoyonedaObjEquiv M F G Y y) := sorry

lemma isSheaf_functorEnrichedHom (F G : Cᵒᵖ ⥤ A) (hG : Presheaf.IsSheaf J G)
    [HasFunctorEnrichedHom A F G] :
    Presheaf.IsSheaf J (functorEnrichedHom A F G) := fun M ↦ by
  rw [Presieve.isSheaf_iff_of_nat_equiv
    (functorEnrichedHomCoyonedaObjEquiv M F G)
    (fun _ _ _ _ ↦ functorEnrichedHomCoyonedaObjEquiv_naturality _ _)]
  rw [← isSheaf_iff_isSheaf_of_type]
  exact Presheaf.IsSheaf.hom (F ⊗ (Functor.const _).obj M) G hG

end Presheaf

namespace GrothendieckTopology

variable [MonoidalClosed A]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂]

namespace W

lemma whiskerLeft {G₁ G₂ : Cᵒᵖ ⥤ A} {g : G₁ ⟶ G₂} (hg : J.W g) (F : Cᵒᵖ ⥤ A) :
    J.W (F ◁ g) := fun H h ↦ by
  have := hg _ (Presheaf.isSheaf_functorEnrichedHom F H h)
  rw [← Function.Bijective.of_comp_iff' (f := MonoidalClosed.curry)
    ((ihom.adjunction _).homEquiv _ _).bijective]
  rw [← Function.Bijective.of_comp_iff (g := MonoidalClosed.curry) _
    ((ihom.adjunction _).homEquiv _ _).bijective] at this
  convert this using 1
  ext α : 1
  dsimp
  rw [curry_natural_left]

lemma whiskerRight [BraidedCategory A]
    {F₁ F₂ : Cᵒᵖ ⥤ A} {f : F₁ ⟶ F₂} (hf : J.W f) (G : Cᵒᵖ ⥤ A) :
    J.W (f ▷ G) :=
  (J.W.arrow_mk_iso_iff (Arrow.isoMk (β_ F₁ G) (β_ F₂ G))).2 (hf.whiskerLeft G)

end W

end GrothendieckTopology

end CategoryTheory
