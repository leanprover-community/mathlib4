/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The IPC property

Given a family of categories `I i` (`i : α`) and a family of functors `F i : I i ⥤ C`, we construct
the natural morphism `colim_k (∏ᶜ s ↦ (F s).obj (k s)) ⟶ ∏ᶜ s ↦ colim_k (F s).obj (k s)`.

Similarly to the study of finite limits commuting with filtered colimits, we then study sufficient
conditions for this morphism to be an isomorphism.

Our final goal is that for a small category `D` the presheaf category `Dᵒᵖ ⥤ Type v` satisfies the
IPC property, which is used in the calculation of products in the category of Ind-objects.
-/

universe w v v₁ u u₁

namespace CategoryTheory.Limits

section

variable {C : Type u} [Category.{v} C] {α : Type w} {I : α → Type u₁} [∀ i, Category.{v₁} (I i)]
  [HasLimitsOfShape (Discrete α) C] (F : ∀ i, I i ⥤ C) [∀ i, HasColimitsOfShape (I i) C]
  [HasColimitsOfShape (∀ i, I i) C]

/-- Given a family of functors `I i ⥤ C` for `i : α`, we obtain a functor `(∀ i, I i) ⥤ C` which
maps `k : ∀ i, I i` to `∏ᶜ (fun s : α) => (F s).obj (k s)`. -/
@[simps!]
noncomputable def pointwiseProduct : (∀ i, I i) ⥤ C :=
  Functor.pi F ⋙ (piEquivalenceFunctorDiscrete _ _).functor ⋙ lim

/-- The inclusions `(F s).obj (k s) ⟶ colimit (F s)` induce a cocone on `pointwiseProduct F` with
cone point `∏ᶜ (fun s : α) => colimit (F s)`. -/
@[simps]
noncomputable def coconePointwiseProduct : Cocone (pointwiseProduct F) where
  pt := ∏ᶜ fun (s : α) => colimit (F s)
  ι :=
    { app := fun k => Pi.map fun s => colimit.ι _ _
      naturality := fun k k' f => Pi.hom_ext _ _ (fun s => by simp) }

/-- The natural morphism `colim_k (∏ᶜ s ↦ (F s).obj (k s)) ⟶ ∏ᶜ s ↦ colim_k (F s).obj (k s)`.
We will say that a category has the `IPC` property if this morphism is an isomorphism as long
as the indexing categories are filtered. -/
noncomputable def colimitPointwiseProductToProductColimit :
    colimit (pointwiseProduct F) ⟶ ∏ᶜ fun (s : α) => colimit (F s) :=
  colimit.desc (pointwiseProduct F) (coconePointwiseProduct F)

@[reassoc (attr := simp)]
theorem ι_colimitPointwiseProductToProductColimit_π (k : ∀ i, I i) (s : α) :
    colimit.ι (pointwiseProduct F) k ≫ colimitPointwiseProductToProductColimit F ≫ Pi.π _ s =
      Pi.π _ s ≫ colimit.ι (F s) (k s) := by
  simp [colimitPointwiseProductToProductColimit]

end

section FME157

variable {α : Type w} {I : α → Type u₁} [∀ i, Category.{v₁} (I i)]

instance [∀ i, IsFilteredOrEmpty (I i)] : IsFilteredOrEmpty (∀ i, I i) where
  cocone_objs k l := ⟨fun s => IsFiltered.max (k s) (l s),
    fun s => IsFiltered.leftToMax (k s) (l s), fun s => IsFiltered.rightToMax (k s) (l s), trivial⟩
  cocone_maps k l f g := ⟨fun s => IsFiltered.coeq (f s) (g s),
    fun s => IsFiltered.coeqHom (f s) (g s),
    funext fun s => by simp [IsFiltered.coeq_condition (f s) (g s)]⟩

attribute [local instance] IsFiltered.nonempty

instance [∀ i, IsFiltered (I i)] : IsFiltered (∀ i, I i) where

end FME157

section types

variable {α : Type u} {I : α → Type u} [∀ i, SmallCategory (I i)] [∀ i, IsFiltered (I i)]

theorem isIso_colimitPointwiseProductToProductColimit_types (F : ∀ i, I i ⥤ Type u) :
    IsIso (colimitPointwiseProductToProductColimit F) := sorry

end types

section final

theorem isIso_colimitPointwiseProductToProductColimit {C : Type v} [SmallCategory C]
    {α : Type v} {I : α → Type v} [∀ i, Category.{v} (I i)]
    [∀ i, IsFiltered (I i)] (F : ∀ i, I i ⥤ Cᵒᵖ ⥤ Type v) :
  IsIso (colimitPointwiseProductToProductColimit F) := sorry


end final

end CategoryTheory.Limits
