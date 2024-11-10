/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Filtered

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

variable {C : Type u} [Category.{v} C] {α : Type w} {I : α → Type u₁} [∀ i, Category (I i)]
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

end CategoryTheory.Limits
