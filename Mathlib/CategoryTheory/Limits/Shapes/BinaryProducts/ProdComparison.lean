/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# Product comparison morphisms

Naturality of the product and coproduct constructions with respect to functors.

## References
* [Stacks: Products of pairs](https://stacks.math.columbia.edu/tag/001R)
* [Stacks: coproducts of pairs](https://stacks.math.columbia.edu/tag/04AN)
-/

@[expose] public noncomputable section

universe v v₂ v₃ u u₂ u₃ w w'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E) {A A' B B' : C}
variable [HasBinaryProduct A B] [HasBinaryProduct A' B']
variable [HasBinaryProduct (F.obj A) (F.obj B)]
variable [HasBinaryProduct (F.obj A') (F.obj B')]
variable [HasBinaryProduct (G.obj (F.obj A)) (G.obj (F.obj B))]
variable [HasBinaryProduct ((F ⋙ G).obj A) ((F ⋙ G).obj B)]

to_dual_name_hint Prod Coprod

/-- The product comparison morphism.

In `CategoryTheory/Limits/Preserves` we show this is always an iso iff
`F` preserves binary products. -/
@[to_dual
/-- The coproduct comparison morphism.

In `CategoryTheory/Limits/Preserves` we show this is always an iso iff
`F` preserves binary coproducts. -/]
def prodComparison (F : C ⥤ D) (A B : C) [HasBinaryProduct A B]
    [HasBinaryProduct (F.obj A) (F.obj B)] : F.obj (A ⨯ B) ⟶ F.obj A ⨯ F.obj B :=
  prod.lift (F.map prod.fst) (F.map prod.snd)

variable (A B)

@[to_dual (attr := reassoc (attr := simp)) inl_coprodComparison]
theorem prodComparison_fst : prodComparison F A B ≫ prod.fst = F.map prod.fst :=
  prod.lift_fst _ _

@[to_dual (attr := reassoc (attr := simp)) inr_coprodComparison]
theorem prodComparison_snd : prodComparison F A B ≫ prod.snd = F.map prod.snd :=
  prod.lift_snd _ _

@[deprecated (since := "2026-09-26")] alias coprodComparison_inl := inl_coprodComparison
@[deprecated (since := "2026-09-26")] alias coprodComparison_inr := inr_coprodComparison

variable {A B}

/-- Naturality of the `prodComparison` morphism in both arguments. -/
@[to_dual (attr := reassoc)
/-- Naturality of the `coprodComparison` morphism in both arguments. -/]
theorem prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    F.map (prod.map f g) ≫ prodComparison F A' B' =
      prodComparison F A B ≫ prod.map (F.map f) (F.map g) := by
  rw [prodComparison, prodComparison, prod.lift_map, ← F.map_comp, ← F.map_comp, prod.comp_lift, ←
    F.map_comp, prod.map_fst, ← F.map_comp, prod.map_snd]

variable {F}

/-- Naturality of the `prodComparison` morphism in a natural transformation. -/
@[to_dual (attr := reassoc)
/-- Naturality of the `coprodComparison` morphism in a natural transformation. -/]
theorem prodComparison_natural_of_natTrans {H : C ⥤ D} [HasBinaryProduct (H.obj A) (H.obj B)]
    (α : F ⟶ H) :
    α.app (prod A B) ≫ prodComparison H A B =
      prodComparison F A B ≫ prod.map (α.app A) (α.app B) := by
  rw [prodComparison, prodComparison, prod.lift_map, prod.comp_lift, α.naturality, α.naturality]

variable (F)

/-- The product comparison morphism from `F(A ⨯ -)` to `FA ⨯ F-`, whose components are given by
`prodComparison`.
-/
@[to_dual (attr := simps)
/-- The coproduct comparison morphism from `FA ⨿ F-` to `F(A ⨿ -)`, whose components are given by
`coprodComparison`.
-/]
def prodComparisonNatTrans [HasBinaryProducts C] [HasBinaryProducts D] (F : C ⥤ D) (A : C) :
    prod.functor.obj A ⋙ F ⟶ F ⋙ prod.functor.obj (F.obj A) where
  app B := prodComparison F A B
  naturality f := by simp [prodComparison_natural]

@[to_dual (attr := reassoc) map_inl_inv_coprodComparison]
theorem inv_prodComparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.fst = prod.fst := by simp [IsIso.inv_comp_eq]

@[to_dual (attr := reassoc) map_inr_inv_coprodComparison]
theorem inv_prodComparison_map_snd [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.snd = prod.snd := by simp [IsIso.inv_comp_eq]

/-- If the product comparison morphism is an iso, its inverse is natural. -/
@[to_dual (attr := reassoc)
/-- If the coproduct comparison morphism is an iso, its inverse is natural. -/]
theorem prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A B)]
    [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ≫ F.map (prod.map f g) =
      prod.map (F.map f) (F.map g) ≫ inv (prodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural]

/-- The natural isomorphism `F(A ⨯ -) ≅ FA ⨯ F-`, provided each `prodComparison F A B` is an
isomorphism (as `B` changes).
-/
@[to_dual (attr := simps!)
/-- The natural isomorphism `FA ⨿ F- ≅ F(A ⨿ -)`, provided each `coprodComparison F A B` is an
isomorphism (as `B` changes).
-/]
def prodComparisonNatIso [HasBinaryProducts C] [HasBinaryProducts D] (A : C)
    [∀ B, IsIso (prodComparison F A B)] :
    prod.functor.obj A ⋙ F ≅ F ⋙ prod.functor.obj (F.obj A) :=
  @asIso _ _ _ _ (delta% prodComparisonNatTrans F A) (NatIso.isIso_of_isIso_app _)

theorem prodComparison_comp :
    prodComparison (F ⋙ G) A B =
      G.map (prodComparison F A B) ≫ prodComparison G (F.obj A) (F.obj B) := by
  unfold prodComparison
  ext <;> simp [← G.map_comp]

@[reassoc]
lemma map_braiding_hom_comp_prodComparison
    [HasBinaryProduct B A] [HasBinaryProduct (F.obj B) (F.obj A)] :
    F.map (prod.braiding _ _).hom ≫ prodComparison F A B  =
    prodComparison F B A ≫ (prod.braiding _ _).hom := by
  ext <;> simp [← Functor.map_comp]

end CategoryTheory.Limits
