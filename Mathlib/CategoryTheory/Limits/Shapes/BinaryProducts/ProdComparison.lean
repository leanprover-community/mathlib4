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

@[expose] public section

universe v v₁ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

open WalkingPair

variable {C : Type u} [Category.{v} C]

variable {X Y : C}

variable (C)

noncomputable section ProdComparison

universe w w' u₃

variable {C} {D : Type u₂} [Category.{w} D] {E : Type u₃} [Category.{w'} E]
variable (F : C ⥤ D) (G : D ⥤ E) {A A' B B' : C}
variable [HasBinaryProduct A B] [HasBinaryProduct A' B']
variable [HasBinaryProduct (F.obj A) (F.obj B)]
variable [HasBinaryProduct (F.obj A') (F.obj B')]
variable [HasBinaryProduct (G.obj (F.obj A)) (G.obj (F.obj B))]
variable [HasBinaryProduct ((F ⋙ G).obj A) ((F ⋙ G).obj B)]

/-- The product comparison morphism.

In `CategoryTheory/Limits/Preserves` we show this is always an iso iff F preserves binary products.
-/
def prodComparison (F : C ⥤ D) (A B : C) [HasBinaryProduct A B]
    [HasBinaryProduct (F.obj A) (F.obj B)] : F.obj (A ⨯ B) ⟶ F.obj A ⨯ F.obj B :=
  prod.lift (F.map prod.fst) (F.map prod.snd)

variable (A B)

@[reassoc (attr := simp)]
theorem prodComparison_fst : prodComparison F A B ≫ prod.fst = F.map prod.fst :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
theorem prodComparison_snd : prodComparison F A B ≫ prod.snd = F.map prod.snd :=
  prod.lift_snd _ _

variable {A B}

/-- Naturality of the `prodComparison` morphism in both arguments. -/
@[reassoc]
theorem prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    F.map (prod.map f g) ≫ prodComparison F A' B' =
      prodComparison F A B ≫ prod.map (F.map f) (F.map g) := by
  rw [prodComparison, prodComparison, prod.lift_map, ← F.map_comp, ← F.map_comp, prod.comp_lift, ←
    F.map_comp, prod.map_fst, ← F.map_comp, prod.map_snd]

variable {F}

/-- Naturality of the `prodComparison` morphism in a natural transformation. -/
@[reassoc]
theorem prodComparison_natural_of_natTrans {H : C ⥤ D} [HasBinaryProduct (H.obj A) (H.obj B)]
    (α : F ⟶ H) :
    α.app (prod A B) ≫ prodComparison H A B =
      prodComparison F A B ≫ prod.map (α.app A) (α.app B) := by
  rw [prodComparison, prodComparison, prod.lift_map, prod.comp_lift, α.naturality, α.naturality]

variable (F)

set_option backward.defeqAttrib.useBackward true in
/-- The product comparison morphism from `F(A ⨯ -)` to `FA ⨯ F-`, whose components are given by
`prodComparison`.
-/
@[simps]
def prodComparisonNatTrans [HasBinaryProducts C] [HasBinaryProducts D] (F : C ⥤ D) (A : C) :
    prod.functor.obj A ⋙ F ⟶ F ⋙ prod.functor.obj (F.obj A) where
  app B := prodComparison F A B
  naturality f := by simp [prodComparison_natural]

@[reassoc]
theorem inv_prodComparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.fst = prod.fst := by simp [IsIso.inv_comp_eq]

@[reassoc]
theorem inv_prodComparison_map_snd [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.snd = prod.snd := by simp [IsIso.inv_comp_eq]

/-- If the product comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
theorem prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A B)]
    [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ≫ F.map (prod.map f g) =
      prod.map (F.map f) (F.map g) ≫ inv (prodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural]

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `F(A ⨯ -) ≅ FA ⨯ F-`, provided each `prodComparison F A B` is an
isomorphism (as `B` changes).
-/
@[simps]
def prodComparisonNatIso [HasBinaryProducts C] [HasBinaryProducts D] (A : C)
    [∀ B, IsIso (prodComparison F A B)] :
    prod.functor.obj A ⋙ F ≅ F ⋙ prod.functor.obj (F.obj A) := by
  refine { @asIso _ _ _ _ _ (?_) with hom := prodComparisonNatTrans F A }
  apply NatIso.isIso_of_isIso_app

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

end ProdComparison

noncomputable section CoprodComparison

universe w

variable {C} {D : Type u₂} [Category.{w} D]
variable (F : C ⥤ D) {A A' B B' : C}
variable [HasBinaryCoproduct A B] [HasBinaryCoproduct A' B']
variable [HasBinaryCoproduct (F.obj A) (F.obj B)] [HasBinaryCoproduct (F.obj A') (F.obj B')]

/-- The coproduct comparison morphism.

In `Mathlib/CategoryTheory/Limits/Preserves/` we show
this is always an iso iff F preserves binary coproducts.
-/
def coprodComparison (F : C ⥤ D) (A B : C) [HasBinaryCoproduct A B]
    [HasBinaryCoproduct (F.obj A) (F.obj B)] : F.obj A ⨿ F.obj B ⟶ F.obj (A ⨿ B) :=
  coprod.desc (F.map coprod.inl) (F.map coprod.inr)

@[reassoc (attr := simp)]
theorem coprodComparison_inl : coprod.inl ≫ coprodComparison F A B = F.map coprod.inl :=
  coprod.inl_desc _ _

@[reassoc (attr := simp)]
theorem coprodComparison_inr : coprod.inr ≫ coprodComparison F A B = F.map coprod.inr :=
  coprod.inr_desc _ _

/-- Naturality of the `coprodComparison` morphism in both arguments. -/
@[reassoc]
theorem coprodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    coprodComparison F A B ≫ F.map (coprod.map f g) =
      coprod.map (F.map f) (F.map g) ≫ coprodComparison F A' B' := by
  rw [coprodComparison, coprodComparison, coprod.map_desc, ← F.map_comp, ← F.map_comp,
    coprod.desc_comp, ← F.map_comp, coprod.inl_map, ← F.map_comp, coprod.inr_map]

set_option backward.defeqAttrib.useBackward true in
/-- The coproduct comparison morphism from `FA ⨿ F-` to `F(A ⨿ -)`, whose components are given by
`coprodComparison`.
-/
@[simps]
def coprodComparisonNatTrans [HasBinaryCoproducts C] [HasBinaryCoproducts D] (F : C ⥤ D) (A : C) :
    F ⋙ coprod.functor.obj (F.obj A) ⟶ coprod.functor.obj A ⋙ F where
  app B := coprodComparison F A B
  naturality f := by simp [coprodComparison_natural]

@[reassoc]
theorem map_inl_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inl ≫ inv (coprodComparison F A B) = coprod.inl := by simp

@[reassoc]
theorem map_inr_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inr ≫ inv (coprodComparison F A B) = coprod.inr := by simp

/-- If the coproduct comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
theorem coprodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (coprodComparison F A B)]
    [IsIso (coprodComparison F A' B')] :
    inv (coprodComparison F A B) ≫ coprod.map (F.map f) (F.map g) =
      F.map (coprod.map f g) ≫ inv (coprodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, coprodComparison_natural]

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `FA ⨿ F- ≅ F(A ⨿ -)`, provided each `coprodComparison F A B` is an
isomorphism (as `B` changes).
-/
@[simps]
def coprodComparisonNatIso [HasBinaryCoproducts C] [HasBinaryCoproducts D] (A : C)
    [∀ B, IsIso (coprodComparison F A B)] :
    F ⋙ coprod.functor.obj (F.obj A) ≅ coprod.functor.obj A ⋙ F :=
  { @asIso _ _ _ _ _ (NatIso.isIso_of_isIso_app ..) with hom := coprodComparisonNatTrans F A }

end CoprodComparison

end CategoryTheory.Limits

end
