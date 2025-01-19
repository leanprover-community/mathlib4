/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts


/-!
# (Co)products in functor categories

Given functors `X Y : D ⥤ C` we prove the isomorphisms
`(X × Y).obj d ≅ X.obj d × Y.obj d` and `(X ⨿ Y).obj d ≅ X.obj d ⨿ Y.obj d`.
whenever `C` has binary products and coproducts, respectively.
-/

universe  v v₁ v₂ u u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {K : Type u₁} [Category.{v₁} K]

section Product

variable [HasBinaryProducts C]

/-- The evaluation of a binary product of functors at an object is isomorphic to
the product of the evaluations at that object. -/
noncomputable def prodObjIso (X Y : K ⥤ C) (k : K) : (X ⨯ Y).obj k ≅ (X.obj k) ⨯ (Y.obj k) :=
  limitObjIsoLimitCompEvaluation (pair X Y ) k ≪≫
    HasLimit.isoOfNatIso (mapPairIso (Iso.refl _) (Iso.refl _))

/-- The isomorphism `prodObjIso` commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem prodObjIso_hom_comp_prod_fst (X Y : K ⥤ C) (k : K) :
    (prodObjIso X Y k).hom ≫ prod.fst = (prod.fst (X:= X) (Y:= Y)).app k := by
  simp [prodObjIso]

/-- The isomorphism `prodObjIso` commutes with the second projections. -/
@[reassoc (attr := simp)]
theorem prodObjIso_hom_comp_prod_snd (X Y : K ⥤ C) (k : K) :
    (prodObjIso X Y k).hom ≫ prod.snd = (prod.snd (X:= X) (Y:= Y)).app k := by
  simp [prodObjIso]

/-- The inverse of the isomorphism `prodObjIso` commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem piObjIso_inv_comp_prod_fst (X Y : K ⥤ C) (k : K) :
    (prodObjIso X Y k).inv ≫ (prod.fst (X:= X) (Y:= Y)).app k = prod.fst := by
  simp [prodObjIso]

/-- The inverse of the isomorphism `prodObjIso` commutes with the second projections. -/
@[reassoc (attr := simp)]
theorem piObjIso_inv_comp_prod_snd (X Y : K ⥤ C) (k : K) :
    (prodObjIso X Y k).inv ≫ (prod.snd (X:= X) (Y:= Y)).app k = prod.snd := by
  simp [prodObjIso]

/-- The naturality of the isomorphism `(prodObjIso _ _ _).hom` -/
@[reassoc (attr := simp)]
theorem prodObjIso_hom_naturality (X Y : K ⥤ C) {k k' : K} (f : k ⟶ k') :
    (X ⨯ Y).map f ≫ (prodObjIso X Y k').hom =
      (prodObjIso X Y k).hom ≫ prod.map (X.map f) (Y.map f)  := by
  simp only [prodObjIso, limit_map_limitObjIsoLimitCompEvaluation_hom]
  aesop

/-- The naturality of the isomorphism `(prodObjIso _ _ _).inv` -/
@[reassoc (attr := simp)]
theorem prodObjIso_inv_naturality (X Y : K ⥤ C) {k k' : K} (f : k ⟶ k') :
    (prodObjIso X Y k).inv ≫ (X ⨯ Y).map f =
      prod.map (X.map f) (Y.map f) ≫ (prodObjIso X Y k').inv  := by
  simp only [prodObjIso, limitObjIsoLimitCompEvaluation_inv_limit_map]
  aesop

/-- Given a product cocone `α : Z ⟶ X` and `β : Z ⟶ Y`, the component of the gap map
`Z ⟶ X ⨯ Y` at an object `k` is the same as the gap map of the components of
`α.app k` and `β.app k`, up to the isomorphism `prodObjIso X Y k`.-/
@[reassoc (attr := simp)]
theorem prodObjIso_hom_gap (X Y Z : K ⥤ C) (α : Z ⟶ X) (β : Z ⟶ Y) (k : K) :
    (prod.lift α β).app k ≫ (prodObjIso X Y k).hom = prod.lift (α.app k) (β.app k) := by
  simp only [prodObjIso]
  aesop

end Product

section Coproduct

variable [HasBinaryCoproducts C]

/-- The evaluation of a binary coproduct of functors at an object is isomorphic to
the coproduct of the evaluations at that object. -/
noncomputable def coprodObjIso (X Y : K ⥤ C) (k : K) : (X ⨿ Y).obj k ≅ (X.obj k) ⨿ (Y.obj k) :=
  colimitObjIsoColimitCompEvaluation (pair X Y ) k ≪≫
    HasColimit.isoOfNatIso (mapPairIso (Iso.refl _) (Iso.refl _))

/-- The isomorphism `coprodObjIso` commutes with the first coprojection. -/
@[reassoc (attr := simp)]
theorem coprodObjIso_hom_comp_coprod_inl (X Y : K ⥤ C) (k : K) :
    (coprod.inl (X:= X) (Y:= Y)).app k ≫ (coprodObjIso X Y k).hom = coprod.inl := by
  simp [coprodObjIso]

/-- The isomorphism `coprodObjIso` commutes with the second coprojection. -/
@[reassoc (attr := simp)]
theorem coprodObjIso_hom_comp_coprod_inr (X Y : K ⥤ C) (k : K) :
    (coprod.inr (X:= X) (Y:= Y)).app k ≫ (coprodObjIso X Y k).hom = coprod.inr := by
  simp [coprodObjIso]

/-- The inverse of the isomorphism `coprodObjIso` commutes with the first coprojection. -/
@[reassoc (attr := simp)]
theorem coprodObjIso_inv_comp_coprod_inl (X Y : K ⥤ C) (k : K) :
    coprod.inl ≫ (coprodObjIso X Y k).inv = (coprod.inl (X:= X) (Y:= Y)).app k := by
  simp [coprodObjIso]

/-- The inverse of the isomorphism `coprodObjIso` commutes with the second coprojection. -/
@[reassoc (attr := simp)]
theorem coprodObjIso_inv_comp_coprod_inr (X Y : K ⥤ C) (k : K) :
    coprod.inr ≫ (coprodObjIso X Y k).inv = (coprod.inr (X:= X) (Y:= Y)).app k := by
  simp [coprodObjIso]

/-- The naturality of the isomorphism `(coprodObjIso _ _ _).hom` -/
@[reassoc (attr := simp)]
theorem coprodObjIso_hom_naturality (X Y : K ⥤ C) {k k' : K} (f : k ⟶ k') :
    (X ⨿ Y).map f ≫ (coprodObjIso X Y k').hom =
      (coprodObjIso X Y k).hom ≫ coprod.map (X.map f) (Y.map f)  := by
  simp only [coprodObjIso, colimit_map_colimitObjIsoColimitCompEvaluation_hom]
  aesop

/-- The naturality of the isomorphism `(coprodObjIso _ _ _).inv` -/
@[reassoc (attr := simp)]
theorem coprodObjIso_inv_naturality (X Y : K ⥤ C) {k k' : K} (f : k ⟶ k') :
    (coprodObjIso X Y k).inv ≫ (X ⨿ Y).map f =
      coprod.map (X.map f) (Y.map f) ≫ (coprodObjIso X Y k').inv  := by
  simp only [coprodObjIso, colimitObjIsoColimitCompEvaluation_inv_colimit_map]
  aesop

/-- Given a coproduct cocone `α : X ⟶ Z` and `β : Y ⟶ Z`, the component of the cogap map
`X ⨿ Y ⟶ Z` at an object `k` is the same as the cogap map of the components of
`α.app k` and `β.app k`, up to the isomorphism `coprodObjIso X Y k`.-/
theorem coprodObjIso_hom_cogap (X Y Z : K ⥤ C) (α : X ⟶ Z) (β : Y ⟶ Z) (k : K) :
    (coprodObjIso X Y k).hom ≫ coprod.desc (α.app k) (β.app k) = (coprod.desc α β).app k := by
  simp only [coprodObjIso]
  aesop

end Coproduct

end CategoryTheory.Limits
