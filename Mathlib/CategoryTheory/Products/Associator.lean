/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.DiscreteCategory

#align_import category_theory.products.associator from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
The associator functor `((C × D) × E) ⥤ (C × (D × E))` and its inverse form an equivalence.
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

namespace CategoryTheory.prod

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] (E : Type u₃)
  [Category.{v₃} E]

/-- The associator functor `(C × D) × E ⥤ C × (D × E)`.
-/
@[simps]
def associator : (C × D) × E ⥤ C × D × E where
  obj X := (X.1.1, (X.1.2, X.2))
  map := @fun _ _ f => (f.1.1, (f.1.2, f.2))
#align category_theory.prod.associator CategoryTheory.prod.associator

/-- The inverse associator functor `C × (D × E) ⥤ (C × D) × E `.
-/
@[simps]
def inverseAssociator : C × D × E ⥤ (C × D) × E where
  obj X := ((X.1, X.2.1), X.2.2)
  map := @fun _ _ f => ((f.1, f.2.1), f.2.2)
#align category_theory.prod.inverse_associator CategoryTheory.prod.inverseAssociator

/-- The equivalence of categories expressing associativity of products of categories.
-/
def associativity : (C × D) × E ≌ C × D × E :=
  Equivalence.mk (associator C D E) (inverseAssociator C D E)
    (NatIso.ofComponents fun X => eqToIso (by simp))
    (NatIso.ofComponents fun X => eqToIso (by simp))
#align category_theory.prod.associativity CategoryTheory.prod.associativity

instance associatorIsEquivalence : (associator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).functor.IsEquivalence)
#align category_theory.prod.associator_is_equivalence CategoryTheory.prod.associatorIsEquivalence

instance inverseAssociatorIsEquivalence : (inverseAssociator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).inverse.IsEquivalence)
#align category_theory.prod.inverse_associator_is_equivalence CategoryTheory.prod.inverseAssociatorIsEquivalence

/-- The left unitor functor `1 × C ⥤ C`
-/
@[simps]
def leftUnitor : Discrete PUnit × C ⥤ C where
  obj X := X.2
  map f := f.2
#align category_theory.prod.left_unitor CategoryTheory.prod.leftUnitor

/-- The right unitor functor `C × 1 ⥤ C`
-/
@[simps]
def rightUnitor : C × Discrete PUnit ⥤ C where
  obj X := X.1
  map f := f.1
#align category_theory.prod.right_unitor CategoryTheory.prod.rightUnitor

/-- The left inverse unitor `C ⥤ 1 × C`
-/
@[simps]
def leftInverseUnitor : C ⥤ Discrete PUnit × C where
  obj X := ⟨⟨PUnit.unit⟩, X⟩
  map f := ⟨𝟙 _, f⟩
#align category_theory.prod.left_inverse_unitor CategoryTheory.prod.leftInverseUnitor

/-- The right inverse unitor `C ⥤ C × 1`
-/
@[simps]
def rightInverseUnitor : C ⥤ C × Discrete PUnit where
  obj X := ⟨X, ⟨PUnit.unit⟩⟩
  map f := ⟨f, 𝟙 _⟩
#align category_theory.prod.right_inverse_unitor CategoryTheory.prod.rightInverseUnitor

/-- The equivalence of categories expressing left unity of products of categories.
-/
def leftUnitorEquivalence : Discrete PUnit × C ≌ C where
  functor := leftUnitor C
  inverse := leftInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _
#align category_theory.prod.left_unitor_equivalence CategoryTheory.prod.leftUnitorEquivalence

/-- The equivalence of categories expressing right unity of products of categories.
-/
def rightUnitorEquivalence : C × Discrete PUnit ≌ C where
  functor := rightUnitor C
  inverse := rightInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _
#align category_theory.prod.right_unitor_equivalence CategoryTheory.prod.rightUnitorEquivalence

instance leftUnitorIsEquivalence : (leftUnitor C).IsEquivalence :=
  (leftUnitorEquivalence C).isEquivalence_functor
#align category_theory.prod.left_unitor_is_equivalence CategoryTheory.prod.leftUnitorIsEquivalence

instance rightUnitorIsEquivalence : (rightUnitor C).IsEquivalence :=
  (rightUnitorEquivalence C).isEquivalence_functor
#align category_theory.prod.right_unitor_is_equivalence CategoryTheory.prod.rightUnitorIsEquivalence

-- TODO pentagon natural transformation? ...satisfying?
end CategoryTheory.prod
