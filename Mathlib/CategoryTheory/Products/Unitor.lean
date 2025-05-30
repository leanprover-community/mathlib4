/-
Copyright (c) 2024 Shanghe Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanghe Chen
-/
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The left/right unitor equivalences `1 × C ≌ C` and `C × 1 ≌ C`.
-/

universe w v u

open CategoryTheory

namespace CategoryTheory.prod

variable (C : Type u) [Category.{v} C]

/-- The left unitor functor `1 × C ⥤ C` -/
@[simps]
def leftUnitor : Discrete (PUnit : Type w) × C ⥤ C where
  obj X := X.2
  map f := f.2

/-- The right unitor functor `C × 1 ⥤ C` -/
@[simps]
def rightUnitor : C × Discrete (PUnit : Type w) ⥤ C where
  obj X := X.1
  map f := f.1

/-- The left inverse unitor `C ⥤ 1 × C` -/
@[simps]
def leftInverseUnitor : C ⥤ Discrete (PUnit : Type w) × C where
  obj X := ⟨⟨PUnit.unit⟩, X⟩
  map f := ⟨𝟙 _, f⟩

/-- The right inverse unitor `C ⥤ C × 1` -/
@[simps]
def rightInverseUnitor : C ⥤ C × Discrete (PUnit : Type w) where
  obj X := ⟨X, ⟨PUnit.unit⟩⟩
  map f := ⟨f, 𝟙 _⟩

/-- The equivalence of categories expressing left unity of products of categories. -/
@[simps]
def leftUnitorEquivalence : Discrete (PUnit : Type w) × C ≌ C where
  functor := leftUnitor C
  inverse := leftInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The equivalence of categories expressing right unity of products of categories. -/
@[simps]
def rightUnitorEquivalence : C × Discrete (PUnit : Type w) ≌ C where
  functor := rightUnitor C
  inverse := rightInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance leftUnitor_isEquivalence : (leftUnitor C).IsEquivalence :=
  (leftUnitorEquivalence C).isEquivalence_functor

instance rightUnitor_isEquivalence : (rightUnitor C).IsEquivalence :=
  (rightUnitorEquivalence C).isEquivalence_functor

end CategoryTheory.prod
