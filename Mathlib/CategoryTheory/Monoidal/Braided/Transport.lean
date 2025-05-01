/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence

/-!

# Transporting closed symmetric monoidal structures along equivalences
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Category Monoidal MonoidalCategory

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Monoidal

instance Transported.instBraidedCategory (e : C ≌ D) [MonoidalCategory.{v₁} C] [BraidedCategory C] :
    BraidedCategory (Transported e) :=
  braidedCategoryOfFullyFaithful (equivalenceTransported e).inverse

instance (e : C ≌ D) [MonoidalCategory.{v₁} C] [BraidedCategory C] :
    (equivalenceTransported e).inverse.Braided where
  braided X Y := by
    simp [Transported.instBraidedCategory, braidedCategoryOfFullyFaithful,
      braidedCategoryOfFaithful]

instance (e : C ≌ D) [MonoidalCategory.{v₁} C] [BraidedCategory C] :
    (equivalenceTransported e).functor.Braided where
  braided X Y := by
    sorry

instance (e : C ≌ D) [MonoidalCategory.{v₁} C] [SymmetricCategory C] :
    SymmetricCategory (Transported e) :=
  symmetricCategoryOfFullyFaithful (equivalenceTransported e).inverse

instance (e : C ≌ D) [MonoidalCategory.{v₁} C] [SymmetricCategory C] [MonoidalClosed C] :
    MonoidalClosed (Transported e) :=
  Reflective.monoidalClosed (equivalenceTransported e).toAdjunction

end CategoryTheory.Monoidal
