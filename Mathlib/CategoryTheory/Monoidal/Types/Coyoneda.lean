/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.types.coyoneda
! leanprover-community/mathlib commit 95a87616d63b3cb49d3fe678d416fbe9c4217bf4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Types.Basic
import Mathbin.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# `(𝟙_ C ⟶ -)` is a lax monoidal functor to `Type`
-/


open CategoryTheory

open CategoryTheory.Limits

open Tactic

universe v u

namespace CategoryTheory

open Opposite

open MonoidalCategory

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- `(𝟙_ C ⟶ -)` is a lax monoidal functor to `Type`. -/
def coyonedaTensorUnit (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    LaxMonoidalFunctor C (Type v) :=
  { coyoneda.obj (op (𝟙_ C)) with
    ε := fun p => 𝟙 _
    μ := fun X Y p => (λ_ (𝟙_ C)).inv ≫ (p.1 ⊗ p.2)
    μ_natural' := by tidy
    associativity' := fun X Y Z => by
      ext ⟨⟨f, g⟩, h⟩; dsimp at f g h 
      dsimp; simp only [iso.cancel_iso_inv_left, category.assoc]
      conv_lhs =>
        rw [← category.id_comp h, tensor_comp, category.assoc, associator_naturality, ←
          category.assoc, unitors_inv_equal, triangle_assoc_comp_right_inv]
      conv_rhs => rw [← category.id_comp f, tensor_comp]
    left_unitality' := by tidy
    right_unitality' := fun X => by
      ext ⟨f, ⟨⟩⟩; dsimp at f 
      dsimp; simp only [category.assoc]
      rw [right_unitor_naturality, unitors_inv_equal, iso.inv_hom_id_assoc] }
#align category_theory.coyoneda_tensor_unit CategoryTheory.coyonedaTensorUnit

end CategoryTheory

