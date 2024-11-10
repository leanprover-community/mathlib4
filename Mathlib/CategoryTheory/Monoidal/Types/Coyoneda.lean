/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

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

/-- `(𝟙_ C ⟶ -)` is a lax monoidal functor to `Type`. -/
def coyonedaTensorUnit (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    LaxMonoidalFunctor C (Type v) := .ofTensorHom
    (F := coyoneda.obj (op (𝟙_ C)))
    (ε := fun _p => 𝟙 _)
    (μ := fun _ _ p => (λ_ (𝟙_ C)).inv ≫ (p.1 ⊗ p.2))
    (μ_natural := by aesop_cat)
    (associativity := fun X Y Z => by
      ext ⟨⟨f, g⟩, h⟩; dsimp at f g h
      dsimp; simp only [Iso.cancel_iso_inv_left, Category.assoc]
      conv_lhs =>
        rw [← Category.id_comp h, tensor_comp, Category.assoc, associator_naturality, ←
          Category.assoc, unitors_inv_equal, tensorHom_id, triangle_assoc_comp_right_inv]
      conv_rhs => rw [← Category.id_comp f, tensor_comp]
      simp)
    (left_unitality := by
      intros
      ext ⟨⟨⟩, f⟩; dsimp at f
      dsimp
      simp)
    (right_unitality := fun X => by
      ext ⟨f, ⟨⟩⟩; dsimp at f
      dsimp
      simp [unitors_inv_equal])

end CategoryTheory
