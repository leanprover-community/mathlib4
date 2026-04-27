/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# `(𝟙_ C ⟶ -)` is a lax monoidal functor to `Type`
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Opposite MonoidalCategory

attribute [local simp] types_tensorObj_def types_tensorUnit_def in
instance (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    (coyoneda.obj (op (𝟙_ C))).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (ε := TypeCat.ofHom (fun _ ↦ 𝟙 _))
    (μ := fun X Y ↦ TypeCat.ofHom (fun p ↦ (λ_ (𝟙_ C)).inv ≫ (p.1 ⊗ₘ p.2)))
    (μ_natural := by cat_disch)
    (associativity := fun X Y Z => by
      ext ⟨⟨f, g⟩, h⟩; dsimp at f g h
      dsimp; simp only [Category.assoc, Iso.cancel_iso_inv_left]
      conv_lhs =>
        rw [← Category.id_comp h, ← tensorHom_comp_tensorHom, Category.assoc, associator_naturality,
          ← Category.assoc, unitors_inv_equal, tensorHom_id, triangle_assoc_comp_right_inv]
      conv_rhs => rw [← Category.id_comp f, ← tensorHom_comp_tensorHom]
      simp)
    (right_unitality := fun X => by
      ext ⟨f, ⟨⟩⟩
      simp [unitors_inv_equal])

end CategoryTheory
