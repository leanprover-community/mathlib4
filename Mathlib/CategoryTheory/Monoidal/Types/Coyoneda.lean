/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

#align_import category_theory.monoidal.types.coyoneda from "leanprover-community/mathlib"@"95a87616d63b3cb49d3fe678d416fbe9c4217bf4"

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

-- Porting note: made it noncomputable.
-- `failed to compile definition, consider marking it as 'noncomputable' because it`
-- `depends on 'CategoryTheory.typesMonoidal', and it does not have executable code`
-- I don't know if that is a problem, might need to change it back in the future, but
-- if so it might be better to fix then instead of at the moment of porting.

/-- `(𝟙_ C ⟶ -)` is a lax monoidal functor to `Type`. -/
noncomputable
def coyonedaTensorUnit (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    LaxMonoidalFunctor C (Type v) :=
  { coyoneda.obj (op (𝟙_ C)) with
    ε := fun _p => 𝟙 _
    μ := fun X Y p => (λ_ (𝟙_ C)).inv ≫ (p.1 ⊗ p.2)
    μ_natural := by aesop_cat
                    -- 🎉 no goals
    associativity := fun X Y Z => by
      ext ⟨⟨f, g⟩, h⟩; dsimp at f g h
      -- ⊢ (((fun X Y p => (λ_ (𝟙_ C)).inv ≫ (p.fst ⊗ p.snd)) X Y ⊗ 𝟙 ((Functor.mk src✝ …
                       -- ⊢ (((fun X Y p => (λ_ (𝟙_ C)).inv ≫ (p.fst ⊗ p.snd)) X Y ⊗ 𝟙 ((Functor.mk src✝ …
      dsimp; simp only [Iso.cancel_iso_inv_left, Category.assoc]
      -- ⊢ ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ≫ (f ⊗ g) ⊗ h)) ≫ (α_ X Y Z).hom = (λ_ ( …
             -- ⊢ ((λ_ (𝟙_ C)).inv ≫ (f ⊗ g) ⊗ h) ≫ (α_ X Y Z).hom = f ⊗ (λ_ (𝟙_ C)).inv ≫ (g  …
      conv_lhs =>
        rw [← Category.id_comp h, tensor_comp, Category.assoc, associator_naturality, ←
          Category.assoc, unitors_inv_equal, triangle_assoc_comp_right_inv]
      conv_rhs => rw [← Category.id_comp f, tensor_comp]
      -- 🎉 no goals
    left_unitality := by aesop_cat
                         -- 🎉 no goals
    right_unitality := fun X => by
      ext ⟨f, ⟨⟩⟩; dsimp at f
      -- ⊢ (ρ_ ((Functor.mk src✝.toPrefunctor).obj X)).hom (f, PUnit.unit) = ((𝟙 ((Func …
                   -- ⊢ (ρ_ ((Functor.mk src✝.toPrefunctor).obj X)).hom (f, PUnit.unit) = ((𝟙 ((Func …
      dsimp; simp only [Category.assoc]
      -- ⊢ f = ((λ_ (𝟙_ C)).inv ≫ (f ⊗ 𝟙 (𝟙_ C))) ≫ (ρ_ X).hom
             -- ⊢ f = (λ_ (𝟙_ C)).inv ≫ (f ⊗ 𝟙 (𝟙_ C)) ≫ (ρ_ X).hom
      rw [rightUnitor_naturality, unitors_inv_equal, Iso.inv_hom_id_assoc] }
      -- 🎉 no goals
#align category_theory.coyoneda_tensor_unit CategoryTheory.coyonedaTensorUnit

end CategoryTheory
