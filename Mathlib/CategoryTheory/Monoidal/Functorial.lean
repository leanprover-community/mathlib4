/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Functor.Functorial

#align_import category_theory.monoidal.functorial from "leanprover-community/mathlib"@"73dd4b5411ec8fafb18a9d77c9c826907730af80"

/-!
# Unbundled lax monoidal functors

## Design considerations
The essential problem I've encountered that requires unbundled functors is
having an existing (non-monoidal) functor `F : C ⥤ D` between monoidal categories,
and wanting to assert that it has an extension to a lax monoidal functor.

The two options seem to be
1. Construct a separate `F' : LaxMonoidalFunctor C D`,
   and assert `F'.toFunctor ≅ F`.
2. Introduce unbundled functors and unbundled lax monoidal functors,
   and construct `LaxMonoidal F.obj`, then construct `F' := LaxMonoidalFunctor.of F.obj`.

Both have costs, but as for option 2. the cost is in library design,
while in option 1. the cost is users having to carry around additional isomorphisms forever,
I wanted to introduce unbundled functors.

TODO:
later, we may want to do this for strong monoidal functors as well,
but the immediate application, for enriched categories, only requires this notion.
-/


open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory.{v₂} D]

-- Perhaps in the future we'll redefine `LaxMonoidalFunctor` in terms of this,
-- but that isn't the immediate plan.
/-- An unbundled description of lax monoidal functors. -/
class LaxMonoidal (F : C → D) [Functorial.{v₁, v₂} F] where
  /-- unit morphism -/
  ε : 𝟙_ D ⟶ F (𝟙_ C)
  /-- tensorator -/
  μ : ∀ X Y : C, F X ⊗ F Y ⟶ F (X ⊗ Y)
  μ_natural_left :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      map F f ▷ F X' ≫ μ Y X' = μ X X' ≫ map F (f ▷ X') := by
    aesop_cat
  μ_natural_right :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y) ,
      F X' ◁ map F f ≫ μ X' Y = μ X' X ≫ map F (X' ◁ f) := by
    aesop_cat
  /-- associativity of the tensorator -/
  associativity :
    ∀ X Y Z : C,
      μ X Y ▷ F Z ≫ μ (X ⊗ Y) Z ≫ map F (α_ X Y Z).hom =
        (α_ (F X) (F Y) (F Z)).hom ≫ F X ◁ μ Y Z ≫ μ X (Y ⊗ Z) := by
    aesop_cat
  /-- left unitality -/
  left_unitality : ∀ X : C, (λ_ (F X)).hom = ε ▷ F X ≫ μ (𝟙_ C) X ≫ map F (λ_ X).hom := by
    aesop_cat
  /-- right unitality -/
  right_unitality : ∀ X : C, (ρ_ (F X)).hom = F X ◁ ε ≫ μ X (𝟙_ C) ≫ map F (ρ_ X).hom := by
    aesop_cat
#align category_theory.lax_monoidal CategoryTheory.LaxMonoidal

/-- An unbundled description of lax monoidal functors. -/
abbrev LaxMonoidal.ofTensorHom (F : C → D) [Functorial.{v₁, v₂} F]
    /- unit morphism -/
    (ε : 𝟙_ D ⟶ F (𝟙_ C))
    /- tensorator -/
    (μ : ∀ X Y : C, F X ⊗ F Y ⟶ F (X ⊗ Y))
    /- naturality -/
    (μ_natural :
      ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
        (map F f ⊗ map F g) ≫ μ Y Y' = μ X X' ≫ map F (f ⊗ g) := by
    aesop_cat)
    /- associativity of the tensorator -/
    (associativity :
      ∀ X Y Z : C,
        (μ X Y ⊗ 𝟙 (F Z)) ≫ μ (X ⊗ Y) Z ≫ map F (α_ X Y Z).hom =
          (α_ (F X) (F Y) (F Z)).hom ≫ (𝟙 (F X) ⊗ μ Y Z) ≫ μ X (Y ⊗ Z) := by
      aesop_cat)
    /- left unitality -/
    (left_unitality : ∀ X : C, (λ_ (F X)).hom = (ε ⊗ 𝟙 (F X)) ≫ μ (𝟙_ C) X ≫ map F (λ_ X).hom := by
      aesop_cat)
    /- right unitality -/
    (right_unitality : ∀ X : C, (ρ_ (F X)).hom = (𝟙 (F X) ⊗ ε) ≫ μ X (𝟙_ C) ≫ map F (ρ_ X).hom := by
      aesop_cat) :
      LaxMonoidal.{v₁, v₂} F where
  ε := ε
  μ := μ
  μ_natural_left f X := by simpa using μ_natural f (𝟙 X)
  μ_natural_right X f := by simpa using μ_natural (𝟙 X) f
  associativity X Y Z := by simpa using associativity X Y Z
  left_unitality X := by simpa using left_unitality X
  right_unitality X := by simpa using right_unitality X

attribute [simp, nolint simpNF] LaxMonoidal.μ_natural_left LaxMonoidal.μ_natural_right

-- The unitality axioms cannot be used as simp lemmas because they require
-- higher-order matching to figure out the `F` and `X` from `F X`.

attribute [simp] LaxMonoidal.associativity

namespace LaxMonoidalFunctor

/-- Construct a bundled `LaxMonoidalFunctor` from the object level function
and `Functorial` and `LaxMonoidal` typeclasses.
-/
@[simps]
def of (F : C → D) [I₁ : Functorial.{v₁, v₂} F] [I₂ : LaxMonoidal.{v₁, v₂} F] :
    LaxMonoidalFunctor.{v₁, v₂} C D :=
  { I₁, I₂ with obj := F }
#align category_theory.lax_monoidal_functor.of CategoryTheory.LaxMonoidalFunctor.of

end LaxMonoidalFunctor

instance (F : LaxMonoidalFunctor.{v₁, v₂} C D) : LaxMonoidal.{v₁, v₂} F.obj :=
  { F with }

section

instance laxMonoidalId : LaxMonoidal.{v₁, v₁} (id : C → C) where
  ε := 𝟙 _
  μ X Y := 𝟙 _
#align category_theory.lax_monoidal_id CategoryTheory.laxMonoidalId

end

-- TODO instances for composition, as required
-- TODO `StrongMonoidal`, as well as `LaxMonoidal`
end CategoryTheory
