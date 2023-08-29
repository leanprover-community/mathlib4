/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Types

#align_import category_theory.isomorphism_classes from "leanprover-community/mathlib"@"28aa996fc6fb4317f0083c4e6daf79878d81be33"

/-!
# Objects of a category up to an isomorphism

`IsIsomorphic X Y := Nonempty (X ≅ Y)` is an equivalence relation on the objects of a category.
The quotient with respect to this relation defines a functor from our category to `Type`.
-/


universe v u

namespace CategoryTheory

section Category

variable {C : Type u} [Category.{v} C]

/-- An object `X` is isomorphic to an object `Y`, if `X ≅ Y` is not empty. -/
def IsIsomorphic : C → C → Prop := fun X Y => Nonempty (X ≅ Y)
#align category_theory.is_isomorphic CategoryTheory.IsIsomorphic

variable (C)

/-- `IsIsomorphic` defines a setoid. -/
def isIsomorphicSetoid : Setoid C where
  r := IsIsomorphic
  iseqv := ⟨fun X => ⟨Iso.refl X⟩, fun ⟨α⟩ => ⟨α.symm⟩, fun ⟨α⟩ ⟨β⟩ => ⟨α.trans β⟩⟩
#align category_theory.is_isomorphic_setoid CategoryTheory.isIsomorphicSetoid

end Category

/-- The functor that sends each category to the quotient space of its objects up to an isomorphism.
-/
def isomorphismClasses : Cat.{v, u} ⥤ Type u where
  obj C := Quotient (isIsomorphicSetoid C.α)
  map {C D} F := Quot.map F.obj fun X Y ⟨f⟩ => ⟨F.mapIso f⟩
  map_id {C} := by  -- Porting note: this used to be `tidy`
    dsimp; apply funext; intro x
    -- ⊢ Quot.map (𝟙 C).obj (_ : ∀ (X Y : ↑C), Setoid.r X Y → Setoid.r ((𝟙 C).obj X)  …
           -- ⊢ ∀ (x : Quot Setoid.r), Quot.map (𝟙 C).obj (_ : ∀ (X Y : ↑C), Setoid.r X Y →  …
                         -- ⊢ Quot.map (𝟙 C).obj (_ : ∀ (X Y : ↑C), Setoid.r X Y → Setoid.r ((𝟙 C).obj X)  …
    apply x.recOn  -- Porting note: `induction x` not working yet
    -- ⊢ ∀ (a b : ↑C) (p : Setoid.r a b), (_ : Quot.map (𝟙 C).obj (_ : ∀ (X Y : ↑C),  …
    · intro _ _ p
      -- ⊢ (_ : Quot.map (𝟙 C).obj (_ : ∀ (X Y : ↑C), Setoid.r X Y → Setoid.r ((𝟙 C).ob …
      simp only [types_id_apply]
      -- 🎉 no goals
    · intro _
      -- ⊢ Quot.map (𝟙 C).obj (_ : ∀ (X Y : ↑C), Setoid.r X Y → Setoid.r ((𝟙 C).obj X)  …
      rfl
      -- 🎉 no goals
  map_comp {C D E} f g := by -- Porting note(s): idem
    dsimp; apply funext; intro x
    -- ⊢ Quot.map (f ≫ g).obj (_ : ∀ (X Y : ↑C), Setoid.r X Y → Setoid.r (g.obj (f.ob …
           -- ⊢ ∀ (x : Quot Setoid.r), Quot.map (f ≫ g).obj (_ : ∀ (X Y : ↑C), Setoid.r X Y  …
                         -- ⊢ Quot.map (f ≫ g).obj (_ : ∀ (X Y : ↑C), Setoid.r X Y → Setoid.r (g.obj (f.ob …
    apply x.recOn
    -- ⊢ ∀ (a b : ↑C) (p : Setoid.r a b), (_ : Quot.map (f ≫ g).obj (_ : ∀ (X Y : ↑C) …
    · intro _ _ _
      -- ⊢ (_ : Quot.map (f ≫ g).obj (_ : ∀ (X Y : ↑C), Setoid.r X Y → Setoid.r (g.obj  …
      simp only [types_id_apply]
      -- 🎉 no goals
    · intro _
      -- ⊢ Quot.map (f ≫ g).obj (_ : ∀ (X Y : ↑C), Setoid.r X Y → Setoid.r (g.obj (f.ob …
      rfl
      -- 🎉 no goals
#align category_theory.isomorphism_classes CategoryTheory.isomorphismClasses

theorem Groupoid.isIsomorphic_iff_nonempty_hom {C : Type u} [Groupoid.{v} C] {X Y : C} :
    IsIsomorphic X Y ↔ Nonempty (X ⟶ Y) :=
  (Groupoid.isoEquivHom X Y).nonempty_congr
#align category_theory.groupoid.is_isomorphic_iff_nonempty_hom CategoryTheory.Groupoid.isIsomorphic_iff_nonempty_hom

end CategoryTheory
