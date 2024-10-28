/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# Typeclasses for `S`-objects and `S`-morphisms

**Warning**: This is not usually how typeclasses should be used.
This is only a sensible approach when the morphism is considered as a structure on `X`,
typically in algebraic geometry.

For other applications use unbundled arrows or `CategoryTheory.Over`.

## Main definition
- `CategoryTheory.OverClass`: `OverClass X S` equips `X` with a morphism into `S`.
  `X ⮕ S : X ⟶ S` is the structure morphism.
- `CategoryTheory.HomIsOver`:
  `HomIsOver f S` asserts that `f` is commutes with the structure morphisms.

-/


namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (f : X ⟶ Y) (S S' : C)

/--
`OverClass X S` is the typeclass containing the data of a structure morphism `X ⮕ S : X ⟶ S`.
-/
class OverClass (X S : C) : Type v where
  ofHom ::
  /-- The structure morphism. Use `X ⮕ S` instead. -/
  hom : X ⟶ S

/--
The structure morphism `X ⮕ S : X ⟶ S` given `OverClass X S`.
The instance argument is an `optParam` instead so that it appears in the discrimination tree.
-/
def over (X S : C) (_ : OverClass X S := by infer_instance) : X ⟶ S := OverClass.hom

/-- The structure morphism `X ⮕ S : X ⟶ S` given `OverClass X S`. -/
notation:90 X:90 " ⮕ " S:90 => CategoryTheory.over X S inferInstance

/-- See Note [custom simps projection] -/
def OverClass.Simps.over (X S : C) [OverClass X S] : X ⟶ S := X ⮕ S

initialize_simps_projections OverClass (hom → over)

/--
`X.CanonicallyOverClass S` is the typeclass containing the data of a
structure morphism `X ⮕ S : X ⟶ S`,
and that `S` is (uniquely) inferrable from the structure of `X`.
-/
class CanonicallyOverClass (X : C) (S : semiOutParam C) extends OverClass X S where

/-- See Note [custom simps projection] -/
def CanonicallyOverClass.Simps.over (X S : C) [CanonicallyOverClass X S] : X ⟶ S := X ⮕ S

initialize_simps_projections CanonicallyOverClass (hom → over)

@[simps]
instance [CanonicallyOverClass X Y] [OverClass Y S] : OverClass X S := ⟨X ⮕ Y ≫ Y ⮕ S⟩

/-- Given `OverClass X S` and `OverClass Y S` and `f : X ⟶ Y`,
`HomIsOver f S` is the typeclass asserting `f` commutes with the structure morphisms. -/
class HomIsOver (f : X ⟶ Y) (S : C) [OverClass X S] [OverClass Y S] : Prop where
  comp_over : f ≫ Y ⮕ S = X ⮕ S := by simp

@[reassoc (attr := simp)]
lemma comp_over [OverClass X S] [OverClass Y S] [HomIsOver f S] :
    f ≫ Y ⮕ S = X ⮕ S :=
  HomIsOver.comp_over

/-- `Scheme.IsOverTower X Y S` is the typeclass asserting that the structure morphisms
`X ⮕ Y`, `Y ⮕ S`, and `X ⮕ S` commute. -/
abbrev IsOverTower (X Y S : C) [OverClass X S] [OverClass Y S] [OverClass X Y] :=
  HomIsOver (X ⮕ Y) S

instance [CanonicallyOverClass X Y] [OverClass Y S] : IsOverTower X Y S :=
  ⟨rfl⟩

lemma isOver_of_isOverTower [OverClass X S] [OverClass X S'] [OverClass Y S]
    [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' := by
  constructor
  rw [← comp_over (Y ⮕ S), comp_over_assoc f, comp_over]

instance [CanonicallyOverClass X S]
    [OverClass X S'] [OverClass Y S] [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' :=
  isOver_of_isOverTower f S S'

instance [OverClass X S]
    [OverClass X S'] [CanonicallyOverClass Y S] [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' :=
  isOver_of_isOverTower f S S'

end CategoryTheory
