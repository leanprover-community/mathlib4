/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Typeclasses for `S`-schemes and `S`-morphisms

## Main definition
- `AlgebraicGeometry.Scheme.Over`: `X.Over S` equips `X` with a `S`-scheme structure.
  `X ⮕ S : X ⟶ S` is the structure morphism.
- `AlgebraicGeometry.Scheme.Hom.IsOver`: `f.IsOver S` asserts that `f` is a `S`-morphism.

-/


namespace AlgebraicGeometry.Scheme

universe u

open CategoryTheory

variable {X Y : Scheme.{u}} (f : X.Hom Y) (S S' : Scheme.{u})

/--
`X.Over S` is the typeclass containing the data of a structure morphism `X ⮕ S : X ⟶ S`.
-/
protected class Over (X S : Scheme.{u}) : Type u where
  /-- The structure morphism. Use `X ⮕ S` instead. -/
  ofHom :: hom : X ⟶ S

/--
The structure morphism `X ⮕ S : X ⟶ S` given `X.Over S`.
The instance argument is an `optParam` instead so that it appears in the discrimination tree.
-/
def over (X S : Scheme.{u}) (_ : X.Over S := by infer_instance) : X ⟶ S := Scheme.Over.hom

/-- The structure morphism `X ⮕ S : X ⟶ S` given `X.Over S`. -/
notation:90 X:90 " ⮕ " S:90 => Scheme.over X S inferInstance

/-- See Note [custom simps projection] -/
def Over.Simps.over (X S : Scheme.{u}) [X.Over S] : X ⟶ S := X ⮕ S

initialize_simps_projections Scheme.Over (hom → over)

/--
`X.CanonicallyOver S` is the typeclass containing the data of a structure morphism `X ⮕ S : X ⟶ S`,
and that `S` is (uniquely) inferrable from the structure of `X`.
-/
class CanonicallyOver (X : Scheme.{u}) (S : semiOutParam (Scheme.{u})) extends X.Over S where

/-- See Note [custom simps projection] -/
def CanonicallyOver.Simps.over (X S : Scheme.{u}) [X.CanonicallyOver S] : X ⟶ S := X ⮕ S

initialize_simps_projections Scheme.CanonicallyOver (hom → over)

@[simps]
instance [X.CanonicallyOver Y] [Y.Over S] : X.Over S := ⟨X ⮕ Y ≫ Y ⮕ S⟩

/-- Given `X.Over S` and `Y.Over S` and `f : X ⟶ Y`,
`f.IsOver S` is the typeclass asserting `f` commutes with the structure morphisms. -/
class Hom.IsOver (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S] : Prop where
  comp_over : f ≫ Y ⮕ S = X ⮕ S := by simp

@[reassoc (attr := simp)]
lemma Hom.comp_over [X.Over S] [Y.Over S] [f.IsOver S] :
    f ≫ Y ⮕ S = X ⮕ S :=
  IsOver.comp_over

/-- `Scheme.IsOverTower X Y S` is the typeclass asserting that the structure morphisms
`X ⮕ Y`, `Y ⮕ S`, and `X ⮕ S` commute. -/
abbrev IsOverTower (X Y S : Scheme.{u}) [X.Over S] [Y.Over S] [X.Over Y] :=
  (X ⮕ Y).IsOver S

instance [X.CanonicallyOver Y] [Y.Over S] : Scheme.IsOverTower X Y S :=
  ⟨rfl⟩

lemma isOver_of_isOverTower [X.Over S] [X.Over S'] [Y.Over S] [Y.Over S'] [S.Over S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [f.IsOver S] : f.IsOver S' := by
  constructor
  rw [← (Y ⮕ S).comp_over, f.comp_over_assoc, Hom.comp_over]

instance [X.CanonicallyOver S] [X.Over S'] [Y.Over S] [Y.Over S'] [S.Over S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [f.IsOver S] : f.IsOver S' :=
  isOver_of_isOverTower f S S'

instance [X.Over S] [X.Over S'] [Y.CanonicallyOver S] [Y.Over S'] [S.Over S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [f.IsOver S] : f.IsOver S' :=
  isOver_of_isOverTower f S S'

end AlgebraicGeometry.Scheme
