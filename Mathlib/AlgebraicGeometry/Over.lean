/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Comma.OverClass

/-!
# Typeclasses for `S`-schemes and `S`-morphisms

We define these as thin wrappers around `CategoryTheory/Comma/OverClass`.

## Main definition
- `AlgebraicGeometry.Scheme.Over`: `X.Over S` equips `X` with a `S`-scheme structure.
  `X ↘ S : X ⟶ S` is the structure morphism.
- `AlgebraicGeometry.Scheme.Hom.IsOver`: `f.IsOver S` asserts that `f` is a `S`-morphism.

-/

namespace AlgebraicGeometry.Scheme

universe u

open CategoryTheory

variable {X Y : Scheme.{u}} (f : X.Hom Y) (S S' : Scheme.{u})

/--
`X.Over S` is the typeclass containing the data of a structure morphism `X ↘ S : X ⟶ S`.
-/
protected abbrev Over (X S : Scheme.{u}) := OverClass X S

/--
`X.CanonicallyOver S` is the typeclass containing the data of a structure morphism `X ↘ S : X ⟶ S`,
and that `S` is (uniquely) inferrable from the structure of `X`.
-/
abbrev CanonicallyOver := CanonicallyOverClass X S

/-- Given `X.Over S` and `Y.Over S` and `f : X ⟶ Y`,
`f.IsOver S` is the typeclass asserting `f` commutes with the structure morphisms. -/
abbrev Hom.IsOver (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S] := HomIsOver f S

/-! Also note the existence of `CategoryTheory.IsOverTower X Y S`. -/

end AlgebraicGeometry.Scheme
