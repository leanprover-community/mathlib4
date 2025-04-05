/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Kim Morrison
-/
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
The hom functor, sending `(X, Y)` to the type `X ⟶ Y`.
-/


universe v u

open Opposite

open CategoryTheory

namespace CategoryTheory.Functor

variable (C : Type u) [Category.{v} C]

/-- `Functor.hom` is the hom-pairing, sending `(X, Y)` to `X ⟶ Y`, contravariant in `X` and
covariant in `Y`. -/
@[simps]
def hom : Cᵒᵖ × C ⥤ Type v where
  obj p := unop p.1 ⟶ p.2
  map f h := f.1.unop ≫ h ≫ f.2

end CategoryTheory.Functor
