/-
Copyright (c) 2026 Abel Donate. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abel Donate
-/
module

public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# Simplicial set as monoidal closed category

In `Mathlib/AlgebraicTopology/SimplicialCategory/SimplicialObject.lean`, it is shown that the
category of simplicial sets is a simplicial category. On the other hand, it is also a monoidal
closed category (see `Mathlib/CategoryTheory/Monoidal/Closed/FunctorToTypes.lean`). The simplicial
hom `sHom X Y` is the internal hom `(ihom X).obj Y`.

We deduce the adjunction `SSet.sHomEquiv : (K ⊗ X ⟶ Y) ≃ (K ⟶ sHom X Y)` for simplicial sets
`X`, `Y` and `K`.
-/

public section

universe v

namespace SSet

open CategoryTheory MonoidalCategory MonoidalClosed SimplicialCategory

variable (K X Y : SSet.{v})

/-- The adjunction property `(K ⊗ X ⟶ Y) ≃ (K ⟶ sHom X Y)` for simplicial sets. -/
def sHomEquiv : (K ⊗ X ⟶ Y) ≃ (K ⟶ sHom X Y) :=
  ((β_ K X).homCongr (Iso.refl Y)).trans ((ihom.adjunction X).homEquiv K Y)

end SSet
