/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat
import Mathlib.Algebra.Category.AlgebraCat.Basic

/-! # Category-theoretic interpretations of `clifford_algebra`

## Main definitions

* `QuadraticModuleCat.cliffordAlgebra`: the functor from quadratic modules to algebras
-/

universe v u
open CategoryTheory

variable {R : Type u} [CommRing R]

/-- The "clifford algebra" functor, sending a quadratic `R`-module `V` to the clifford algebra on
`V`.

This is `CliffordAlgebra.map` through the lens of category theory. -/
@[simps]
def QuadraticModuleCat.cliffordAlgebra : QuadraticModuleCat.{u} R ⥤ AlgebraCat.{u} R where
  obj M := { carrier := CliffordAlgebra M.form }
  map {_M _N} f := CliffordAlgebra.map f.toIsometry
  map_id _M := CliffordAlgebra.map_id _
  map_comp {_M _N _P} f g := (CliffordAlgebra.map_comp_map g.toIsometry f.toIsometry).symm
