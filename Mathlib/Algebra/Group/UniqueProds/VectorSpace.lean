/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# A `ℚ`-vector space has `TwoUniqueSums`.
-/

public section

variable {G : Type*}

/-- Any `ℚ`-vector space has `TwoUniqueSums`, because it is isomorphic to some
  `(Basis.ofVectorSpaceIndex ℚ G) →₀ ℚ` by choosing a basis, and `ℚ` already has
  `TwoUniqueSums` because it's ordered. -/
instance [AddCommGroup G] [Module ℚ G] : TwoUniqueSums G :=
  TwoUniqueSums.of_injective_addHom _ (Module.Basis.ofVectorSpace ℚ G).repr.injective inferInstance
