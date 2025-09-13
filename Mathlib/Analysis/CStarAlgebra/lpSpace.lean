/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! # `lp ∞ A` as a C⋆-algebra

We place these here because, for reasons related to the import hierarchy, they should not be placed
in earlier files.
-/
open scoped ENNReal

noncomputable section

variable {I : Type*} {A : I → Type*}

example [∀ i, NonUnitalCStarAlgebra (A i)] : NonUnitalCStarAlgebra (lp A ∞) := by infer_instance

example [∀ i, NonUnitalCommCStarAlgebra (A i)] : NonUnitalCommCStarAlgebra (lp A ∞) := by
  infer_instance

-- it's slightly weird that we need the `Nontrivial` instance here
-- it's because we have no way to say that `‖(1 : A i)‖` is uniformly bounded as a type class
-- aside from `∀ i, NormOneClass (A i)`, this holds automatically for C⋆-algebras though.
instance [∀ i, CStarAlgebra (A i)] : WithNormedRing (lp A ∞) where
  dist_eq := dist_eq_norm
  norm_mul_le := norm_mul_le

example [∀ i, Nontrivial (A i)] [∀ i, CommCStarAlgebra (A i)] : CommCStarAlgebra (lp A ∞) := by
  infer_instance

end
