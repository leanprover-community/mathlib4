/-
Copyright (c) 2026 Ryan Nolan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Nolan
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Indefinite Metrics

This file defines indefinite metrics over modules. An indefinite metric is formalized as a
symmetric bilinear form that is not required to be positive-definite. This provides the
algebraic foundation for indefinite inner product spaces.

## Main definitions

* `IndefiniteMetric`: A structure bundling a bilinear form with a proof of its symmetry.
* `IndefiniteMetric.toQuadraticForm`: The quadratic form associated with an indefinite metric.
-/

@[expose] public section

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- An indefinite metric on a module `M` over a commutative ring `R` is a symmetric
bilinear form. It drops the positive-definite requirement of standard inner products. -/
structure IndefiniteMetric (R : Type*) (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  /-- The underlying bilinear form. -/
  bilin : LinearMap.BilinForm R M
  /-- Proof that the bilinear form is symmetric. -/
  symm : bilin.IsSymm

namespace IndefiniteMetric

variable (K : IndefiniteMetric R M)

/-- The quadratic form associated with an indefinite metric. -/
def toQuadraticForm : QuadraticForm R M :=
  LinearMap.BilinMap.toQuadraticMap K.bilin

end IndefiniteMetric
