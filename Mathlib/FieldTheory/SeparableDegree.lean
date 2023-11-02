/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.Polynomial.SeparableDegree

/-!

# Separable degree

This file contains basics about the separable degree of a field extension.

## Main results

- `sepDegree E F`: the separable degree of an algebraic extension `E / F` of fields, defined to be
  the cardinal of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.
  (Mathematically, it should be the algebraic closure of `F`, but in order to make the type
  compatible with `Module.rank E F`, we use the algebraic closure of `E`.)
  Note that if `E / F` is not algebraic, then this definition makes no mathematical sense.
- `finSepDegree E F`: the separable degree of `E / F` as a natural number, which is zero if
  `sepDegree E F` is not finite.

## Tags

separable degree, degree, polynomial
-/

open scoped Classical Polynomial

open FiniteDimensional Polynomial IntermediateField

noncomputable section

universe u v v' w

variable (F : Type u) (E : Type v) [Field F] [Field E]

variable [Algebra F E]

namespace Field

/-- If `E / F` is an algebraic extension, then the separable degree of `E / F`
is the number of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.
Note that if `E / F` is not algebraic, then this definition makes no mathematical sense.
-/
def sepDegree := Cardinal.mk (E →ₐ[F] (AlgebraicClosure E))

/-- The separable degree of `E / F` as a natural number. -/
def finSepDegree : ℕ := Cardinal.toNat (sepDegree F E)

end Field
