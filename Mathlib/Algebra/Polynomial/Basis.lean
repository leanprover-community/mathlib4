/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!

# Basis of a polynomial ring

-/

open Module

universe u

variable (R : Type u) [Semiring R]

namespace Polynomial

/-- The monomials form a basis on `R[X]`. To get the rank of a polynomial ring,
use this and `Basis.mk_eq_rank`. -/
def basisMonomials : Basis ℕ R R[X] :=
  Basis.ofRepr (toFinsuppIsoLinear R)

@[simp]
theorem coe_basisMonomials : (basisMonomials R : ℕ → R[X]) = fun s => monomial s 1 :=
  funext fun _ => ofFinsupp_single _ _

end Polynomial
