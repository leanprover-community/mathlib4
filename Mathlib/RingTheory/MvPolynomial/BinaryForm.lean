/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Binary forms

A binary form of degree `d` is a homogeneous polynomial in two variables of degree `d`.

## Main definitions

- `BinaryForm R d` is the type of binary forms over a commutative ring `R` of degree `d`.
- `BinaryForm.basis R d` is the basis of `BinaryForm R d` consisting of the monomials
  `X ^ i * Y ^ (d - i)` for `i : Fin (d + 1)`.

-/


universe u

open MvPolynomial Finsupp

/-- A binary form of degree `d` is a homogeneous polynomial in two variables of degree `d`. -/
abbrev BinaryForm (R : Type u) [CommSemiring R] (d : ℕ) : Type u :=
  homogeneousSubmodule (Fin 2) R d

namespace BinaryForm

variable (R : Type u) [CommSemiring R] (d : ℕ)

-- no, this should be generalised first.
def basis : Basis (Fin (d + 1)) R (BinaryForm R d) :=
  .ofEquivFun {
    toFun p i := p.val.coeff (single 0 (i : ℕ) + single 1 (d - i))
    invFun p := ⟨∑ i : Fin (d + 1), monomial (single 0 (i : ℕ) + single 1 (d - i)) (p i),
      sum_mem fun c _ ↦ isHomogeneous_monomial _ <|
        by simpa [-single_tsub] using Nat.add_sub_cancel' c.is_le⟩
    map_add' p q := by ext; simp
    map_smul' c p := by ext; simp
    left_inv p := by
      ext c
      simp [-single_tsub, coeff_sum]
  }

#check isHomogeneous_C

end BinaryForm
