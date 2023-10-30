/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# Minimal Axioms for a Field

This file defines constructors to define a `Field` structure on a Type, while proving
a minimum number of equalities.

## Main Definitions

* `Field.ofMinimalAxioms`: Define a `Field` structure on a Type by proving a minimized set of axioms

-/

set_option autoImplicit true

/-- Define a `Field` structure on a Type by proving a minimized set of axioms.
Note that this uses the default definitions for `npow`, `nsmul`, `zsmul`, `div` and `sub`
See note [reducible non-instances]. -/
@[reducible]
def Field.ofMinimalAxioms (K : Type u)
    [Add K] [Mul K] [Neg K] [Inv K] [Zero K] [One K]
    (add_assoc : ∀ a b c : K, a + b + c = a + (b + c))
    (zero_add : ∀ a : K, 0 + a = a)
    (add_left_neg : ∀ a : K, -a + a = 0)
    (mul_assoc : ∀ a b c : K, a * b * c = a * (b * c))
    (mul_comm : ∀ a b : K, a * b = b * a)
    (one_mul : ∀ a : K, 1 * a = a)
    (mul_inv_cancel : ∀ a : K, a ≠ 0 → a * a⁻¹ = 1)
    (inv_zero : (0 : K)⁻¹ = 0)
    (left_distrib : ∀ a b c : K, a * (b + c) = a * b + a * c)
    (exists_pair_ne : ∃ x y : K, x ≠ y) : Field K :=
  letI := CommRing.ofMinimalAxioms add_assoc zero_add
    add_left_neg mul_assoc mul_comm one_mul left_distrib
  { exists_pair_ne := exists_pair_ne
    mul_inv_cancel := mul_inv_cancel
    inv_zero := inv_zero }
