/-
Copyright (c) 2022 Eric Wieser, Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.Order.Field.Canonical.Defs
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Finset.Lattice.Fold

/-!
# `Finset.sup` of `Nat.cast`
-/

open Finset

namespace Nat
variable {ι R : Type*}

section LinearOrderedSemiring
variable [LinearOrderedSemiring R] {s : Finset ι}

set_option linter.docPrime false in
@[simp, norm_cast]
lemma cast_finsetSup' (f : ι → ℕ) (hs) : ((s.sup' hs f : ℕ) : R) = s.sup' hs fun i ↦ (f i : R) := by
  induction hs using Finset.Nonempty.cons_induction <;> simp [*]

set_option linter.docPrime false in
@[simp, norm_cast]
lemma cast_finsetInf' (f : ι → ℕ) (hs) : (↑(s.inf' hs f) : R) = s.inf' hs fun i ↦ (f i : R) := by
  induction hs using Finset.Nonempty.cons_induction <;> simp [*]

end LinearOrderedSemiring

@[simp, norm_cast]
lemma cast_finsetSup [CanonicallyLinearOrderedSemifield R] [FloorSemiring R]
    (s : Finset ι) (f : ι → ℕ) : (↑(s.sup f) : R) = s.sup fun i ↦ (f i : R) := by
  comp_sup_eq_sup_comp _ (by simp) (by simp)

end Nat
