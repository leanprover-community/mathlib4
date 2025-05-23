/-
Copyright (c) 2022 Eric Wieser, Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# `Finset.sup` and ring operations
-/

open Finset

namespace Nat
variable {ι R : Type*}

section LinearOrderedSemiring
variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {s : Finset ι}

set_option linter.docPrime false in
@[simp, norm_cast]
lemma cast_finsetSup' (f : ι → ℕ) (hs) : ((s.sup' hs f : ℕ) : R) = s.sup' hs fun i ↦ (f i : R) :=
  comp_sup'_eq_sup'_comp _ _ cast_max

set_option linter.docPrime false in
@[simp, norm_cast]
lemma cast_finsetInf' (f : ι → ℕ) (hs) : (↑(s.inf' hs f) : R) = s.inf' hs fun i ↦ (f i : R) :=
  comp_inf'_eq_inf'_comp _ _ cast_min

@[simp, norm_cast]
lemma cast_finsetSup [OrderBot R] [CanonicallyOrderedAdd R] (s : Finset ι) (f : ι → ℕ) :
    (↑(s.sup f) : R) = s.sup fun i ↦ (f i : R) :=
  comp_sup_eq_sup_comp _ cast_max (by simp)

end LinearOrderedSemiring

end Nat

section

variable {R ι : Type*} [LinearOrder R] [NonUnitalNonAssocSemiring R]
  [CanonicallyOrderedAdd R] [OrderBot R]

lemma Finset.mul_sup₀ (s : Finset ι) (f : ι → R) (a : R) :
    a * s.sup f = s.sup (a * f ·) := by
  classical
  induction s using Finset.induction with
  | empty => simp [bot_eq_zero]
  | insert _ _ _ IH => simp only [sup_insert, mul_max, ← IH]

/-- Also see `Finset.sup'_mul₀` for a version for `GroupWithZero`s. -/
lemma Finset.sup_mul₀ (s : Finset ι) (f : ι → R) (a : R) :
    s.sup f * a = s.sup (f · * a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [bot_eq_zero]
  | insert _ _ _ IH => simp only [sup_insert, max_mul, ← IH]

end
