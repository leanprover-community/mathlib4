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
variable [LinearOrderedSemiring R] [FloorSemiring R] {s : Finset ι}

set_option linter.docPrime false in
@[simp, norm_cast]
lemma cast_finsetSup' (f : ι → ℕ) (hs) : ((s.sup' hs f : ℕ) : R) = s.sup' hs fun i ↦ (f i : R) := by
  apply le_antisymm
  · rw [← le_floor_iff, sup'_le_iff]
    · intros i hi
      apply le_floor
      exact le_sup' (fun i ↦ (f i : R)) hi
    · exact le_sup'_of_le (fun i ↦ (f i : R)) hs.choose_spec (Nat.cast_nonneg _)
  apply sup'_le
  exact fun i hi ↦ Nat.mono_cast (le_sup' _ hi)

set_option linter.docPrime false in
@[simp, norm_cast]
lemma cast_finsetInf' (f : ι → ℕ) (hs) : (↑(s.inf' hs f) : R) = s.inf' hs fun i ↦ (f i : R) :=
  eq_of_forall_le_iff fun c ↦ by simp only [le_inf'_iff, ← Nat.ceil_le]

end LinearOrderedSemiring

@[simp, norm_cast]
lemma cast_finsetSup [CanonicallyLinearOrderedSemifield R] [FloorSemiring R]
    (s : Finset ι) (f : ι → ℕ) : (↑(s.sup f) : R) = s.sup fun i ↦ (f i : R) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [← sup'_eq_sup hs, ← sup'_eq_sup hs, Nat.cast_finsetSup']

end Nat
