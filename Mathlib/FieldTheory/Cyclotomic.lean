/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

variable (K : Type*) [Field K]

theorem exists_isPrimitiveRoot_of_isSepClosed {n : ℕ} [IsSepClosed K] [NeZero (n : K)] :
    ∃ (ξ : K), IsPrimitiveRoot ξ n := by
  apply exists_isPrimitiveRoot_of_splits_cyclotomic
  apply IsSepClosed.splits_domain (Polynomial.cyclotomic n K)
  apply Polynomial.separable_cyclotomic
