/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors

/-! # Non-zero-divisors in algebras -/

open nonZeroDivisors

lemma Algebra.algebraMapSubmonoid_nonZeroDivisors_le
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] : algebraMapSubmonoid S R⁰ ≤ S⁰ := by
  rintro _ ⟨r, hr, rfl⟩
  have := (algebraMap R S).domain_nontrivial
  simpa using nonZeroDivisors.ne_zero hr
