/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Cardinality

/-!
# The cardinality of the complex numbers

This file shows that the complex numbers have cardinality continuum, i.e. `#ℂ = 𝔠`.
-/
-- Porting note: the lemmas `mk_complex` and `mk_univ_complex` should be in the namespace `Cardinal`
-- like their real counterparts.

open Cardinal Set

open Cardinal

/-- The cardinality of the complex numbers, as a type. -/
@[simp]
theorem mk_complex : #ℂ = 𝔠 := by
  rw [mk_congr Complex.equivRealProd, mk_prod, lift_id, mk_real, continuum_mul_self]

/-- The cardinality of the complex numbers, as a set. -/
theorem mk_univ_complex : #(Set.univ : Set ℂ) = 𝔠 := by rw [mk_univ, mk_complex]

/-- The complex numbers are not countable. -/
theorem not_countable_complex : ¬(Set.univ : Set ℂ).Countable := by
  rw [← le_aleph0_iff_set_countable, not_le, mk_univ_complex]
  apply cantor
