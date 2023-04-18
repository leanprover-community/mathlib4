/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios

! This file was ported from Lean 3 source module data.complex.cardinality
! leanprover-community/mathlib commit 1c4e18434eeb5546b212e830b2b39de6a83c473c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Complex.Basic
import Mathbin.Data.Real.Cardinality

/-!
# The cardinality of the complex numbers

This file shows that the complex numbers have cardinality continuum, i.e. `#ℂ = 𝔠`.
-/


open Cardinal Set

open Cardinal

/-- The cardinality of the complex numbers, as a type. -/
@[simp]
theorem mk_complex : (#ℂ) = 𝔠 := by
  rw [mk_congr Complex.equivRealProd, mk_prod, lift_id, mk_real, continuum_mul_self]
#align mk_complex mk_complex

/-- The cardinality of the complex numbers, as a set. -/
@[simp]
theorem mk_univ_complex : (#(Set.univ : Set ℂ)) = 𝔠 := by rw [mk_univ, mk_complex]
#align mk_univ_complex mk_univ_complex

/-- The complex numbers are not countable. -/
theorem not_countable_complex : ¬(Set.univ : Set ℂ).Countable :=
  by
  rw [← le_aleph_0_iff_set_countable, not_le, mk_univ_complex]
  apply cantor
#align not_countable_complex not_countable_complex

