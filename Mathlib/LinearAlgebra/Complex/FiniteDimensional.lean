/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.Interval.Set.Infinite

/-!
# Complex number as a finite-dimensional vector space over `ℝ`

This file contains the `FiniteDimensional ℝ ℂ` instance, as well as some results about the rank
(`finrank` and `Module.rank`).
-/

open Module

namespace Complex

instance : FiniteDimensional ℝ ℂ := .of_fintype_basis basisOneI

/-- `ℂ` is a finite extension of `ℝ` of degree 2, i.e `[ℂ : ℝ] = 2` -/
@[simp, stacks 09G4]
theorem finrank_real_complex : finrank ℝ ℂ = 2 := by
  rw [finrank_eq_card_basis basisOneI, Fintype.card_fin]

@[simp]
theorem rank_real_complex : Module.rank ℝ ℂ = 2 := by simp [← finrank_eq_rank, finrank_real_complex]

theorem rank_real_complex'.{u} : Cardinal.lift.{u} (Module.rank ℝ ℂ) = 2 := by
  rw [← finrank_eq_rank, finrank_real_complex, Cardinal.lift_natCast, Nat.cast_ofNat]

/-- `Fact` version of the dimension of `ℂ` over `ℝ`, locally useful in the definition of the
circle. -/
theorem finrank_real_complex_fact : Fact (finrank ℝ ℂ = 2) :=
  ⟨finrank_real_complex⟩

end Complex

instance (priority := 100) FiniteDimensional.complexToReal (E : Type*) [AddCommGroup E]
    [Module ℂ E] [FiniteDimensional ℂ E] : FiniteDimensional ℝ E :=
  FiniteDimensional.trans ℝ ℂ E

theorem rank_real_of_complex (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Module.rank ℝ E = 2 * Module.rank ℂ E :=
  Cardinal.lift_inj.{_,0}.1 <| by
    rw [← lift_rank_mul_lift_rank ℝ ℂ E, Complex.rank_real_complex']
    simp only [Cardinal.lift_id']

theorem finrank_real_of_complex (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Module.finrank ℝ E = 2 * Module.finrank ℂ E := by
  rw [← Module.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]

section Rational

open Cardinal Module

@[simp]
lemma Real.rank_rat_real : Module.rank ℚ ℝ = continuum := by
  refine (Free.rank_eq_mk_of_infinite_lt ℚ ℝ ?_).trans mk_real
  simpa [mk_real] using aleph0_lt_continuum

/-- `C` has an uncountable basis over `ℚ`. -/
@[simp, stacks 09G0]
lemma Complex.rank_rat_complex : Module.rank ℚ ℂ = continuum := by
  refine (Free.rank_eq_mk_of_infinite_lt ℚ ℂ ?_).trans Cardinal.mk_complex
  simpa using aleph0_lt_continuum

/-- `ℂ` and `ℝ` are isomorphic as vector spaces over `ℚ`, or equivalently,
as additive groups. -/
theorem Complex.nonempty_linearEquiv_real : Nonempty (ℂ ≃ₗ[ℚ] ℝ) :=
  LinearEquiv.nonempty_equiv_iff_rank_eq.mpr <| by simp

end Rational
