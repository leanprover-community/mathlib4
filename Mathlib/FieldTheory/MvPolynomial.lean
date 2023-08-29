/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Dimension
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.MvPolynomial.Basic

#align_import field_theory.mv_polynomial from "leanprover-community/mathlib"@"039a089d2a4b93c761b234f3e5f5aeb752bac60f"

/-!
# Multivariate polynomials over fields

This file contains basic facts about multivariate polynomials over fields, for example that the
dimension of the space of multivariate polynomials over a field is equal to the cardinality of
finitely supported functions from the indexing set to `ℕ`.
-/


noncomputable section

open Classical

open Set LinearMap Submodule

open BigOperators

namespace MvPolynomial

universe u v

variable {σ : Type u} {K : Type v}

variable (σ K) [Field K]

theorem quotient_mk_comp_C_injective (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) :
    Function.Injective ((Ideal.Quotient.mk I).comp MvPolynomial.C) := by
  refine' (injective_iff_map_eq_zero _).2 fun x hx => _
  -- ⊢ x = 0
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hx
  -- ⊢ x = 0
  refine' _root_.by_contradiction fun hx0 => absurd (I.eq_top_iff_one.2 _) hI
  -- ⊢ 1 ∈ I
  have := I.mul_mem_left (MvPolynomial.C x⁻¹) hx
  -- ⊢ 1 ∈ I
  rwa [← MvPolynomial.C.map_mul, inv_mul_cancel hx0, MvPolynomial.C_1] at this
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.quotient_mk_comp_C_injective MvPolynomial.quotient_mk_comp_C_injective

end MvPolynomial

namespace MvPolynomial

universe u

variable {σ : Type u} {K : Type u} [Field K]

open Classical

theorem rank_mvPolynomial : Module.rank K (MvPolynomial σ K) = Cardinal.mk (σ →₀ ℕ) := by
  rw [← Cardinal.lift_inj, ← (basisMonomials σ K).mk_eq_rank]
  -- 🎉 no goals
#align mv_polynomial.rank_mv_polynomial MvPolynomial.rank_mvPolynomial

end MvPolynomial
