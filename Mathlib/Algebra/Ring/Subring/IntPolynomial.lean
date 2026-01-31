/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Polynomial.Subring

deprecated_module (since := "2026-01-31")

@[expose] public section

variable {K : Type*} [Field K] (R : Subring K)

namespace Polynomial

@[deprecated (since := "2026-01-31")] alias int := toSubring
@[deprecated (since := "2026-01-31")] alias int_coeff_eq := coeff_toSubring
@[deprecated (since := "2026-01-31")] alias int_leadingCoeff_eq := leadingCoeff_toSubring

namespace Polynomial

variable (P : K[X]) (hP : ∀ n : ℕ, P.coeff n ∈ R)

@[simp]
theorem int_coeff_eq (n : ℕ) : ↑((P.int R hP).coeff n) = P.coeff n := rfl

@[simp]
theorem int_leadingCoeff_eq : ↑(P.int R hP).leadingCoeff = P.leadingCoeff := rfl

@[simp]
theorem int_monic_iff : (P.int R hP).Monic ↔ P.Monic := by
  rw [Monic, Monic, ← int_leadingCoeff_eq, OneMemClass.coe_eq_one]

@[simp]
theorem int_natDegree : (P.int R hP).natDegree = P.natDegree := rfl

variable {L : Type*} [Ring L] [Algebra K L]

@[simp]
theorem int_eval₂_eq (x : L) : eval₂ (algebraMap R L) x (P.int R hP) = aeval x P := by
  rw [aeval_eq_sum_range, eval₂_eq_sum_range]
  exact Finset.sum_congr rfl (fun n _ => by rw [Algebra.smul_def]; rfl)

end Polynomial
