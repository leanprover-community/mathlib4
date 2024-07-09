/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Algebra.Int
import Mathlib.Algebra.MvPolynomial.Supported

/-!
# Polynomials with coefficients in `ℕ` or `ℤ` supported by a set of variables

-/

namespace MvPolynomial

open Algebra

variable {σ : Type*} {s : Set σ}

theorem exists_restrict_to_vars (R : Type*) [CommRing R] {F : MvPolynomial σ ℤ}
    (hF : ↑F.vars ⊆ s) : ∃ f : (s → R) → R, ∀ x : σ → R, f (x ∘ (↑) : s → R) = aeval x F := by
  rw [← mem_supported, supported_eq_range_rename, AlgHom.mem_range] at hF
  cases' hF with F' hF'
  use fun z ↦ aeval z F'
  intro x
  simp only [← hF', aeval_rename]
#align mv_polynomial.exists_restrict_to_vars MvPolynomial.exists_restrict_to_vars
