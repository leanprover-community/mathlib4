/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.PhiIrreducible
import Archive.GaussianMomentConjecture.PhiVieta
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Assembly bridge: the swapped-mapped `Φ` is the clean `Phi R M`

`GMC2.PhiIrreducible.phi_irreducible_ratfunc` proves irreducibility of the swapped-and-mapped
polynomial; `GMC2.PhiVieta.Phi R M = X^M − C(t)·R.map` is the clean form the Vieta argument
(`prod_roots_Phi`) is stated for.  This module proves they are the *same polynomial*, so
`Irreducible (Phi R M)` follows from (A) — connecting the irreducibility, Vieta, and orbit-product
pieces onto one `Φ`.
-/

open Polynomial

namespace GMC2.DvdKAssembly

variable {F : Type*} [Field F]

/-- The composite `F → F[t] → F(t)` is the direct `algebraMap F (RatFunc F)`. -/
theorem algebraMap_comp_C :
    (algebraMap (Polynomial F) (RatFunc F)).comp (Polynomial.C) = algebraMap F (RatFunc F) := by
  rw [IsScalarTower.algebraMap_eq F (Polynomial F) (RatFunc F), Polynomial.algebraMap_eq]

/-- **The bridge.**  The clean `Phi R M` equals the swapped-mapped polynomial. -/
theorem Phi_eq_map_swap (R : F[X]) (M : ℕ) :
    GMC2.PhiVieta.Phi R M
      = Polynomial.map (algebraMap (Polynomial F) (RatFunc F))
          (Polynomial.Bivariate.swap (Polynomial.C ((X : F[X]) ^ M) - Polynomial.C R * X)) := by
  rw [GMC2.PhiIrreducible.swap_phi_eq, GMC2.PhiVieta.Phi, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_map, Polynomial.map_map, algebraMap_comp_C, Polynomial.map_C,
    RatFunc.algebraMap_X, Polynomial.map_pow, Polynomial.map_X]
  ring

/-- **`Phi R M` is irreducible over `F(t)`** — from (A), via the bridge.  This is the
transitivity input, now on the exact `Φ` Vieta uses. -/
theorem irreducible_Phi (R : F[X]) (M : ℕ) (hM : 1 ≤ M) (hR0 : R.coeff 0 ≠ 0) :
    Irreducible (GMC2.PhiVieta.Phi R M) := by
  rw [Phi_eq_map_swap]
  exact GMC2.PhiIrreducible.phi_irreducible_ratfunc R M hM hR0

end GMC2.DvdKAssembly
