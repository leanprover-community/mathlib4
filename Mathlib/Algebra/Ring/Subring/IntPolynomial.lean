/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Ring.Subring.Polynomial

deprecated_module (since := "2026-01-31")

@[expose] public section

namespace Polynomial

@[deprecated (since := "2026-01-31")]
alias int := toSubring

@[deprecated (since := "2026-01-31")]
alias int_coeff_eq := toSubring_coeff

@[deprecated (since := "2026-01-31")]
alias int_leadingCoeff_eq := toSubring_coeff

@[deprecated (since := "2026-01-31")]
alias int_monic_iff := toSubring_monic_iff

@[deprecated (since := "2026-01-31")]
alias int_natDegree := toSubring_natDegree

@[deprecated (since := "2026-01-31")]
alias int_eval₂_eq := toSubring_eval₂

end Polynomial
