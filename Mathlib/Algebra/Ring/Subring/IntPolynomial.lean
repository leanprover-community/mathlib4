/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap

deprecated_module (since := "2026-01-31")

@[expose] public section

namespace Polynomial

@[deprecated (since := "2026-01-31")] alias int := toSubring
@[deprecated (since := "2026-01-31")] alias int_coeff_eq := coeff_toSubring
@[deprecated (since := "2026-01-31")] alias int_leadingCoeff_eq := leadingCoeff_toSubring
@[deprecated (since := "2026-01-31")] alias int_monic_iff := monic_toSubring
@[deprecated (since := "2026-01-31")] alias int_natDegree := natDegree_toSubring
@[deprecated (since := "2026-01-31")] alias int_eval₂_eq := eval₂_toSubring

end Polynomial
