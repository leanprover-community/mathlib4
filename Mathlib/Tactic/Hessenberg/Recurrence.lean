/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The characteristic polynomial recurrence for upper Hessenberg matrices

`hessCharPoly n H` computes the characteristic polynomial of the `n × n` upper Hessenberg
matrix `H` (stored as an array of entries in row-major ordering).

It uses a recursive algorithm given as equation 5.1 of [Rehman-Ipsen][rehmanipsen2011] that
successively computes characteristic polynomials `pᵢ(X) = det (X * I - Hᵢ)` of leading principal
submatrices `Hᵢ` of order `i`:

```
p_0 := 1

p_{k+1} = (X - C H[k][k]) p_k - ∑_{t<k} C (H[t][k] ∏_{j=t}^{k-1} H[j+1][j]) p_t
```

## References

* [Rizwana Rehman, Ilse C. F. Ipsen,
  *La Budde's method for computing characteristic polynomials*][rehmanipsen2011]
-/

public section

open Polynomial

namespace Mathlib.Tactic.Hessenberg

variable {R : Type*} [CommRing R]

/-- The characteristic polynomial of the leading `k × k` block of the `n × n` Hessenberg
matrix represented by an array of entries in row-major ordering. -/
noncomputable def hessP (n : ℕ) (H : Array R) : ℕ → R[X]
  | 0 => 1
  | k + 1 =>
    (X - C (H.getD (n * k + k) 0)) * hessP n H k -
      ∑ t : Fin k, C (H.getD (n * (t : ℕ) + k) 0 *
        ∏ j ∈ Finset.Ico (t : ℕ) k, H.getD (n * (j + 1) + j) 0) * hessP n H (t : ℕ)

/-- The characteristic polynomial of an `n × n` Hessenberg matrix represented by an array of
entries in row-major ordering. -/
noncomputable abbrev hessCharPoly (n : ℕ) (H : Array R) : R[X] := hessP n H n

theorem hessP_zero (n : ℕ) (H : Array R) : hessP n H 0 = 1 := by
  simp only [hessP]

theorem hessP_succ (n k : ℕ) (H : Array R) :
    hessP n H (k + 1) =
      (X - C (H.getD (n * k + k) 0)) * hessP n H k -
        ∑ t : Fin k, C (H.getD (n * (t : ℕ) + k) 0 *
          ∏ j ∈ Finset.Ico (t : ℕ) k, H.getD (n * (j + 1) + j) 0) *
          hessP n H (t : ℕ) := by
  simp only [hessP]

theorem hessCharPoly_eq (n : ℕ) (H : Array R) : hessCharPoly n H = hessP n H n := rfl

end Mathlib.Tactic.Hessenberg

end
