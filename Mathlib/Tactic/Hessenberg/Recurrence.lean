/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# The characteristic polynomial recurrence for upper Hessenberg matrices

`hessCharPoly n H` defines the characteristic polynomial of the `n × n` upper Hessenberg
matrix `H` (stored as an array of entries in row-major ordering).

It uses a recursive algorithm given as equation 5.1 of [Rehman-Ipsen][rehmanipsen2011] that
successively computes characteristic polynomials `pᵢ(X) = det (X * I - Hᵢ)` of leading principal
submatrices `Hᵢ` of order `i`:

```
p_0 := 1

p_{k+1} = (X - C H[k][k]) p_k - ∑_{t<k} C (H[t][k] ∏_{j=t}^{k-1} H[j+1][j]) p_t
```

This file defines both noncomputable, `hessCharPoly`, and computable `coeffHessCharPoly` (via
representation of a polynomial as lists of coefficients) versions of the recurrence.

We have both versions of the recurrence so that for a literal matrix `H` we can produce the
coefficients of the characteristic polynomial by computing `coeffHessCharPoly` using the kernel. The
theorem `ofCoeffList_coeffHessCharPoly` interprets the result as `hessCharPoly`, a polynomial in
`R[X]`.

## References

* [Rizwana Rehman, Ilse C. F. Ipsen,
  *La Budde's method for computing characteristic polynomials*][rehmanipsen2011]
-/

public section

open Polynomial

namespace Mathlib.Tactic.Hessenberg

variable {R : Type*} [CommRing R] (n : ℕ) (H : Array R)

/-- The characteristic polynomial of the leading `k × k` block of the `n × n` Hessenberg
matrix represented by an array of entries in row-major ordering. -/
noncomputable def hessP : ℕ → R[X]
  | 0 => 1
  | k + 1 =>
    (X - C (H.getD (n * k + k) 0)) * hessP k -
      ∑ t : Fin k, C (H.getD (n * (t : ℕ) + k) 0 *
        ∏ j ∈ Finset.Ico (t : ℕ) k, H.getD (n * (j + 1) + j) 0) * hessP (t : ℕ)

/-- The characteristic polynomial of an `n × n` Hessenberg matrix represented by an array of
entries in row-major ordering. -/
noncomputable abbrev hessCharPoly : R[X] := hessP n H n

variable {n H}

theorem hessP_zero : hessP n H 0 = 1 := by
  simp only [hessP]

theorem hessP_succ (k : ℕ) :
    hessP n H (k + 1) =
      (X - C (H.getD (n * k + k) 0)) * hessP n H k -
        ∑ t : Fin k, C (H.getD (n * (t : ℕ) + k) 0 *
          ∏ j ∈ Finset.Ico (t : ℕ) k, H.getD (n * (j + 1) + j) 0) *
          hessP n H (t : ℕ) := by
  simp only [hessP]

theorem hessCharPoly_eq : hessCharPoly n H = hessP n H n := rfl

/-! ## The recurrence on coefficient lists

This section defines the recurrence on a polynomial representation (lists of coefficients) that the
kernel can compute.
-/

variable (n H)

/-- Compute the coefficients of `∑_{t ≤ i} H[t][k] · r · (∏_{j=t}^{i-1} H[j+1][j]) · p_t` by
recursion on `i`, where `p_t` is the polynomial defined in the coefficient list `ps[t]`. `r`
accumulates the product of `H[i+1][i]` entries at each step. -/
@[expose]
def coeffHessSum (k : ℕ) :
    (i : ℕ) → (r : R) → (ps : Array (List R)) → List R
  | 0, r, ps => (ps.getD 0 []).map (H.getD (n * 0 + k) 0 * r * ·)
  | i + 1, r, ps =>
    List.zipWithAll (fun a b => a.getD 0 + b.getD 0)
      ((ps.getD (i + 1) []).map (H.getD (n * (i + 1) + k) 0 * r * ·))
      (coeffHessSum k i (r * H.getD (n * (i + 1) + i) 0) ps)

/-- Compute the coefficients of `pₖ` from the coefficient lists of `p₀, ..., p_{k-1}`. The
coefficients of each polynomial are stored as a `List R` in `ps`. -/
@[expose]
def coeffHessStep (k : ℕ) (ps : Array (List R)) : List R :=
  match k with
  | 0 => [1]
  | 1 =>
    List.zipWithAll (fun a b => a.getD 0 - b.getD 0) (0 :: ps.getD 0 [])
      ((ps.getD 0 []).map (H.getD (n * 0 + 0) 0 * ·))
  | k' + 2 =>
    List.zipWithAll (fun a b => a.getD 0 - b.getD 0)
      (List.zipWithAll (fun a b => a.getD 0 - b.getD 0) (0 :: ps.getD (k' + 1) [])
        ((ps.getD (k' + 1) []).map (H.getD (n * (k' + 1) + (k' + 1)) 0 * ·)))
      (coeffHessSum n H (k' + 1) k' (H.getD (n * (k' + 1) + k') 0) ps)

/-- Compute the coefficients of `hessCharPoly n H`. -/
@[expose]
def coeffHessCharPoly : List R :=
  ((fun ps => ps.push (coeffHessStep n H ps.size ps))^[n] #[[1]]).getD n []

variable {n H}

theorem ofCoeffList_coeffHessSum (k : ℕ) :
    ∀ (i : ℕ) (r : R) (ps : Array (List R)),
      ofCoeffList (coeffHessSum n H k i r ps) =
        ∑ t : Fin (i + 1),
          C (H.getD (n * (t : ℕ) + k) 0 *
              (r * ∏ j ∈ Finset.Ico (t : ℕ) i, H.getD (n * (j + 1) + j) 0)) *
            ofCoeffList (ps.getD (t : ℕ) [])
  | 0, r, ps => by simp [coeffHessSum]
  | i + 1, r, ps => by
    rw [coeffHessSum, ofCoeffList_zipWithAll_add, ofCoeffList_coeffHessSum,
      Fin.sum_univ_succAbove _ (.last (i + 1))]
    congrm ?_ + ∑ t, ?_ <;> simp [Finset.prod_Ico_succ_top, Fin.is_le]
    ring

theorem ofCoeffList_coeffHessStep (k : ℕ) (ps : Array (List R)) :
    ofCoeffList (coeffHessStep n H (k + 1) ps) =
      (X - C (H.getD (n * k + k) 0)) * ofCoeffList (ps.getD k []) -
        ∑ t : Fin k,
          C (H.getD (n * (t : ℕ) + k) 0 * ∏ j ∈ Finset.Ico (t : ℕ) k, H.getD (n * (j + 1) + j) 0) *
            ofCoeffList (ps.getD (t : ℕ) []) := by
  cases k with
  | zero =>
    simp [coeffHessStep, sub_mul]
  | succ k =>
    rw [coeffHessStep, ofCoeffList_zipWithAll_sub, ofCoeffList_zipWithAll_sub,
      ofCoeffList_zero_cons, ofCoeffList_map_mul, ofCoeffList_coeffHessSum, sub_mul]
    congrm _ - ∑ t, ?_
    rw [Finset.prod_Ico_succ_top (Nat.lt_succ_iff.mp t.isLt)]
    simp only [map_mul]
    ring

@[simp]
theorem ofCoeffList_coeffHessCharPoly :
    ofCoeffList (coeffHessCharPoly n H) = hessCharPoly n H := by
  let f (ps : Array (List R)) := ps.push (coeffHessStep n H ps.size ps)
  have hsize k : (f^[k] #[[1]]).size = k + 1 := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Array.size_push, ih]
  suffices ∀ k, ∀ m ≤ k, ofCoeffList ((f^[k] #[[1]]).getD m []) = hessP n H m from this n n le_rfl
  intro k
  induction k with
  | zero => simp [ofCoeffList_cons, hessP_zero]
  | succ k ih =>
    intro m hm
    rw [Function.iterate_succ_apply', Array.getD_eq_getD_getElem?, Array.getElem?_push, hsize]
    split_ifs with hmk
    · rw [Option.getD_some, hmk, ofCoeffList_coeffHessStep, hessP_succ]
      aesop
    · rw [← Array.getD_eq_getD_getElem?, ih m (by lia)]

end Mathlib.Tactic.Hessenberg

end
