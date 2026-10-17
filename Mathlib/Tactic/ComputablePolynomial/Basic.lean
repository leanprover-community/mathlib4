/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ring

/-!
# Computable univariate polynomials (`SparsePoly`): definition and addition

A computational representation of univariate polynomials over a commutative ring `R` with
`DecidableEq R`. A `SparsePoly R` is stored as a list of `(exponent, coefficient)` pairs in `ℕ × R`
with the exponents in strictly decreasing order and all coefficients nonzero (so the zero
polynomial is the empty list). This invariant makes the representation canonical.

This file defines the structure, the semantics `toPoly : SparsePoly R → Polynomial R`, and
addition. Further files in this directory build up to a `CommRing` instance, an `AlgEquiv` with
`Polynomial R`, division, and the reflection tactics (`poly_decide`, `poly_eval`, `poly_dvd`),
for which this library is the computational backend.

## Implementation notes

`DecidableEq R` is required so that zero coefficients can be recognised and dropped, keeping the
list canonical (hence equality of `SparsePoly R` is decidable by structural comparison).

J. Davenport notes that Lean permits the trivial ring (in which `0 = 1`); supporting it here costs
extra case analysis, and one may wish to rethink whether to allow it.

## Provenance

Started by Mario Carneiro at the Hausdorff Institute, June 2024, with design notes and an
original Lean prototype by James Davenport
(https://github.com/JamesHDavenport/Dagstuhl23401, `verify-irred/VerifyIrred`); the
multivariate analogue (`MvSparsePoly`) and the reflection tactics were developed subsequently.
-/

@[expose] public section

/-- A computable univariate polynomial over `R`, stored as a list of `(exponent, coefficient)`
pairs with exponents in strictly decreasing order and all coefficients nonzero (so the zero
polynomial is `[]`). These invariants make the representation canonical. -/
@[ext] structure SparsePoly (R : Type) [CommRing R] : Type where
  /-- The underlying list of `(exponent, coefficient)` pairs, ordered by strictly decreasing
  exponent with all coefficients nonzero. -/
  coeffs : List (ℕ × R)
  sorted : coeffs.Pairwise (·.1 > ·.1)
  nonzero : ∀ x ∈ coeffs, x.2 ≠ 0

namespace SparsePoly
open Polynomial

variable {R}

instance [CommRing R] [Lean.ToFormat R] : Lean.ToFormat (SparsePoly R) where
  format x :=
    have := x.coeffs.foldl (init := none) fun (f : Option Lean.Format) (i, x) =>
      let monomial := if i = 0 then f!"({x})" else if i = 1 then f!"({x})*X" else f!"({x})*X^{i}"
      match f with
      | none => monomial
      | some f => f ++ " + " ++ monomial
    this.getD f!"0"

variable [CommRing R] [DecidableEq R]
/-- Builds a `SparsePoly R` from a list already sorted by strictly decreasing exponent, dropping
any pairs with zero coefficient to restore the canonical invariant. -/
def ofSortedList
    (coeffs : List (ℕ × R)) (sorted : coeffs.Pairwise (·.1 > ·.1)) :
    SparsePoly R where
  coeffs := coeffs.filter (·.2 ≠ 0)
  sorted := sorted.sublist (List.filter_sublist)
  nonzero := by simp [List.mem_filter]

theorem ofSortedList_of_nonzero {R : Type} [CommRing R] [DecidableEq R]
    (coeffs : List (ℕ × R)) (nonzero : ∀ x ∈ coeffs, x.2 ≠ 0) (sorted) :
    (ofSortedList coeffs sorted).coeffs = coeffs := by
  simp (config := {contextual := true}) [ofSortedList, nonzero]

instance : Zero (SparsePoly R) where
  zero := { coeffs := [], sorted := .nil, nonzero := nofun }

/-- The constant polynomial. `ofSortedList` drops the term when `r = 0`. -/
def C (r : R) : SparsePoly R := ofSortedList [(0, r)] (List.pairwise_singleton _ _)

instance : One (SparsePoly R) where
  one := C 1

/-- `degLt a l` holds when every pair in `l` has exponent strictly less than `a`. -/
def degLt (a : ℕ) (l : List (ℕ × R)) : Prop := ∀ x ∈ l, x.1 < a

/-- Interprets a list of `(exponent, coefficient)` pairs as the Mathlib polynomial
`∑ Polynomial.C a * Polynomial.X ^ i`. -/
noncomputable def toPolyCore : List (ℕ × R) → R[X]
  | [] => 0
  | (i, a) :: x => Polynomial.C a * Polynomial.X^i + toPolyCore x

/-- The Mathlib `Polynomial R` represented by a `SparsePoly R`. -/
noncomputable def toPoly (x : SparsePoly R) : Polynomial R :=
  toPolyCore x.coeffs

/-- Adds two exponent-sorted coefficient lists by merging on exponent, summing coefficients on
matching exponents and dropping any term whose sum is zero. -/
def addCore : List (ℕ × R) → List (ℕ × R) → List (ℕ × R)
  | [], yy => yy
  | xx, [] => xx
  | xx@((i, a) :: x), yy@((j, b) :: y) =>
    if i < j then
      (j, b) :: addCore xx y
    else if j < i then
      (i, a) :: addCore x yy
    else
      ( fun c => if c=0 then addCore x y else (i, c) :: addCore x y) (a+b)
    termination_by xx yy => xx.length + yy.length

theorem addCore_degLt {n : ℕ} : ∀ {x y : List (ℕ × R)},
    degLt n x → degLt n y → degLt n (addCore x y)
  | [], yy, _, hy => by
    unfold addCore
    exact hy
  | (i, a) :: x, [], hx, _ => by
    unfold addCore
    exact hx
  | xx@((i, a) :: x), yy@((j, b) :: y), hx, hy => by
    have hx_head : i < n := hx (i, a) List.mem_cons_self
    have hx_tail : degLt n x := fun e he => hx e (List.mem_cons_of_mem _ he)
    have hy_head : j < n := hy (j, b) List.mem_cons_self
    have hy_tail : degLt n y := fun e he => hy e (List.mem_cons_of_mem _ he)
    unfold addCore
    split
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact hy_head
      · exact addCore_degLt hx hy_tail e he
    · split
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact hx_head
        · exact addCore_degLt hx_tail hy e he
      · dsimp only
        split
        · exact addCore_degLt hx_tail hy_tail
        · intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact hx_head
          · exact addCore_degLt hx_tail hy_tail e he
termination_by x y => x.length + y.length

theorem addCore_sorted : ∀ {x y : List (ℕ × R)},
    x.Pairwise (·.1 > ·.1) → y.Pairwise (·.1 > ·.1) →
    (addCore x y).Pairwise (·.1 > ·.1)
  | [], yy, _, hy => by
    unfold addCore
    exact hy
  | (i, a) :: x, [], hx, _ => by
    unfold addCore
    exact hx
  | xx@((i, a) :: x), yy@((j, b) :: y), hx, hy => by
    have ⟨hi, hx'⟩ := List.pairwise_cons.1 hx
    have ⟨hj, hy'⟩ := List.pairwise_cons.1 hy
    unfold addCore
    split
    · next ij =>
      constructor
      · apply addCore_degLt
        · intro
          | _, .head _ => exact ij
          | p, .tail _ hp => exact (hi _ hp).trans ij
        · exact hj
      · exact addCore_sorted hx hy'
    · split
      · next ji =>
        constructor
        · apply addCore_degLt
          · exact hi
          · intro
            | _, .head _ => exact ji
            | p, .tail _ hp => exact (hj _ hp).trans ji
        · exact addCore_sorted hx' hy
      · cases (by omega : i = j)
        dsimp only
        split
        · exact addCore_sorted hx' hy'
        · constructor
          · exact addCore_degLt hi hj
          · exact addCore_sorted hx' hy'
termination_by x y => x.length + y.length

instance : Add (SparsePoly R) where
  add x y :=
    let coeffs := addCore x.coeffs y.coeffs
    ofSortedList coeffs (addCore_sorted x.sorted y.sorted)

end SparsePoly
