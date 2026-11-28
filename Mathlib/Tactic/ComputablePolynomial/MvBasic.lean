/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.MvDegreesOrder
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Computable multivariate polynomials (`MvSparsePoly`): definition and addition

A computational, sparse, distributed representation of multivariate polynomials over a
commutative ring `R` with `DecidableEq R`: a list of `(exponent-vector, coefficient)` terms kept
strictly decreasing in the monomial order with all coefficients nonzero, giving a canonical
normal form. This file defines the structure, the semantics `toPoly` into Mathlib's
`MvPolynomial (Fin nvars) R`, and addition.

## Implementation notes

`DecidableEq R` is required so that zero coefficients can be recognised and dropped, keeping the
term list canonical.

J. Davenport notes that Lean permits the trivial ring (in which `0 = 1`); supporting it here costs
extra case analysis, and one may wish to rethink whether to allow it.
-/

@[expose] public section

variable {nvars : ℕ}

/-- A computable sparse multivariate polynomial over `R` in `nvars` variables: the list of its
`(exponent-vector, coefficient)` terms, kept strictly decreasing in the monomial order and with all
coefficients non-zero, giving a canonical normal form. -/
@[ext] structure MvSparsePoly (R : Type) [CommRing R] (nvars : ℕ)
    [WOrdering nvars] : Type where
  /-- The list of `(exponent-vector, coefficient)` terms making up the polynomial. -/
  terms : List (MvDegrees nvars × R)
  /-- The terms are strictly decreasing in the monomial order (so degrees are distinct). -/
  sorted : terms.Pairwise (·.1 > ·.1)
  /-- Every stored coefficient is non-zero. -/
  nonzero : ∀ x ∈ terms, x.2 ≠ 0

namespace MvSparsePoly

open MvPolynomial

variable {R : Type} [CommRing R] [DecidableEq R]

/-- Build a polynomial from a sorted term list, dropping zero coefficients. -/
def ofSortedList
    (terms : List (MvDegrees nvars × R)) (sorted : terms.Pairwise (·.1 > ·.1)) :
    MvSparsePoly R nvars where
  terms := terms.filter (·.2 ≠ 0)
  sorted := sorted.sublist List.filter_sublist
  nonzero := by simp [List.mem_filter]

instance : Zero (MvSparsePoly R nvars) where
  zero := { terms := [], sorted := .nil, nonzero := nofun }

/-- The constant polynomial. `ofSortedList` handles `r = 0` (where `0` is the zero of the
`MvDegrees` monoid). -/
def C (r : R) : MvSparsePoly R nvars := ofSortedList [(0, r)] (by simp)

instance : One (MvSparsePoly R nvars) where
  one := C 1

/-- All exponents in a term list are strictly below `a`. -/
def degLt (a : MvDegrees nvars) (l : List (MvDegrees nvars × R)) : Prop :=
  ∀ x ∈ l, x.1 < a

/-- The `Finsupp` underlying an `MvDegrees`, bridging to Mathlib's `MvPolynomial`. -/
noncomputable def MvDegrees.toFinsupp (deg : MvDegrees nvars) : Fin nvars →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i => deg.degrees[i]'(by simp [deg.correct, i.2])) (by simp)

/-- Interpret a raw term list as an honest `MvPolynomial`, by summing the monomials
`monomial (toFinsupp i) a` over the terms. This is the noncomputable semantics against which the
computable operations are proved correct. -/
noncomputable def toPolyCore : List (MvDegrees nvars × R) → MvPolynomial (Fin nvars) R
  | [] => 0
  | (i, a) :: x => monomial (MvDegrees.toFinsupp i) a + toPolyCore x

/-- Interpret an `MvSparsePoly` as the corresponding Mathlib `MvPolynomial`, via `toPolyCore` on its
term list. -/
noncomputable def toPoly (x : MvSparsePoly R nvars) : MvPolynomial (Fin nvars) R :=
  toPolyCore x.terms

/-- Add two sorted term lists by a single merge pass: at each step keep the larger-degree head,
and on equal degrees add the coefficients (dropping the term if the sum is zero). Preserves the
strictly-decreasing sortedness. -/
def addCore : List (MvDegrees nvars × R) → List (MvDegrees nvars × R) → List (MvDegrees nvars × R)
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

/-- `addCore` preserves the `degLt` bound. -/
theorem addCore_degLt {n : MvDegrees nvars} : ∀ {x y : List (MvDegrees nvars × R)},
    degLt n x → degLt n y → degLt n (addCore x y) := by
  intro x y hx hy
  unfold addCore
  split
  · exact hy
  · exact hx
  · next i a x' j b y' =>
    let ⟨hi, hx'⟩ := List.forall_mem_cons.1 hx
    let ⟨hj, hy'⟩ := List.forall_mem_cons.1 hy
    split
    · next ij =>
      unfold degLt
      intro x hx_mem
      cases hx_mem with
      | head => exact hj
      | tail h => exact addCore_degLt hx hy' x (by aesop)
    split
    · next ji =>
      unfold degLt
      intro x hx_mem
      cases hx_mem with
      | head => exact hi
      | tail h => exact addCore_degLt hx' hy x (by aesop)
    · next h_not_ij h_not_ji =>
      dsimp only
      split
      · exact addCore_degLt hx' hy'
      · unfold degLt
        intro x hx_mem
        cases hx_mem with
        | head => exact hi
        | tail h => exact addCore_degLt hx' hy' x (by aesop)
termination_by x y => x.length + y.length

theorem addCore_sorted : ∀ {x y : List (MvDegrees nvars × R)},
    x.Pairwise (·.1 > ·.1) → y.Pairwise (·.1 > ·.1) →
    (addCore x y).Pairwise (·.1 > ·.1) := by
  intro x y hx hy
  unfold addCore
  split
  · exact hy
  · exact hx
  · next i a x j b y =>
    let .cons hi hx' := hx
    let .cons hj hy' := hy
    split
    · next ij =>
      constructor
      · apply addCore_degLt
        · intro
          | _, .head _ => exact ij
          | p, .tail _ hp => exact (hi _ hp).trans ij
        · exact hj
      · exact addCore_sorted hx hy'
    split
    · next ji =>
      constructor
      · apply addCore_degLt
        · exact hi
        · intro
          | _, .head _ => exact ji
          | p, .tail _ hp => exact (hj _ hp).trans ji
      · exact addCore_sorted hx' hy
    · have eq_ij : i = j := by
        rcases lt_trichotomy i j with hlt | heq | hgt
        · contradiction
        · exact heq
        · contradiction
      subst eq_ij
      dsimp only
      split
      · exact addCore_sorted hx' hy'
      · exact .cons (addCore_degLt hi hj) (addCore_sorted hx' hy')
termination_by x y => x.length + y.length

instance : Add (MvSparsePoly R nvars) where
  add x y := ofSortedList (addCore x.terms y.terms) (addCore_sorted x.sorted y.sorted)


end MvSparsePoly
