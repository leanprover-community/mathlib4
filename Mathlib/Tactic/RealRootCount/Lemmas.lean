/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.Sturm.RootCount
public import Mathlib.Tactic.RealRootCount.CoeffList

/-!
# Checking the `real_root_count` certificate coefficient lists
-/

@[expose] public section

open Polynomial SignType Mathlib.Tactic.RealRootCount.CoeffList

namespace Mathlib.Tactic.RealRootCount

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- Drop trailing zeros. -/
def trim (l : List K) : List K := (l.reverse.dropWhile (· == 0)).reverse

/-- The remainder `-s - d * t` of `-s` divided by `t`, given the quotient `d`. -/
def rem (s t d : List K) : List K := trim (add (neg s) (neg (mul d t)))

/-- `chain s t ds` is `[s, t, r₂, r₃, …]`: each next entry is the remainder `rem` of the previous
two by the next quotient in `ds`, stopping when it is zero (`[]`). When `checkSturm s t ds` holds,
this is the Sturm sequence of `s` and `t`. -/
def chain : List K → List K → List (List K) → List (List K)
  | s, [], _ => [s]
  | s, t, [] => [s, t]
  | s, t, d :: ds => s :: chain t (rem s t d) ds

/-- `checkSturm s t ds` checks that `chain s t ds` is the Sturm sequence of `s` and `t`: every
entry is nonzero, each remainder is shorter than its divisor, and the last remainder is zero. -/
def checkSturm : List K → List K → List (List K) → Bool
  | s, [], [] => decide (lead s ≠ 0)
  | s, t, d :: ds =>
    let r := rem s t d
    decide (lead s ≠ 0) && decide (r.length < t.length) && checkSturm t r ds
  | _, _, _ => false

end Field

/-- The number of sign variations of a sequence of coefficient lists at `x`. -/
def variations (c : List (List ℚ)) (x : ℚ) : ℕ := (c.map (CoeffList.eval x)).signVariations

/-- `B ≥ 1` bounds the roots of `l` by Cauchy's bound: `|cᵢ| ≤ (B - 1) * |cₙ|`. -/
def checkBound (l : List ℚ) (B : ℚ) : Bool :=
  decide (1 ≤ B) && decide (lead l ≠ 0) &&
    l.dropLast.all fun c => decide (|c| ≤ (B - 1) * |lead l|)

/-- The real polynomial of a rational coefficient list. -/
noncomputable abbrev toReal (l : List ℚ) : ℝ[X] := (ofCoeffList l).map (algebraMap ℚ ℝ)

/-! Each lemma below turns one check into one field of a `Polynomial.RootCountCert`. -/

/-- The `sturmSeq_eq` field: a successful `checkSturm` gives the Sturm sequence of `toReal l`. -/
theorem sturmSeq_of_check {l : List ℚ} {ds : List (List ℚ)}
    (h : checkSturm l (CoeffList.derivative l) ds = true) :
    sturmSeq (toReal l) (Polynomial.derivative (toReal l)) =
      (chain l (CoeffList.derivative l) ds).map toReal := by
  sorry

/-- The `root_bound` field: a successful `checkBound` bounds the real roots of `toReal l`. -/
theorem abs_lt_of_checkBound {l : List ℚ} {B : ℚ} (h : checkBound l B = true) :
    ∀ x, (toReal l).IsRoot x → |x| < B := by
  sorry

/-- The `variations` field: sign variations computed on the lists are those of the real
polynomials. -/
theorem variations_of_check {L : List (List ℚ)} {B : ℚ} {n : ℕ}
    (h : variations L (-B) = variations L B + n) :
    ((L.map toReal).map (sign ∘ Polynomial.eval (-(B : ℝ)))).signVariations =
      ((L.map toReal).map (sign ∘ Polynomial.eval (B : ℝ))).signVariations + n := by
  sorry

end Mathlib.Tactic.RealRootCount
