/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# Sqrt

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

public section

namespace Inclusion

def natSqrt (fuel geuss n : ℕ) : ℕ := match fuel, geuss, n with
  | 0, _, geuss => geuss
  | fuel + 1, n, geuss =>
    let next : ℕ := (geuss + n / geuss) / 2
    if next < geuss then natSqrt fuel n next else geuss

def Interval.sqrt (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic where
  lb := match (I.lb : Option Dyadic) with
    | none => some 0
    | some q =>
      let lbsq : ℕ := (⌊q.toRat * 4 ^ prec⌋).toNat
      let lb : ℕ := natSqrt 8192 lbsq lbsq
      if lb * lb ≤ lbsq then Dyadic.ofIntWithPrec lb prec else 0
  ub := match (I.ub : Option Dyadic) with
    | none => ⊤
    | some q =>
      let ubsq : ℕ := (⌈q.toRat * 4 ^ prec⌉).toNat
      let ub : ℕ := natSqrt 8192 ubsq ubsq
      if ubsq ≤ ub * ub then Dyadic.ofIntWithPrec ub prec
      else if ubsq ≤ (ub + 1) * (ub + 1) then Dyadic.ofIntWithPrec (ub + 1) prec
      else ⊤

theorem Interval.sqrt_mem
    {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I.map Dyadic.toRealOrderEmbedding) (prec : ℕ) :
    √x ∈ (I.sqrt prec).map Dyadic.toRealOrderEmbedding := by
  sorry

@[inclusion_op interval_dyadic_real]
theorem sqrt_mem {x : ℝ} {I : Interval Dyadic} (prec : ℕ) (hx : x ∈ I) : √x ∈ I.sqrt prec :=
  Interval.sqrt_mem hx prec

end Inclusion
