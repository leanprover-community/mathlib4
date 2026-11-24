/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public meta import Mathlib.Algebra.Field.Rat
public meta import Mathlib.Tactic.RealRootCount.SturmCertificate

/-!
# Computing a Sturm sequence and its certificate

This file provides the definitions required to compute a `SturmCertificate`, which describes the
Sturm sequence of a polynomial with rational coefficients and its derivative, up to positive
factors.

## Main definitions

- `SturmCertificate.fromCoeffList`: computes the factor that clears the denominators of a
  coefficient list, and the `SturmCertificate` for the resulting polynomial.
-/

namespace Mathlib.Tactic.RealRootCount

meta section

/-- The least common multiple of the denominators of elements of `p`. -/
def lcmDen (p : List ℚ) : ℕ := p.foldl (fun d x => d.lcm x.den) 1

/-- The greatest common divisor of the numerators of elements of `p`. -/
def gcdNum (p : List ℚ) : ℕ := p.foldl (fun g x => g.gcd x.num.natAbs) 0

/-- Compute `k > 0` such that the elements of `k • p` are coprime integers, or `1` if `p` contains
no nonzero elements. -/
def primitiveFactor (p : List ℚ) : ℚ :=
  let g := gcdNum p
  if g = 0 then 1 else lcmDen p / g

/-- Compute the division over `ℚ` of the polynomials that `p` and `q` represent.

Returns `(quot, rem)` which satisfies `p = quot * q + rem` and `rem` has lower degree than `q`.
Division by the zero polynomial is defined as: `divMod p [] = ([], p)`. -/
def divMod (p q : List ℚ) : List ℚ × List ℚ := Id.run do
  let trim (p : List ℚ) := (p.reverse.dropWhile (· == 0)).reverse
  let q := trim q
  if q.isEmpty then return ([], trim p)
  let mut rem := trim p
  let mut quot : List ℚ := []
  for _ in [0:rem.length + 1 - q.length] do
    if rem.length < q.length then break
    let c := coeffLead rem / coeffLead q
    let shift := List.replicate (rem.length - q.length) 0
    quot := coeffAddSmul c (shift ++ [1]) quot
    rem := trim (coeffAddSmul (-c) (shift ++ q) rem)
  return (quot, rem)

/-- Compute the next step of the Sturm sequence after `p` and `q` as the primitive part
of `-(p % q)`. -/
def sturmStep (p q : List ℤ) : SturmStep :=
  -- `-p = quot * q + rem` so `rem = -(p % q)` and `p + quot * q + rem = 0`
  let (quot, rem) := divMod (p.map fun x => -(x : ℚ)) (q.map (↑))
  let k := primitiveFactor rem
  let a : ℤ := lcmDen (k⁻¹ :: quot)
  -- by definition of `a`, `a • quot` is a list of integers.
  let b := quot.map fun x : ℚ => (a * x).num
  -- by definition of `a`, `a * k⁻¹` is an integer.
  let c := (a * k⁻¹).num
  -- by definition of `k`, `k • rem` is a list of integers.
  let r := rem.map fun x => (k * x).num
  { a, b, c, r }

/-- Compute the steps of the Sturm sequence of `p` and its derivative. -/
def sturmSteps (p : List ℤ) : List SturmStep := Id.run do
  let mut p := p
  let mut q := coeffDerivative p
  let mut steps := #[]
  for _ in [0:p.length - 1] do
    let s := sturmStep p q
    steps := steps.push s
    if s.r.isEmpty then break
    p := q
    q := s.r
  return steps.toList

/-- Compute `k > 0` such that the elements of `k • p` are integers, and the `SturmCertificate` for
the polynomial with the coefficient list `k • p`. -/
public def SturmCertificate.fromCoeffList (p : List ℚ) : ℕ × SturmCertificate :=
  let k := lcmDen p
  -- by definition of `k`, `k • p` is a list of integers
  let p := p.map fun x : ℚ => (k * x).num
  let steps := sturmSteps p
  (k, { p, steps })

end

end Mathlib.Tactic.RealRootCount
