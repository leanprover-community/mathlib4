/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.List.SignVariations

/-!
# A certificate for a Sturm sequence

A `SturmCertificate` describes the Sturm sequence of a polynomial with integer coefficients and its
derivative, up to positive factors. `realRootCount?` validates the certificate and returns the
number of distinct real roots of the polynomial.

`SturmCertificate.fromCoeffList` computes the certificate for a polynomial with rational
coefficients, after clearing the denominators of its coefficients.

## Main definitions

- `SturmCertificate`: the certificate.
- `SturmCertificate.entries?`: validate the certificate and compute the entries of the Sturm
  sequence that it describes.
- `realRootCount?`: validate the certificate and compute the number of distinct real roots of the
  certificate's polynomial.
- `realRootCountIoo?`: validate the certificate and compute the number of distinct real roots in an
  open interval with rational endpoints of the certificate's polynomial.
- `SturmCertificate.fromCoeffList`: computes the factor that clears the denominators of a
  coefficient list, and the `SturmCertificate` for the resulting polynomial.

## Implementation Notes

The definitions that validate a certificate are exposed because `realRootCount? d = some n` is
intended to be unfolded in a kernel computation.

## Representation of polynomials

A polynomial is represented by the list of its coefficients, constant term first, as in
`Polynomial.ofCoeffList`. For example the list `[2, -4, 0, 0, 0, 1]` represents `X ^ 5 - 4 * X + 2`.
A list may end in zeros, so `coeffLead p` is the leading coefficient only when it is nonzero.
-/

public section

namespace Mathlib.Tactic.RealRootCount

@[expose] section

/-! ### Validating a certificate -/

variable {R : Type*}

/-- The derivative of the polynomial that `p` represents.

`ofCoeffList (coeffDerivative p) = derivative (ofCoeffList p)` -/
def coeffDerivative [Semiring R] (p : List R) : List R :=
  (p.tail.zipIdx 1).map fun x => x.2 * x.1

/-- The last entry of `p`, or `0` for `[]`. When it is nonzero, it is the leading coefficient of
the polynomial that `p` represents.

`coeffLead p ≠ 0 → (ofCoeffList p).leadingCoeff = coeffLead p` -/
def coeffLead [Zero R] (p : List R) : R := p.getLastD 0

/-- The coefficient list of `c • p + q`.

`ofCoeffList (coeffAddSmul c p q) = c • ofCoeffList p + ofCoeffList q` -/
def coeffAddSmul [Semiring R] (c : R) : List R → List R → List R
  | [], q => q
  | x :: p, [] => c * x :: coeffAddSmul c p []
  | x :: p, y :: q => (c * x + y) :: coeffAddSmul c p q

/-- The coefficient list of `p * q`.

`ofCoeffList (coeffMul p q) = ofCoeffList p * ofCoeffList q` -/
def coeffMul [Semiring R] (p q : List R) : List R :=
  p.foldr (fun c acc => coeffAddSmul c q (0 :: acc)) []

/-- A step of a Sturm sequence.

Let `p` and `q` be positive multiples of two consecutive entries of a Sturm sequence. `SturmStep`
stores `a`, `b`, `c` and `r` that satisfy `a • p + b * q + c • r = 0`, where `a` and `c` are
positive and `r` is of lower degree than `q`.

These conditions give `r = (a / c) • (-p % q)`, i.e. `r` is a positive multiple of the next entry
in the sequence. -/
structure SturmStep where
  /-- The positive integer that multiplies `p`. -/
  a : ℤ
  /-- The coefficient list of the polynomial that multiplies `q`. -/
  b : List ℤ
  /-- The positive integer that multiplies `r`. -/
  c : ℤ
  /-- The coefficient list of a positive multiple of the next entry of the Sturm sequence. -/
  r : List ℤ

namespace SturmStep

/-- Check that the `SturmStep` is valid for the two previous Sturm sequence entries `p` and `q`:
`a` and `c` are positive, `r` is of lower degree than `q` and `a • p + b * q + c • r = 0`. The
equation is checked by computing the coefficient list of its left-hand side. -/
def check (s : SturmStep) (p q : List ℤ) : Bool :=
  0 < s.a &&
  0 < s.c &&
  coeffLead q != 0 &&
  s.r.length < q.length &&
  (coeffAddSmul s.c s.r (coeffAddSmul s.a p (coeffMul s.b q))).all (· == 0)

end SturmStep

/-- A certificate that a list of polynomials is the Sturm sequence of the polynomial with
coefficient list `p` and its derivative up to positive scaling factors. -/
structure SturmCertificate where
  /-- The coefficient list of the polynomial. -/
  p : List ℤ
  /-- The steps that give the entries of the Sturm sequence after `p` and its derivative. -/
  steps : List SturmStep

/-- Reconstruct the entries of a Sturm sequence from its first two entries `p` and `q` and the list
`steps`, without the final zero remainder. The function returns `none` if a step is invalid or the
sequence does not end with a zero remainder. -/
def sturmEntries? (p q : List ℤ) (steps : List SturmStep) : Option (List (List ℤ)) :=
  match q, steps with
  | [], [] => some [p]
  | q, s :: ss => if s.check p q then (sturmEntries? q s.r ss).map (p :: ·) else none
  | _, _ => none

/-- The sequence of polynomials of the Sturm sequence that the certificate describes.
The function returns `none` if the certificate is invalid. -/
def SturmCertificate.entries? (d : SturmCertificate) : Option (List (List ℤ)) :=
  if coeffLead d.p != 0 then sturmEntries? d.p (coeffDerivative d.p) d.steps else none

/-- Compute the number of distinct real roots of the polynomial in the `SturmCertificate`. The
function returns `none` if the certificate is invalid. -/
def realRootCount? (d : SturmCertificate) : Option ℕ :=
  d.entries?.map fun sturmSeq =>
    let atTop := (sturmSeq.map coeffLead).signVariations
    let atBot := (sturmSeq.map fun e =>
      let l := coeffLead e; if e.length % 2 = 0 then -l else l).signVariations
    atBot - atTop

/-- Compute the integer `d ^ (p.length - 1) * f (n / d)`, where `f` is the polynomial
that `p` represents and `d > 0`.

`evalScaled n d p = d ^ (p.length - 1) * aeval (n / d : ℚ) (ofCoeffList p)` -/
def evalScaled (n : ℤ) (d : ℕ) (p : List ℤ) : ℤ :=
  match p with
  | [] => 0
  | c :: p => c * d ^ p.length + n * evalScaled n d p

/-- Compute the number of distinct real roots of the polynomial in the `SturmCertificate` that are
in the open interval from `an / ad` to `bn / bd`. The function returns `none` if the certificate is
invalid, `ad` or `bd` is zero, `an / ad < bn / bd` is false, or an endpoint is a root of the
certificate's polynomial.

Each endpoint is given by a separate numerator and denominator instead of a rational number because
we want the kernel computation to use integer arithmetic only, and the result does not depend on the
numerator and denominator being coprime. -/
def realRootCountIoo? (d : SturmCertificate) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) : Option ℕ :=
  if 0 < ad && 0 < bd && an * bd < bn * ad && evalScaled an ad d.p != 0 &&
      evalScaled bn bd d.p != 0 then
    d.entries?.map fun sturmSeq =>
      let atA := (sturmSeq.map (evalScaled an ad)).signVariations
      let atB := (sturmSeq.map (evalScaled bn bd)).signVariations
      atA - atB
  else none

end

/-! ### Computing a certificate -/

/-- The least common multiple of the denominators of elements of `p`. -/
private def lcmDen (p : List ℚ) : ℕ := p.foldl (fun d x => d.lcm x.den) 1

/-- The greatest common divisor of the numerators of elements of `p`. -/
private def gcdNum (p : List ℚ) : ℕ := p.foldl (fun g x => g.gcd x.num.natAbs) 0

/-- Compute `k > 0` such that the elements of `k • p` are coprime integers, or `1` if `p` contains
no nonzero elements. -/
private def primitiveFactor (p : List ℚ) : ℚ :=
  let g := gcdNum p
  if g = 0 then 1 else lcmDen p / g

/-- Remove the trailing zeros of `p`. -/
private def trim (p : List ℚ) : List ℚ := (p.reverse.dropWhile (· == 0)).reverse

/-- Compute the division over `ℚ` of the polynomials that `p` and `q` represent.

Returns `(quot, rem)` which satisfies `p = quot * q + rem` and `rem` has lower degree than `q`.
Division by the zero polynomial is defined as: `divMod p [] = ([], p)`. -/
private def divMod (p q : List ℚ) : List ℚ × List ℚ := Id.run do
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
private def sturmStep (p q : List ℤ) : SturmStep :=
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
private def sturmSteps (p : List ℤ) : List SturmStep := Id.run do
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

/-- For the coefficient list `p` of a nonzero polynomial, compute `k > 0` such that the elements of
`k • p` are integers, and the `SturmCertificate` for the polynomial with the coefficient list
`k • p`. -/
def SturmCertificate.fromCoeffList (p : List ℚ) : ℕ × SturmCertificate :=
  let p := trim p
  let k := lcmDen p
  -- by definition of `k`, `k • p` is a list of integers
  let p := p.map fun x : ℚ => (k * x).num
  let steps := sturmSteps p
  (k, { p, steps })

end Mathlib.Tactic.RealRootCount

end
