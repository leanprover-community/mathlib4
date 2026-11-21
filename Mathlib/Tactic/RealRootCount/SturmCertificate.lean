/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Data.List.SignVariations

/-!
# A certificate for a Sturm sequence

A `SturmCertificate` describes the Sturm sequence of a polynomial with integer coefficients and its
derivative, up to positive factors. `realRootCount?` validates the certificate and returns the
number of distinct real roots of the polynomial.

## Main definitions

- `SturmCertificate`: the certificate.
- `checkSturm`: check that the `SturmCertificate` represents a valid Sturm sequence.
- `realRootCount?`: validate the certificate and compute the number of distinct real roots of the
  certificate's polynomial.
- `realRootCountIoo?`: validate the certificate and compute the number of distinct real roots in an
  open interval with rational endpoints of the certificate's polynomial.

## Implementation Notes

Definitions are exposed because `realRootCount? d = some n` is intended to be unfolded in a kernel
computation.

## Representation of polynomials

A polynomial is represented by the list of its coefficients, constant term first, as in
`Polynomial.ofCoeffList`. For example the list `[2, -4, 0, 0, 0, 1]` represents `X ^ 5 - 4 * X + 2`.
A list may end in zeros, so `coeffLead p` is the leading coefficient only when it is nonzero.
-/

@[expose] public section

namespace Mathlib.Tactic.RealRootCount

variable {R : Type*}

/-- The derivative of the polynomial that `p` represents. -/
def coeffDerivative [Semiring R] (p : List R) : List R :=
  (p.tail.zipIdx 1).map fun x => x.2 * x.1

/-- The last entry of `p`, or `0` for `[]`. When it is nonzero, it is the leading coefficient of
the polynomial that `p` represents. -/
def coeffLead [Zero R] (p : List R) : R := p.getLastD 0

/-- The coefficient list of `c * p + q`. -/
def coeffAddSmul [Semiring R] (c : R) : List R → List R → List R
  | [], q => q
  | x :: p, [] => c * x :: coeffAddSmul c p []
  | x :: p, y :: q => (c * x + y) :: coeffAddSmul c p q

/-- The coefficient list of `p * q`. -/
def coeffMul [Semiring R] (p q : List R) : List R :=
  p.foldr (fun c acc => coeffAddSmul c q (0 :: acc)) []

/-- A step of the Sturm sequence.

`r` is a polynomial which satisfies the equation `a * p + b * q + c * r = 0` and `r` is of lower
degree than `q`. It follows from these two conditions that `r = (a / c) * (- p % q)` and so if `p`
and `q` are positive multiples of consecutive entries of a Sturm sequence then `r` is a positive
multiple of the next entry. -/
structure SturmStep where
  /-- The positive integer factor of `p`. -/
  a : ℤ
  /-- The coefficients of the polynomial factor `b` of `q`. -/
  b : List ℤ
  /-- The positive integer factor of `r`. -/
  c : ℤ
  /-- The coefficients of `r`, a positive multiple of the next entry in the Sturm sequence. -/
  r : List ℤ

namespace SturmStep

/-- Check that the `SturmStep` is valid for the two previous Sturm sequence entries `p` and `q`:
`a` and `c` are positive, `r` is of lower degree than `q` and `a * p + b * q + c * r = 0`. The
equation is checked by computing the coefficient list of its left-hand side. -/
def check (s : SturmStep) (p q : List ℤ) : Bool :=
  0 < s.a &&
  0 < s.c &&
  coeffLead q != 0 &&
  s.r.length < q.length &&
  (coeffAddSmul s.c s.r (coeffAddSmul s.a p (coeffMul s.b q))).all (· == 0)

end SturmStep

/-- A certificate that a list of polynomials is the Sturm sequence of some polynomial `f` and its
derivative up to positive scaling factors. -/
structure SturmCertificate where
  /-- A positive integer such that `k * f` has integer coefficients. -/
  k : ℕ
  /-- The coefficient list of `k * f`. -/
  s : List ℤ
  /-- The steps that give the entries of the Sturm sequence after `s` and its derivative. -/
  steps : List SturmStep

/-- The sequence of polynomials that starts with `p` and `q` and continues with the `r` of each
`SturmStep`, without the last one. In steps that pass `checkSteps` the last `r` is the zero
entry `[]` that ends the sequence. -/
def chain (p q : List ℤ) : List SturmStep → List (List ℤ)
  | [] => [p]
  | s :: ss => p :: chain q s.r ss

/-- The sequence of polynomials of the Sturm sequence that the certificate describes. -/
def SturmCertificate.entries (d : SturmCertificate) : List (List ℤ) :=
  chain d.s (coeffDerivative d.s) d.steps

/-- Check each step in the Sturm sequence that starts with `p` and `q`, and that the sequence
ends with the zero entry `[]`. -/
def checkSteps : List ℤ → List ℤ → List SturmStep → Bool
  | _, [], [] => true
  | p, q, s :: ss => s.check p q && checkSteps q s.r ss
  | _, _, _ => false

/-- Check that the `SturmCertificate` represents a valid Sturm sequence. -/
def checkSturm (d : SturmCertificate) : Bool :=
  0 < d.k && coeffLead d.s != 0 && checkSteps d.s (coeffDerivative d.s) d.steps

/-- Compute the number of real roots of the polynomial in the `SturmCertificate`.
The function returns `none` if the certificate is invalid. -/
def realRootCount? (d : SturmCertificate) : Option ℕ :=
  let sturmSeq := d.entries
  let atTop := (sturmSeq.map coeffLead).signVariations
  let atBot :=
    (sturmSeq.map fun e => let l := coeffLead e; if e.length % 2 = 0 then -l else l).signVariations
  if checkSturm d then some (atBot - atTop) else none

/-- Compute the integer `d ^ (p.length - 1) * f (n / d)`, where `f` is the polynomial
that `p` represents and d > 0. -/
def evalScaled (n : ℤ) (d : ℕ) (p : List ℤ) : ℤ :=
  match p with
  | [] => 0
  | c :: p => c * d ^ p.length + n * evalScaled n d p

/-- Compute the number of real roots of the polynomial in the `SturmCertificate` that are in the
open interval from `an / ad` to `bn / bd`.  The function returns `none` if the certificate is
invalid, `ad` or `bd` is zero, `an / ad < bn / bd` is false, or an endpoint is a root of the
certificate's polynomial. -/
def realRootCountIoo? (d : SturmCertificate) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) : Option ℕ :=
  let sturmSeq := d.entries
  let atA := (sturmSeq.map (evalScaled an ad)).signVariations
  let atB := (sturmSeq.map (evalScaled bn bd)).signVariations
  if checkSturm d && 0 < ad && 0 < bd && an * bd < bn * ad && evalScaled an ad d.s != 0 &&
      evalScaled bn bd d.s != 0 then some (atA - atB) else none

end Mathlib.Tactic.RealRootCount

end
