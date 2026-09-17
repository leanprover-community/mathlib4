/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public meta import Mathlib.Tactic.Hessenberg.Charpoly
public import Mathlib.Tactic.Hessenberg.Charpoly  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Hessenberg.Similarity

/-!
# Coefficient lists of characteristic polynomials from Hessenberg certificates

This file contains `charpolyCoeffList`, which computes the coefficient list of the characteristic
polynomial of a matrix literal over `ℚ` with its proof: the kernel evaluates `coeffHessCharpoly` on
the row-major array of the Hessenberg matrix of a `Hessenberg.Similarity` certificate.

## Main definitions

- `charpolyCoeffList`: the coefficient list of the characteristic polynomial of a matrix literal
  over `ℚ`, with its proof.
- `CoeffListResult`: the coefficient list together with its literal and proof.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Hessenberg

/-- The coefficient list of the characteristic polynomial of the matrix literal `M` over `ℚ`, with
its proof. -/
structure CoeffListResult {n : ℕ} (M : Q(Matrix (Fin $n) (Fin $n) ℚ)) where
  /-- The coefficients, constant term first. -/
  coeffs : List ℚ
  /-- The list literal of `coeffs`. -/
  cs : Q(List ℚ)
  /-- The proof that `cs` is the coefficient list of the characteristic polynomial. -/
  charpoly_eq : Q(Matrix.charpoly $M = Polynomial.ofCoeffList $cs)

/-- The coefficient list of the characteristic polynomial of the `n × n` matrix literal `M` over `ℚ`
with rows of entries `entries`: the kernel evaluates `coeffHessCharpoly` on the row-major array of
the Hessenberg matrix of the certificate. -/
def charpolyCoeffList (n : ℕ) (M : Q(Matrix (Fin $n) (Fin $n) ℚ)) (entries : Array (Array Expr)) :
    MetaM (CoeffListResult M) := do
  let ⟨cert, Harr, hH, red⟩ ← mkHessenbergSimilarity n M entries
  let coeffs := coeffHessCharpoly n red.H.flatten
  have cs : Q(List ℚ) := mkListLitQ (← coeffs.mapM (mkRatNumeralQ q(ℚ)))
  let hcs ← mkDecideProofQ q(coeffHessCharpoly $n $Harr = $cs)
  -- `M.charpoly = cert.H.charpoly = hessCharpoly n cert.H.toArray`, interpreted as a polynomial
  -- with `ofCoeffList`, then the coefficient list is replaced by its value
  have charpoly_eq : Q(Matrix.charpoly $M = Polynomial.ofCoeffList $cs) :=
    q(((($cert).charpoly_eq.symm.trans
          (charpoly_eq_hessCharpoly ($cert).H ($cert).isUpperHessenberg)).trans
        (ofCoeffList_coeffHessCharpoly (n := $n)).symm).trans
      (congrArg Polynomial.ofCoeffList ((congrArg (coeffHessCharpoly $n) $hH).trans $hcs)))
  return { coeffs, cs, charpoly_eq }

end Mathlib.Tactic.Hessenberg
