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

This file contains the computation of the coefficient list of the characteristic polynomial of a
matrix literal, by the recurrence `coeffHessCharpoly` on the Hessenberg matrix of a
`Hessenberg.Similarity` certificate of the matrix, with a proof that `Matrix.charpoly` is the
polynomial with these coefficients.

## Main definitions

- `charpolyCoeffList`: computes the coefficient list of the characteristic polynomial of a matrix
  literal with a proof that `Matrix.charpoly` is the polynomial with these coefficients.
- `CoeffListResult`: the coefficient list literal of a matrix literal, with its proof.
- `inferCharpolyRing`: checks that the characteristic polynomial computation can be performed on
  `S`.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Hessenberg

/-- The instances of a commutative ring `S` required to compute the characteristic polynomial. -/
structure CharpolyRing {u : Level} (S : Q(Type u)) where
  /-- The commutative ring instance on `S`. -/
  cS : Q(CommRing $S)
  /-- `ℚ` is an `S`-algebra. -/
  aS : Q(Algebra $S ℚ)
  /-- The algebra map `S → ℚ` is injective. -/
  fS : Q(FaithfulSMul $S ℚ)

/-- Check that the commutative ring `S` has the instances available for the characteristic
polynomial to be computed. -/
def inferCharpolyRing {u : Level} (S : Q(Type u)) (cS : Q(CommRing $S)) :
    MetaM (Except MessageData (CharpolyRing S)) := do
  let .some aS ← trySynthInstanceQ q(Algebra $S ℚ)
    | return .error m!"expected an `{q(Algebra $S ℚ)}` instance"
  let .some fS ← trySynthInstanceQ q(FaithfulSMul $S ℚ)
    | return .error m!"expected a `{q(FaithfulSMul $S ℚ)}` instance"
  return .ok { cS, aS, fS }

/-- The coefficient list of the characteristic polynomial of the matrix literal `A` and a proof that
it's equal to `Matrix.charpoly`. -/
structure CoeffListResult {u : Level} {S : Q(Type u)} (cS : Q(CommRing $S)) {n : ℕ}
    (A : Q(Matrix (Fin $n) (Fin $n) $S)) where
  /-- The list literal of the coefficients, constant term first. -/
  cs : Q(List $S)
  /-- The proof that `cs` is the coefficient list of the characteristic polynomial. -/
  charpoly_eq : Q(Matrix.charpoly $A = Polynomial.ofCoeffList $cs)

/-- Compute the coefficient list of the characteristic polynomial of the matrix literal `A` with
rows of entries `entries` with a proof that `Matrix.charpoly A` is the polynomial with these
coefficients. -/
def charpolyCoeffList {u : Level} (S : Q(Type u)) (r : CharpolyRing S) (n : ℕ)
    (A : Q(Matrix (Fin $n) (Fin $n) $S)) (entries : Array (Array Expr)) :
    MetaM (CoeffListResult r.cS A) := do
  have ⟨_cS, _aS, _fS⟩ := r
  let evalEntry (e : Q($S)) : MetaM ℚ := do
    let some v := (← Mathlib.Meta.NormNum.derive e).toRat
      | throwError "the following entry cannot be evaluated to a rational{indentExpr e}"
    return v
  let ⟨cert, Harr, hH, red⟩ ← mkHessenbergSimilarity q(algebraMap $S ℚ) n A entries evalEntry

  -- The coefficients of the characteristic polynomial pulled back to `S`.
  have cs : Q(List $S) :=
    mkListLitQ (← (coeffHessCharpoly n red.H.flatten).mapM (mkRatNumeralQ S))

  let hcs ← mkDecideProofQ q(coeffHessCharpoly $n $Harr = ($cs).map (algebraMap $S ℚ))
  have hq : Q(Matrix.charpoly (($A).map (algebraMap $S ℚ)) =
      Polynomial.ofCoeffList (($cs).map (algebraMap $S ℚ))) :=
    q(((($cert).charpoly_eq.symm.trans
          (charpoly_eq_hessCharpoly ($cert).H ($cert).isUpperHessenberg)).trans
        (ofCoeffList_coeffHessCharpoly (n := $n)).symm).trans
      (congrArg Polynomial.ofCoeffList ((congrArg (coeffHessCharpoly $n) $hH).trans $hcs)))
  have charpoly_eq : Q(Matrix.charpoly $A = Polynomial.ofCoeffList $cs) :=
    q(Polynomial.map_injective (algebraMap $S ℚ) (FaithfulSMul.algebraMap_injective $S ℚ)
      ((Matrix.charpoly_map $A (algebraMap $S ℚ)).symm.trans
        (($hq).trans (Polynomial.map_ofCoeffList (algebraMap $S ℚ) $cs).symm)))
  return { cs, charpoly_eq }

end Mathlib.Tactic.Hessenberg
