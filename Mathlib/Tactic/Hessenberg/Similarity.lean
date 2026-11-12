/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public meta import Mathlib.Tactic.Hessenberg.Reduce
public meta import Mathlib.Tactic.Matrix.Cert
public meta import Mathlib.Tactic.Matrix.MulExpand
public import Mathlib.Data.Matrix.Reflection  -- shake: keep (Qq dependency)
public import Mathlib.LinearAlgebra.Matrix.Array  -- shake: keep (Qq dependency)
public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Similarity  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Hessenberg.Reduce
public import Mathlib.Tactic.Matrix.Cert
public import Mathlib.Tactic.Matrix.MulExpand
public import Mathlib.Tactic.Matrix.Swaps

/-!
# Certificate construction for Hessenberg similarity

`mkHessenbergSimilarity` constructs a `Hessenberg.Similarity` certificate and corresponding
Hessenberg reduction from a literal matrix over `ℚ` (or more generally a ring `S` with
`f : S → ℚ`).

## Main definitions

- `mkHessenbergSimilarity`: produce and elaborate the Hessenberg similarity certificate of a matrix
  literal.
- `SimilarityResult`: the `Hessenberg.Similarity` certificate together with the reduction data.

## Implementation notes

The untrusted computation `reduce` (in `Mathlib.Tactic.Hessenberg.Reduce`) produces `L` a unit lower
triangular matrix, `σ` a permutation corresponding to the row and column swaps, and `H` an upper
Hessenberg matrix.

The `mkHessenbergSimilarity` function certifies `Aσ * L = L * H` (where `Aσ` is the reindexing of
`A.map f` by `σ`) via the products `Aσ * L = P` and `L * H = P`, each proved by `certifyProductEq`
on the lists of rows.

The conditions that `L` is lower triangular with nonzero diagonal and `H` is
upper Hessenberg are decided by the kernel.
-/

public meta section

open Lean Meta Qq Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Hessenberg

/-- The result of producing a Hessenberg similarity of `A`. -/
structure SimilarityResult {n : ℕ} (A : Q(Matrix (Fin $n) (Fin $n) ℚ)) where
  /-- The elaborated `Matrix.Hessenberg.Similarity` certificate term. -/
  cert : Q(Matrix.Hessenberg.Similarity $A)
  /-- The literal of the row-major array of the Hessenberg matrix of the certificate. -/
  Harr : Q(Array ℚ)
  /-- The proof that `Harr` is the array of the Hessenberg matrix of the certificate. -/
  toArray_eq : Q(($cert).H.toArray = $Harr)
  /-- The reduction data underlying the certificate. -/
  red : Reduction

/-- Produce the `Matrix.Hessenberg.Similarity` certificate and corresponding reduction of `A.map f`
for the `n × n` matrix literal `A` over `S` and the map `f : S → ℚ`, from the parsed entries
`entries` of `A`, where `evalEntry` evaluates the image under `f` of an entry. -/
def mkHessenbergSimilarity {u : Level} {S : Q(Type u)} (f : Q($S → ℚ)) (n : ℕ)
    (A : Q(Matrix (Fin $n) (Fin $n) $S)) (entries : Array (Array Q($S)))
    (evalEntry : Q($S) → MetaM ℚ) : MetaM (SimilarityResult q(($A).map $f)) := do
  -- Evaluate the entries and reduce the matrix `M := A.map f` to Hessenberg form.
  let M : Q(Matrix (Fin $n) (Fin $n) ℚ) := q(($A).map $f)
  let vals ← entries.mapM (·.mapM evalEntry)
  let red := reduce n vals
  have σ : Q(Equiv.Perm (Fin $n)) := q(Equiv.symm (permOfSwaps $(← mkSwapsLitQ n red.swaps)))

  -- Construct the rows of `Aσ`, `L`, `H` and of the product `P := Aσ * L = L * H`.
  let rows (V : Array (Array ℚ)) : List (List ℚ) := V.toList.map Array.toList
  let pVals := ListMatrix.mul n n n (rows (red.arrange vals)) (rows red.L)
  let aσRows : List (List Q(ℚ)) := (red.arrange entries).toList.map (·.toList.map fun e => q($f $e))
  let lRows ← red.L.toList.mapM (·.toList.mapM (mkRatNumeralQ q(ℚ)))
  let hRows ← red.H.toList.mapM (·.toList.mapM (mkRatNumeralQ q(ℚ)))
  let pRows ← pVals.mapM (·.mapM (mkRatNumeralQ q(ℚ)))

  let P := ListMatrixLit.ofRows q(inferInstance) n n pRows
  have Pm := P.matrix

  let mulLH := proveMul (q(inferInstance) : Q(Zero ℚ)) (q(inferInstance) : Q(Add ℚ))
    (q(inferInstance) : Q(Mul ℚ)) n n n lRows hRows
  have Lm : Q(Matrix (Fin $n) (Fin $n) ℚ) := q(ofLists $n $n $(mulLH.A))
  have Hm : Q(Matrix (Fin $n) (Fin $n) ℚ) := q(ofLists $n $n $(mulLH.B))

  let H : ListMatrixLit q(ℚ) n n := { matrix := Hm, lit := mulLH.B, rows := hRows }

  let mulAσL := proveMul (q(inferInstance) : Q(Zero ℚ)) (q(inferInstance) : Q(Add ℚ))
    (q(inferInstance) : Q(Mul ℚ)) n n n aσRows lRows
  have Aσm : Q(Matrix (Fin $n) (Fin $n) ℚ) := q(ofLists $n $n $(mulAσL.A))

  -- `M.reindex σ σ` unfolds to the literal `Aσ`
  have hAσ : Q(Matrix.reindex $σ $σ $M = $Aσm) :=
    mkExpectedPropHint q((Matrix.etaExpand_eq (Matrix.reindex $σ $σ $M)).symm)
      q(Matrix.reindex $σ $σ $M = $Aσm)

  -- The products `L * H = P` and `Aσ * L = P`
  have hLH : Q($Lm * $Hm = $Pm) := ← certifyProductEq none q(inferInstance) mulLH P
  have hAL : Q($Aσm * $Lm = $Pm) := ← certifyProductEq none q(inferInstance) mulAσL P

  -- The similarity `M.reindex σ σ * L = L * H`
  have hmul : Q((Matrix.reindex $σ $σ $M) * $Lm = $Lm * $Hm) :=
    q((congrArg (· * $Lm) $hAσ).trans (($hAL).trans ($hLH).symm))

  -- Check the certificate fields by decide
  let hhess ← mkDecideProofQ q(($Hm).IsUpperHessenberg)
  let hlower ← mkDecideProofQ q(($Lm).IsLowerTriangular)
  let hdiag ← mkDecideProofQ q(∀ i, ($Lm).diag i ≠ 0)
  have cert : Q(Matrix.Hessenberg.Similarity $M) :=
    q(⟨$Lm, $σ, $Hm, $hmul, $hlower, $hdiag, $hhess⟩)

  -- Certify the Hessenberg matrix array in row-major form
  have Harr := H.array
  have toArray_eq : Q(($cert).H.toArray = $Harr) :=
    mkExpectedPropHint (← certifyOfArray q(inferInstance) H) q(($cert).H.toArray = $Harr)
  return { cert, Harr, toArray_eq, red }

end Mathlib.Tactic.Hessenberg
