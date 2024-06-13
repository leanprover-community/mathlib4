/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Linarith.Datatypes
import Mathlib.Tactic.Linarith.SimplexAlgorithm.PositiveVector

/-!
# Hooks to enable the use of the simplex algorithm in `linarith`
-/

open Batteries

namespace Linarith.SimplexAlgorithm

/-- Preprocess the goal to pass it to `findPositiveVector`. -/
def preprocess (matType : ℕ → ℕ → Type) [UsableInSimplexAlgorithm matType] (hyps : List Comp)
    (maxVar : ℕ) : matType (maxVar + 1) (hyps.length) × List Nat :=
  let values : List (ℕ × ℕ × ℚ) := hyps.foldlIdx (init := []) fun idx cur comp =>
    cur ++ comp.coeffs.map fun (var, c) => (var, idx, c)

  let strictIndexes := hyps.findIdxs (·.str == Ineq.lt)
  (ofValues values, strictIndexes)

/-- Extract the certificate from the `vec` found by `findPositiveVector`. -/
def postprocess (vec : Array ℚ) : HashMap ℕ ℕ :=
  let common_den : ℕ := vec.foldl (fun acc item => acc.lcm item.den) 1
  let vecNat : Array ℕ := vec.map (fun x : ℚ => (x * common_den).floor.toNat)
  HashMap.ofList <| vecNat.toList.enum.filter (fun ⟨_, item⟩ => item != 0)


end SimplexAlgorithm

open SimplexAlgorithm

/-- An oracle that uses the simplex algorithm. -/
def CertificateOracle.simplexAlgorithmSparse : CertificateOracle where
  produceCertificate hyps maxVar := do
    let (A, strictIndexes) := preprocess SparseMatrix hyps maxVar
    let vec ← findPositiveVector A strictIndexes
    return postprocess vec

/--
The same oracle as `CertificateOracle.simplexAlgorithmSparse`, but uses dense matrices. Works faster
on dense states.
-/
def CertificateOracle.simplexAlgorithmDense : CertificateOracle where
  produceCertificate hyps maxVar := do
    let (A, strictIndexes) := preprocess DenseMatrix hyps maxVar
    let vec ← findPositiveVector A strictIndexes
    return postprocess vec

end Linarith
