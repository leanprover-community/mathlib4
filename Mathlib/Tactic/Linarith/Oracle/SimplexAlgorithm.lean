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
def preprocess (hyps : List Comp) (maxVar : ℕ) : Matrix (maxVar + 1) (hyps.length) × List Nat :=
  let mdata : Array (Array ℚ) := Array.ofFn fun i : Fin (maxVar + 1) =>
    Array.mk <| hyps.map (·.coeffOf i)
  let strictIndexes : List ℕ := hyps.findIdxs (·.str == Ineq.lt)
  ⟨⟨mdata⟩, strictIndexes⟩

/-- Extract the certificate from the `vec` found by `findPositiveVector`. -/
def postprocess (vec : Array ℚ) : HashMap ℕ ℕ :=
  let common_den : ℕ := vec.foldl (fun acc item => acc.lcm item.den) 1
  let vecNat : Array ℕ := vec.map (fun x : ℚ => (x * common_den).floor.toNat)
  HashMap.ofList <| vecNat.toList.enum.filter (fun ⟨_, item⟩ => item != 0)


end SimplexAlgorithm

open SimplexAlgorithm

/-- An oracle that uses the Simplex Algorithm. -/
def CertificateOracle.simplexAlgorithm : CertificateOracle where
  produceCertificate hyps maxVar := do
    let ⟨A, strictIndexes⟩ := preprocess hyps maxVar
    let vec ← findPositiveVector A strictIndexes
    return postprocess vec

end Linarith
