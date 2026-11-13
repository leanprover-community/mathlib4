/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.Tactic.Primality.Lucas
public import Mathlib.Init
public import Mathlib.Tactic.Primality.Cert

/-!
# Producers

This file builds primality certificates from the witnesses the user provides.
-/

public meta section

open Lean

namespace Mathlib.Tactic.Primality

-- TODO: add more witness types (Pocklington variants).
/-- The witness of a primality certificate for one prime, tagged by the certificate type. -/
inductive Witness where
  /-- The witness of a Lucas certificate. -/
  | lucas (w : LucasWitness)

-- TODO: add a witness searching mode based on factorising `p - 1`.
/-- The witnesses of a certificate. -/
inductive CertMode where
  /-- The certificate with a list of explicit witnesses in `witnesses`. A prime `p` takes the
  first entry whose factors are the prime factors of `p - 1` and whose root is a primitive root of
  `p`. -/
  | witnesses (witnesses : List Witness)

/-- Find the root and the factorization of `p - 1` given by the first entry of `witnesses` that is
a Lucas witness for the prime `p`. -/
def witnessFor (witnesses : List Witness) (p : ℕ) : CoreM (ℕ × List (ℕ × ℕ)) := do
  for .lucas w in witnesses do
    if let some factorization := w.factorization? p then
      return (w.root, factorization)
  throwError "no provided witness certifies the primality of {p}"

/-- Numbers below this bound are proved prime by `norm_num`'s evaluation of `Nat.minFac`. -/
def normNumBound : ℕ := 2 ^ 10

/-- Builds the certificate of `p` from the first entry of `witnesses` that fits each prime, with
`norm_num` below `normNumBound` and the user's proofs for the primes in `known`. Each prime's
certificate is built once. -/
partial def Cert.ofWitnesses (witnesses : List Witness) (known : Std.HashSet ℕ) (p : ℕ) :
    CoreM Cert :=
  StateT.run' (go p) {}
where
  /-- Builds the certificate of `p`. The state caches the certificates constructed for each
  nontrivial intermediate result. -/
  go (p : ℕ) : StateT (Std.HashMap ℕ Cert) CoreM Cert := do
    if let some cert := (← get)[p]? then
      return cert
    if known.contains p then
      return .known
    if p < normNumBound then
      return .normNum
    let (root, factorization) ← witnessFor witnesses p
    let cert : Cert := .lucas root (← factorization.mapM fun (q, e) ↦ return (q, e, ← go q))
    modify (·.insert p cert)
    return cert

end Mathlib.Tactic.Primality
