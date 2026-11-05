/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.NormNum.Prime  -- shake: keep (`Nat.Prime` extension for `deriveBool`)
public import Mathlib.Tactic.Primality.Lucas

/-!
# Primality certificates

The type of primality certificates and the certifier that constructs a `Nat.Prime` proof term
from one.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Primality

/-- A certificate that `p` is prime. -/
inductive Cert : Nat → Type where
  /-- `p` is proved prime by `norm_num`. -/
  | normNum {p : Nat} : Cert p
  /-- A proof that `p` is prime is provided, which must be stored in the initial cache of
  `certifyPrime`. -/
  | known {p : Nat} : Cert p
  /-- A Lucas certificate with the primitive root `root` and the prime factors of `p - 1` with
  their certificates in `factors`. -/
  | lucas {p : Nat} (root : Nat) (factors : List ((q : Nat) × Cert q)) : Cert p

/-- Proves `Nat.Prime p` from the certificate `cert`. Each prime is proved only once. -/
partial def certifyPrime {p : Nat} (cert : Cert p) :
    StateT (Std.HashMap Nat Expr) MetaM Q(Nat.Prime $p) := do
  if let some pf := (← get)[p]? then
    return pf
  let pf : Q(Nat.Prime $p) ← match cert with
    | .normNum =>
      let ⟨true, pf⟩ ← Mathlib.Meta.NormNum.deriveBool q(Nat.Prime $p) |
        throwError "{p} is not prime"
      pure pf
    | .known => throwError "no proof that {p} is prime is provided"
    | .lucas root factors =>
      pure <| certifyLucas p root (← factors.mapM fun ⟨q, cert⟩ ↦ return ⟨q, ← certifyPrime cert⟩)
  modify (·.insert p pf)
  return pf

end Mathlib.Tactic.Primality
