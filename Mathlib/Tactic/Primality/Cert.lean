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

The type of primality certificates and the certifier that constructs a `Nat.Prime` proof term.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Primality

/-- A primality certificate for `p` (not recorded in the type). -/
inductive Cert : Type where
  /-- `p` is proved prime by `norm_num`. -/
  | normNum
  /-- A proof that `p` is prime is provided, which should be stored in the initial state of
  `certifyPrime`. -/
  | known
  /-- A Lucas certificate with the primitive root `root` and the factorization of `p - 1` in
  `factorization`, each prime factor with its exponent and certificate. -/
  | lucas (root : ℕ) (factorization : List (ℕ × ℕ × Cert))

/-- Proves `Nat.Prime p` from the certificate `cert`. Each prime is proved only once. -/
partial def certifyPrime (p : ℕ) (cert : Cert) :
    StateT (Std.HashMap ℕ Expr) MetaM Q(Nat.Prime $p) := do
  if let some pf := (← get)[p]? then
    return pf
  let pf : Q(Nat.Prime $p) ← match cert with
    | .normNum =>
      let ⟨true, pf⟩ ← Mathlib.Meta.NormNum.deriveBool q(Nat.Prime $p) |
        throwError "{p} is not prime"
      pure pf
    | .known => throwError "no proof that {p} is prime is provided"
    | .lucas root factorization =>
      pure <| certifyLucas p root
        (← factorization.mapM fun (q, e, cert) ↦ return ⟨q, e, ← certifyPrime q cert⟩)
  modify (·.insert p pf)
  return pf

end Mathlib.Tactic.Primality
