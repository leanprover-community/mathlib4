/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Primality.Producers

/-!
# `primality`

This file defines the `primality` tactic, which closes goals `Nat.Prime n` using a closed family of
primality certificates, with witnesses it finds itself or takes from the user.
-/

public meta section

open Lean Meta Elab Tactic Qq Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Primality

/-- Configuration for `primality`. -/
structure Config where
  /-- The certificate configuration to use. -/
  cert : CertConfig := .search {}

/-- Function elaborating `Config`. -/
declare_config_elab elabPrimalityConfig Config

/-- Evaluates `e` to a numeral with `norm_num`, if it can. -/
def evalNumeral? (e : Q(Nat)) : MetaM (Option (Nat × (nQ : Q(Nat)) × Q(IsNat $e $nQ))) := do
  let some ⟨nQ, pn⟩ ← try some <$> deriveNat e q(Nat.instAddMonoidWithOne) catch _ => pure none |
    return none
  let .lit (.natVal n) := nQ | return none
  return some ⟨n, nQ, pn⟩

/-- Store the proofs `hs` of `Nat.Prime n` in a hashmap. -/
def elabKnownPrimes (hs : Array Term) : TacticM (Std.HashMap Nat Expr) := do
  let mut known : Std.HashMap Nat Expr := {}
  for h in hs do
    let h ← elabTerm h none
    let_expr Nat.Prime e := ← instantiateMVars (← inferType h) |
      throwError "{h} is not recognized as a proof of `Nat.Prime n`"
    have e : Q(Nat) := e
    have h : Q(Nat.Prime $e) := h
    let some ⟨q, qQ, pn⟩ ← evalNumeral? e |
      throwError "{h} is not recognized as a proof of `Nat.Prime n`"
    known := known.insert q q(isNat.natElim (p := fun m ↦ Nat.Prime m → Nat.Prime $qQ) $pn id $h)
  return known

/-- `primality` tries to prove a goal `Nat.Prime n`, using the hints provided by the user if any.
Refer to `MathlibTest.Tactic.Primality` for a gallery of usages. -/
syntax (name := primality) "primality" optConfig (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| primality $cfg:optConfig $[[$hs,*]]?) => withMainContext do
    let cfg ← elabPrimalityConfig cfg
    let known ← elabKnownPrimes <| hs.map (·.getElems) |>.getD #[]
    liftMetaFinishingTactic fun g ↦ do
      let_expr Nat.Prime e := ← instantiateMVars (← g.getType) |
        throwError "the goal is not of the form `Nat.Prime n`"
      have e : Q(Nat) := e
      let some ⟨p, pQ, pn⟩ ← evalNumeral? e |
        throwError "{e} does not evaluate to a numeral; try simplifying it first"
      let cert ← mkCert cfg.cert (.ofArray known.keysArray) p
      let hp : Q(Nat.Prime $pQ) ← StateT.run' (certifyPrime cert) known
      g.assign q(isNat.natElim (p := Nat.Prime) $pn $hp)

end Mathlib.Tactic.Primality
