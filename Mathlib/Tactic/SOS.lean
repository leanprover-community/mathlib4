/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Tactic.SOS.Certificate
public import Mathlib.Tactic.SOS.Raw
public import Mathlib.Tactic.SOS.Polynomial
public import Mathlib.Tactic.SOS.Reify
public import Mathlib.Tactic.SOS.Lift
public import Mathlib.Tactic.SOS.Verifier
public import Mathlib.Tactic.SOS.Tactic

/-!
# Sum-of-squares automation

Mathlib-facing soundness proofs and tactic elaboration for the `sos` tactic.

The proof-producing frontend lives in Mathlib. The computational engine is
provided by the external `sos` package, whose modules do not import Mathlib.

## Trust boundary

The native CSDP solver is a search oracle: it proposes floating-point Gram
matrices, which the engine rationalizes into exact certificates. Mathlib then
checks the certificate identity with kernel reduction and applies the
soundness theorems in `Mathlib.Tactic.SOS.Verifier`; neither certificate
checking nor proof replay uses `native_decide`. The committed axiom audit in
`MathlibTest.Tactic.SOS.Axioms` guards the principal soundness theorems.

This separation removes CSDP's numerical algorithm from the *logical* trusted
base: an incorrect solver answer is rejected rather than proving a false
statement. It does not make arbitrary native code process-safe. The CSDP FFI
runs inside the Lean process while a proof is elaborated, so its native memory
safety and the integrity of its distributed binaries remain part of the
ordinary software and host-security trusted base.
-/
