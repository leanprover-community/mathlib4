/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.Tactic.NormNum
public import Mathlib.InformationTheory.EntropyNumber.Basic
public import Mathlib.InformationTheory.Complexity.CNF

@[expose] public section


/-!
# Core Complexity Definitions

This file contains the minimal definitions required for the formal
complexity-theoretic framework.  It defines the entropy cost of
verifying a literal and provides encoding utilities for canonical CNF
instances.

## Main definitions

* `PathToConstraint` — the entropy cost of verifying a single literal.
* `CanonicalCNFProgram` — readability alias for an encoded canonical
  CNF viewed as a program.
* `encodeCanonicalCNFAsProgram` — encode a `CanonicalCNF` as a
  program tape.

## Main results

* `encodeCanonicalCNFAsProgram_eq_encodeCNF` -- the canonical CNF
  encoding equals `encodeCNF` on the underlying value.
* `encodeCanonicalCNFAsProgram_length` -- the encoded length equals the `encodeCNF` length.
-/

open InformationTheory InformationTheory.EntropyNat

namespace InformationTheory

namespace Complexity

/--
Calculates the entropy cost to verify a single literal.

In this model, verifying the `i`-th literal in a `k`-variable system
requires a computational path of complexity `i`. This represents the
information needed to "address" or "focus on" the `i`-th component of
the state vector.

The path is an `EntropyNat`, making the cost a direct, physical
quantity.
-/
def PathToConstraint {k : ℕ} (l : Literal k) : EntropyNat :=
  -- The complexity is the index of the variable being constrained.
  EntropyNat.ofNat l.particle_idx.val

/--
`CanonicalCNFProgram` is the program-level view of an encoded
canonical CNF.  This is a readability alias for reviewers: canonical
SAT instances are handled as executable binary programs in the
machine model.
-/
abbrev CanonicalCNFProgram (_k : ℕ) := List Bool

/-- Encode a canonical CNF as a `CanonicalCNFProgram`. -/
def encodeCanonicalCNFAsProgram {k : ℕ}
    (ccnf : CanonicalCNF k) : CanonicalCNFProgram k :=
  encodeCNF ccnf.val

/-- The encoded canonical CNF is definitionally a program tape. -/
@[simp] theorem encodeCanonicalCNFAsProgram_eq_encodeCNF
    {k : ℕ} (ccnf : CanonicalCNF k) :
    encodeCanonicalCNFAsProgram ccnf =
      encodeCNF ccnf.val := rfl

/-- Program size for canonical CNF is just encoded tape length. -/
@[simp] theorem encodeCanonicalCNFAsProgram_length
    {k : ℕ} (ccnf : CanonicalCNF k) :
    (encodeCanonicalCNFAsProgram ccnf).length =
      (encodeCNF ccnf.val).length := rfl

end Complexity

end InformationTheory
