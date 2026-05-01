/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.InformationTheory.Complexity.Tableau
public import Mathlib.InformationTheory.Complexity.UTM
public import Mathlib.InformationTheory.Complexity.Decomposition
public import Mathlib.InformationTheory.Entropy.Program

@[expose] public section


/-!
# Information Theory Bridge

This file bridges the complexity side (CNF walks, circuit evaluation)
with the information side (programs, entropy). It contains:

1. **Time = Information** — the n² walk bound is simultaneously a
   time-complexity bound and an information-complexity bound.
2. **Three-Layer Equivalence** — Boolean evaluation, NDM circuit
   evaluation, and entropy walk all determine SAT equivalently,
   all in polynomial cost.
3. **Entropy Walk Completeness** — SAT ↔ ∃ zero-entropy walk,
   with address record and clause count invariants.

The full integration theorem `three_layer_meets_proof_chain`
(which additionally connects to the P = NP infrastructure, Rota
axioms, and RECT/IRECT bridge) lives in `PPNP.lean` where it
has access to the information content and complexity class defs.

## Main definitions

* `nSquared_time_complexity_is_information_complexity` -- for any
  budget `n^2`, a program with matching time and information
  complexity exists.
* `walk_nSquared_bound_is_time_and_information` -- for a satisfiable
  CNF, a program whose time and information complexity coincide
  and are bounded by `n^2`.

## Main results

* `three_layer_equivalence` -- Boolean evaluation, NDM circuit
  evaluation, and entropy walk determine SAT equivalently.
* `entropy_walk_completeness` -- SAT is equivalent to the existence of a zero-entropy walk.
-/

namespace InformationTheory

open InformationTheory InformationTheory.EntropyNat

/--
For any integer budget `n²`, there exists a concrete program whose
time complexity and information complexity are both exactly `n²`.
-/
theorem nSquared_time_complexity_is_information_complexity
    (n : ℕ) :
    ∃ (prog : ComputationalDescription),
      prog.complexity = n * n ∧
      programToEntropy prog = (n * n : ℝ) := by
  rcases program_entropy_inverse (n * n) with ⟨prog, h_entropy, h_complexity⟩
  refine ⟨prog, h_complexity, ?_⟩
  simpa [Nat.cast_mul] using h_entropy

/--
For a satisfiable CNF walk, there exists a program whose time
complexity and information complexity are the same value, and this
shared value is bounded by the canonical `n²` input bound.
-/
theorem walk_nSquared_bound_is_time_and_information
    {k : ℕ} (cnf : SyntacticCNF k)
    (endpoint : { v : Vector Bool k // evalCNF cnf v = true }) :
    let n := (encodeCNF cnf).length
    ∃ (prog : ComputationalDescription),
      prog.complexity =
        (walkCNFPaths cnf endpoint).complexity ∧
      programToEntropy prog =
        ((walkCNFPaths cnf endpoint).complexity : ℝ) ∧
      prog.complexity ≤ n * n := by
  intro n
  have h_walk_bound :
      (walkCNFPaths cnf endpoint).complexity ≤ n * n := by
    calc
      (walkCNFPaths cnf endpoint).complexity
          ≤ cnf.length * k := walkComplexity_upper_bound _ endpoint
      _ ≤ n * n := by
        apply Nat.mul_le_mul
        · simpa [n] using cnf_length_le_encoded_length cnf
        · simpa [n] using encodeCNF_size_ge_k k cnf
  rcases program_entropy_inverse
    ((walkCNFPaths cnf endpoint).complexity) with
    ⟨prog, h_entropy, h_complexity⟩
  refine ⟨prog, h_complexity, h_entropy, ?_⟩
  simpa [h_complexity] using h_walk_bound

/-!
## Three-Layer Equivalence

The NDM circuit evaluation (`ndmCircuitEval`), the address-space
walk (`ndmAddressWalk`), and the entropy walk (`ndmEntropyWalk`)
all determine SAT equivalently, all in polynomial cost.
-/

/--
**Three-Layer Equivalence: Boolean ↔ Circuit ↔ Entropy.**

The NDM circuit IS `evalCNF`, circuit acceptance equals zero
entropy walk, circuit SAT equals standard SAT, and all costs
are polynomial. This is the formal statement that three
independent computational layers agree on satisfiability.
-/
theorem three_layer_equivalence {k : ℕ}
    (cnf : SyntacticCNF k)
    (h_clause_bound : ∀ c ∈ cnf, c.length ≤ k)
    (h_clauses_nonempty : ∀ c ∈ cnf, c ≠ []) :
    -- 1. Circuit = Boolean: the NDM circuit IS evalCNF
    (∀ a : Vector Bool k,
      ndmCircuitEval cnf a = evalCNF cnf a) ∧
    -- 2. Circuit ↔ Entropy zero
    (∀ a : Vector Bool k,
      ndmCircuitEval cnf a = true ↔
        (ndmEntropyWalk cnf
          (assignmentCompositePrime a)).totalEntropy = 0) ∧
    -- 3. SAT equivalence: circuit SAT = standard SAT
    ((∃ a : Vector Bool k, ndmCircuitEval cnf a = true) ↔
      (∃ a : Vector Bool k, evalCNF cnf a = true)) ∧
    -- 4. Circuit cost is polynomial: O(|cnf| × k)
    (cnf.map (fun c => c.length)).sum ≤ cnf.length * k ∧
    -- 5. Address walk cost is polynomial
    ndmWalkComplexity cnf ≤ cnf.length * (k * (2 * k)) := by
  exact ⟨ndmCircuitEval_eq_evalCNF cnf,
         fun a => ndmCircuit_entropy_bridge cnf a
           h_clauses_nonempty,
         ndmCircuit_sat_iff cnf,
         ndmCircuit_cost_polynomial cnf h_clause_bound,
         ndmWalkComplexity_polynomial cnf h_clause_bound⟩

/--
**Entropy Walk Completeness: SAT ↔ ∃ zero-entropy walk.**

The entropy walk produces zero total entropy if and only if the
assignment satisfies the CNF. The walk records match the address
walk, visit every clause, and the cost is polynomial.
-/
theorem entropy_walk_completeness {k : ℕ}
    (cnf : SyntacticCNF k)
    (h_clauses_nonempty : ∀ c ∈ cnf, c ≠ [])
    (h_clause_bound : ∀ c ∈ cnf, c.length ≤ k) :
    -- SAT ↔ ∃ zero-entropy walk
    ((∃ a : Vector Bool k,
        (ndmEntropyWalk cnf
          (assignmentCompositePrime a)).totalEntropy = 0) ↔
      (∃ a : Vector Bool k, evalCNF cnf a = true)) ∧
    -- The entropy walk records match the address walk
    (∀ composite : ℕ,
      (ndmEntropyWalk cnf composite).addressRecord =
        ndmAddressWalk cnf) ∧
    -- The entropy walk visits every clause
    (∀ composite : ℕ,
      (ndmEntropyWalk cnf composite).clauseEntropies.length =
        cnf.length) ∧
    -- The walk cost is polynomial
    ndmWalkComplexity cnf ≤ cnf.length * (k * (2 * k)) := by
  exact ⟨ndmEntropyWalk_sat_iff_exists_zero cnf
           h_clauses_nonempty,
         ndmEntropyWalk_addresses_eq cnf,
         ndmEntropyWalk_clauseEntropies_length cnf,
         ndmWalkComplexity_polynomial cnf h_clause_bound⟩

end InformationTheory
