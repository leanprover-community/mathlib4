/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module
public import Mathlib.InformationTheory.Complexity.CNF
public import Mathlib.InformationTheory.EntropyNumber.Basic



/-!
# Tableau Construction from CNF

This file constructs a **Satisfying Tableau** from a CNF formula and a
satisfying assignment. The tableau records a *walk path* for every
clause -- the `EntropyNat` encoding of the variable index that
satisfies it.

## Main definitions

* `PathToConstraint` -- the `EntropyNat` path cost for a single
  literal.
* `SatisfyingTableau` -- a CNF together with a satisfying assignment
  and walk paths.
* `SatisfyingTableau.complexity` -- total walk-path cost.
* `walkCNFPaths` -- the noncomputable walk that builds a tableau from a
  certified satisfying assignment.
* `computeTableau?` -- the computable version returning `Option`.

## Main results

* `path_complexity_le_k` -- each clause path costs at most `k`.
* `walkComplexity_upper_bound` -- total walk cost is at most
  `cnf.length * k`.
* `computeTableau_none_iff_not_sat` -- `computeTableau?` returns `none`
  iff the candidate does not satisfy the CNF.
* `computeTableau_time_bounded` -- the computable tableau satisfies the
  same upper bound.
-/

@[expose] public section

namespace InformationTheory

/-!
## Path to Constraint
-/

/-- The `EntropyNat` path cost to verify a single literal.
Verifying the `i`-th literal in a `k`-variable system requires a
computational path of complexity `i`. -/
def PathToConstraint {k : ℕ} (l : Literal k) : EntropyNat :=
  EntropyNat.ofNat l.particle_idx.val

/-- A boolean oracle for literal evaluation. This is the ONLY information
    that `walkCNFPaths` extracts from its second argument (the NP existential):
    for each literal, does it evaluate to true or false?

    The NP verifier's `∃ v` provides this oracle via `evalLiteral`.
    The CNF provides all structural content. The oracle provides
    only `k` bits of boolean selection. -/
abbrev LiteralOracle (k : ℕ) := Literal k → Bool

/-- Extract the boolean oracle from an assignment vector.
    `walkCNFPaths` uses `sat_assignment` ONLY through this function. -/
@[inline] def oracleOf {k : ℕ} (v : Vector Bool k) : LiteralOracle k :=
  fun lit => evalLiteral lit v

/-!
## The Satisfying Tableau (Certificate Structure)

A `SatisfyingTableau` bundles:
1. `cnf`: The constraint formula.
2. `assignment`: A `Vector Bool k` -- the satisfying assignment.
3. `walk_paths`: A `List EntropyNat` -- the recorded walk.
   For each clause, this records the `PathToConstraint` of the literal reached.
4. `h_valid`: A proof that the satisfying assignment satisfies all constraints.

The `walk_paths` field is the physical record of the walk. Its sum
(`complexity`) measures the total path length -- the information cost of the
walk record. This is bounded by the CNF's structure alone.
-/
/-- A satisfying-tableau record bundles a CNF, a satisfying assignment, the
walk paths the constructor produced clause by clause, and a proof that the
assignment satisfies the CNF. The walk paths' total length measures the
extracted information. -/
structure SatisfyingTableau (k : ℕ) where
  /-- The CNF formula being satisfied. -/
  cnf : SyntacticCNF k
  /-- A satisfying assignment for `cnf`. -/
  assignment : Vector Bool k
  /-- The walk record produced by the constructor: one path per clause. -/
  walk_paths : List EntropyNat
  /-- Proof that `assignment` satisfies `cnf`. -/
  h_valid : evalCNF cnf assignment = true

/--
**Measures the complexity of a Satisfying Tableau.**

The complexity is the sum of the `EntropyNat` lengths in the walk record.
Each path is bijectively a natural number (`EntropyNat.toNat`), so this sum is a concrete
`ℕ` -- the total information cost of the walk record.
-/
def SatisfyingTableau.complexity {k : ℕ} (tableau : SatisfyingTableau k) : ℕ :=
  (tableau.walk_paths.map EntropyNat.toNat).sum

/--
**The Full Walk: Visits every clause and records the path to its satisfied literal.**

Given a CNF and a satisfying assignment, `walkCNFPaths` walks
every clause in the CNF. For each clause, it finds the first literal satisfied
by the assignment and records the `PathToConstraint` -- the distance to
that literal's variable index.

The walk visits |cnf| clauses. Each clause's literal index is at most k.
Therefore the total walk cost is bounded by |cnf| x k, which is bounded by n^2
where n = |SyntacticCNF.encode cnf|.

Since `walk_paths : List EntropyNat` is `List (List Bool)` which flattens
to `List Bool` = `ComputerTape` = `ComputerProgram`, the walk itself constructs
the computation tape.
-/
def walkCNFPaths {k : ℕ} (cnf : SyntacticCNF k)
    (sat_assignment : { v : Vector Bool k //
      evalCNF cnf v = true }) :
    SatisfyingTableau k :=
  let assignment := sat_assignment.val
  let h_valid := sat_assignment.property
  -- Build the walk path for each clause.
  let walk_paths := cnf.map (fun clause =>
    let witness_literal_opt :=
      clause.find? (fun lit => evalLiteral lit assignment)
    match witness_literal_opt with
    | some lit => PathToConstraint lit
    | none => EntropyNat.ofNat 0
  )
  -- Assemble the tableau.
  { cnf := cnf,
    assignment := assignment,
    walk_paths := walk_paths,
    h_valid := h_valid }

/-- `walkCNFPaths` uses its second input only as a boolean oracle.
    Two satisfying assignments that agree on all literal evaluations
    produce identical walk paths. The assignment is a boolean oracle,
    not a structural input.

    This theorem makes explicit that the NP existential's role in the
    construction is purely boolean selection — the CNF provides all
    structural content. -/
theorem walkCNFPaths_oracle_determines_paths {k : ℕ}
    (cnf : SyntacticCNF k)
    (a₁ a₂ : { v : Vector Bool k // evalCNF cnf v = true })
    (h_oracle : oracleOf a₁.val = oracleOf a₂.val) :
    (walkCNFPaths cnf a₁).walk_paths = (walkCNFPaths cnf a₂).walk_paths := by
  have h_eq : (fun lit => evalLiteral lit a₁.val) = (fun lit => evalLiteral lit a₂.val) := by
    ext lit; exact congr_fun h_oracle lit
  unfold walkCNFPaths
  simp only [h_eq]

/--
Flatten the walk-path trace into a `ComputerProgram`.
This makes explicit that the walk record trace is an executable tape/program.
-/
def SatisfyingTableau.toComputerProgram {k : ℕ}
    (tableau : SatisfyingTableau k) : ComputerProgram :=
  List.flatten (tableau.walk_paths.map (fun p => p.val))

lemma path_complexity_le_k {k : ℕ} (clause : Clause k) (assignment : Vector Bool k) :
  (EntropyNat.toNat (match clause.find? (fun lit => evalLiteral lit assignment) with
   | some lit => EntropyNat.ofNat lit.particle_idx.val
   | none => EntropyNat.ofNat 0)) ≤ k := by
  cases h_find : clause.find? (fun lit => evalLiteral lit assignment) with
  | none =>
    simp only [EntropyNat.toNat, EntropyNat.ofNat, List.length_replicate]
    exact Nat.zero_le k
  | some witness_lit =>
    simp only [EntropyNat.toNat, EntropyNat.ofNat, List.length_replicate]
    exact Nat.le_of_lt witness_lit.particle_idx.isLt

/--
**The N^2 Walk Bound: Total walk cost is bounded by |cnf| x k.**

The walk visits |cnf| clauses. At each clause, the farthest reachable literal
has index < k. Therefore the total cost is at most |cnf| x k. Since both
|cnf| <= n and k <= n (where n = |SyntacticCNF.encode cnf|, proved by
`cnf_length_le_encoded_length` and `SyntacticCNF.encode_size_ge_k`), the total cost
is bounded by n x n = n^2.

This bound depends ONLY on the CNF's dimensions -- not on the satisfying assignment.
Any satisfying assignment produces a walk with cost <= |cnf| x k.
-/
theorem walkComplexity_upper_bound {k : ℕ}
    (cnf : SyntacticCNF k)
    (sat_assignment : { v : Vector Bool k //
      evalCNF cnf v = true }) :
  (walkCNFPaths cnf sat_assignment).complexity ≤ cnf.length * k :=
by
  have h_bound_element : ∀ clause ∈ cnf,
    (EntropyNat.toNat (match clause.find? (fun lit => evalLiteral lit sat_assignment.val) with
    | some lit => EntropyNat.ofNat lit.particle_idx.val
    | none => EntropyNat.ofNat 0)) ≤ k := by
    intro clause _
    exact path_complexity_le_k clause sat_assignment.val
  unfold walkCNFPaths SatisfyingTableau.complexity
  simp [PathToConstraint, List.map_map]
  induction cnf with
  | nil => simp
  | cons head tail ih =>
    simp [List.map_cons, List.sum_cons, List.length_cons]
    have h_head :
        (EntropyNat.toNat (match
          head.find? (fun lit =>
            evalLiteral lit sat_assignment.val) with
        | some lit => EntropyNat.ofNat lit.particle_idx.val
        | none => EntropyNat.ofNat 0)) ≤ k :=
      path_complexity_le_k head sat_assignment.val
    have h_tail :
        (tail.map (EntropyNat.toNat ∘ fun clause =>
          match clause.find? (fun lit =>
            evalLiteral lit sat_assignment.val) with
          | some lit => EntropyNat.ofNat lit.particle_idx.val
          | none =>
            EntropyNat.ofNat 0)).sum ≤
              tail.length * k := by
      have h_tail_sat :
          evalCNF tail sat_assignment.val = true := by
        have h_full_sat := sat_assignment.property
        unfold evalCNF at h_full_sat ⊢
        rw [List.all_cons] at h_full_sat
        simp only [Bool.and_eq_true] at h_full_sat
        exact h_full_sat.2
      let tail_sat_assignment :
          { v : Vector Bool k //
            evalCNF tail v = true } :=
        ⟨sat_assignment.val, h_tail_sat⟩
      apply ih tail_sat_assignment
      intro clause h_mem_tail
      exact path_complexity_le_k clause sat_assignment.val
    -- `omega` does not see through `EntropyNat.toNat` coercions; use `ℕ` inequalities.
    exact (Nat.add_le_add h_head h_tail).trans (Nat.le_of_eq (by
      rw [Nat.succ_mul, Nat.add_comm]))

/--
**Computable Walk (The Universal Tableau Generator).**

This is the computable version of `walkCNFPaths`. It takes a CNF and a
candidate assignment (`Vector Bool k`) and returns `some SatisfyingTableau`
if the candidate is valid, `none` otherwise.

This function does NOT use `Exists.choose` or Classical.choice.
It is purely computable -- executable Lean code.

The walk logic is identical to `walkCNFPaths`: visit every clause, record the
path to the satisfied literal. The only difference is that the validity check
(`evalCNF cnf candidate`) is performed computationally via `if h_valid : ...`.
-/
def computeTableau? {k : ℕ} (cnf : SyntacticCNF k)
  (candidate : Vector Bool k) : Option (SatisfyingTableau k) :=
  if h_valid : evalCNF cnf candidate = true then
    let walk_paths := cnf.map (fun clause =>
      match clause.find? (fun lit => evalLiteral lit candidate) with
      | some lit => PathToConstraint lit
      | none     => EntropyNat.ofNat 0
    )
    some {
      cnf := cnf,
      assignment := candidate,
      walk_paths := walk_paths,
      h_valid := h_valid
    }
  else
    none

/--
**Lemma: `computeTableau_none_iff_not_sat` returns `none` iff
the candidate does not satisfy the CNF.**

This follows directly from the `if`/`else` branch structure of `computeTableau?`.
-/
theorem computeTableau_none_iff_not_sat {k : ℕ} (cnf : SyntacticCNF k) (v : Vector Bool k) :
    computeTableau? cnf v = none ↔ evalCNF cnf v = false := by
  constructor
  · intro h_none
    unfold computeTableau? at h_none
    cases h : evalCNF cnf v
    · rfl
    · simp [h] at h_none
  · intro h_false
    unfold computeTableau?
    simp [h_false]

/--
**Lemma: When `computeTableau?` returns `some`, the resulting tableau's
complexity is bounded by `cnf.length * k`.**

This matches the `walkComplexity_upper_bound` bound. The walk logic in
`computeTableau?` constructs the same `walk_paths` structure as
`walkCNFPaths`, so the same per-clause bound applies.
-/
theorem computeTableau_time_bounded {k : ℕ} (cnf : SyntacticCNF k) (v : Vector Bool k)
    (tableau : SatisfyingTableau k)
    (h : computeTableau? cnf v = some tableau) :
    tableau.complexity ≤ cnf.length * k := by
  -- Extract that evalCNF cnf v = true from the `some` branch
  have h_valid : evalCNF cnf v = true := by
    unfold computeTableau? at h
    split at h
    · case isTrue h_true => exact h_true
    · case isFalse => simp at h
  -- The tableau from computeTableau? has specific structure
  have h_tableau : tableau = {
      cnf := cnf,
      assignment := v,
      walk_paths := cnf.map (fun clause =>
        match clause.find? (fun lit => evalLiteral lit v) with
        | some lit => PathToConstraint lit
        | none     => EntropyNat.ofNat 0),
      h_valid := h_valid
    } := by
    unfold computeTableau? at h
    simp [h_valid] at h
    exact h.symm
  -- The tableau equals the one produced by walkCNFPaths, so reuse its bound
  let sat_assignment : { w : Vector Bool k // evalCNF cnf w = true } := ⟨v, h_valid⟩
  have h_eq : tableau.complexity = (walkCNFPaths cnf sat_assignment).complexity := by
    rw [h_tableau]
    rfl
  rw [h_eq]
  exact walkComplexity_upper_bound cnf sat_assignment

end InformationTheory
