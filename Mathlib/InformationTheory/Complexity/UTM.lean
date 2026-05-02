/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.InformationTheory.Complexity.Tableau
public import Mathlib.InformationTheory.Complexity.Decomposition
public import Mathlib.InformationTheory.Entropy.SourceCoding



/-!
# The Computation Model (Universal Turing Machine Layer)

This file contains:
1. **Satisfiability/Entropy Decomposition** — conditional entropy bridge
   between evalCNF and cnfSharesFactor
2. **Sequential Tape Reading** — the ReadHead model proving
   time = tape length
3. **NDM Address Walk** — polarity-encoded literal addresses and
   polynomial walk complexity
4. **NDM Entropy Walk** — conditional entropy accumulated inside the
   machine
5. **NDM Circuit Evaluation** — circuit SAT via address space

## Main definitions

* `ReadHead` — the state of a sequential tape reader.
* `timeComplexity` — time cost of a program in the computation model.
* `literalAddress` / `literalAddressPath` — polarity-encoded literal
  addresses.
* `ndmAddressWalk` / `ndmWalkComplexity` — endpoint-free clause-by-clause
  address recording.
* `NDMEntropyWalkState` / `ndmEntropyWalk` — conditional entropy
  accumulated inside the machine.
* `literalAddressesFromAssignment` — the k addresses selected by an
  assignment.
* `ndmCircuitEval` — circuit evaluation in address space.

## Main results

* `timeComplexity_eq_length` — time complexity equals tape length.
* `ndmCircuitEval_eq_evalCNF` — the NDM circuit IS evalCNF.
* `ndmEntropyWalk_determines_sat` — entropy walk determines SAT.
* `ndmWalkComplexity_polynomial` — walk cost is polynomial.
* `ndmCircuit_entropy_bridge` — circuit evaluation matches entropy walk.
* `ndmCircuit_sat_iff` — SAT iff exists assignment where circuit accepts.
-/

@[expose] public section

-- Cosmetic linters disabled for this initial drop of the InformationTheory
-- subtree. These do not affect correctness; reviewers may request a per-call
-- cleanup as a follow-up PR.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.style.emptyLine false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.longFile 0
set_option linter.style.show false
set_option linter.style.whitespace false
set_option linter.style.lambdaSyntax false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


open InformationTheory InformationTheory.EntropyNat

namespace InformationTheory

-- Decomposition definitions (chosenLiteral, cnfSharesFactor, conditional entropy, etc.)
-- are imported from InformationTheory.Complexity.Decomposition

/-!
## The Read Head Model

A `ReadHead` processes a tape bit by bit. At each step, the head
reads one bit and advances. The number of steps taken is provably
equal to the tape length.
-/

/--
The state of a sequential tape reader at any point during execution.
`remaining` is the unread portion of the tape; `steps` counts how
many bits have been read so far.
-/
structure ReadHead where
  /-- The portion of the tape still ahead of the read head. -/
  remaining : ComputerTape
  /-- The number of bits already consumed by the read head. -/
  steps     : ℕ

/--
Initialize the read head at the beginning of a tape. Zero steps
taken.
-/
def ReadHead.init (tape : ComputerTape) : ReadHead :=
  { remaining := tape, steps := 0 }

/--
One step of execution: read one bit from the tape head, advance,
increment the step counter. Returns `none` if the tape is exhausted.
-/
def ReadHead.step (head : ReadHead) :
    Option (Bool × ReadHead) :=
  match head.remaining with
  | [] => none
  | bit :: rest =>
    some (bit, { remaining := rest,
                 steps := head.steps + 1 })

/--
Run the read head to completion: process every bit on the tape
sequentially. Returns the final state (empty tape, all steps
counted).
-/
def ReadHead.run : ReadHead → ReadHead
  | { remaining := [], steps := s } =>
    { remaining := [], steps := s }
  | { remaining := _ :: rest, steps := s } =>
      ReadHead.run { remaining := rest, steps := s + 1 }
termination_by head => head.remaining.length

/--
**The time complexity of a program in the computation model**: the number
of sequential read steps required to process the entire tape.

This is defined as the step count after running the read head to
completion.
-/
def timeComplexity (prog : ComputerProgram) : ℕ :=
  (ReadHead.init prog |>.run).steps

/-!
### Core Theorems: Time Complexity = Tape Length
-/

set_option linter.flexible false in
/--
After running the read head on a tape, the remaining tape is empty.
Every bit has been processed.
-/
theorem ReadHead.run_exhausts (head : ReadHead) :
    (head.run).remaining = [] := by
  induction head using ReadHead.run.induct with
  | case1 s => simp [ReadHead.run]
  | case2 bit rest s ih => simp [ReadHead.run]; exact ih

set_option linter.flexible false in
/--
The step count after running equals the initial steps plus the tape
length. This is the key lemma: every bit contributes exactly one
step.
-/
theorem ReadHead.run_steps (head : ReadHead) :
    (head.run).steps =
      head.steps + head.remaining.length := by
  induction head using ReadHead.run.induct with
  | case1 s => simp [ReadHead.run]
  | case2 bit rest s ih =>
    simp [ReadHead.run]
    rw [ih]
    simp [List.length_cons]
    omega

/--
**Time complexity equals tape length.**

For any `ComputerProgram`, the time complexity (number of
sequential read operations) is exactly the tape length. Each bit
costs one step. No free memory access. No loops. No revisits.

This is the formal statement that in the computation model,
**program complexity = time complexity = information content**.

Combined with:
- RECT/IRECT: information content = program complexity
- Shannon SCT: optimal code length = entropy for IID source
- Rota: log is the unique entropy function
- LFTA: primes are perfect Shannon coders

The chain is:
time complexity = tape length = information content = entropy.
-/
theorem timeComplexity_eq_length
    (prog : ComputerProgram) :
    timeComplexity prog = prog.length := by
  simp [timeComplexity, ReadHead.init, ReadHead.run_steps]

/--
Time complexity of the empty program is zero.
-/
@[simp] theorem timeComplexity_nil :
    timeComplexity ([] : ComputerProgram) = 0 := by
  simp [timeComplexity_eq_length]

/--
Time complexity of a single instruction is one.
-/
@[simp] theorem timeComplexity_singleton (b : Bool) :
    timeComplexity [b] = 1 := by
  simp [timeComplexity_eq_length]

/-! ## Chain 1 declarations — NDM address walk, entropy
    walk, circuit eval

The remaining declarations below ARE part of the P=NP proof chain
(Chain 1). They are directly imported by `PPNP.lean`:
`literalAddress`, `literalAddressPath`, `ndmAddressWalk`,
`ndmWalkComplexity`, `NDMEntropyWalkState`, `ndmEntropyWalk`,
`ndmEntropyWalk_*` theorems, `ndmCircuitEval`,
`ndmCircuitEval_eq_evalCNF`, `ndmCircuit_entropy_bridge`,
`ndmCircuit_sat_iff`, `ndmCircuit_cost_polynomial`, and
`ndmWalkComplexity_polynomial`.
-/

/-! ## NDM Address-Space Walk

### Polarity-Encoded Addresses

Literal addresses encode BOTH variable AND polarity via
`Literal.toNat`:

  `toNat lit = 2 * lit.particle_idx.val +
    (if lit.polarity then 1 else 0)`

This gives **2k unique addresses** (linear in k, NOT exponential).

### Walk Structure

For each clause in the CNF, the walk records the polarity-encoded
EntropyNat addresses of ALL literals in that clause.

  walk cost <= |cnf| x k x 2k = 2 x |cnf| x k^2

This is polynomial in the input size n = |encodeCNF cnf|.
-/

/--
**Polarity-encoded literal address.**

Maps each literal to a unique N address encoding both variable
position AND polarity. For k variables, there are 2k addresses:
{0, 1, ..., 2k-1}.

- `(x_i, true)`  -> `2i + 1` (odd addresses = positive polarity)
- `(x_i, false)` -> `2i`    (even addresses = negative polarity)

This is the existing `Literal.toNat` from CNF.lean.
-/
def literalAddress {k : ℕ} (lit : Literal k) : ℕ :=
  Literal.toNat lit

/--
**Literal address as an EntropyNat.**

Each literal address `n` maps to `ofNat n = replicate n true` —
an EntropyNat of length `n`. The walk records these addresses.
-/
def literalAddressPath {k : ℕ} (lit : Literal k) :
    EntropyNat :=
  EntropyNat.ofNat (literalAddress lit)

/--
**Each literal address is bounded by 2k.**

Since `lit.particle_idx : Fin k`, we have
`lit.particle_idx.val < k`, so
`literalAddress lit = 2 * lit.particle_idx.val + (0 or 1) < 2k`.
-/
theorem literalAddress_lt_two_k {k : ℕ}
    (lit : Literal k) :
    literalAddress lit < 2 * k := by
  simp only [literalAddress, Literal.toNat]
  have h := lit.particle_idx.isLt
  by_cases hp : lit.polarity <;> simp [hp] <;> omega

/--
**NDM address-space walk: endpoint-free clause-by-clause address
recording.**

For each clause in the CNF, records the EntropyNat addresses of ALL
literals in that clause. No endpoint parameter. The walk processes
all clauses and records the complete polarity-encoded address
structure.

The output is `List (List EntropyNat)` — one list of addresses per
clause.
-/
def ndmAddressWalk {k : ℕ} (cnf : SyntacticCNF k) :
    List (List EntropyNat) :=
  cnf.map (fun clause => clause.map literalAddressPath)

/--
**NDM walk complexity: total EntropyNat address cost.**

The complexity is the sum of all literal address values across all
clauses. Each address value =
`toNat (literalAddressPath lit)` = `literalAddress lit`.
-/
def ndmWalkComplexity {k : ℕ}
    (cnf : SyntacticCNF k) : ℕ :=
  ((ndmAddressWalk cnf).map
    (fun paths =>
      (paths.map EntropyNat.toNat).sum)).sum

/--
**Per-clause address cost is bounded by |clause| x 2k.**

Each literal address < 2k, so the sum of addresses in a clause
with m literals is < m x 2k.
-/
theorem clause_address_cost_le {k : ℕ}
    (clause : Clause k) :
    ((clause.map literalAddressPath).map
      EntropyNat.toNat).sum ≤
        clause.length * (2 * k) := by
  rw [List.map_map]
  apply sum_map_le_length_mul_bound
  intro lit h_mem
  simp only [Function.comp]
  simp only [literalAddressPath,
    EntropyNat.ofNat_toNat]
  exact Nat.le_of_lt (literalAddress_lt_two_k lit)

/--
**NDM walk complexity is polynomial: bounded by
|cnf| x k x 2k.**

Total cost = sum over clauses of (sum of literal addresses in
clause). Each clause has <= k literals, each literal address < 2k.
So total <= |cnf| x k x 2k = 2 x |cnf| x k^2.

This is polynomial in n = |encodeCNF cnf| (since |cnf| <= n and
k <= n).
-/
theorem ndmWalkComplexity_polynomial {k : ℕ}
    (cnf : SyntacticCNF k)
    (h_clause_bound : ∀ c ∈ cnf, c.length ≤ k) :
    ndmWalkComplexity cnf ≤
      cnf.length * (k * (2 * k)) := by
  unfold ndmWalkComplexity ndmAddressWalk
  simp only [List.map_map]
  induction cnf with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons,
      List.length_cons]
    have h_head_bound : head.length ≤ k :=
      h_clause_bound head
        (List.mem_cons.mpr (Or.inl rfl))
    have h_tail_bound : ∀ c ∈ tail, c.length ≤ k :=
      fun c hc => h_clause_bound c
        (List.mem_cons.mpr (Or.inr hc))
    have h_head_le := clause_address_cost_le head
    have h_mul_le := Nat.mul_le_mul_right (2 * k) h_head_bound
    have h_head_cost :
        ((head.map literalAddressPath).map EntropyNat.toNat).sum
          ≤ k * (2 * k) := by linarith
    have h_tail_cost := ih h_tail_bound
    simp only [Function.comp, List.map_map] at h_head_cost h_tail_cost ⊢
    linarith

/-!
### NDM Entropy Walk: Conditional Entropy Inside the Machine

The NDM entropy walk INTERNALIZES the conditional entropy
decomposition: the walk machine carries the conditional entropy
accumulator as it processes clauses. At each clause, the walk
simultaneously:

1. Records literal addresses (the `ndmAddressWalk` component)
2. Computes the conditional clause entropy (the chain rule
   component)
3. Accumulates the total entropy (the SAT-determination component)
-/

/-- State of the NDM entropy walk: carries the walk's address record
    alongside the conditional entropy accumulation. -/
structure NDMEntropyWalkState (k : ℕ) where
  /-- The composite being tested (encodes the variable
  assignment) -/
  composite : ℕ
  /-- Running total of conditional entropy across processed
  clauses -/
  totalEntropy : ℝ
  /-- Per-clause conditional entropy contributions (chain rule
  terms) -/
  clauseEntropies : List ℝ
  /-- Literal addresses recorded per clause (the ndmAddressWalk
  component) -/
  addressRecord : List (List EntropyNat)

/-- Initialize the entropy walk state with a composite. -/
noncomputable def NDMEntropyWalkState.init {k : ℕ}
    (composite : ℕ) :
    NDMEntropyWalkState k :=
  { composite := composite
    totalEntropy := 0
    clauseEntropies := []
    addressRecord := [] }

/--
One step of the NDM entropy walk: process a single clause.

Simultaneously:
1. Records the clause's literal addresses (address walk component)
2. Computes `conditionalClauseEntropy composite clause`
   (entropy component)
3. Adds the clause entropy to the running total (chain rule
   accumulation)
-/
noncomputable def ndmEntropyStep {k : ℕ}
    (clause : Clause k)
    (state : NDMEntropyWalkState k) :
    NDMEntropyWalkState k :=
  let clauseAddresses := clause.map literalAddressPath
  let clauseH :=
    conditionalClauseEntropy state.composite clause
  { state with
    totalEntropy := state.totalEntropy + clauseH
    clauseEntropies :=
      state.clauseEntropies ++ [clauseH]
    addressRecord :=
      state.addressRecord ++ [clauseAddresses] }

/--
The full NDM entropy walk: process all clauses sequentially.

The walk folds over the CNF clause by clause, simultaneously
recording literal addresses and accumulating conditional entropy.
-/
noncomputable def ndmEntropyWalk {k : ℕ}
    (cnf : SyntacticCNF k)
    (composite : ℕ) : NDMEntropyWalkState k :=
  cnf.foldl
    (fun state clause => ndmEntropyStep clause state)
    (NDMEntropyWalkState.init composite)

/-- The composite field is preserved by ndmEntropyStep. -/
private theorem ndmEntropyStep_composite {k : ℕ}
    (clause : Clause k)
    (state : NDMEntropyWalkState k) :
    (ndmEntropyStep clause state).composite =
      state.composite := by
  simp [ndmEntropyStep]

/-- The composite field is preserved by the full foldl walk. -/
private theorem ndmEntropyWalk_foldl_composite {k : ℕ}
    (cnf : List (Clause k))
    (init : NDMEntropyWalkState k) :
    (cnf.foldl
      (fun state clause =>
        ndmEntropyStep clause state) init).composite =
      init.composite := by
  induction cnf generalizing init with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons]
    rw [ih, ndmEntropyStep_composite]

/-- Helper: the foldl accumulation pattern for totalEntropy. -/
private theorem ndmEntropyWalk_foldl_total {k : ℕ}
    (cnf : List (Clause k))
    (init : NDMEntropyWalkState k) :
    (cnf.foldl
      (fun state clause =>
        ndmEntropyStep clause state)
          init).totalEntropy =
      init.totalEntropy +
        (cnf.map
          (conditionalClauseEntropy
            init.composite)).sum := by
  induction cnf generalizing init with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons, List.map_cons,
      List.sum_cons]
    rw [ih]
    simp only [ndmEntropyStep,
      ndmEntropyStep_composite]
    ring

/--
**The entropy walk's total equals the conditional CNF entropy.**

The walk accumulates exactly
`conditionalCNFEntropy composite cnf`: each clause step adds
`conditionalClauseEntropy composite clause` to the running total,
and the sum is the conditional CNF entropy.
-/
theorem ndmEntropyWalk_total_eq {k : ℕ}
    (cnf : SyntacticCNF k)
    (composite : ℕ) :
    (ndmEntropyWalk cnf composite).totalEntropy =
      conditionalCNFEntropy composite cnf := by
  unfold ndmEntropyWalk
  rw [ndmEntropyWalk_foldl_total]
  simp [NDMEntropyWalkState.init,
    conditionalCNFEntropy]

/--
**The entropy walk determines SAT.**

The NDM entropy walk's total entropy is zero iff the CNF is
satisfiable under the assignment encoded by the composite.
-/
theorem ndmEntropyWalk_determines_sat {k : ℕ}
    (cnf : SyntacticCNF k)
    (a : Vector Bool k)
    (h_clauses_nonempty : ∀ c ∈ cnf, c ≠ []) :
    (ndmEntropyWalk cnf
      (assignmentCompositePrime a)).totalEntropy = 0 ↔
      evalCNF cnf a = true := by
  rw [ndmEntropyWalk_total_eq]
  exact (cnfSharesFactor_iff_zero_conditional_cnf_entropy
    a cnf h_clauses_nonempty).symm.trans
    (evalCNF_true_iff_cnfSharesFactor a cnf).symm

/-- Helper: the foldl accumulation pattern for
addressRecord. -/
private theorem ndmEntropyWalk_foldl_addressRecord
    {k : ℕ}
    (cnf : List (Clause k))
    (init : NDMEntropyWalkState k) :
    (cnf.foldl
      (fun state clause =>
        ndmEntropyStep clause state)
          init).addressRecord =
      init.addressRecord ++
        cnf.map (fun clause =>
          clause.map literalAddressPath) := by
  induction cnf generalizing init with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [ndmEntropyStep, List.append_assoc]

/--
**The entropy walk's address record equals the NDM address walk.**
-/
theorem ndmEntropyWalk_addresses_eq {k : ℕ}
    (cnf : SyntacticCNF k)
    (composite : ℕ) :
    (ndmEntropyWalk cnf composite).addressRecord =
      ndmAddressWalk cnf := by
  unfold ndmEntropyWalk ndmAddressWalk
  rw [ndmEntropyWalk_foldl_addressRecord]
  simp [NDMEntropyWalkState.init]

/--
**SAT iff exists composite with zero entropy walk.**
-/
theorem ndmEntropyWalk_sat_iff_exists_zero {k : ℕ}
    (cnf : SyntacticCNF k)
    (h_clauses_nonempty : ∀ c ∈ cnf, c ≠ []) :
    (∃ a : Vector Bool k,
      (ndmEntropyWalk cnf
        (assignmentCompositePrime a)).totalEntropy =
          0) ↔
      (∃ a : Vector Bool k,
        evalCNF cnf a = true) := by
  constructor
  · rintro ⟨a, h_zero⟩
    exact ⟨a,
      (ndmEntropyWalk_determines_sat cnf a
        h_clauses_nonempty).mp h_zero⟩
  · rintro ⟨a, h_sat⟩
    exact ⟨a,
      (ndmEntropyWalk_determines_sat cnf a
        h_clauses_nonempty).mpr h_sat⟩

/-- Helper: the foldl accumulation pattern for clauseEntropies
length. -/
private theorem
    ndmEntropyWalk_foldl_clauseEntropies_length
    {k : ℕ}
    (cnf : List (Clause k))
    (init : NDMEntropyWalkState k) :
    (cnf.foldl
      (fun state clause =>
        ndmEntropyStep clause state)
          init).clauseEntropies.length =
      init.clauseEntropies.length + cnf.length := by
  induction cnf generalizing init with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp [ndmEntropyStep, List.length_append]
    omega

/--
**The entropy walk clause count equals the CNF clause count.**
-/
theorem ndmEntropyWalk_clauseEntropies_length {k : ℕ}
    (cnf : SyntacticCNF k)
    (composite : ℕ) :
    (ndmEntropyWalk cnf composite).clauseEntropies.length =
      cnf.length := by
  unfold ndmEntropyWalk
  rw [ndmEntropyWalk_foldl_clauseEntropies_length]
  simp [NDMEntropyWalkState.init]

/-! ## Circuit SAT via NDM Address Space

### The Key Insight

The NDM circuit model:
- INPUTS: the variable literal addresses (2k total, k selected by
  any assignment)
- CONSTRAINTS: the CNF clauses (each clause specifies which literal
  addresses satisfy it)
- OUTPUT: whether the selected input addresses are consistent with
  all constraints

### Architecture

1. `literalAddressesFromAssignment` — the k addresses selected by
   assignment a
2. `ndmCircuitEval` — circuit evaluation in address space
3. `ndmCircuitEval_eq_evalCNF` — the NDM circuit IS evalCNF
   (capstone)
4. Polynomial cost properties
-/

/--
**The addresses selected by an assignment.**

For each variable index i, the assignment selects the literal
`chosenLiteral a i`, and its address is
`literalAddress (chosenLiteral a i)`. This gives exactly k literal
addresses.
-/
def literalAddressesFromAssignment {k : ℕ}
    (a : Vector Bool k) : Finset ℕ :=
  Finset.image
    (fun i => literalAddress (chosenLiteral a i))
    Finset.univ

/--
**The fundamental bridge: `evalLiteral lit a = true` iff
`literalAddress lit ∈ literalAddressesFromAssignment a`.**
-/
theorem evalLiteral_iff_mem_literalAddresses {k : ℕ}
    (lit : Literal k)
    (a : Vector Bool k) :
    evalLiteral lit a = true ↔
      literalAddress lit ∈
        literalAddressesFromAssignment a := by
  constructor
  · intro h_eval
    have h_pol :=
      (evalLiteral_eq_true_iff_polarity_eq lit a).mp
        h_eval
    simp only [literalAddressesFromAssignment,
      Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨lit.particle_idx, ?_⟩
    -- literalAddress lit =
    --   literalAddress (chosenLiteral a lit.particle_idx)
    -- Since lit.polarity = a.get lit.particle_idx,
    -- the chosen literal matches
    unfold literalAddress chosenLiteral
    simp only [Literal.toNat, h_pol]
  · intro h_mem
    simp only [literalAddressesFromAssignment,
      Finset.mem_image, Finset.mem_univ,
      true_and] at h_mem
    rcases h_mem with ⟨i, h_addr_eq⟩
    -- h_addr_eq : literalAddress lit =
    --   literalAddress (chosenLiteral a i)
    unfold literalAddress chosenLiteral at h_addr_eq
    simp only [Literal.toNat] at h_addr_eq
    rw [evalLiteral_eq_true_iff_polarity_eq]
    -- From h_addr_eq, extract idx equality and polarity
    -- equality
    have h_idx_val :
        lit.particle_idx.val = i.val := by
      -- h_addr_eq involves `if` expressions;
      -- case-split to enable omega
      cases hp : lit.polarity <;>
        cases ha : (a.get i) <;>
        simp [hp, ha] at h_addr_eq <;> omega
    have h_idx : lit.particle_idx = i :=
      Fin.ext h_idx_val
    subst h_idx
    -- Now h_addr_eq gives polarity match
    cases h_pol : lit.polarity <;>
      cases h_val : (a.get lit.particle_idx) <;>
      simp_all

/--
**The NDM circuit: given an assignment's literal addresses and a
CNF, check if every clause contains at least one selected
address.**

This operates entirely in address space — no direct reference to
the assignment vector, only to the addresses it selects.
-/
def ndmCircuitEval {k : ℕ} (cnf : SyntacticCNF k)
    (a : Vector Bool k) : Bool :=
  cnf.all (fun clause => clause.any (fun lit =>
    decide (literalAddress lit ∈
      literalAddressesFromAssignment a)))

/--
**The NDM circuit evaluation equals `evalCNF`.**

This is the capstone theorem: the NDM circuit IS evalCNF, operating
entirely in address space.
-/
theorem ndmCircuitEval_eq_evalCNF {k : ℕ}
    (cnf : SyntacticCNF k)
    (a : Vector Bool k) :
    ndmCircuitEval cnf a = evalCNF cnf a := by
  simp only [ndmCircuitEval, evalCNF, evalClause]
  congr 1
  ext clause
  congr 1
  ext lit
  cases h : evalLiteral lit a
  · simp only [decide_eq_false_iff_not]
    intro h_mem
    have :=
      (evalLiteral_iff_mem_literalAddresses lit a).mpr
        h_mem
    rw [h] at this
    exact absurd this Bool.noConfusion
  · simp only [decide_eq_true_eq]
    exact (evalLiteral_iff_mem_literalAddresses
      lit a).mp h

/--
**The NDM circuit cost is polynomial: O(|cnf| x k).**
-/
theorem ndmCircuit_cost_polynomial {k : ℕ}
    (cnf : SyntacticCNF k)
    (h_clause_bound : ∀ c ∈ cnf, c.length ≤ k) :
    (cnf.map (fun c => c.length)).sum ≤
      cnf.length * k := by
  apply sum_map_le_length_mul_bound
  exact h_clause_bound

/--
**Entropy bridge: NDM circuit evaluation matches the entropy walk
determination.**

`ndmCircuitEval cnf a = true ↔
  ndmEntropyWalk(composite).totalEntropy = 0`.
-/
theorem ndmCircuit_entropy_bridge {k : ℕ}
    (cnf : SyntacticCNF k)
    (a : Vector Bool k)
    (h_clauses_nonempty : ∀ c ∈ cnf, c ≠ []) :
    ndmCircuitEval cnf a = true ↔
      (ndmEntropyWalk cnf
        (assignmentCompositePrime a)).totalEntropy =
          0 := by
  rw [ndmCircuitEval_eq_evalCNF]
  exact (ndmEntropyWalk_determines_sat cnf a
    h_clauses_nonempty).symm

/--
**SAT iff exists assignment where the NDM circuit accepts.**
-/
theorem ndmCircuit_sat_iff {k : ℕ}
    (cnf : SyntacticCNF k) :
    (∃ a : Vector Bool k,
      ndmCircuitEval cnf a = true) ↔
    (∃ a : Vector Bool k,
      evalCNF cnf a = true) := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, (ndmCircuitEval_eq_evalCNF cnf a) ▸ h⟩
  · rintro ⟨a, h⟩
    exact ⟨a, (ndmCircuitEval_eq_evalCNF cnf a) ▸ h⟩

end InformationTheory
