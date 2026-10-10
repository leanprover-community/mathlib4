/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Batteries.Data.Nat.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.Matrix.OfLists
public import Mathlib.Tactic.Matrix.Parsing

import Mathlib.Util.Qq

/-!
# Simproc deciding `Matrix.IsIndecomposable`

`Matrix.reduceIsIndecomposable` rewrites `M.IsIndecomposable` to `True` or `False` for a closed
square matrix literal `M` indexed by `Fin n`. Requires a kernel-decidable equality for the matrix
entry type.

This is equivalent to determining whether the graph corresponding to `M` is strongly
connected.

## Main definitions

- `Matrix.reduceIsIndecomposable`: the simproc deciding `M.IsIndecomposable`.
- `SpansFrom`: a list of edges that reaches every vertex followed in order from a root vertex.
- `isClosed`: a set of vertices with no edges leaving.
- `packedAdj`: a Boolean adjacency matrix stored as the bits of a natural number, computed from a
  matrix literal by `packRows`.
- `decideStronglyConnected`: searches the graph from and to vertex `0`, returning two spanning
  trees or a closed set of vertices.

## Implementation notes

This simproc simply runs two bfs on the graph from vertex `0` forwards and
backwards. If all vertices are reached in both passes, then the indecomposability is certified by
the two search trees. Otherwise, `M` is decomposable, witnessed by a set of rows whose entries
outside the set evaluate to 0.

There is an existing implementation of Tarjan's algorithm at `Tactic.Order.Graph.findSCCs`, but it
doesn't return a witness for the strongly connected components, and the algorithm is also an
overkill.

The Boolean adjacency matrix of a `!![…]` literal is packed into one natural number, with entry
`(i, j)` at bit `i * n + j`, and both certificates are checked against that number, since reading
the literal by position costs the kernel a walk per entry.
-/

@[expose] public section

open Matrix Relation

namespace Mathlib.Tactic.Matrix.IsIndecomposable

/-! ### Reachability in a Boolean adjacency matrix -/

/-- The vertices reached from the set bits of `s` by following the edges `es` in order, an edge
counting only when it leaves a vertex already reached and is an edge of `adj`. -/
def reached {n : ℕ} (adj : Fin n → Fin n → Bool) (s : ℕ) (es : List (Fin n × Fin n)) : ℕ :=
  es.foldl (init := s) fun visited (p, c) ↦
    bif visited.testBit p && adj p c then visited ||| 1 <<< (c : ℕ) else visited

theorem reflTransGen_of_testBit_reached {n : ℕ} {adj : Fin n → Fin n → Bool} {root : Fin n}
    {s : ℕ} {es : List (Fin n × Fin n)}
    (hs : ∀ v : Fin n, s.testBit v → ReflTransGen (fun i j ↦ adj i j) root v) {v : Fin n}
    (hv : (reached adj s es).testBit v) : ReflTransGen (fun i j ↦ adj i j) root v := by
  induction es generalizing s with
  | nil => exact hs v hv
  | cons e es ih => exact ih (fun w hw ↦ by grind [Fin.ext_iff]) hv

/-- The edges `es`, followed in order from `root`, reach every vertex of `adj`. -/
abbrev SpansFrom {n : ℕ} (adj : Fin n → Fin n → Bool) (es : List (Fin n × Fin n))
    (root : Fin n) : Prop :=
  reached adj (1 <<< (root : ℕ)) es = 2 ^ n - 1

/-- If `adj` has a spanning tree from `root`, then `root` reaches every vertex. -/
theorem SpansFrom.reflTransGen {n : ℕ} {adj : Fin n → Fin n → Bool} {es : List (Fin n × Fin n)}
    {root : Fin n} (h : SpansFrom adj es root) (v : Fin n) :
    ReflTransGen (fun i j ↦ adj i j) root v :=
  reflTransGen_of_testBit_reached (s := 1 <<< (root : ℕ)) (es := es) (by grind) (by simp [h])

/-! ### Closed sets of vertices in a Boolean adjacency matrix, and the packed version -/

/-- Whether no edge leaves the set of vertices given by the set bits of `s`. -/
def isClosed {n : ℕ} (adj : Fin n → Fin n → Bool) (s : ℕ) : Bool :=
  (List.finRange n).all fun i ↦ !s.testBit i ||
    (List.finRange n).all fun j ↦ s.testBit j || !adj i j

/-- Entry `(i, j)` of the `n × n` Boolean adjacency matrix represented by `bits`. -/
def packedAdj (n bits : ℕ) (i j : Fin n) : Bool :=
  bits.testBit (i * n + j)

/-- Whether no edge of the `n × n` Boolean adjacency matrix represented by `bits` leaves the set
of vertices given by the set bits of `s`. Each row of `bits` is read at once, so this function
only takes `O(n)` kernel steps. -/
def isClosedPacked (n bits s : ℕ) : Bool :=
  (List.range n).all fun i ↦
    let row := bits >>> (i * n) &&& (2 ^ n - 1)
    !s.testBit i || (row &&& s) == row

theorem isClosed_of_isClosedPacked {n bits s : ℕ} (h : isClosedPacked n bits s = true) :
    isClosed (packedAdj n bits) s = true := by
  simp [isClosedPacked, Nat.eq_iff_testBit_eq] at h
  grind [isClosed, packedAdj]

/-! ### Certificates for a matrix from its Boolean adjacency matrix -/

variable {R : Type*} [Zero R]

/-- If both `adj` and the reverse of it have spanning trees from `root`, then `M` is
indecomposable (strong connectivity of `adj`). -/
theorem isIndecomposable_of_spansFrom {n : ℕ}
    {M : Matrix (Fin n) (Fin n) R} {adj : Fin n → Fin n → Bool}
    (hadj : ∀ i j, adj i j ↔ M i j ≠ 0) {root : Fin n} {fwd bwd : List (Fin n × Fin n)}
    (hf : SpansFrom adj fwd root) (hb : SpansFrom (fun i j ↦ adj j i) bwd root) :
    M.IsIndecomposable := by
  refine (isIndecomposable_iff_reflTransGen M).2 fun i j ↦ ?_
  simpa only [hadj] using (hb.reflTransGen i).swap.trans (hf.reflTransGen j)

/-- If `adj` has a nonempty proper subset of vertices that is closed, then `M` is decomposable. -/
theorem not_isIndecomposable_of_isClosed {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    {adj : Fin n → Fin n → Bool} (hadj : ∀ i j, adj i j ↔ M i j ≠ 0) {s : ℕ}
    (h : isClosed adj s = true) {i j : Fin n} (hij : s.testBit i ≠ s.testBit j) :
    ¬M.IsIndecomposable := by
  intro hM
  obtain ⟨a, ha⟩ := (isIndecomposable_iff_blockTriangular_const M).1 hM (s.testBit ·)
    (by grind [isClosed, BlockTriangular, Bool.lt_iff])
  simp_all [funext_iff]

/-! ### The Boolean adjacency matrix of a matrix literal -/

variable [DecidableEq R]

/-- The nonzero entries of `row`, as the set bits of a natural number. -/
def packRow (row : List R) : ℕ :=
  row.foldr (fun (a : R) acc ↦ (if a = 0 then 0 else 1) ||| acc <<< 1) 0

/-- The Boolean adjacency matrix of the `n × n` matrix with rows `rows`, as the set bits of a
natural number with entry `(i, j)` at bit `i * n + j`. -/
def packRows (n : ℕ) (rows : List (List R)) : ℕ :=
  rows.foldr (fun row acc ↦ (packRow row &&& (2 ^ n - 1)) ||| acc <<< n) 0

theorem testBit_packRow (row : List R) (j : ℕ) :
    (packRow row).testBit j = decide (row.getD j 0 ≠ 0) := by
  induction row generalizing j with
  | nil => simp [packRow]
  | cons a row ih =>
    cases j <;> by_cases a = 0 <;> simp_all [packRow, Nat.testBit_one_eq_true_iff_self_eq_zero]

theorem testBit_packRows {n : ℕ} (rows : List (List R)) (i : ℕ) {j : ℕ} (hj : j < n) :
    (packRows n rows).testBit (i * n + j) = decide ((rows.getD i []).getD j 0 ≠ 0) := by
  induction rows generalizing i with
  | nil => simp [packRows]
  | cons row rows ih =>
    cases i <;> simp_all [packRows, testBit_packRow, Nat.add_mul, Nat.add_right_comm _ n]

theorem packedAdj_packRows_iff {n : ℕ} (rows : List (List R)) (i j : Fin n) :
    packedAdj n (packRows n rows) i j ↔ ofLists n n rows i j ≠ 0 := by
  simp [packedAdj, testBit_packRows]

end Mathlib.Tactic.Matrix.IsIndecomposable

end

public meta section

open Lean Meta Qq Matrix

namespace Mathlib.Tactic.Matrix.IsIndecomposable

/-- Breadth-first search from `root` along `adj`, returning the tree edges in discovery order and
the reached vertices. -/
def bfs (n : Nat) (adj : Nat → Nat → Bool) (root : Nat) :
    Array (Nat × Nat) × Array Bool := Id.run do
  let mut visited := (Array.replicate n false).set! root true
  let mut tree := #[]
  let mut current := #[root]
  while !current.isEmpty do
    let mut next := #[]
    for p in current do
      for c in 0...n do
        if adj p c && !visited[c]! then
          visited := visited.set! c true
          tree := tree.push (p, c)
          next := next.push c
    current := next
  return (tree, visited)

/-- The list literal of the edges `edges`. -/
def mkEdgeListLitQ (n : Nat) (edges : Array (Nat × Nat)) : MetaM Q(List (Fin $n × Fin $n)) := do
  let es ← edges.toList.mapM fun (p, c) ↦ do
    let pQ : Q(Fin $n) ← mkFinLitQ n p
    let cQ : Q(Fin $n) ← mkFinLitQ n c
    return q(($pQ, $cQ))
  return mkListLitQ (α := q(Fin $n × Fin $n)) es

/-- The outcome of searching a directed graph from and to vertex `0`. -/
inductive StrongConnectivityResult where
  /-- The graph is strongly connected, with the spanning out-tree `outTree` from `0` and in-tree
  `inTree` to `0`. -/
  | connected (outTree inTree : Array (Nat × Nat))
  /-- The graph is not strongly connected. No edge leaves the nonempty proper set of vertices
  `closedSet`. -/
  | disconnected (closedSet : Array Bool)

/-- Search the directed graph with Boolean adjacency matrix `adjMatrix` from and to vertex `0`. -/
def decideStronglyConnected (adjMatrix : Array (Array Bool)) : StrongConnectivityResult :=
  let n := adjMatrix.size
  let adj (p c : Nat) : Bool := (adjMatrix[p]!)[c]!
  let (outTree, fromRoot) := bfs n adj 0
  -- The vertices reached from `0` are closed under the edges.
  if !fromRoot.all id then .disconnected fromRoot else
  let (inTree, toRoot) := bfs n (fun p c ↦ adj c p) 0
  -- The vertices not reaching `0` are closed under the edges.
  if !toRoot.all id then .disconnected (toRoot.map not) else
  .connected outTree inTree

/-- The Boolean adjacency matrix of the matrix with rows `lit`, evaluated by the kernel. Returns
`none` if the kernel cannot decide which entries are zero. -/
def evalAdjMatrix? {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (dα : Q(DecidableEq $α)) (n : Nat)
    (lit : Q(List (List $α))) : MetaM (Option (Array (Array Bool))) := do
  let .ok (.lit (.natVal bits)) := Kernel.whnf (← getEnv) {} q(packRows $n $lit) | return none
  return some <| Array.ofFn (n := n) fun i ↦ Array.ofFn (n := n) fun j ↦ bits.testBit (i * n + j)

/-- The number `packRows n lit` that packs the Boolean adjacency matrix of `ofLists n n lit`, and
the proof that `packedAdj` reads that matrix from it. -/
def certifyPackedAdj {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (dα : Q(DecidableEq $α))
    (n : Nat) (lit : Q(List (List $α))) :
    (bits : Q(Nat)) × Q(∀ i j, packedAdj $n $bits i j ↔ ofLists $n $n $lit i j ≠ 0) :=
  ⟨q(packRows $n $lit), q(packedAdj_packRows_iff $lit)⟩

/-- Prove that the matrix with rows `lit` is indecomposable from the spanning out-tree `outTree`
from vertex `0` and the in-tree `inTree` to it in its graph. -/
def certifyIsIndecomposable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (dα : Q(DecidableEq $α))
    (n : Nat) (lit : Q(List (List $α))) (outTree inTree : Array (Nat × Nat)) :
    MetaM Q((ofLists $n $n $lit).IsIndecomposable) := do
  let root : Q(Fin $n) ← mkFinLitQ n 0
  let outTreeQ ← mkEdgeListLitQ n outTree
  let inTreeQ ← mkEdgeListLitQ n inTree
  let ⟨bits, hadj⟩ := certifyPackedAdj zα dα n lit
  let adj : Q(Fin $n → Fin $n → Bool) := q(packedAdj $n $bits)
  let hout ← mkDecideProofQ q(SpansFrom $adj $outTreeQ $root)
  let hin ← mkDecideProofQ q(SpansFrom (fun i j ↦ $adj j i) $inTreeQ $root)
  return q(isIndecomposable_of_spansFrom $hadj $hout $hin)

/-- Prove that the matrix with rows `lit` is decomposable from a nonempty proper set `closedSet` of
vertices that no edge of its graph leaves. -/
def certifyNotIsIndecomposable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α))
    (dα : Q(DecidableEq $α)) (n : Nat) (lit : Q(List (List $α))) (closedSet : Array Bool) :
    MetaM Q(¬(ofLists $n $n $lit).IsIndecomposable) := do
  let (some i, some j) := (closedSet.findIdx? id, closedSet.findIdx? not)
    | throwError "reduceIsIndecomposable: the closed set {closedSet} is empty or full"
  let closedSetQ : Q(Nat) := mkNatLitQ (Nat.ofBits (n := n) (closedSet[·]!))
  let iQ : Q(Fin $n) ← mkFinLitQ n i
  let jQ : Q(Fin $n) ← mkFinLitQ n j
  let hij ← mkDecideProofQ q(Nat.testBit $closedSetQ $iQ ≠ Nat.testBit $closedSetQ $jQ)
  let ⟨bits, hadj⟩ := certifyPackedAdj zα dα n lit
  let hc ← mkDecideProofQ q(isClosedPacked $n $bits $closedSetQ = true)
  return q(not_isIndecomposable_of_isClosed $hadj (isClosed_of_isClosedPacked $hc) $hij)

/-- Core of the `Matrix.reduceIsIndecomposable` simproc. -/
def reduceIsIndecomposableCore : Simp.Simproc := fun e ↦ do
  let e ← instantiateMVars e
  let_expr Matrix.IsIndecomposable finN R zR M := e | return .continue
  let_expr Fin nE := finN | return .continue
  let some n ← getNatValue? nE | return .continue
  let u ← getDecLevel R
  have α : Q(Type u) := R
  have zα : Q(Zero $α) := zR
  if n == 0 then
    have M : Q(Matrix (Fin 0) (Fin 0) $α) := M
    let pf : Q(($M).IsIndecomposable) := q((isIndecomposable_iff_reflTransGen $M).2 (·.elim0))
    return .done { expr := q(True), proof? := q(eq_true $pf) }
  have M : Q(Matrix (Fin $n) (Fin $n) $α) := M
  let .some dα ← trySynthInstanceQ q(DecidableEq $α) | return .continue
  let some (_, _, _, entries) ← matchMatrixLit? M | return .continue
  let rows : List (List Q($α)) := entries.toList.map Array.toList
  let lit : Q(List (List $α)) := mkListLitQ (α := q(List $α)) (rows.map mkListLitQ)
  let some adjMatrix ← evalAdjMatrix? zα dα n lit | return .continue
  -- The certificates are stated on `ofLists n n lit`. The kernel checks that it is `M` when it
  -- checks the hint.
  match decideStronglyConnected adjMatrix with
  | .connected outTree inTree =>
    let pf ← certifyIsIndecomposable zα dα n lit outTree inTree
    let type ← mkEq e q(True)
    return .done { expr := q(True), proof? := mkExpectedPropHint q(eq_true $pf) type }
  | .disconnected closedSet =>
    let pf ← certifyNotIsIndecomposable zα dα n lit closedSet
    let type ← mkEq e q(False)
    return .done { expr := q(False), proof? := mkExpectedPropHint q(eq_false $pf) type }

end Mathlib.Tactic.Matrix.IsIndecomposable

open Mathlib.Tactic.Matrix.IsIndecomposable

/-- `Matrix.reduceIsIndecomposable` decides `M.IsIndecomposable` for a closed matrix literal `M`
indexed by `Fin n` with `n` a numeral, whose entries have an equality the kernel can decide. -/
simproc_decl Matrix.reduceIsIndecomposable (Matrix.IsIndecomposable _) :=
  reduceIsIndecomposableCore
