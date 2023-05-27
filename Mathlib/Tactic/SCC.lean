/-
Copyright (c) 2018 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module tactic.scc
! leanprover-community/mathlib commit d6814c584384ddf2825ff038e868451a7c956f31
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Init.Logic
import Mathlib.Control.Basic
import Qq

/-!
# Strongly Connected Components

This file defines tactics to construct proofs of equivalences between a set of mutually equivalent
propositions. The tactics use implications transitively to find sets of equivalent propositions.

## Implementation notes

The tactics use a strongly connected components algorithm on a graph where propositions are
vertices and edges are proofs that the source implies the target. The strongly connected components
are therefore sets of propositions that are pairwise equivalent to each other.

The resulting strongly connected components are encoded in a disjoint set data structure to
facilitate the construction of equivalence proofs between two arbitrary members of an equivalence
class.

## Possible generalizations

Instead of reasoning about implications and equivalence, we could generalize the machinery to
reason about arbitrary partial orders.

## References

 * Tarjan, R. E. (1972), "Depth-first search and linear graph algorithms",
   SIAM Journal on Computing, 1 (2): 146–160, doi:10.1137/0201010
 * Dijkstra, Edsger (1976), A Discipline of Programming, NJ: Prentice Hall, Ch. 25.
 * <https://en.wikipedia.org/wiki/Disjoint-set_data_structure>

## Tags

graphs, tactic, strongly connected components, disjoint sets
-/


namespace Mathlib.Tactic.SCC
open Lean Meta Elab Tactic Qq

/-- `Closure` implements a disjoint set data structure using path compression
optimization. For the sake of the scc algorithm, it also stores the preorder
numbering of the equivalence graph of the local assumptions.

The `ExprMap` encodes a directed forest by storing for every non-root
node, a reference to its parent and a proof of equivalence between
that node's expression and its parent's expression. Given that data
structure, checking that two nodes belong to the same tree is easy and
fast by repeatedly following the parent references until a root is reached.
If both nodes have the same root, they belong to the same tree, i.e. their
expressions are equivalent. The proof of equivalence can be formed by
composing the proofs along the edges of the paths to the root.

More concretely, if we ignore preorder numbering, the set
`{ {e₀,e₁,e₂,e₃}, {e₄,e₅} }` is represented as:

```
e₀ → ⊥      -- no parent, i.e. e₀ is a root
e₁ → e₀, p₁ -- with p₁ : e₁ ↔ e₀
e₂ → e₁, p₂ -- with p₂ : e₂ ↔ e₁
e₃ → e₀, p₃ -- with p₃ : e₃ ↔ e₀
e₄ → ⊥      -- no parent, i.e. e₄ is a root
e₅ → e₄, p₅ -- with p₅ : e₅ ↔ e₄
```

We can check that `e₂` and `e₃` are equivalent by seeking the root of
the tree of each. The parent of `e₂` is `e₁`, the parent of `e₁` is
`e₀` and `e₀` does not have a parent, and thus, this is the root of its tree.
The parent of `e₃` is `e₀` and it's also the root, the same as for `e₂` and
they are therefore equivalent. We can build a proof of that equivalence by using
transitivity on `p₂`, `p₁` and `p₃.symm` in that order.

Similarly, we can discover that `e₂` and `e₅` aren't equivalent.

A description of the path compression optimization can be found at:
<https://en.wikipedia.org/wiki/Disjoint-set_data_structure#Path_compression>

-/
def Closure := HashMap Q(Prop) (ℕ ⊕ (Q(Prop) × Expr))

/-- The tactic monad with mutable `Closure`. -/
abbrev ClosureM := StateRefT Closure TacticM

/-- `m.run` creates an empty `Closure` `c`, executes `m` on `c`, and then deletes `c`,
returning the output of `m`. -/
def ClosureM.run {α : Type _} (m : ClosureM α) : TacticM α := StateRefT'.run' m mkHashMap

/-- Gets the closure. -/
def getClosure : ClosureM Closure := get

/-- Modifies the closure. -/
def modifyClosure : (Closure → Closure) → ClosureM Unit := modify

/-- `toTacticFormat` pretty-prints the `Closure` as a list. Assuming the closure was built by
`dfsAt`, each element corresponds to a node `pᵢ : Expr` and is one of the folllowing:
- if `pᵢ` is a root: `"pᵢ ⇐ i"`, where `i` is the preorder number of `pᵢ`,
- otherwise: `"(pᵢ, pⱼ) : P"`, where `P` is `pᵢ ↔ pⱼ`.
Useful for debugging. -/
def toTacticFormat : ClosureM Format := do
  let m ← getClosure
  let l := m.toList
  let fmt ←
    l.mapM fun ⟨x, y⟩ => do
        match y with
        | Sum.inl y => return f!"{← ppExpr x} ⇐ {y}"
        | Sum.inr ⟨y, p⟩ => return f!"({← ppExpr x}, {← ppExpr y}) : {← ppExpr (← inferType p)}"
  return format fmt

/-- `(n, r, p) ← root e` returns `r` the root of the tree that `e` is a part of (which might be
itself) along with `p` a proof of `e ↔ r` and `n`, the preorder numbering of the root. -/
partial def root (e : Q(Prop)) : ClosureM (ℕ × Q(Prop) × Expr) := do
  let cl ← getClosure
  match cl.find? e with
    | none =>
      return (0, e, q(Iff.refl $e))
    | some (Sum.inl n) => do
      pure (n, e, q(Iff.refl $e))
    | some (Sum.inr (e₀, (p₀ : Q($e ↔ $e₀)))) => do
      let (n, e₁, (p₁ : Q($e₀ ↔ $e₁))) ← root e₀
      modifyClosure fun cl => cl.insert e (Sum.inr (e₁, q(Iff.trans $p₀ $p₁)))
      pure (n, e₁, q(Iff.trans $p₀ $p₁))

/-- `merge p`, with `p` a proof of `e₀ ↔ e₁` for some `e₀` and `e₁`, merges the trees of `e₀` and
`e₁` and keeps the root with the smallest preorder number as the root. This ensures that, in the
depth-first traversal of the graph, when encountering an edge going into a vertex whose equivalence
class includes a vertex that originated the current search, that vertex will be the root of the
corresponding tree. -/
def merge (p : Expr) : ClosureM Unit := do
  let ty : Q(Prop) ← inferType p
  let ~q($e₀ ↔ $e₁) := ty | throwError "{p} must be a proof of `e₀ ↔ e₁`"
  have p : Q($e₀ ↔ $e₁) := p
  let (n₂, e₂, (p₂ : Q($e₀ ↔ $e₂))) ← root e₀
  let (n₃, e₃, (p₃ : Q($e₁ ↔ $e₃))) ← root e₁
  if !(e₂ == e₃) then
    if n₂ < n₃ then
      modifyClosure fun cl =>
        cl.insert e₃ (Sum.inr (e₂, q(Iff.trans (Iff.trans (Iff.symm $p₃) (Iff.symm $p)) $p₂)))
    else
      modifyClosure fun cl =>
        cl.insert e₂ (Sum.inr (e₃, q(Iff.trans (Iff.trans (Iff.symm $p₂) $p) $p₃)))

/-- Sequentially assign numbers to the nodes of the graph as they are being visited. -/
def assignPreorder (e : Q(Prop)) : ClosureM Unit :=
  modifyClosure fun cl => cl.insert e (Sum.inl cl.size)

/-- `proveEqv e₀ e₁` constructs a proof of equivalence of `e₀` and `e₁` if
they are equivalent. -/
def proveEqv (e₀ e₁ : Q(Prop)) : ClosureM Q($e₀ ↔ $e₁) := do
  let (_, r, (p₀ : Q($e₀ ↔ $r))) ← root e₀
  let (_, r', (p₁ : Q($e₁ ↔ $r))) ← root e₁
  unless r == r' do throwError "{e₀} and {e₁} are not equivalent"
  return q(Iff.trans $p₀ (Iff.symm $p₁))

/-- `proveImpl e₀ e₁` constructs a proof of `e₀ → e₁` if they are equivalent. -/
def proveImpl (e₀ e₁ : Q(Prop)) : ClosureM Q($e₀ → $e₁) := do
  let p ← proveEqv e₀ e₁
  return q(Iff.mp $p)

/-- `isEqv cl e₀ e₁` checks whether `e₀` and `e₁` are equivalent without building a proof. -/
def isEqv (e₀ e₁ : Q(Prop)) : ClosureM Bool := do
  let (_, r, _) ← root e₀
  let (_, r', _) ← root e₁
  return r == r'

/-- `mergePath path e`, where `path` and `e` forms a cycle with proofs of implication between
consecutive vertices. The proofs are compiled into proofs of equivalences and added to the closure
structure. `e` and the first vertex of `path` do not have to be the same but they have to be
in the same equivalence class. -/
def mergePath (path : List (Q(Prop) × Expr)) (e : Q(Prop)) : ClosureM Unit := do
  let some (e', _) := path.head? | throwError "{path} should not be nil"
  let p₁ : Expr ← proveImpl e e'
  let p₂ : Expr := q(@id $e)
  let path := (e, p₁) :: path
  let (_, ls) ← List.mapAccumLM
    (fun p p' => Prod.mk <$>
      mkAppOptM ``Implies.trans #[none, some p'.1, none, some p, some p'.2] <*> pure p)
    p₂ path
  let (_, rs) ← List.mapAccumRM
    (fun p p' => Prod.mk <$>
      mkAppOptM ``Implies.trans #[none, none, none, some p.2, some p'] <*> pure p')
    p₂ path
  let ps ← zipWithM (fun p₀ p₁ => mkAppM ``Iff.intro #[p₀, p₁]) ls.tail rs.dropLast
  ps.forM merge

/-- (implementation of `collapse`) -/
def collapse' : List (Q(Prop) × Expr) → List (Q(Prop) × Expr) → Q(Prop) → ClosureM Unit
  | acc, [], v => mergePath acc v
  | acc, (x, pr) :: xs, v => do
    let b ← isEqv x v
    let acc' := (x, pr) :: acc
    if b then mergePath acc' v else collapse' acc' xs v

/-- `collapse path v`, where `v` is a vertex that originated the current search
(or a vertex in the same equivalence class as the one that originated the current search).
It or its equivalent should be found in `path`. Since the vertices following `v` in the path
form a cycle with `v`, they can all be added to an equivalence class. -/
def collapse : List (Q(Prop) × Expr) → Q(Prop) → ClosureM Unit :=
  collapse' []

/-- mutable graphs between local propositions that imply each other with the proof of implication -/
def ImplGraph := HashMap Q(Prop) (List (Q(Prop) × Expr))

/-- `SCCM` monad state. -/
structure State where
  /-- mutable graphs between local propositions that imply each other with the proof of
  implication -/
  graph : ImplGraph := mkHashMap
  /-- visited propositions by `dfsAt` -/
  visit : HashMap Q(Prop) Bool := mkHashMap

abbrev SCCM := StateRefT State ClosureM

/-- `m.run` creates an empty `State` `s`, executes `m` on `s`, and then deletes
`s`, returning the output of `m`. -/
def SCCM.run {α : Type _} (m : SCCM α) : ClosureM α := StateRefT'.run' m {}

/-- Gets the state. -/
def getState : SCCM State := get

/-- Modifies the state. -/
def modifyState : (State → State) → SCCM Unit := modify

/-- `addEdge p`, with `p` a proof of `v₀ → v₁` or `v₀ ↔ v₁`, adds an edge to the implication
graph . -/
partial def addEdge (p : Expr) : SCCM Unit := do
  let ty : Q(Prop) ← inferType p
  match ty with
  | ~q((($v₀ : Prop)) → $v₁) => do
    let ⟨g, _⟩ ← getState
    let xs := (g.find? v₀).getD []
    let xs' := (g.find? v₁).getD []
    modifyState fun ⟨g, vi⟩ => ⟨g.insert v₀ ((v₁, p) :: xs) |>.insert v₁ xs', vi⟩
  | ~q($v₀ ↔ $v₁) => do
    let p : Q($v₀ ↔ $v₁) := p
    addEdge q(Iff.mp $p)
    addEdge q(Iff.mpr $p)
  | _ => throwError "{p} must be a proof of `e₀ → e₁` or `e₀ ↔ e₁`"

open List

/-- Strongly connected component algorithm inspired by Tarjan's and
Dijkstra's scc algorithm. Whereas they return strongly connected
components by enumerating them, this algorithm returns a disjoint set
data structure using path compression. This is a compact
representation that allows us, after the fact, to construct a proof of
equivalence between any two members of an equivalence class.

 * Tarjan, R. E. (1972), "Depth-first search and linear graph algorithms",
   SIAM Journal on Computing, 1 (2): 146–160, doi:10.1137/0201010
 * Dijkstra, Edsger (1976), A Discipline of Programming, NJ: Prentice Hall, Ch. 25.
-/
partial def dfsAt (vs : List (Q(Prop) × Expr)) (v : Q(Prop)) : SCCM Unit := do
  let ⟨g, vi⟩ ← getState
  let (_, v', _) ← root v
  match vi.find? v' with
  | some true => return
  | some false => collapse vs v
  | none =>
    assignPreorder v
    modifyState fun ⟨g, vi⟩ => ⟨g, vi.insert v false⟩
    let some ns := g.find? v | throwError "{v} is not found in the graph"
    ns.forM fun (w, e) => dfsAt ((v, e) :: vs) w
    modifyState fun ⟨g, vi⟩ => ⟨g, vi.insert v true⟩

/-- Use the local assumptions to create a set of equivalence classes. -/
def mkSCC : ClosureM (HashMap Q(Prop) (List (Q(Prop) × Expr))) :=
  SCCM.run do
    let ls ← getLocalHyps
    ls.forM fun l => try addEdge l catch _ => return
    let ⟨g, _⟩ ← getState
    g.forM fun v _ => dfsAt [] v
    return g

def proveEqvTarget : ClosureM Unit := do
  let ty : Q(Prop) ← whnf (← getMainTarget)
  let ~q($p ↔ $q) := ty | throwError "goal is not the form `p ↔ q`"
  closeMainGoal (← proveEqv p q)


/-- `scc` uses the available equivalences and implications to prove a goal of the form `p ↔ q`.
```lean
example (p q r : Prop) (hpq : p → q) (hqr : q ↔ r) (hrp : r → p) : p ↔ r := by
  scc
```
-/
elab "scc" : tactic =>
  ClosureM.run do
    discard mkSCC
    let ty : Q(Prop) ← getMainTarget
    let ~q($p ↔ $q) := ty | throwError "goal is not the form `p ↔ q`"
    closeMainGoal (← proveEqv p q)

/-- Collect all the available equivalences and implications and
add assumptions for every equivalence that can be proven using the
strongly connected components technique. Mostly useful for testing. -/
elab "scc'" : tactic =>
  ClosureM.run do
    let g ← mkSCC
    let ls := g.toList.map Prod.fst
    let ls' := product ls ls
    ls'.forM fun x => do
      let n ← getUnusedUserName `h
      try
        let e ← proveEqv x.1 x.2
        liftMetaTactic fun m₁ => do
          let m₂ ← m₁.assert n q($(x.1) ↔ $(x.2)) e
          let (_, m₃) ← m₂.intro n
          return [m₃]
      catch _ => return

end Mathlib.Tactic.SCC
