/-
Copyright (c) 2018 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module tactic.scc
! leanprover-community/mathlib commit d6814c584384ddf2825ff038e868451a7c956f31
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Tactic.Tauto

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

namespace ClosureM

/-- `m.run` creates an empty `Closure` `c`, executes `m` on `c`, and then deletes `c`,
returning the output of `m`. -/
def run {α : Type _} (m : ClosureM α) : TacticM α := StateRefT'.run' m mkHashMap

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
        | Sum.inl y => return f!"{x} ⇐ {y}"
        | Sum.inr ⟨y, p⟩ => return f!"({x}, {y}) : {← inferType p}"
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
  if e₂ == e₃ then
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
  guard (r == r') <|> throwError "{e₀} and {e₁} are not equivalent"
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

end ClosureM

/-- mutable graphs between local propositions that imply each other with the proof of implication -/
def ImplGraph := HashMap Q(Prop) (List (Q(Prop) × Expr))

/-- `with_impl_graph f` creates an empty `impl_graph` `g`, executes `f` on `g`, and then deletes
`g`, returning the output of `f`. -/
unsafe def with_impl_graph {α} : (impl_graph → tactic α) → tactic α :=
  using_new_ref (expr_map.mk (List <| expr × expr))

namespace ImplGraph

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `add_edge g p`, with `p` a proof of `v₀ → v₁` or `v₀ ↔ v₁`, adds an edge to the implication
      graph `g`. -/
    unsafe
  def
    add_edge
    ( g : impl_graph ) : expr → tactic Unit
    |
      p
      =>
      do
        let t ← infer_type p
          match
            t
            with
            |
                q( $ ( v₀ ) → $ ( v₁ ) )
                =>
                do
                  is_prop v₀ >>= guardb
                    is_prop v₁ >>= guardb
                    let m ← read_ref g
                    let xs := ( m v₀ ) . getD [ ]
                    let xs' := ( m v₁ ) . getD [ ]
                    modify_ref g fun m => ( m v₀ ( ( v₁ , p ) :: xs ) ) . insert v₁ xs'
              |
                q( $ ( v₀ ) ↔ $ ( v₁ ) )
                =>
                do
                  let p₀ ← mk_mapp ` ` Iff.mp [ none , none , p ]
                    let p₁ ← mk_mapp ` ` Iff.mpr [ none , none , p ]
                    add_edge p₀
                    add_edge p₁
              | _ => failed

section Scc

open List

parameter (g : expr_map (List <| expr × expr))

parameter (visit : ref <| expr_map Bool)

parameter (cl : closure)

/-- `merge_path path e`, where `path` and `e` forms a cycle with proofs of implication between
consecutive vertices. The proofs are compiled into proofs of equivalences and added to the closure
structure. `e` and the first vertex of `path` do not have to be the same but they have to be
in the same equivalence class. -/
unsafe def merge_path (path : List (expr × expr)) (e : expr) : tactic Unit := do
  let p₁ ← cl.prove_impl e Path.headI.fst
  let p₂ ← mk_mapp `` id [e]
  let path := (e, p₁) :: Path
  let (_, ls) ←
    Path.mapAccumLM
        (fun p p' => Prod.mk <$> mk_mapp `` Implies.trans [none, p'.1, none, p, p'.2] <*> pure p) p₂
  let (_, rs) ←
    Path.mapAccumRM
        (fun p p' => Prod.mk <$> mk_mapp `` Implies.trans [none, none, none, p.2, p'] <*> pure p')
        p₂
  let ps ← zipWithM (fun p₀ p₁ => mk_app `` Iff.intro [p₀, p₁]) ls.tail rs.dropLast
  ps cl

/-- (implementation of `collapse`) -/
unsafe def collapse' : List (expr × expr) → List (expr × expr) → expr → tactic Unit
  | Acc, [], v => merge_path Acc v
  | Acc, (x, pr) :: xs, v => do
    let b ← cl.is_eqv x v
    let acc' := (x, pr) :: Acc
    if b then merge_path acc' v else collapse' acc' xs v

/-- `collapse path v`, where `v` is a vertex that originated the current search
(or a vertex in the same equivalence class as the one that originated the current search).
It or its equivalent should be found in `path`. Since the vertices following `v` in the path
form a cycle with `v`, they can all be added to an equivalence class. -/
unsafe def collapse : List (expr × expr) → expr → tactic Unit :=
  collapse' []

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
unsafe def dfs_at : List (expr × expr) → expr → tactic Unit
  | vs, v => do
    let m ← read_ref visit
    let (_, v', _) ← cl.root v
    match m v' with
      | some tt => pure ()
      | some ff => collapse vs v
      | none => do
        cl v
        modify_ref visit fun m => m v ff
        let ns ← g v
        ns fun ⟨w, e⟩ => dfs_at ((v, e) :: vs) w
        modify_ref visit fun m => m v tt
        pure ()

end Scc

/-- Use the local assumptions to create a set of equivalence classes. -/
unsafe def mk_scc (cl : closure) : tactic (expr_map (List (expr × expr))) :=
  with_impl_graph fun g =>
    using_new_ref (expr_map.mk Bool) fun visit => do
      let ls ← local_context
      ls fun l => try (g l)
      let m ← read_ref g
      m fun ⟨v, _⟩ => impl_graph.dfs_at m visit cl [] v
      pure m

end ImplGraph

-- failed to format: unknown constant 'term.pseudo.antiquot'
unsafe
  def
    prove_eqv_target
    ( cl : closure ) : tactic Unit
    := do let q( $ ( p ) ↔ $ ( q ) ) ← target >>= whnf cl p q >>= exact

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `scc` uses the available equivalences and implications to prove
      a goal of the form `p ↔ q`.

      ```lean
      example (p q r : Prop) (hpq : p → q) (hqr : q ↔ r) (hrp : r → p) : p ↔ r :=
      by scc
      ```
      -/
    unsafe
  def
    interactive.scc
    : tactic Unit
    :=
      closure.with_new_closure
        fun cl => do impl_graph.mk_scc cl let q( $ ( p ) ↔ $ ( q ) ) ← target cl p q >>= exact

/-- Collect all the available equivalences and implications and
add assumptions for every equivalence that can be proven using the
strongly connected components technique. Mostly useful for testing. -/
unsafe def interactive.scc' : tactic Unit :=
  closure.with_new_closure fun cl => do
    let m ← impl_graph.mk_scc cl
    let ls := m.toList.map Prod.fst
    let ls' := Prod.mk <$> ls <*> ls
    ls' fun x => do
        let h ← get_unused_name `h
        try <| closure.prove_eqv cl x.1 x.2 >>= note h none

/-- `scc` uses the available equivalences and implications to prove
a goal of the form `p ↔ q`.

```lean
example (p q r : Prop) (hpq : p → q) (hqr : q ↔ r) (hrp : r → p) : p ↔ r :=
by scc
```

The variant `scc'` populates the local context with all equivalences that `scc` is able to prove.
This is mostly useful for testing purposes.
-/
add_tactic_doc
  { Name := "scc"
    category := DocCategory.tactic
    declNames := [`` interactive.scc, `` interactive.scc']
    tags := ["logic"] }

end Mathlib.Tactic.SCC
