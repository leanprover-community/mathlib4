/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Trail
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!

# Trail, Path, and Cycle

In a simple graph,

* A *circuit* is a nonempty trail whose first and last vertices are the
  same.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk.IsCircuit`

## Tags
trails, paths, circuits, cycles, bridge edges
-/

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w}
variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

namespace Walk

variable {G} {u v w : V}

/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
@[mk_iff isCircuit_def]
structure IsCircuit {u : V} (p : G.Walk u u) : Prop extends IsTrail p where
  ne_nil : p ≠ nil

-- Porting note: used to use `extends to_trail : is_trail p` in structure
protected lemma IsCircuit.isTrail {p : Walk G u u} (h : IsCircuit p) : IsTrail p := h.toIsTrail

@[simp]
theorem isCircuit_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCircuit ↔ p.IsCircuit := by
  subst_vars
  rfl

lemma IsCircuit.not_nil {p : G.Walk v v} (hp : IsCircuit p) : ¬ p.Nil := (hp.ne_nil ·.eq_nil)

section WalkDecomp

variable [DecidableEq V]

protected theorem IsCircuit.rotate {u v : V} {c : G.Walk v v} (hc : c.IsCircuit)
    (h : u ∈ c.support) : (c.rotate h).IsCircuit := by
  refine ⟨hc.isTrail.rotate _, ?_⟩
  cases c
  · exact (hc.ne_nil rfl).elim
  · intro hn
    have hn' := congr_arg length hn
    rw [rotate, length_append, add_comm, ← length_append, take_spec] at hn'
    simp at hn'


end WalkDecomp

end Walk

/-! ### Mapping paths -/

namespace Walk

variable {G G' G''}
variable (f : G →g G') {u v : V} (p : G.Walk u v)
variable {p f}

end Walk

end SimpleGraph
