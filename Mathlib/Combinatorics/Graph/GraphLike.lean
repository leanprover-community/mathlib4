/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Laura Monk, Freddie Nash
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.Graph.Basic

/-!
In this file we make `Graph` an instance of `GraphLike`.
-/

@[expose] public section

variable {α β : Type*} {G : Graph α β}

namespace Graph

/-- The type of darts in a (multi-)graph. Special care is given to ensure there are two loop darts
rather than one. -/
inductive Dart (α β : Type*)
| dir (e : β) (x y : α) (hne : x ≠ y) : Dart α β
| fwd (e : β) (x : α) : Dart α β
| bck (e : β) (x : α) : Dart α β

/-- The edge of a dart. -/
def Dart.edge (d : Dart α β) : β := match d with
| Dart.dir e _ _ _ => e
| Dart.fwd e _ => e
| Dart.bck e _ => e

/-- The first vertex of a dart. -/
def Dart.fst (d : Dart α β) : α := match d with
| Dart.dir _ x _ _ => x
| Dart.fwd _ x => x
| Dart.bck _ x => x

/-- The second vertex of a dart. -/
def Dart.snd (d : Dart α β) : α := match d with
| Dart.dir _ _ y _ => y
| Dart.fwd _ x => x
| Dart.bck _ x => x

instance : DartLike α (Dart α β) where
  fst d := d.fst
  snd d := d.snd

instance : GraphLike α (Dart α β) (Graph α β) where
  verts G := V(G)
  darts G := { d | G.IsLink d.edge d.fst d.snd }
  fst_mem_of_darts h := h.left_mem
  snd_mem_of_darts h := h.right_mem
  Adj G := G.Adj
  exists_darts_iff_adj {G u v} := by
    refine ⟨?_, fun ⟨e, he⟩ ↦ ?_⟩
    · rintro ⟨d, ha, rfl, rfl⟩
      exact ha.adj
    obtain rfl | hne := eq_or_ne u v
    · exact ⟨Dart.fwd e u, he, rfl, rfl⟩
    exact ⟨Dart.dir e u v hne, he, rfl, rfl⟩

lemma darts_def (G : Graph α β) : GraphLike.darts G = { d | G.IsLink d.edge d.fst d.snd } :=
  rfl

end Graph
