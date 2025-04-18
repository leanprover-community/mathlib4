import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

@[ext]
structure MyGraph (V : Type*)  where
  /-- Vertices of the graph -/
  verts : Set V
  /-- Edges of the graph -/
  Adj : V → V → Prop
  edge_vert : ∀ {v w : V}, Adj v w → v ∈ verts
  symm : Symmetric Adj
  loopless : Irreflexive Adj

namespace SimpleGraph

open ConnectedComponent Subgraph

variable {α β : Type*} {n : ℕ} {G : SimpleGraph α}

def coloringOfComponents
    (h : ∀ (c : G.ConnectedComponent), (G.induce c).Coloring β) :
    G.Coloring β := by
  exact ⟨fun v ↦ h (G.connectedComponentMk v) ⟨v, rfl⟩, by
    simp only [top_adj]
    intro a b hab heq
    have := connectedComponentMk_eq_of_adj hab
    have hadj : (G.induce (G.connectedComponentMk a).supp).Adj ⟨a, rfl⟩
       ⟨b, ((G.connectedComponentMk a).mem_supp_congr_adj hab).1 rfl⟩ := by simpa using hab
    exact (h _).valid hadj (by convert heq)⟩

theorem colorable_iff_forall_connectedComponents  :
    G.Colorable n ↔ ∀ c : G.ConnectedComponent, (G.induce c).Colorable n :=
  ⟨fun ⟨C⟩ _ ↦ ⟨fun v ↦ C v.1, fun h h1 ↦ C.valid h h1⟩,
     fun h ↦ ⟨coloringOfComponents (fun c ↦ (h c).some)⟩⟩

lemma ConnectedComponent.induce_supp_connected (c : G.ConnectedComponent) :
    (G.induce c).Connected := by
  rw [connected_induce_iff, connected_iff_forall_exists_walk_subgraph]
  refine ⟨c.nonempty_supp,?_⟩
  intro u v hu hv
  obtain ⟨w⟩ := ConnectedComponent.exact (hv ▸ hu)
  use w
  induction w with
  | nil => simpa
  | cons h p ih =>
    simp_rw [Walk.toSubgraph, sup_le_iff]
    constructor
    · apply subgraphOfAdj_le_of_adj
      simpa using ⟨hu, hu ▸ (connectedComponentMk_eq_of_adj h).symm, h⟩
    · exact ih (hu ▸ (connectedComponentMk_eq_of_adj h).symm) hv

/-- `G` is `n`-colorable if all its induced connected subgraphs are `n`-colorable -/
theorem colorable_iff_forall_induced_connected :
    (∀ s, (G.induce s).Connected → (G.induce s).Colorable n) ↔ G.Colorable n := by
  constructor <;> intro h
  · rw [colorable_iff_forall_connectedComponents]
    exact fun c ↦ h _ c.induce_supp_connected
  · intro s _
    obtain ⟨C⟩ := h
    exact ⟨fun v ↦ (C v.1), fun a ↦ Hom.map_adj C a⟩

section PartialColorings

variable {s t : Set α} {G' : Subgraph G}
namespace Subgraph

/-- A `β coloring` of a subgraph `G'` is `C : α → β` that sends adjacent vertices in `G'` to
different colors. -/
abbrev Coloring (G' : G.Subgraph) (β : Type*) := G'.Adj →r (⊤ : SimpleGraph β).Adj

variable {C : G'.Coloring β} {a : α}
theorem Coloring.valid {v w : α} (h : G'.Adj v w) : C v ≠ C w :=
  C.map_rel h

def Coloring.mk (color : α → β) (valid : ∀ {v w : α}, G'.Adj v w → color v ≠ color w) :
    G'.Coloring β :=
  ⟨color, valid⟩

def Coloring.mk' (color : α → β)
    (valid' : ∀ {v w : α}, v ∈ G'.verts → w ∈ G'.verts → G'.Adj v w → color v ≠ color w) :
    G'.Coloring β :=
  ⟨color, by intro a b h1; apply valid' h1.fst_mem h1.snd_mem h1⟩

instance : Coe (G'.Coloring β) (G'.spanningCoe.Coloring β) where
  coe := fun C ↦ ⟨C, by intro _ _ ; simpa using C.valid⟩

instance : Coe (G'.Coloring β) (G'.coe.Coloring β) where
  coe := fun C ↦ ⟨fun a ↦ C a.1, by intro _ _ ; simpa using C.valid⟩


end Subgraph
abbrev PartialColoring (G : SimpleGraph α) (s : Set α) (β : Type*) :=
    (G.induce s).Coloring β

@[simp]
def ofCongr (C : G.PartialColoring s β) (h : s = t) : G.PartialColoring t β := by
  unfold PartialColoring at *
  rwa [← h]

end PartialColorings
end SimpleGraph
