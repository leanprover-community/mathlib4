import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace SimpleGraph

open ConnectedComponent Subgraph

variable {α β : Type*} {n : ℕ} {G : SimpleGraph α}

def coloringOfComponents
    (h : ∀ (c : G.ConnectedComponent), (G.induce c.supp).Coloring β) :
    G.Coloring β := by
  exact ⟨fun v ↦ h (G.connectedComponentMk v) ⟨v, rfl⟩, by
    simp only [top_adj]
    intro a b hab heq
    have := connectedComponentMk_eq_of_adj hab
    have hadj : (G.induce (G.connectedComponentMk a).supp).Adj ⟨a, rfl⟩
       ⟨b, ((G.connectedComponentMk a).mem_supp_congr_adj hab).1 rfl⟩ := by simpa using hab
    exact (h _).valid hadj (by convert heq)⟩

theorem colorable_iff_forall_connectedComponents  :
    G.Colorable n ↔ ∀ c : G.ConnectedComponent, (G.induce c.supp).Colorable n :=
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

/-- `G` is `n`-colorable if all its induced connected subgraphs are `n`-colorable-/
theorem colorable_iff_forall_induced_connected :
    (∀ s, (G.induce s).Connected → (G.induce s).Colorable n) ↔ G.Colorable n := by
  constructor <;> intro h
  · rw [colorable_iff_forall_connectedComponents]
    exact fun c ↦ h _ c.induce_supp_connected
  · intro s _
    obtain ⟨C⟩ := h
    exact ⟨fun v ↦ (C v.1), fun a ↦ Hom.map_adj C a⟩

lemma colorable_iff_spanningCoe (s : Set α) :
    (G.induce s).Colorable (n + 1) ↔ (G.induce s).spanningCoe.Colorable (n + 1) := by
  classical
  constructor <;> intro ⟨C⟩
  · exact ⟨fun v ↦ if h : v ∈ s then (C ⟨v, h⟩) else 0, by
      simp only [map_adj, comap_adj, Function.Embedding.subtype_apply, Subtype.exists,
        exists_and_left, exists_prop, existsAndEq, and_true, true_and, top_adj, ne_eq, and_imp]
      intro a b h ha hb he
      split_ifs at he
      apply C.valid _ he
      simpa⟩
  · exact ⟨fun v ↦ (C v.1), by
      simp only [comap_adj, Function.Embedding.subtype_apply, top_adj, ne_eq, Subtype.forall]
      intro a ha b hb h
      apply C.valid
      simpa using ⟨h,ha,hb⟩⟩

end SimpleGraph
