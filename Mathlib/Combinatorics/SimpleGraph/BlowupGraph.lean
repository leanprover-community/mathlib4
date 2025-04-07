import Mathlib.Combinatorics.SimpleGraph.Coloring

namespace SimpleGraph

/-- Given a family of vertex types indexed by `ι`, pulling back from `H : SimpleGraph ι`
yields the blow-up graph on the family. Two vertices are adjacent if and only if their
indices are adjacent in `H`. -/
abbrev blowupGraph {ι : Type*} (H : SimpleGraph ι) (V : ι → Type*) : SimpleGraph (Σ i, V i) :=
  SimpleGraph.comap Sigma.fst H

lemma blowupGraph_adj {ι : Type*} (H : SimpleGraph ι) (V : ι → Type*) (x y : Σ i, V i) :
    (blowupGraph H V).Adj x y ↔ H.Adj x.1 y.1 := by rfl

/-- Embedding of `H` into `blowupGraph H V` with nonempty parts.-/
def blowupGraph.selfEmbedding {ι : Type*} (H : SimpleGraph ι) (V : ι → Type*) (f : ∀ (i : ι), V i) :
    H ↪g (blowupGraph H V) := ⟨⟨fun i ↦ ⟨i, f i⟩, fun _ _ h ↦ (Sigma.mk.inj_iff.1 h).1⟩, by simp⟩

lemma blowupGraph_top {ι : Type*} (V : ι → Type*) :
    blowupGraph ⊤ V = completeMultipartiteGraph V := rfl

lemma blowupGraph_bot {ι : Type*} (V : ι → Type*) : blowupGraph ⊥ V = ⊥ := rfl

lemma blowupGraph_cliqueFree_iff  {ι : Type*} {n : ℕ} (H : SimpleGraph ι) (V : ι → Type*) (f : ∀ i, (V i)) :
    H.CliqueFree n ↔ (blowupGraph H V).CliqueFree n := by
  constructor <;> intro h
  · rw [cliqueFree_iff, isEmpty_iff] at *
    intro e
    apply h
    use ⟨Sigma.fst ∘ e, fun a b (h : (e a).fst = (e b).fst) ↦ by
      by_contra!
      rw [← top_adj, ← e.map_adj_iff, blowupGraph_adj, h] at this
      exact H.loopless _ this⟩
    dsimp
    intros
    rw [← blowupGraph_adj, e.map_adj_iff]
  · exact h.comap (blowupGraph.selfEmbedding _ _ f)

lemma blowupGraph_colorable_iff  {ι : Type*} {n : ℕ} (H : SimpleGraph ι) (V : ι → Type*) (f : ∀ i, (V i)) :
    H.Colorable n ↔ (blowupGraph H V).Colorable n := by
  constructor <;> intro ⟨c⟩
  · exact ⟨fun x ↦ c x.fst, fun h1 h2 ↦ c.valid h1 h2⟩
  · exact ⟨fun x ↦ c ⟨x, f x⟩, by intro a b had; exact c.valid (by rwa [blowupGraph_adj])⟩

end SimpleGraph
