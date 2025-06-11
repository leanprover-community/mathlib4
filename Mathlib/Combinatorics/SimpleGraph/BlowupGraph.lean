/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
  # Blow-up graphs
-/
namespace SimpleGraph

variable {ι : Type*} (H : SimpleGraph ι) --[DecidableRel H.Adj]
(V : ι → Type*) --[∀ i, DecidableEq (V i)]


/--
Given a family of vertex types indexed by `ι`, pulling back from `H : SimpleGraph ι`
yields the blow-up graph on the family. Two vertices are adjacent if and only if their
indices are adjacent in `H`.
-/
abbrev blowupGraph  : SimpleGraph (Σ i, V i) := SimpleGraph.comap Sigma.fst H

lemma blowupGraph_adj (x y : Σ i, V i) :
    (blowupGraph H V).Adj x y ↔ H.Adj (Sigma.fst x) (Sigma.fst y) := by rfl

lemma blowupGraph_not_adj_fst_eq {i : ι} (x y : V i) : ¬ (blowupGraph H V).Adj ⟨_, x⟩ ⟨_, y⟩ := by
  intro hf
  rw [blowupGraph_adj] at hf
  exact H.loopless i hf

lemma edgeSet_eq : H.edgeSet = {e | H.Adj e.out.1 e.out.2} := by
  ext e
  constructor <;> intro h <;>
  · change s(e.out.1, e.out.2) ∈ H.edgeSet at *
    convert h; ext; simp


lemma blowupGraph_edgeSet :
    (blowupGraph H V).edgeSet = {e | H.Adj (e.out.1.1) (e.out.2.1)} := edgeSet_eq _

/-- Embedding of `H` into `blowupGraph H V` with nonempty parts. -/
def blowupGraph.selfEmbedding (f : ∀ (i : ι), V i) :
    H ↪g (blowupGraph H V) := ⟨⟨fun i ↦ ⟨i, f i⟩, fun _ _ h ↦ (Sigma.mk.inj_iff.1 h).1⟩, by simp⟩

lemma blowupGraph_top : blowupGraph ⊤ V = completeMultipartiteGraph V := rfl

lemma blowupGraph_bot : blowupGraph ⊥ V = ⊥ := rfl

lemma blowupGraph_cliqueFree_iff  {n : ℕ} (f : ∀ i, (V i)) :
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

lemma blowupGraph_colorable_iff {n : ℕ} (f : ∀ i, (V i)) :
    H.Colorable n ↔ (blowupGraph H V).Colorable n := by
  constructor <;> intro ⟨c⟩
  · exact ⟨fun x ↦ c x.fst, fun h1 h2 ↦ c.valid h1 h2⟩
  · exact ⟨fun x ↦ c ⟨x, f x⟩, by intro a b had; exact c.valid (by rwa [blowupGraph_adj])⟩
end SimpleGraph
