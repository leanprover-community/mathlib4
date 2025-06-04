import Mathlib.Combinatorics.SimpleGraph.Coloring

namespace SimpleGraph

variable {ι : Type*} (H : SimpleGraph ι) --[DecidableRel H.Adj]
(V : ι → Type*) --[∀ i, DecidableEq (V i)]

/--
Given a family of vertex types indexed by `ι`, pulling back from `H : SimpleGraph ι`
yields the blow-up graph on the family. Two vertices are adjacent if and only if their
indices are adjacent in `H`.
-/
abbrev blowupGraph  : SimpleGraph (Σ i, V i) :=
  SimpleGraph.comap Sigma.fst H

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

section Finite
--variable [DecidableRel H.Adj] [Fintype ι] [∀ i, Fintype (V i)]
--#synth Fintype (blowupGraph H V).edgeSet
noncomputable def blowupGraph_edgeSetIso (f : ∀ i, (V i)) :
  (blowupGraph H V).edgeSet ≃ Σ e : H.edgeSet, (V e.val.out.1) × (V e.val.out.2) where
  toFun := fun e ↦ by
    refine ⟨?_, ?_, ?_⟩
    · rw [blowupGraph_edgeSet] at e
      rw [edgeSet_eq]
      refine ⟨s(e.val.out.1.1, e.val.out.2.1), ?_⟩
      rw [Set.mem_setOf_eq]
      rw [adj_iff_exists_edge_coe]
      simp only [Set.mem_setOf_eq, Prod.mk.eta, Quot.out_eq, Subtype.exists, exists_prop,
        exists_eq_right, mem_edgeSet]
      convert e.2
    · convert e.val.out.1.2
      simp_all
      sorry
    sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

end Finite

#check SimpleGraph.comap

variable {α β ι : Type*} {k : ℕ}
/--
A `Flag α k` consists of `G : SimpleGraph α` and a labelling of `ι` vertices of `G` by an
injective map `θ : ι ↪ α`. (We call this a `σ`-flag if the labelled subgraph is
`σ : SimpleGraph ι`).
-/
structure Flag (α ι : Type*) where
  G : SimpleGraph α
  θ : ι ↪ α

/-- An embedding of flags -/
abbrev Embedding.Flag {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι }
    (e : F₁.G ↪g F₂.G) : Prop := F₂.θ = e ∘ F₁.θ

def FlagIso (α ι : Type*) : Flag α ι ≃ (SimpleGraph α) × (ι ↪ α) where
  toFun := fun F => (F.G, F.θ)
  invFun := fun p => { G := p.1, θ := p.2 }
  left_inv := fun F => by cases F; rfl
  right_inv := fun p => by cases p; rfl

def Flag.IsSigma (F : Flag α ι) (σ : SimpleGraph ι) : Prop :=
  F.G.comap F.θ = σ

lemma Flag.IsSigma_self (F : Flag α ι) : F.IsSigma (F.G.comap F.θ) := rfl

lemma Flag.IsSigma_ofEmbedding {α β ι : Type*} {σ : SimpleGraph ι} {F₁ : Flag α ι}
    {F₂ : Flag β ι} (e : F₁.G ↪g F₂.G) (he : e.Flag) (h1 : F₁.IsSigma σ) : F₂.IsSigma σ := by
  rw [IsSigma, he, ← h1] at *
  ext; simp

variable {α ι  : Type*} [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]

noncomputable instance : Fintype (Flag α ι) :=  Fintype.ofEquiv _ (FlagIso α ι).symm

open Classical in
/--
The Finset of all `σ`-flags with vertex type `α` (where both `α` and `ι` are finite).
-/
noncomputable def SigmaFlags (σ : SimpleGraph ι) : Finset (Flag α ι) := {F | F.IsSigma σ}




end SimpleGraph
