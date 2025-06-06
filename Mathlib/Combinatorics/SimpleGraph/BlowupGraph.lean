/-
Copyright (c) 2021 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
/-!
  # Blow-up graphs and counting induced subgraphs
-/
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

variable {α β ι : Type*} {k : ℕ}
/--
A `Flag α ι` consists of `G : SimpleGraph α` and a labelling of `ι` vertices of `G` by an
injective map `θ : ι ↪ α`. (We call this a `σ`-flag if the labelled subgraph is
`σ : SimpleGraph ι`).
-/
structure Flag (α ι : Type*) where
  G : SimpleGraph α
  θ : ι ↪ α

/-- Added to prove `Fintype` instance later -/
def FlagIso (α ι : Type*) : Flag α ι ≃ (SimpleGraph α) × (ι ↪ α) where
  toFun := fun F ↦ (F.G, F.θ)
  invFun := fun p ↦ { G := p.1, θ := p.2 }
  left_inv := fun F ↦ by cases F; rfl
  right_inv := fun p ↦ by cases p; rfl

/-- An embedding of flags -/
abbrev Embedding.Flag {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι } (e : F₁.G ↪g F₂.G) :
    Prop := F₂.θ = e ∘ F₁.θ

/-- An isomorphism of flags -/
abbrev Iso.Flag {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι } (e : F₁.G ≃g F₂.G) :
    Prop := F₂.θ = e ∘ F₁.θ

lemma Flag.Iso_symm {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι} (e : F₁.G ≃g F₂.G)
    (he : e.Flag) : F₁.θ = e.symm ∘ F₂.θ := by
  ext; simp [he]

/--
`F` is a `σ`-flag iff the labelled subgraph given by `θ` is `σ`
-/
def Flag.IsSigma (F : Flag α ι) (σ : SimpleGraph ι) : Prop :=
  F.G.comap F.θ = σ

lemma Flag.isSigma_self (F : Flag α ι) : F.IsSigma (F.G.comap F.θ) := rfl

lemma Flag.isSigma_of_embedding {α β ι : Type*} {σ : SimpleGraph ι} {F₁ : Flag α ι}
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
#check Finset.card_eq_sum_card_fiberwise
#check Finset.sum_comm' -- use this below
variable {k m n : ℕ}
local notation "‖" x "‖" => Fintype.card x

#check SimpleGraph.induce
#check Subtype.ext_iff_val
open Finset
/--
Embeddings of `H` in `G[t]` are equivalent to embeddings of `H` in `G` that map into `t`.
-/
def induceEquiv (G : SimpleGraph α) (H : SimpleGraph β) (t : Set α) : H ↪g (G.induce t) ≃
    {e : H ↪g G | Set.range e ⊆ t} where
  toFun := fun e ↦ ⟨Embedding.induce _|>.comp e, by rintro x ⟨y , rfl⟩; simp⟩
  invFun := fun e ↦ ⟨⟨(fun b ↦ ⟨_, e.2 ⟨b , rfl⟩⟩), fun _ _ _ ↦ e.1.inj' (by aesop)⟩,
                     by simp, by simp⟩
  left_inv := fun e ↦ by ext; simp
  right_inv := fun e ↦ by ext; simp

lemma subset_iff_of_card_le_card {α : Type*} {s t : Finset α} [Fintype α] [DecidableEq α]
  (hst : #s ≤ #t) : s ⊆ t ↔ #(t \ s) = #t - #s := by
  constructor <;> intro h
  · rw [card_sdiff h]
  · have : #(t \ s) + #s = #t := by omega
    rw [card_sdiff_add_card] at this
    have : t = t ∪ s := by apply eq_of_subset_of_card_le subset_union_left this.le
    exact left_eq_union.mp this

/--
Given `s : Finset α`, the number of super-sets of `s` of size `k` is `choose (‖α‖ - #s) (k - #s)`,
for `#s ≤ k`.
-/
lemma card_supersets {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α} (hk : #s ≤ k) :
    #{t : Finset α | #t = k ∧ s ⊆ t} = Nat.choose (‖α‖ - #s) (k - #s) := by
  simp_rw [← card_compl, ← card_powersetCard]
  apply card_nbij (i := (· \ s))
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    simp only [mem_powersetCard]
    refine ⟨fun _ ↦ by simp, ?_⟩
    rw [subset_iff_of_card_le_card (card_le_card ht.2)] at ht
    rw [ht.2]
    omega
  · intro t₁ ht1 t₂ ht2 he
    dsimp at he
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht1 ht2
    rw [← sdiff_union_of_subset ht1.2, ← sdiff_union_of_subset ht2.2, he]
  · intro t ht
    simp only [mem_coe, mem_powersetCard] at ht
    use (t ∪ s)
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, subset_union_right, and_true]
    have hd := disjoint_left.2 fun _ ha hs ↦ (mem_compl.1 <| ht.1 ha) hs
    exact ⟨by rw [card_union_of_disjoint hd]; omega, union_sdiff_cancel_right hd⟩

/-- **The principle of counting subgraphs by averaging**
If `G` is a graph on `α` and `H` is a graph on `β`, then
`#(H ↪g G) * (choose (‖α‖ - ‖β‖) (k - ‖β‖))` is equal to the sum of the number of embeddings
`H ↪g (G.induce t)` over subsets `t` of `α` of size `k`, for any `‖β‖ ≤ k`.
-/
lemma sum_card_embeddings_induce_eq (G : SimpleGraph α) (H : SimpleGraph β) [Fintype β] {k : ℕ}
    (hk : ‖β‖ ≤ k) : ∑ t : Finset α with t.card = k , ‖H ↪g (G.induce t)‖
                              = ‖H ↪g G‖ * Nat.choose (‖α‖ - ‖β‖) (k - ‖β‖) := by
  classical
  calc
    _ = ∑ t : Finset α with t.card = k , ‖{e : H ↪g G | Set.range e ⊆ t}‖  := by
      simp_rw [Fintype.card_congr <| induceEquiv ..]
    _ = ∑ t : Finset α  with t.card = k, ∑ e : H ↪g G,
      ite (Set.range e ⊆ t) 1 0 := by
      congr; simp only [Set.coe_setOf, sum_boole, Nat.cast_id]
      ext t; apply Fintype.card_subtype
    _ = ∑ e : H ↪g G, ∑ t : Finset α with #t = k,
      ite (Set.range e ⊆ t) 1 0 := Finset.sum_comm
    _ = ∑ e : H ↪g G, ∑ t : Finset α with (#t = k ∧ Set.range e ⊆ t), 1 := by
      simp_rw [sum_ite, sum_const_zero, add_zero]
      congr; ext e; congr 1; ext s; simp
    _ = _ := by
      simp_rw [← card_eq_sum_ones]
      rw [← card_univ (α := (H ↪g G)), card_eq_sum_ones, sum_mul, one_mul]
      congr; ext e
      have hs : #((Set.range e).toFinset) = ‖β‖ := by
        simp_rw [Set.toFinset_range]
        apply card_image_of_injective _ (RelEmbedding.injective e)
      rw [← hs, ← card_supersets (hs ▸ hk)]
      congr
      ext t
      constructor <;> intro ⟨ht1, ht2⟩ <;> exact ⟨ht1, fun x hx ↦ ht2 (by simpa using hx)⟩

end SimpleGraph


-- /--
-- Given a `k`-set `s` in `[n + m + k]`, the number of `m + k` super-sets of `s` is
-- `choose (n + m) m`
-- -/

-- lemma card_superset {k m n : ℕ} {s t : Finset (Fin (n + m + k))} (hs : #s = k) (ht : #t = m + k):
--     s ⊆ t ↔ #(t \ s) = m := by
--   constructor <;> intro h
--   · rw [card_sdiff h]; omega
--   · have : #(t \ s) + #s = #t := by omega
--     rw [card_sdiff_add_card] at this
--     have : t = t ∪ s := by apply eq_of_subset_of_card_le subset_union_left this.le
--     exact left_eq_union.mp this

-- lemma card_supersets {k m n : ℕ} {s : Finset (Fin (n + m + k))} (hs : s.card = k) :
--     #{t : Finset (Fin (n + m + k)) | #t = m + k ∧ s ⊆ t} = Nat.choose (n + m) m := by
--   have : #(sᶜ) = n + m := by rw [card_compl, Fintype.card_fin]; omega
--   simp_rw [← this]
--   rw [← card_powersetCard]
--   apply card_nbij (i := fun t ↦ (t \ s))
--   · intro t ht
--     simp only [mem_filter, mem_univ, true_and] at ht
--     simp only [mem_powersetCard]
--     exact ⟨fun _ ↦ by simp, (card_superset hs ht.1).1 ht.2⟩
--   · intro t₁ ht1 t₂ ht2 he
--     dsimp at he
--     simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht1 ht2
--     rw [← sdiff_union_of_subset ht1.2, ← sdiff_union_of_subset ht2.2, he]
--   · intro t ht
--     simp only [mem_coe, mem_powersetCard] at ht
--     use (t ∪ s)
--     simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, subset_union_right, and_true]
--     refine ⟨?_,?_⟩
--     · simp_rw [← hs,← ht.2]
--       exact card_union_of_disjoint <| disjoint_left.2 fun _ ha hs ↦ (mem_compl.1 <| ht.1 ha) hs
--     · rw [union_sdiff_cancel_right]
--       exact disjoint_left.2 fun _ ha hs ↦ (mem_compl.1 <| ht.1 ha) hs

-- /-- **The principle of counting subgraphs by averaging**
-- If `G` is a graph on `[n + m + k]` and `H` is a graph on `[k]`, then the number of embeddings
-- `#(H ↪g G) * (choose (n + m) m)` is equal to the sum of the number of embeddings
-- `H ↪g (G.induce t)`
-- over subsets `t` of `[n + m + k]` of size `m + k`.
-- -/
-- lemma sum_embeddings_induce_eq (G : SimpleGraph (Fin (n + m + k))) (H : SimpleGraph (Fin k)) :
--    ∑ t : Finset (Fin (n + m + k)) with t.card = m + k, ‖H ↪g (G.induce t)‖
--      = ‖H ↪g G‖ * Nat.choose (n + m) m := by
--   classical
--   calc
--     _ = ∑ t : Finset (Fin (n + m + k)) with t.card = m + k, ‖{e : H ↪g G | Set.range e ⊆ t}‖
--  := by
--       simp_rw [Fintype.card_congr <| induceEquiv ..]
--     _ = ∑ t : Finset (Fin (n + m + k)) with t.card = m + k, ∑ e : H ↪g G,
--       ite (Set.range e ⊆ t) 1 0 := by
--       congr; simp only [Set.coe_setOf, sum_boole, Nat.cast_id]
--       ext t; apply Fintype.card_subtype
--     _ = ∑ e : H ↪g G, ∑ t : Finset (Fin (n + m + k)) with #t =  m + k,
--       ite (Set.range e ⊆ t) 1 0 := Finset.sum_comm
--     _ = ∑ e : H ↪g G, ∑ t : Finset (Fin (n + m + k)) with (#t =  m + k ∧ Set.range e ⊆ t), 1
-- := by
--       simp_rw [sum_ite, sum_const_zero, add_zero]
--       congr; ext e; congr 1; ext s; simp
--     _ = _ := by
--       simp_rw [← card_eq_sum_ones]
--       rw [← card_univ, card_eq_sum_ones, sum_mul, one_mul]
--       congr; ext e
--       have hs : #((Set.range e).toFinset) = k := by
--         simp_rw [Set.toFinset_range, ← card_fin k]
--         apply card_image_of_injective _ (RelEmbedding.injective e)
--       rw [← card_supersets hs]
--       congr
--       ext t
--       constructor <;> intro ⟨ht1, ht2⟩ <;> exact ⟨ht1, fun x hx ↦ ht2 (by simpa using hx)⟩

-- lemma edges_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
--     2 * #G.edgeFinset = ‖(⊤ : SimpleGraph (Fin 2)) ↪g G‖ := by

--   sorry
