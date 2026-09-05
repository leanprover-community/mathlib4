/-
Copyright (c) 2026 Haoyu Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoyu Chen
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Card

/-!
# The Graham–Pollak theorem

R. L. Graham and H. O. Pollak, *On the addressing problem for loop switching*,
Bell System Tech. J. **50** (1971), 2495–2519.

The edge set of the complete graph `K_n` cannot be partitioned into fewer than `n - 1`
complete bipartite graphs (bicliques), and `n - 1` bicliques suffice.  Equivalently,
the *biclique partition number* of `K_n` is exactly `n - 1`.

The proof formalised here is Witsenhausen's linear-algebra argument, the classical
showcase of the "linear algebra method" in combinatorics (see Babai–Frankl,
*Linear Algebra Methods in Combinatorics*, Chapter 1).

Given a partition of the edges of `K_V` into bicliques `(X k, Y k)`, one considers the
linear map `v ↦ ((∑_{i ∈ X k} v i)_k, ∑_i v i)` from `V → ℝ` to `(κ → ℝ) × ℝ`.
If `v` is
in its kernel then

`0 = (∑ i, v i)^2 = ∑ i, (v i)^2 + 2 ∑ k (∑_{i ∈ X k} v i)(∑_{j ∈ Y k} v j)`,
so `∑ i, (v i)^2 = 0`,

because every unordered pair `{i, j}` with `i ≠ j` is counted exactly once by the
bicliques.  Hence `v = 0`, the map is injective, and `card V ≤ card κ + 1`.

## Main results

* `GrahamPollak.BicliquePartition` : a partition of the edge set of `K_V` into bicliques
  indexed by `κ`.
* `GrahamPollak.BicliquePartition.key_identity` : the double-counting identity.
* `GrahamPollak.BicliquePartition.card_le` : **Graham–Pollak**, `card V ≤ card κ + 1`.
* `GrahamPollak.card_le_of_biclique_cover` : the same statement phrased with `SimpleGraph`.
* `GrahamPollak.finBicliquePartition` : the matching construction, showing that `n`
  bicliques do partition `K_{n+1}`.
* `GrahamPollak.bicliquePartitionNumber_eq` : the biclique partition number of `K_{n+1}`
  is exactly `n`.
-/

open Finset

namespace GrahamPollak

variable {V κ : Type*}

/-! ### An algebraic identity -/

/-- Splitting `(∑ i, v i)^2` into its diagonal and off-diagonal contributions. -/
lemma sq_sum_eq [Fintype V] [DecidableEq V] (v : V → ℝ) :
    (∑ i, v i) ^ 2
      = (∑ i, v i ^ 2) + ∑ p ∈ (Finset.univ : Finset V).offDiag, v p.1 * v p.2 := by
  have hprod : (∑ i, v i) ^ 2 = ∑ p ∈ (Finset.univ : Finset V) ×ˢ Finset.univ,
      v p.1 * v p.2 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  have hoff : (Finset.univ : Finset V).offDiag
      = ((Finset.univ : Finset V) ×ˢ Finset.univ).filter (fun p => ¬ p.1 = p.2) := by
    ext p
    simp [Finset.mem_offDiag]
  have hdiag : ∑ p ∈ ((Finset.univ : Finset V) ×ˢ Finset.univ).filter
      (fun p => p.1 = p.2), v p.1 * v p.2 = ∑ i, v i ^ 2 := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp [sq]
  rw [hprod, hoff, ← hdiag, ← Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset V) ×ˢ Finset.univ) (fun p => p.1 = p.2)]

/-! ### Biclique partitions -/

/--
A **biclique partition** of the complete graph `K_V` on the vertex type `V`, with
bicliques indexed by `κ`.

The `k`-th complete bipartite graph has sides `X k` and `Y k`; these are disjoint, and
every edge `{i, j}` of `K_V` (i.e. every unordered pair of distinct vertices) is an edge
of *exactly one* of the bicliques.
-/
structure BicliquePartition (V κ : Type*) where
  /-- The first side of the `k`-th biclique. -/
  X : κ → Finset V
  /-- The second side of the `k`-th biclique. -/
  Y : κ → Finset V
  /-- The two sides of a biclique are disjoint. -/
  disj : ∀ k, Disjoint (X k) (Y k)
  /-- Every edge of the complete graph is covered exactly once. -/
  covers : ∀ i j : V, i ≠ j → ∃! k, (i ∈ X k ∧ j ∈ Y k) ∨ (j ∈ X k ∧ i ∈ Y k)

namespace BicliquePartition

variable [DecidableEq V] (B : BicliquePartition V κ)

/-- The set of *ordered* pairs of vertices joined by the `k`-th biclique. -/
def edges (k : κ) : Finset (V × V) := (B.X k ×ˢ B.Y k) ∪ (B.Y k ×ˢ B.X k)

lemma mem_edges {k : κ} {p : V × V} :
    p ∈ B.edges k ↔
      (p.1 ∈ B.X k ∧ p.2 ∈ B.Y k) ∨ (p.2 ∈ B.X k ∧ p.1 ∈ B.Y k) := by
  simp only [edges, Finset.mem_union, Finset.mem_product]
  tauto

/-- The two endpoints of an edge of a biclique are distinct, since its sides are disjoint. -/
lemma ne_of_mem_edges {k : κ} {i j : V} (h : (i, j) ∈ B.edges k) : i ≠ j := by
  rw [B.mem_edges] at h
  rintro rfl
  rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact (Finset.disjoint_left.mp (B.disj k) hi) hj
  · exact (Finset.disjoint_left.mp (B.disj k) hi) hj

/-- The bicliques of a biclique partition are pairwise disjoint as sets of ordered pairs. -/
lemma pairwise_disjoint_edges [Fintype κ] :
    ((Finset.univ : Finset κ) : Set κ).PairwiseDisjoint B.edges := by
  intro k _ l _ hkl
  show Disjoint (B.edges k) (B.edges l)
  rw [Finset.disjoint_left]
  rintro ⟨i, j⟩ hk hl
  have hij : i ≠ j := B.ne_of_mem_edges hk
  rw [B.mem_edges] at hk hl
  obtain ⟨k₀, -, hk₀⟩ := B.covers i j hij
  exact hkl ((hk₀ k hk).trans (hk₀ l hl).symm)

/-- The bicliques of a biclique partition cover every ordered pair of distinct vertices. -/
lemma biUnion_edges [Fintype V] [Fintype κ] :
    (Finset.univ : Finset κ).biUnion B.edges = (Finset.univ : Finset V).offDiag := by
  ext p
  obtain ⟨i, j⟩ := p
  constructor
  · intro hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨k, -, hk⟩ := hp
    rw [Finset.mem_offDiag]
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, B.ne_of_mem_edges hk⟩
  · intro hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨k, hk, -⟩ := B.covers i j hp.2.2
    rw [Finset.mem_biUnion]
    exact ⟨k, Finset.mem_univ _, by rw [B.mem_edges]; exact hk⟩

section Identity

variable (v : V → ℝ)

/-- The sum of `v i * v j` over the ordered pairs covered by the `k`-th biclique is
twice the product of the two side-sums. -/
lemma sum_edges (k : κ) :
    ∑ p ∈ B.edges k, v p.1 * v p.2 = 2 * ((∑ i ∈ B.X k, v i) * (∑ j ∈ B.Y k, v j)) := by
  have hdisj : Disjoint (B.X k ×ˢ B.Y k) (B.Y k ×ˢ B.X k) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ ha hb
    rw [Finset.mem_product] at ha hb
    exact (Finset.disjoint_left.mp (B.disj k) ha.1) hb.1
  rw [edges, Finset.sum_union hdisj, Finset.sum_product, Finset.sum_product]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- **Key double-counting identity.**  Summing `v i * v j` over all ordered pairs of
distinct vertices can be done biclique by biclique: each unordered pair is covered
exactly once, in one of its two orders. -/
lemma key_identity [Fintype V] [Fintype κ] :
    ∑ p ∈ (Finset.univ : Finset V).offDiag, v p.1 * v p.2
      = 2 * ∑ k, (∑ i ∈ B.X k, v i) * (∑ j ∈ B.Y k, v j) := by
  rw [← B.biUnion_edges, Finset.sum_biUnion B.pairwise_disjoint_edges, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => B.sum_edges v k

end Identity

/-! ### Witsenhausen's linear map -/

/-- The linear map witnessing the Graham–Pollak bound: it records the sums of `v` over
each first side `X k`, together with the total sum of `v`. -/
noncomputable def toLin [Fintype V] : (V → ℝ) →ₗ[ℝ] (κ → ℝ) × ℝ where
  toFun v := (fun k => ∑ i ∈ B.X k, v i, ∑ i, v i)
  map_add' u v := by
    ext k <;> simp [Finset.sum_add_distrib]
  map_smul' c v := by
    ext k <;> simp [Finset.mul_sum]

omit [DecidableEq V] in
lemma toLin_apply [Fintype V] (v : V → ℝ) :
    B.toLin v = (fun k => ∑ i ∈ B.X k, v i, ∑ i, v i) := rfl

/-- The core of Witsenhausen's argument: the map `toLin` is injective. -/
lemma toLin_injective [Fintype V] [Fintype κ] : Function.Injective B.toLin := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hX : ∀ k, ∑ i ∈ B.X k, v i = 0 := by
    intro k
    have := congrArg (fun p => p.1 k) hv
    simpa [toLin_apply] using this
  have htot : ∑ i, v i = 0 := by
    have := congrArg Prod.snd hv
    simpa [toLin_apply] using this
  have hkey := B.key_identity v
  simp only [hX, zero_mul, Finset.sum_const_zero, mul_zero] at hkey
  have hsq := sq_sum_eq v
  rw [htot, hkey, add_zero] at hsq
  have hz : ∑ i, v i ^ 2 = 0 := by simpa using hsq.symm
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v i)).mp hz i
    (Finset.mem_univ i)
  simpa using (pow_eq_zero_iff (n := 2) (by norm_num)).mp hi

include B in
/--
**The Graham–Pollak theorem.**

If the edge set of the complete graph on a finite vertex type `V` is partitioned into
complete bipartite graphs indexed by a finite type `κ`, then `card V ≤ card κ + 1`;
i.e. at least `card V - 1` bicliques are needed.
-/
theorem card_le [Fintype V] [Fintype κ] : Fintype.card V ≤ Fintype.card κ + 1 := by
  have h := LinearMap.finrank_le_finrank_of_injective B.toLin_injective
  rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_prod,
    Module.finrank_fintype_fun_eq_card, Module.finrank_self] at h

end BicliquePartition

/-! ### A graph-theoretic phrasing -/

/-- The complete bipartite graph on the vertex type `V` with sides `X` and `Y`.
(If `X` and `Y` are disjoint this is exactly the complete bipartite graph between them;
the `i ≠ j` clause only serves to make it a loopless simple graph in general.) -/
def biclique (X Y : Finset V) : SimpleGraph V where
  Adj i j := i ≠ j ∧ ((i ∈ X ∧ j ∈ Y) ∨ (j ∈ X ∧ i ∈ Y))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] lemma biclique_adj [DecidableEq V] {X Y : Finset V} {i j : V} :
    (biclique X Y).Adj i j ↔ i ≠ j ∧ ((i ∈ X ∧ j ∈ Y) ∨ (j ∈ X ∧ i ∈ Y)) :=
  Iff.rfl

/--
**The Graham–Pollak theorem, stated with `SimpleGraph`.**

If `biclique (X k) (Y k)`, `k : κ`, is a family of complete bipartite graphs on a finite
vertex type `V` such that every edge of the complete graph on `V` is an edge of exactly
one of them, then `card V ≤ card κ + 1`.
-/
theorem card_le_of_biclique_cover [Fintype V] [DecidableEq V] [Fintype κ]
    (X Y : κ → Finset V) (hd : ∀ k, Disjoint (X k) (Y k))
    (hcov : ∀ i j : V, i ≠ j → ∃! k, (biclique (X k) (Y k)).Adj i j) :
    Fintype.card V ≤ Fintype.card κ + 1 := by
  refine BicliquePartition.card_le
    { X := X, Y := Y, disj := hd, covers := fun i j hij => ?_ }
  obtain ⟨k, hk, huniq⟩ := hcov i j hij
  exact ⟨k, hk.2, fun l hl => huniq l ⟨hij, hl⟩⟩

/--
**The Graham–Pollak theorem, stated as a partition of the edge set of the complete graph.**

If the complete bipartite graphs `biclique (X k) (Y k)`, `k : κ`, are pairwise
edge-disjoint and their supremum is the complete graph `⊤` on the finite vertex type `V`
(that is, they partition the edge set of `K_V`), then `card V ≤ card κ + 1`.
-/
theorem card_le_of_edge_partition [Fintype V] [DecidableEq V] [Fintype κ]
    (X Y : κ → Finset V) (hd : ∀ k, Disjoint (X k) (Y k))
    (hsup : ⨆ k, biclique (X k) (Y k) = ⊤)
    (hpd : Pairwise fun k l => Disjoint (biclique (X k) (Y k)) (biclique (X l) (Y l))) :
    Fintype.card V ≤ Fintype.card κ + 1 := by
  refine card_le_of_biclique_cover X Y hd fun i j hij => ?_
  have hex : ∃ k, (biclique (X k) (Y k)).Adj i j := by
    rw [← SimpleGraph.iSup_adj, hsup, SimpleGraph.top_adj]
    exact hij
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, hk, fun l hl => ?_⟩
  by_contra hlk
  have hinf : ((biclique (X l) (Y l)) ⊓ (biclique (X k) (Y k))).Adj i j :=
    (SimpleGraph.inf_adj _ _ _ _).mpr ⟨hl, hk⟩
  rw [disjoint_iff.mp (hpd hlk)] at hinf
  exact (SimpleGraph.bot_adj i j).mp hinf

/-! ### The construction: `n` bicliques do partition `K_{n+1}` -/

/-- The standard biclique partition of `K_{n+1}` into `n` bicliques: the `k`-th biclique
joins the vertex `k` to every vertex larger than `k`.  The edge `{i, j}` with `i ≠ j`
belongs to the biclique indexed by `min i j`. -/
def finBicliquePartition (n : ℕ) : BicliquePartition (Fin (n + 1)) (Fin n) where
  X k := {k.castSucc}
  Y k := Finset.Ioi k.castSucc
  disj k := by simp
  covers i j hij := by
    have hlt : min i j < max i j := min_lt_max.mpr hij
    have hval : (min i j).val < n := lt_of_lt_of_le hlt (Fin.le_last _)
    have hcast : (Fin.castSucc ⟨(min i j).val, hval⟩ : Fin (n + 1)) = min i j := by
      ext; simp
    refine ⟨⟨(min i j).val, hval⟩, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hij with h | h
      · left
        rw [hcast]
        refine ⟨Finset.mem_singleton.mpr (min_eq_left h.le).symm, ?_⟩
        simpa [min_eq_left h.le] using h
      · right
        rw [hcast]
        refine ⟨Finset.mem_singleton.mpr (min_eq_right h.le).symm, ?_⟩
        simpa [min_eq_right h.le] using h
    · intro l hl
      have hcastl : (Fin.castSucc l : Fin (n + 1)) = min i j := by
        rcases hl with ⟨hi, hj⟩ | ⟨hj, hi⟩
        · rw [Finset.mem_singleton] at hi
          rw [Finset.mem_Ioi] at hj
          rw [← hi] at hj ⊢
          exact (min_eq_left hj.le).symm
        · rw [Finset.mem_singleton] at hj
          rw [Finset.mem_Ioi] at hi
          rw [← hj] at hi ⊢
          exact (min_eq_right hi.le).symm
      exact Fin.castSucc_injective n (hcastl.trans hcast.symm)

/-- The biclique partition number of the complete graph on `n + 1` vertices: `n` bicliques
suffice, and this is optimal. -/
theorem bicliquePartitionNumber_eq (n : ℕ) :
    IsLeast {m : ℕ | Nonempty (BicliquePartition (Fin (n + 1)) (Fin m))} n := by
  constructor
  · exact ⟨finBicliquePartition n⟩
  · rintro m ⟨B⟩
    have h := B.card_le
    simpa using h

/-! ### Axiom check -/


end GrahamPollak
