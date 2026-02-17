/-
Copyright (c) 2025 Runtian Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Runtian Zhou
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Cayley Sum Graphs

This file defines Cayley sum graphs for abelian groups.

## Main definitions

* `SimpleGraph.cayleySumGraph s`: the Cayley sum graph over an additive abelian group `G` with
  connection set `s`. Two vertices `u` and `v` are adjacent iff `u + v ∈ s`.

## Comparison with other graph constructions

| Construction | Edge condition | Framework |
|-------------|----------------|-----------|
| Cayley graph | `v = g • u` for `g ∈ S` | Quiver (directed) |
| Circulant graph | `u - v ∈ S` | SimpleGraph |
| Cayley sum graph | `u + v ∈ S` | SimpleGraph |

The key difference is that:
- Cayley graphs and circulant graphs use *differences* (`g • u = v` or `u - v ∈ S`)
- Cayley sum graphs use *sums* (`u + v ∈ S`)

Cayley sum graphs are naturally undirected for abelian groups since `u + v = v + u`.

## References

* [Chung, Graham - "Quasi-random graphs with given degree sequences"](https://www.math.ucsd.edu/~fan/wp/degree.pdf)
* [Green - "Counting sets with small sumset"](https://arxiv.org/abs/math/0304475)
-/

@[expose] public section

namespace SimpleGraph

variable {G : Type*} [AddCommGroup G]

/-- Cayley sum graph over additive abelian group `G` with connection set `s`.
Two vertices `u` and `v` are adjacent iff `u ≠ v` and `u + v ∈ s`. -/
def cayleySumGraph (s : Set G) : SimpleGraph G where
  Adj u v := u ≠ v ∧ u + v ∈ s
  symm := fun u v ⟨hne, hmem⟩ ↦ ⟨hne.symm, by rwa [add_comm]⟩
  loopless := ⟨fun u ⟨hne, _⟩ ↦ hne rfl⟩

variable (s : Set G)

/-- Two vertices are adjacent in the Cayley sum graph iff they are distinct and their sum
is in the connection set. -/
@[simp]
theorem cayleySumGraph_adj {u v : G} :
    (cayleySumGraph s).Adj u v ↔ u ≠ v ∧ u + v ∈ s := Iff.rfl

/-- Adjacency in a Cayley sum graph is decidable when membership in the connection set
and equality are decidable. -/
instance cayleySumGraph_decidableAdj [DecidableEq G] [DecidablePred (· ∈ s)] :
    DecidableRel (cayleySumGraph s).Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The sum of translated vertices equals the original sum plus twice the translation.
This shows how translation affects Cayley sum graph adjacency. -/
theorem cayleySumGraph_translate_sum {u v d : G} :
    (u + d) + (v + d) = u + v + (d + d) := by
  rw [add_assoc, add_comm d (v + d), add_assoc v d d, ← add_assoc, ← add_assoc]

/-- Adjacency in the Cayley sum graph after translation: the sum changes by 2d.
Unlike circulant graphs (which use differences), Cayley sum graphs are NOT
translation-invariant in general. -/
theorem cayleySumGraph_adj_translate_iff {u v d : G} :
    (cayleySumGraph s).Adj (u + d) (v + d) ↔ u ≠ v ∧ u + v + (d + d) ∈ s := by
  simp only [cayleySumGraph_adj, cayleySumGraph_translate_sum]
  constructor
  · intro ⟨hne, hmem⟩
    exact ⟨fun h ↦ hne (by rw [h]), hmem⟩
  · intro ⟨hne, hmem⟩
    exact ⟨fun h ↦ hne (add_right_cancel h), hmem⟩

/-- In a group of exponent 2 (where `x + x = 0` for all `x`), the Cayley sum graph
is translation-invariant, just like circulant graphs. -/
theorem cayleySumGraph_adj_translate_of_exp2 (hexp2 : ∀ x : G, x + x = 0) {u v d : G} :
    (cayleySumGraph s).Adj (u + d) (v + d) ↔ (cayleySumGraph s).Adj u v := by
  rw [cayleySumGraph_adj_translate_iff, hexp2, add_zero, cayleySumGraph_adj]

/-- The neighbor set in a Cayley sum graph. -/
theorem cayleySumGraph_neighborSet {v : G} :
    (cayleySumGraph s).neighborSet v = {w | w ≠ v ∧ v + w ∈ s} := by
  ext w
  simp only [mem_neighborSet, cayleySumGraph_adj, Set.mem_setOf_eq]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1.symm, h2⟩⟩

section LocallyFinite

/-- When the connection set is finite, the Cayley sum graph is locally finite. -/
noncomputable instance cayleySumGraph_locallyFinite
    [Fintype s] : LocallyFinite (cayleySumGraph s) := by
  intro v
  classical
  -- The neighbors of v are { w | w ≠ v ∧ v + w ∈ s }
  -- This is contained in the image of s under (· - v)
  have h : (cayleySumGraph s).neighborSet v ⊆ (fun x ↦ x - v) '' s := by
    intro w hw
    simp only [mem_neighborSet, cayleySumGraph_adj] at hw
    refine ⟨v + w, hw.2, ?_⟩
    simp only [add_sub_cancel_left]
  exact (Set.Finite.image _ (Set.toFinite s)).subset h |>.fintype

end LocallyFinite

section Examples

/-!
### Connection to Circulant Graphs

The circulant graph uses `u - v ∈ s`, while the Cayley sum graph uses `u + v ∈ s`.
These are related by a change of variables.

For an abelian group `G` of exponent 2 (where `x + x = 0` for all `x`),
subtraction equals addition, so the two notions coincide.
-/

/-- In a group of exponent 2, negation is the identity. -/
theorem neg_eq_self_of_add_self_eq_zero (hexp2 : ∀ x : G, x + x = 0) (x : G) : -x = x :=
  neg_eq_of_add_eq_zero_right (hexp2 x)

/-- In a group of exponent 2, the Cayley sum graph equals the circulant graph. -/
theorem cayleySumGraph_eq_circulantGraph_of_exp2
    (hexp2 : ∀ x : G, x + x = 0) :
    cayleySumGraph s = circulantGraph s := by
  ext u v
  simp only [cayleySumGraph_adj, circulantGraph_adj]
  have neg_eq := neg_eq_self_of_add_self_eq_zero hexp2
  constructor
  · intro ⟨hne, hmem⟩
    refine ⟨hne, Or.inl ?_⟩
    rw [sub_eq_add_neg, neg_eq]
    exact hmem
  · intro ⟨hne, hor⟩
    refine ⟨hne, ?_⟩
    cases hor with
    | inl h =>
      rw [sub_eq_add_neg, neg_eq] at h
      exact h
    | inr h =>
      rw [sub_eq_add_neg, neg_eq, add_comm] at h
      exact h

end Examples

end SimpleGraph
