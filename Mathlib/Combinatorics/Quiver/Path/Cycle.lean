/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Data.List.NodupEquivFin

/-!
# Simple quiver paths and cycles

Parallel to `SimpleGraph.Walk` in `Mathlib/Combinatorics/SimpleGraph/Paths.lean`:

`IsSimple` allows the endpoint to repeat the start (simple directed cycle). `IsPath` forbids
any repeated vertex and is strictly stronger.

`Quiver.IsAcyclic` (below) means no nontrivial closed paths. It implies `¬IsCycle` but is
strictly stronger than forbidding simple cycles only.

`Quiver.cycleLengths` (in `Mathlib/Combinatorics/Quiver/Cyclic.lean`) records lengths of positive
loops without a simplicity hypothesis.

For cardinality bounds use `p.vertices.toFinset` (see `List.toFinset_card_of_nodup`).

## Main statements

* `Quiver.Path.exists_length_add_eq_of_getElem_eq`: a path that visits the same vertex twice can
  be shortened by excising the loop in between. Both shortening results below come from it.
* `Quiver.Path.isSimple_of_minimal_length`: a shortest positive loop is simple.
-/

@[expose] public section

namespace Quiver.Path

open List

variable {V : Type*} [Quiver V]

/-- A path with no repeated vertices (cf. `SimpleGraph.Walk.IsPath`). -/
@[reducible] def IsPath {a b : V} (p : Path a b) : Prop :=
  p.vertices.Nodup

/-- A path with no repeated vertices except possibly at the end. -/
@[reducible] def IsSimple {a b : V} (p : Path a b) : Prop :=
  p.vertices.dropLast.Nodup

/-- A nontrivial simple closed walk. -/
def IsCycle {a : V} (p : Path a a) : Prop :=
  0 < p.length ∧ p.IsSimple

theorem IsPath.nil (a : V) : IsPath (nil : Path a a) := by
  simp [IsPath]

@[simp] lemma isPath_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    IsPath (p.cons e) ↔ IsPath p ∧ c ∉ p.vertices := by
  simp only [IsPath, vertices_cons]
  rw [nodup_concat]; aesop

lemma IsPath.isSimple {a b : V} {p : Path a b} (h : IsPath p) : IsSimple p :=
  h.sublist (dropLast_sublist (l := p.vertices))

/-! ### Excising a repeated vertex -/

/-- If a path visits the same vertex at positions `i < j`, then excising the loop it makes in
between leaves a path from `a` to `b` that is shorter by exactly `j - i`. -/
lemma exists_length_add_eq_of_getElem_eq {a b : V} (p : Path a b) {i j : ℕ}
    (hij : i < j) (hj : j < p.vertices.length)
    (h : p.vertices[i]'(hij.trans hj) = p.vertices[j]) :
    ∃ q : Path a b, q.length + (j - i) = p.length := by
  obtain ⟨v, s, t, rfl, hs, hv⟩ := p.exists_eq_comp_and_length_eq_of_lt_length j hj
  have hi : i < s.vertices.length := by grind [vertices_length]
  have hdrop : i < s.vertices.dropLast.length := by grind [length_dropLast, vertices_length]
  have h1 : s.vertices.dropLast[i]'hdrop = (s.comp t).vertices[i]'(hij.trans hj) := by
    simp only [vertices_comp]
    exact (prefix_append _ _).getElem hdrop
  have hkey : s.vertices[i]'hi = v :=
    ((getElem_dropLast hdrop).symm.trans h1).trans (h.trans hv.symm)
  obtain ⟨w, s₁, m, hsplit, hs₁, hw⟩ := s.exists_eq_comp_and_length_eq_of_lt_length i hi
  obtain rfl : w = v := hw.trans hkey
  exact ⟨s₁.comp t, by simp only [length_comp, hs₁, hs]; grind⟩

/-- A path that repeats a vertex is not of minimal length. -/
lemma exists_length_lt_of_not_isPath {a b : V} {p : Path a b} (h : ¬ p.IsPath) :
    ∃ q : Path a b, q.length < p.length := by
  obtain ⟨x, hx⟩ := exists_duplicate_iff_not_nodup.2 h
  obtain ⟨n, m, hnm, hn, hm⟩ := duplicate_iff_exists_distinct_get.1 hx
  obtain ⟨q, hq⟩ := p.exists_length_add_eq_of_getElem_eq hnm m.isLt
    (by simpa [get_eq_getElem] using hn.symm.trans hm)
  exact ⟨q, by grind⟩

/-- A loop that repeats a vertex before returning to its start is not the shortest positive
loop: excising the repetition leaves a strictly shorter loop that is still nontrivial. -/
lemma exists_pos_length_lt_of_not_isSimple {a : V} {c : Path a a} (h : ¬ c.IsSimple) :
    ∃ q : Path a a, 0 < q.length ∧ q.length < c.length := by
  obtain ⟨x, hx⟩ := exists_duplicate_iff_not_nodup.2 h
  obtain ⟨n, m, hnm, hn, hm⟩ := duplicate_iff_exists_distinct_get.1 hx
  have hlen : c.vertices.dropLast.length = c.length := by
    simp [length_dropLast, vertices_length]
  have hmc : (m : ℕ) < c.length := by have := m.isLt; grind
  obtain ⟨q, hq⟩ := c.exists_length_add_eq_of_getElem_eq hnm (by rw [vertices_length]; grind)
    (by simpa [get_eq_getElem, getElem_dropLast] using hn.symm.trans hm)
  exact ⟨q, by grind, by grind⟩

/-- A shortest positive loop is simple. -/
theorem isSimple_of_minimal_length {a : V} {c : Path a a}
    (hc : ∀ p : Path a a, 0 < p.length → c.length ≤ p.length) : c.IsSimple := by
  by_contra h
  obtain ⟨q, hq_pos, hq_lt⟩ := exists_pos_length_lt_of_not_isSimple h
  exact absurd (hc q hq_pos) (by grind)

end Quiver.Path

namespace Quiver

/-! ### Acyclic quivers -/

variable (V : Type*) [Quiver V]

/-- A quiver is acyclic: the only closed path is trivial.

This matches directed acyclicity (no positive-length closed walk). It implies `¬IsCycle` but is
stronger than `∀ p, ¬p.IsCycle` (a positive loop may repeat vertices without being `IsCycle`). -/
def IsAcyclic : Prop :=
  ∀ {a : V} (p : Path a a), p.length = 0

variable {V}

lemma IsAcyclic.eq_nil (h : IsAcyclic V) {a : V} (p : Path a a) : p = Path.nil :=
  Path.eq_nil_of_length_zero p (h p)

lemma IsAcyclic.not_isCycle (h : IsAcyclic V) {a : V} (p : Path a a) : ¬p.IsCycle := by
  rintro ⟨hp, -⟩
  have := h p
  grind

end Quiver
