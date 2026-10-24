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

Parallel to `SimpleGraph.Walk` in `Mathlib/Combinatorics/SimpleGraph/Paths.lean`. Since
`Quiver.Path` plays the role of `SimpleGraph.Walk`, a path with no repeated vertex is called
simple (`IsSimple`, cf. `SimpleGraph.Walk.IsPath`). `IsCycle` is a nontrivial closed path that
repeats no vertex except its start (cf. `SimpleGraph.Walk.IsCycle`).

`Quiver.IsAcyclic` (below) means no nontrivial closed paths. It implies `¬IsCycle` but is
strictly stronger than forbidding simple cycles only.

`Quiver.cycleLengths` (in `Mathlib/Combinatorics/Quiver/Cyclic.lean`) records lengths of positive
loops without a simplicity hypothesis.

For cardinality bounds, use `p.vertices.toFinset` (see `List.toFinset_card_of_nodup`).

## Main statements

* `Quiver.Path.exists_length_add_eq_of_getElem_eq`: a path that visits the same vertex twice can
  be shortened by excising the loop in between. Both shortening results below come from it.
* `Quiver.Path.IsCycle.of_minimal_length`: a shortest nontrivial loop is a cycle.
-/

@[expose] public section

namespace Quiver.Path

open List

variable {V : Type*} [Quiver V]

/-- A path with no repeated vertices (cf. `SimpleGraph.Walk.IsPath`). -/
structure IsSimple {a b : V} (p : Path a b) : Prop where
  vertices_nodup : p.vertices.Nodup

/-- A cycle: a nontrivial closed path with no repeated vertices except its start
(cf. `SimpleGraph.Walk.IsCycle`). -/
structure IsCycle {a : V} (p : Path a a) : Prop where
  length_ne_zero : p.length ≠ 0
  vertices_dropLast_nodup : p.vertices.dropLast.Nodup

lemma isSimple_def {a b : V} (p : Path a b) : p.IsSimple ↔ p.vertices.Nodup :=
  ⟨IsSimple.vertices_nodup, IsSimple.mk⟩

lemma isCycle_def {a : V} (p : Path a a) :
    p.IsCycle ↔ p.length ≠ 0 ∧ p.vertices.dropLast.Nodup :=
  ⟨fun h ↦ ⟨h.length_ne_zero, h.vertices_dropLast_nodup⟩, fun h ↦ ⟨h.1, h.2⟩⟩

theorem IsSimple.nil (a : V) : IsSimple (nil : Path a a) :=
  ⟨by simp⟩

@[simp] lemma isSimple_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    IsSimple (p.cons e) ↔ IsSimple p ∧ c ∉ p.vertices := by
  simp only [isSimple_def, vertices_cons]
  rw [nodup_concat]; aesop

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
lemma exists_length_lt_of_not_isSimple {a b : V} {p : Path a b} (h : ¬ p.IsSimple) :
    ∃ q : Path a b, q.length < p.length := by
  rw [isSimple_def] at h
  obtain ⟨x, hx⟩ := exists_duplicate_iff_not_nodup.2 h
  obtain ⟨n, m, hnm, hn, hm⟩ := duplicate_iff_exists_distinct_get.1 hx
  obtain ⟨q, hq⟩ := p.exists_length_add_eq_of_getElem_eq hnm m.isLt
    (by simpa [get_eq_getElem] using hn.symm.trans hm)
  exact ⟨q, by grind⟩

/-- A nontrivial loop that is not a cycle is not the shortest nontrivial loop: excising the
repeated vertex leaves a strictly shorter loop that is still nontrivial. -/
lemma exists_length_lt_of_not_isCycle {a : V} {c : Path a a} (h₀ : c.length ≠ 0)
    (h : ¬ c.IsCycle) : ∃ q : Path a a, q.length ≠ 0 ∧ q.length < c.length := by
  have h : ¬ c.vertices.dropLast.Nodup := fun hc ↦ h ⟨h₀, hc⟩
  obtain ⟨x, hx⟩ := exists_duplicate_iff_not_nodup.2 h
  obtain ⟨n, m, hnm, hn, hm⟩ := duplicate_iff_exists_distinct_get.1 hx
  have hlen : c.vertices.dropLast.length = c.length := by
    simp [length_dropLast, vertices_length]
  have hmc : (m : ℕ) < c.length := by have := m.isLt; grind
  obtain ⟨q, hq⟩ := c.exists_length_add_eq_of_getElem_eq hnm (by rw [vertices_length]; grind)
    (by simpa [get_eq_getElem, getElem_dropLast] using hn.symm.trans hm)
  exact ⟨q, by grind, by grind⟩

/-- A shortest nontrivial loop is a cycle. -/
theorem IsCycle.of_minimal_length {a : V} {c : Path a a} (h₀ : c.length ≠ 0)
    (hc : ∀ p : Path a a, p.length ≠ 0 → c.length ≤ p.length) : c.IsCycle := by
  by_contra h
  obtain ⟨q, hq₀, hq_lt⟩ := exists_length_lt_of_not_isCycle h₀ h
  exact absurd (hc q hq₀) (by grind)

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

lemma IsAcyclic.not_isCycle (h : IsAcyclic V) {a : V} (p : Path a a) : ¬p.IsCycle :=
  fun hp ↦ hp.length_ne_zero (h p)

end Quiver
