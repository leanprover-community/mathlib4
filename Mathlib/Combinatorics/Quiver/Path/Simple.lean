/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Cycle
public import Mathlib.Data.Fintype.Card

/-!
# Vertices visited by a path, and length bounds for simple paths

The vertices a path visits, as a `Set` and as a `Finset`, the decomposition of a positive-length
path at its first or last edge, and the bound `p.length ≤ card V - 1` for a path that repeats no
vertex: the material the Perron-Frobenius development needs about simple paths.

## Main definitions

* `Quiver.Path.activeVertices`, `Quiver.Path.vertexFinset`: the vertices a path visits.
* `Quiver.Path.activeFinset`: those vertices, excluding the endpoint.

## Main statements

* `Quiver.Path.path_decomposition_first_edge`, `Quiver.Path.path_decomposition_last_edge`: a path
  of positive length splits off its first, resp. last, edge.
* `Quiver.Path.isPath_of_shortest`: a shortest path repeats no vertex.
* `Quiver.Path.length_le_card_minus_one_of_isSimple`: the length bound for simple paths.

## Tags

quiver, path, simple path, Perron-Frobenius theorem
-/

@[expose] public section

open List Finset

namespace Quiver.Path

variable {V : Type*} [Quiver V]

/-- Every path of positive length decomposes as an initial path followed by a final edge. -/
lemma path_decomposition_last_edge {a b : V} (p : Path a b) (h : p.length > 0) :
    ∃ (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e := by
  cases p with | nil => simp at h | cons p' e => exact ⟨_, p', e, rfl⟩

/-- Every path of positive length decomposes as a first edge followed by the remaining path. -/
lemma path_decomposition_first_edge {a b : V} (p : Path a b) (h : p.length > 0) :
    ∃ (c : V) (e : a ⟶ c) (p' : Path c b),
      p = e.toPath.comp p' ∧ p.length = p'.length + 1 := by
  have h_len : p.length = (p.length - 1) + 1 := by omega
  obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p h_len
  exact ⟨c, e, p', rfl, by omega⟩

/-- The set of vertices in a path. -/
def activeVertices {a : V} : ∀ {b : V}, Path a b → Set V
  | _, nil => {a}
  | _, cons p e => activeVertices p ∪ {«end» (cons p e)}

@[simp] lemma activeVertices_nil {a : V} : activeVertices (nil : Path a a) = {a} := rfl
@[simp] lemma activeVertices_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  activeVertices (p.cons e) = activeVertices p ∪ {c} := by simp [activeVertices]

/-- The set of vertices in a path, excluding the final vertex. -/
def activeFinset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.dropLast.toFinset

/-- The finset of vertices in a path. -/
def vertexFinset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.toFinset

/-- A vertex is in `activeFinset p` iff it is in `p.vertices.dropLast`. -/
@[simp]
lemma mem_activeFinset_iff [DecidableEq V] {a b : V} (p : Path a b) {x : V} :
    x ∈ activeFinset p ↔ x ∈ p.vertices.dropLast := by
  simp only [activeFinset, List.mem_toFinset]

lemma mem_vertices_to_active {V : Type*} [Quiver V]
    {a b : V} {p : Path a b} {x : V} :
    x ∈ p.vertices → x ∈ p.activeVertices := by
  intro hx
  induction p with
  | nil => aesop
  | cons p' e ih =>
    rw [mem_vertices_cons] at hx
    cases hx with
    | inl hx_in => simp [activeVertices_cons, ih hx_in]
    | inr hx_eq => subst hx_eq; simp [activeVertices_cons]
/-- The set of vertices of a simple path has cardinality `p.length + 1`. -/
lemma card_vertexFinset_of_isPath [DecidableEq V] {a b : V} {p : Path a b}
    (hp : IsPath p) : p.vertexFinset.card = p.length + 1 := by
  simp [vertexFinset, List.toFinset_card_of_nodup hp, vertices_length]

/-- If a path is not strictly simple, then there exists a vertex that occurs at least twice. -/
lemma not_isPath_iff_exists_repeated_vertex [DecidableEq V] {a b : V} {p : Path a b} :
    ¬IsPath p ↔ ∃ v, v ∈ p.vertices ∧ p.vertices.count v ≥ 2 := by
  rw [IsPath, ← List.exists_duplicate_iff_not_nodup]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h
    have hv_count := (List.duplicate_iff_two_le_count).1 hv
    exact ⟨v, (List.count_pos_iff).1 (Nat.lt_of_lt_of_le (by decide) hv_count), hv_count⟩
  · intro ⟨v, _hv_mem, hv_count⟩
    exact ⟨v, (List.duplicate_iff_two_le_count).2 hv_count⟩

theorem isPath_of_shortest {a b : V} (p : Path a b)
    (h_min : ∀ q : Path a b, p.length ≤ q.length) :
    IsPath p := by
  classical
  by_contra h_dup
  obtain ⟨v, hv_in, hv_ge₂⟩ := not_isPath_iff_exists_repeated_vertex.mp h_dup
  obtain ⟨p₁, p₂, hp, hv_not_tail⟩ := p.exists_eq_comp_and_notMem_tail_of_mem_vertices hv_in
  have h_p2_count : p₂.vertices.count v = 1 := by
    cases hv : p₂.vertices with
    | nil => exact (vertices_ne_nil p₂ hv).elim
    | cons hd tl =>
      have h_eq : hd = v := Option.some_inj.mp (by simpa [hv] using vertices_head? p₂)
      rw [h_eq] at hv ⊢
      have h_tl : v ∉ tl := fun h_in ↦ hv_not_tail (by rw [hv]; exact h_in)
      simp [List.count_cons_self, List.count_eq_zero.mpr h_tl]
  have hv_in_p1 : v ∈ p₁.vertices.dropLast := by
    have h2 : 2 ≤ (p₁.vertices.dropLast ++ p₂.vertices).count v := by
      simpa [← vertices_comp, ← hp] using hv_ge₂
    rw [List.count_append, h_p2_count] at h2
    exact List.count_pos_iff.mp (by omega)
  have hv_mem_p1 := List.mem_of_mem_dropLast hv_in_p1
  obtain ⟨v', q, c, _, h_q_len, hv'_eq⟩ :=
    p₁.exists_eq_comp_and_length_eq_of_lt_length _ (List.idxOf_lt_length_of_mem hv_mem_p1)
  rcases hv'_eq.trans (List.getElem_idxOf (List.idxOf_lt_length_of_mem hv_mem_p1)) with rfl
  have h_shorter : (q.comp p₂).length < p.length := calc
    (q.comp p₂).length = q.length + p₂.length := length_comp q p₂
    _ < p₁.length + p₂.length := by
      apply Nat.add_lt_add_right
      rw [h_q_len, (IsPrefix.idxOf_eq_of_mem (dropLast_prefix p₁.vertices) hv_in_p1).symm]
      have h_lt := List.idxOf_lt_length_of_mem hv_in_p1
      revert h_lt
      simp [List.length_dropLast, vertices_length]
    _ = p.length := by rw [hp, length_comp]
  grind

/-- The length of a strictly simple path is at most one less than the number of vertices. -/
lemma length_le_card_minus_one_of_isSimple {n : Type*} [Fintype n] [Quiver n]
    {a b : n} (p : Path a b) (hp : p.IsPath) :
    p.length ≤ Fintype.card n - 1 := by
  classical
  have h_card_verts : p.vertexFinset.card = p.length + 1 := card_vertexFinset_of_isPath hp
  have h_card_le_univ : p.vertexFinset.card ≤ Fintype.card n := Finset.card_le_univ p.vertexFinset
  rw [h_card_verts] at h_card_le_univ
  exact Nat.le_sub_one_of_lt h_card_le_univ
end Quiver.Path
