import Mathlib.Data.Set.Basic


variable {α β : Type*} {x y z u v w : α} {e f : β}

open Set

/-- A multigraph with vertex set `V : Set α` and edge set `E : Set β`,
as described by a predicate describing whether an edge `e : β` has ends `x` and `y`. -/
structure Graph (α β : Type*) where
  /-- The vertex set. -/
  V : Set α
  /-- The edge set. -/
  E : Set β
  /-- The predicate that an edge `e` goes from `x` to `y`. -/
  Inc₂ : β → α → α → Prop
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  inc₂_symm : ∀ ⦃e x y⦄, Inc₂ e x y → Inc₂ e y x
  /-- An edge is incident with at most one pair of vertices. -/
  eq_or_eq_of_inc₂_of_inc₂ : ∀ ⦃e x y v w⦄, Inc₂ e x y → Inc₂ e v w → x = v ∨ x = w
  /-- If `e` is incident to something, then `e` is in the edge set -/
  edge_mem_iff_exists_inc₂ : ∀ e, e ∈ E ↔ ∃ x y, Inc₂ e x y
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  vx_mem_left_of_inc₂ : ∀ ⦃e x y⦄, Inc₂ e x y → x ∈ V

namespace Graph

variable {G H : Graph α β}

lemma Inc₂.symm (h : G.Inc₂ e x y) : G.Inc₂ e y x :=
  G.inc₂_symm h

lemma inc₂_comm : G.Inc₂ e x y ↔ G.Inc₂ e y x :=
  ⟨Inc₂.symm, Inc₂.symm⟩

lemma Inc₂.edge_mem (h : G.Inc₂ e x y) : e ∈ G.E :=
  (edge_mem_iff_exists_inc₂ ..).2 ⟨x, y, h⟩

lemma Inc₂.vx_mem_left (h : G.Inc₂ e x y) : x ∈ G.V :=
  G.vx_mem_left_of_inc₂ h

lemma Inc₂.vx_mem_right (h : G.Inc₂ e x y) : y ∈ G.V :=
  h.symm.vx_mem_left

lemma exists_inc₂_of_edge_mem (h : e ∈ G.E) : ∃ x y, G.Inc₂ e x y :=
  (edge_mem_iff_exists_inc₂ ..).1 h

lemma Inc₂.left_eq_or_eq_of_inc₂ (h : G.Inc₂ e x y) (h' : G.Inc₂ e z w) : x = z ∨ x = w :=
  G.eq_or_eq_of_inc₂_of_inc₂ h h'

lemma Inc₂.left_eq_of_inc₂_of_ne (h : G.Inc₂ e x y) (h' : G.Inc₂ e z w) (hzx : x ≠ z) : x = w :=
  (h.left_eq_or_eq_of_inc₂ h').elim (False.elim ∘ hzx) id

/-- `Inc e x` means that `x` is one of the ends of `e`. -/
def Inc (G : Graph α β) (e : β) (x : α) : Prop := ∃ y, G.Inc₂ e x y

@[simp]
lemma Inc₂.inc_left (h : G.Inc₂ e x y) : G.Inc e x :=
  ⟨y, h⟩

@[simp]
lemma Inc₂.inc_right (h : G.Inc₂ e x y) : G.Inc e y :=
  ⟨x, h.symm⟩

lemma Inc.eq_or_eq_of_inc₂ (h : G.Inc e x) (h' : G.Inc₂ e y z) : x = y ∨ x = z :=
  h.choose_spec.left_eq_or_eq_of_inc₂ h'

lemma Inc.eq_of_inc₂_of_ne_left (h : G.Inc e x) (h' : G.Inc₂ e y z) (hxy : x ≠ y) : x = z :=
  (h.eq_or_eq_of_inc₂ h').elim (False.elim ∘ hxy) id

lemma eq_or_eq_or_eq_of_inc_of_inc_of_inc (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ x = z ∨ y = z := by
  by_contra! hcon
  obtain ⟨x', hx'⟩ := hx
  obtain rfl := hy.eq_of_inc₂_of_ne_left hx' hcon.1.symm
  obtain rfl := hz.eq_of_inc₂_of_ne_left hx' hcon.2.1.symm
  exact hcon.2.2 rfl

/-- `G.IsLoopAt e x` means that `e` is a loop edge at the vertex `x`. -/
def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.Inc₂ e x x

lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
  obtain rfl | rfl := h'.eq_or_eq_of_inc₂ h <;> rfl

@[mk_iff]
structure IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop where
  inc : G.Inc e x
  exists_inc₂_ne : ∃ y ≠ x, G.Inc₂ e x y

lemma IsLoopAt.not_isNonloop_at (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  intro h'
  obtain ⟨z, hyz, hy⟩ := h'.exists_inc₂_ne
  rw [← h.eq_of_inc hy.inc_left, ← h.eq_of_inc hy.inc_right] at hyz
  exact hyz rfl

lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e x) (y : α) : ¬ G.IsLoopAt e y :=
  fun h' ↦ h'.not_isNonloop_at x h

lemm


/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
def edgeRestrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  V := G.V
  E := E₀ ∩ G.E
  Inc₂ e x y := e ∈ E₀ ∧ G.Inc₂ e x y
  inc₂_symm e x y h := by rwa [G.inc₂_comm]
  eq_or_eq_of_inc₂_of_inc₂ _ _ _ _ _ h h' := h.2.left_eq_or_eq_of_inc₂ h'.2
  edge_mem_iff_exists_inc₂ e :=
    ⟨fun h ↦ by simp [h, G.exists_inc₂_of_edge_mem h.2, h.1], fun ⟨x, y, h⟩ ↦ ⟨h.1, h.2.edge_mem⟩⟩
  vx_mem_left_of_inc₂ _ _ _ h := h.2.vx_mem_left

/-- Map `G : Graph α β` to a `Graph α' β` with the same edge set
by applying a function `f : α → α'` to each vertex.
Edges between identified vertices become loops. -/
def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β where
  V := f '' G.V
  E := G.E
  Inc₂ e x' y' := ∃ x y, G.Inc₂ e x y ∧ x' = f x ∧ y' = f y
  inc₂_symm := by
    rintro e - - ⟨x, y, h, rfl, rfl⟩
    exact ⟨y, x, h.symm, rfl, rfl⟩
  eq_or_eq_of_inc₂_of_inc₂ := by
    rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
    obtain rfl | rfl := hxy.left_eq_or_eq_of_inc₂ hzw <;> simp
  edge_mem_iff_exists_inc₂ e := by
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨x, y, hxy⟩ := exists_inc₂_of_edge_mem h
      exact ⟨_, _, _, _, hxy, rfl, rfl⟩
    rintro ⟨-, -, x, y, h, rfl, rfl⟩
    exact h.edge_mem
  vx_mem_left_of_inc₂ := by
    rintro e - - ⟨x, y, h, rfl, rfl⟩
    exact mem_image_of_mem _ h.vx_mem_left

end Graph
