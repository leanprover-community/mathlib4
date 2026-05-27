/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Duplicate
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Combinatorics.Quiver.Path.Weight
public import Mathlib.Combinatorics.Quiver.Path.Decomposition
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find

/-!
# Quiver paths for Perron–Frobenius

Path weights, decomposition, simplicity, cycles, and acyclicity lemmas for weighted quivers
arising from non-negative matrices.

## Main definitions

* `IsStrictlySimple`, `IsSimple`, `IsCycle`: simplicity predicates on paths.
* `IsAcyclic`: typeclass for quivers with no nontrivial loops.
* `replicate`, `activeVertices`, `weightFromVertices`: path utilities for weighted quivers.

## Main results

* Lemmas on path weights, cycle lengths, and connectivity used to prove irreducibility and
  primitivity facts for matrices.
* `IsAcyclic` is equivalent to having no simple cycles.

## Tags

quiver path, Perron–Frobenius theorem, irreducible matrix
-/

open List Finset

@[expose] public section

namespace Quiver.Path

variable {V : Type*} [Quiver V] {R : Type*}

section Weight

variable [Monoid R]

def weightFromVertices (w : V → V → R) : ∀ {i j : V}, Path i j → R :=
  weight (fun {i j} (_ : i ⟶ j) => w i j)

lemma weightFromVertices_comp (w : V → V → R) {a b c : V} (p : Path a b) (q : Path b c) :
    weightFromVertices w (p.comp q) = weightFromVertices w p * weightFromVertices w q := by
  simp only [weightFromVertices, weight_comp]

end Weight

section RealWeight

variable {w : V → V → ℝ} {i j : V} (p : Path i j)

lemma weightFromVertices_pos (hw : ∀ i j : V, 0 < w i j) : 0 < weightFromVertices w p := by
  apply weight_pos; intro i j _; exact hw i j

lemma weightFromVertices_nonneg (hw : ∀ i j : V, 0 ≤ w i j) : 0 ≤ weightFromVertices w p := by
  induction p using Path.rec with
  | nil => simp only [weightFromVertices, weight, zero_le_one]
  | cons p' e ih => simp only [weightFromVertices, weight]; exact mul_nonneg ih (hw _ _)

end RealWeight

section PathDecomposition

variable {V : Type*} [Quiver V] {a b : V} (p : Path a b)

/-- Every non-empty path can be decomposed as an initial path plus a final edge. -/
lemma path_decomposition_last_edge {a b : V} (p : Path a b) (h : p.length > 0) :
    ∃ (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e := by
  cases p with | nil => simp at h | cons p' e => exact ⟨_, p', e, rfl⟩

/-- Every non-empty path can be decomposed as a first edge plus a remaining path. -/
lemma path_decomposition_first_edge (h : p.length > 0) :
    ∃ (c : V) (e : a ⟶ c) (p' : Path c b),
      p = e.toPath.comp p' ∧ p.length = p'.length + 1 := by
  have h_len : p.length = (p.length - 1) + 1 := by omega
  obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p h_len
  use c, e, p'; exact ⟨rfl, by omega⟩

end PathDecomposition

section BoundaryEdges

variable {V : Type*} [Quiver V]

lemma cons_eq_comp_toPath {a b c : V} (p : Path a b) (e : b ⟶ c) :
    p.cons e = p.comp e.toPath := rfl

/-- A path from a vertex not in `S` to a vertex in `S` must cross the boundary. -/
theorem exists_boundary_edge {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ (u v : V) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      u ∉ S ∧ v ∈ S ∧ p = p₁.comp (e.toPath.comp p₂) := by
  obtain ⟨u, hu, v, hv, e, p₁, p₂, h⟩ :=
    exists_notMem_mem_hom_path_path_of_notMem_mem p S ha_not_in_S hb_in_S
  exact ⟨u, v, e, p₁, p₂, hu, hv, h⟩

/-- A path from a vertex in `S` to a vertex not in `S` must cross the boundary. -/
theorem exists_boundary_edge_from_set {a b : V} (p : Path a b) (S : Set V)
    (ha_in_S : a ∈ S) (hb_not_in_S : b ∉ S) :
    ∃ (u v : V) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      u ∈ S ∧ v ∉ S ∧ p = p₁.comp (e.toPath.comp p₂) := by
  obtain ⟨u, hu, v, hv, e, p₁, p₂, h⟩ :=
    exists_mem_notMem_hom_path_path_of_notMem_mem p S ha_in_S hb_not_in_S
  exact ⟨u, v, e, p₁, p₂, hu, hv, h⟩

/-- Alternative formulation: there exists an edge crossing the boundary. -/
theorem exists_crossing_edge {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ (u v : V) (_ : u ⟶ v), u ∉ S ∧ v ∈ S := by
  obtain ⟨u, v, e, _, _, hu_not_S, hv_S, _⟩ := exists_boundary_edge p S ha_not_in_S hb_in_S
  exact ⟨u, v, e, hu_not_S, hv_S⟩

end BoundaryEdges

/-- The set of vertices in a path. -/
def activeVertices {a : V} : ∀ {b : V}, Path a b → Set V
  | _, nil => {a}
  | _, cons p e => activeVertices p ∪ {«end» (cons p e)}

@[simp] lemma activeVertices_nil {a : V} : activeVertices (nil : Path a a) = {a} := rfl
@[simp] lemma activeVertices_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  activeVertices (p.cons e) = activeVertices p ∪ {c} := by simp [activeVertices]

lemma vertices_nonempty' {V : Type*} [Quiver V] {a b : V} (p : Path a b) :
    p.vertices.length > 0 :=
  length_vertices_pos p

/-- The set of vertices in a path, excluding the final vertex. -/
def activeFinset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.dropLast.toFinset

def activeVertices' {a : V} {b : V} (p : Path a b) : Set V :=
  {v | v ∈ p.vertices}

@[simp]
lemma mem_activeVertices {a b : V} (p : Path a b) (v : V) :
    v ∈ p.activeVertices' ↔ v ∈ p.vertices := by
  rfl

/-- The finset of vertices in a path. -/
def vertexFinset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.toFinset

/-- A vertex is in `activeFinset p` iff it is in `p.vertices.dropLast`. -/
@[simp]
lemma mem_activeFinset_iff [DecidableEq V] {a b : V} (p : Path a b) {x : V} :
    x ∈ activeFinset p ↔ x ∈ p.vertices.dropLast := by
  simp only [activeFinset, List.mem_toFinset]

lemma vertices_nonempty {a : V} {b : V} (p : Path a b) : p.vertices ≠ [] :=
  vertices_ne_nil p

/-- A path from a single arrow. -/
def List.toPath {a b : V} (e : a ⟶ b) : Path a b :=
  Path.nil.cons e

/-- From a path composition, the prefix path's vertices form a prefix of the full path's
vertices. -/
lemma isPrefix_dropLast_of_comp_eq {V : Type*} [Quiver V] {a b c : V}
    {p : Path a b} {p₁ : Path a c} {p₂ : Path c b}
    (h : p.vertices = p₁.vertices.dropLast ++ p₂.vertices) :
    p₁.vertices.dropLast.IsPrefix p.vertices := by
  rw [h]; exact List.prefix_append _ _

/-- The head of the vertices list is the start vertex. -/
@[simp]
lemma vertices_head_eq_start {a b : V} (p : Path a b) :
    p.vertices.head (vertices_nonempty p) = a :=
  vertices_head_eq p (vertices_nonempty p)

/-- The last element of the vertices list is the end vertex. -/
@[simp]
lemma vertices_getLast_eq_end {a b : V} (p : Path a b) :
    p.vertices.getLast (vertices_nonempty p) = b :=
  vertices_getLast p (vertices_nonempty p)

lemma end_prefix_eq_get_vertices {a b c : V} (p₁ : Path a c) (p₂ : Path c b) :
    c = (p₁.comp p₂).vertices.get ⟨p₁.length, by simp⟩ :=
  (vertices_comp_get_length_eq p₁ p₂).symm

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

end Quiver.Path

namespace Prefunctor

open Quiver

variable {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W)

@[simp]
lemma end_map {a b : V} (p : Path a b) : F.obj (p.end) = (F.mapPath p).end := by
  induction p with
  | nil => rfl
  | cons p' e ih => simp

end Prefunctor

open Quiver

namespace Quiver

/-- The quiver structure on a subtype is induced by the quiver structure on the original type. -/
@[reducible]
def inducedQuiver {V : Type*} [Quiver V] (S : Set V) : Quiver S :=
  ⟨fun a b => a.val ⟶ b.val⟩

end Quiver
namespace Quiver.Subquiver

variable {V : Type*} [Quiver V] (S : Set V)

attribute [local instance] inducedQuiver

/-- The embedding of an induced subquiver on a set `S` into the original quiver. -/
@[simps]
def embedding : Prefunctor S V where
  obj := Subtype.val
  map := id

/-- The vertices in a path mapped by the embedding are all in the original set S. -/
@[simp]
lemma mapPath_embedding_vertices_in_set {i j : S} (p : Path i j) :
  ∀ v, v ∈ ((embedding S).mapPath p).activeVertices → v ∈ S := by
  induction p with
  | nil =>
    intro v hv
    simp only [Prefunctor.mapPath_nil, Path.activeVertices_nil, Set.mem_singleton_iff] at hv
    subst hv
    exact i.property
  | cons p' e ih =>
    intro v hv
    simp only [Prefunctor.mapPath_cons, Path.activeVertices_cons, Set.mem_union,
               Set.mem_singleton_iff] at hv
    cases hv with
    | inl h => exact ih v h
    | inr h => subst h; simp_all only [embedding_obj, Subtype.coe_prop]

open Quiver.Path

/--
If a path in the original quiver only visits vertices in a set `S`, it can be lifted
to a path in the induced subquiver on `S`.
-/
def lift_path_to_induced {S : Set V} [DecidablePred (· ∈ S)]
    {i j : V} (p : Path i j) (hp : ∀ k, k ∈ p.vertices → k ∈ S) :
    letI : Quiver S := inducedQuiver S
    Path (⟨i, hp i (start_mem_vertices p)⟩ : S) (⟨j, hp j (end_mem_vertices p)⟩ : S) := by
  letI : Quiver S := inducedQuiver S
  induction p with
  | nil => exact Path.nil
  | cons p' e ih =>
    exact Path.cons (ih (fun k hk => hp k ((mem_vertices_cons p' e).mpr (Or.inl hk)))) e

end Quiver.Subquiver

namespace Quiver.Path
open Quiver
variable {V : Type*} [Quiver V]

/--
Construct a path by repeating a loop `n` times.
`replicate n p` is the path `p.comp(p.comp(...p))` where `p` is composed `n` times.
If `n=0`, it is the nil path.
-/
def replicate (n : ℕ) {a : V} (p : Path a a) : Path a a :=
  match n with
  | 0 => Path.nil
  | k + 1 => (replicate k p).comp p

@[simp]
lemma length_replicate (n : ℕ) {a : V} (p : Path a a) :
  (replicate n p).length = n * p.length := by
  induction n with
  | zero => simp only [replicate, length_nil, zero_mul]
  | succ k ih =>
    simp only [replicate, length_comp, ih, add_comm, Nat.succ_mul]

/-! ### Path splitting utilities -/

open List

/-- Given a path `p : Path a b` and an index `n ≤ p.length`,
    we can split `p = p₁.comp p₂` with `p₁.length = n`. -/
theorem exists_decomp_at_length {a b : V} (p : Path a b) {n : ℕ} (hn : n ≤ p.length) :
    ∃ (c : V) (p₁ : Path a c) (p₂ : Path c b), p = p₁.comp p₂ ∧ p₁.length = n :=
  p.exists_eq_comp_of_le_length hn

theorem exists_decomp_of_mem_vertices {a b v : V} (p : Path a b)
    (h : v ∈ p.vertices) : ∃ (p₁ : Path a v) (p₂ : Path v b), p = p₁.comp p₂ :=
  p.exists_eq_comp_of_mem_vertices h

theorem split_at_vertex {a b : V} (p : Path a b) (i : ℕ) (hi : i < p.vertices.length) :
    ∃ (v : V) (p₁ : Path a v) (p₂ : Path v b),
      p = p₁.comp p₂ ∧ p₁.length = i ∧ v = p.vertices.get ⟨i, hi⟩ :=
  p.exists_eq_comp_and_length_eq_of_lt_length i hi

open Quiver
variable {V : Type*} [Quiver V]

/-- A path does not repeat vertices (strict simplicity; a nontrivial cycle is not simple). -/
@[simp]
def IsStrictlySimple {a b : V} (p : Path a b) : Prop := p.vertices.Nodup

lemma isStrictlySimple_nil {a : V} : IsStrictlySimple (nil : Path a a) := by simp [IsStrictlySimple]

@[simp]
lemma isStrictlySimple_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  IsStrictlySimple (p.cons e) ↔ IsStrictlySimple p ∧ c ∉ p.vertices := by
  simp only [IsStrictlySimple, vertices_cons]
  rw [List.nodup_concat]; aesop

/-- The set of vertices of a simple path has cardinality `p.length + 1`. -/
lemma card_vertexFinset_of_isStrictlySimple [DecidableEq V] {a b : V} {p : Path a b}
    (hp : IsStrictlySimple p) : p.vertexFinset.card = p.length + 1 := by
  simp [vertexFinset, List.toFinset_card_of_nodup hp, vertices_length]

lemma length_lt_card_of_isStrictlySimple [DecidableEq V] [Fintype V] {a b : V} {p : Path a b}
    (hp : IsStrictlySimple p) :
  p.length < Fintype.card V := by
  simpa [card_vertexFinset_of_isStrictlySimple hp, Nat.succ_eq_add_one] using
    (Finset.card_le_univ p.vertexFinset)

/-- If a path is not strictly simple, then there exists a vertex that occurs at least twice. -/
lemma not_strictly_simple_iff_exists_repeated_vertex [DecidableEq V] {a b : V} {p : Path a b} :
    ¬IsStrictlySimple p ↔ ∃ v, v ∈ p.vertices ∧ p.vertices.count v ≥ 2 := by
  rw [IsStrictlySimple, ← List.exists_duplicate_iff_not_nodup]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h
    have hv_count := (List.duplicate_iff_two_le_count).1 hv
    exact ⟨v, (List.count_pos_iff).1 (Nat.lt_of_lt_of_le (by decide) hv_count), hv_count⟩
  · intro ⟨v, _hv_mem, hv_count⟩
    exact ⟨v, (List.duplicate_iff_two_le_count).2 hv_count⟩

/-- If we have a path p from a to b with c ∈ p.vertices,
    and c is not the end vertex b, then it appears in a proper prefix of the path. -/
lemma exists_prefix_with_vertex {a b c : V} (p : Path a b)
    (h : c ∈ p.vertices) (h_ne : c ≠ b) :
    ∃ (p₁ : Path a c) (p₂ : Path c b), p = p₁.comp p₂ := by
  classical
  obtain ⟨v, p₁, p₂, h_comp, _, hc⟩ := split_at_vertex p _ (List.idxOf_lt_length_of_mem h)
  rcases hc.trans (List.getElem_idxOf (List.idxOf_lt_length_of_mem h)) with rfl
  exact ⟨p₁, p₂, h_comp⟩

/-- Split a path at the **last** occurrence of a vertex. -/
theorem exists_decomp_of_mem_vertices_prop {a b x : V} (p : Path a b) (hx : x ∈ p.vertices) :
    ∃ (p₁ : Path a x) (p₂ : Path x b),
      p = p₁.comp p₂ ∧ x ∉ p₂.vertices.tail :=
  p.exists_eq_comp_and_notMem_tail_of_mem_vertices hx

theorem isStrictlySimple_of_shortest {a b : V} (p : Path a b)
    (h_min : ∀ q : Path a b, p.length ≤ q.length) :
    IsStrictlySimple p := by
  classical
  by_contra h_dup
  obtain ⟨v, hv_in, hv_ge₂⟩ := not_strictly_simple_iff_exists_repeated_vertex.mp h_dup
  obtain ⟨p₁, p₂, hp, hv_not_tail⟩ := exists_decomp_of_mem_vertices_prop p hv_in
  have h_p2_count : p₂.vertices.count v = 1 := by
    cases hv : p₂.vertices with
    | nil => exact (vertices_nonempty p₂ hv).elim
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
    split_at_vertex p₁ _ (List.idxOf_lt_length_of_mem hv_mem_p1)
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

/-- Removing a positive-length cycle from a path gives a strictly shorter path with the same
endpoints. -/
lemma remove_cycle_gives_shorter_path {a v b : V}
    {p_prefix : Path a v} {p_cycle : Path v v} {p_rest : Path v b}
    (h_cycle_pos : p_cycle.length > 0) :
    (p_prefix.comp p_rest).length < (p_prefix.comp (p_cycle.comp p_rest)).length := by
  simp only [length_comp]
  grind

open List

/-- If a vertex `c` appears in path `p`, it is the end vertex or appears in the tail of vertices. -/
lemma vertex_in_path_cases {a b c : V} (p : Path a b) (h : c ∈ p.vertices) :
    c = b ∨ c ∈ p.vertices.dropLast := by
  have h_dec := List.dropLast_append_getLast (vertices_nonempty p)
  rw [← h_dec, List.mem_append, List.mem_singleton] at h
  aesop

/-- The length of a strictly simple path is at most one less than the number of vertices. -/
lemma length_le_card_minus_one_of_isSimple {n : Type*} [DecidableEq n] [Fintype n] [Quiver n]
    {a b : n} (p : Path a b) (hp : p.IsStrictlySimple) :
    p.length ≤ Fintype.card n - 1 := by
  have h_card_verts : p.vertexFinset.card = p.length + 1 := card_vertexFinset_of_isStrictlySimple hp
  have h_card_le_univ : p.vertexFinset.card ≤ Fintype.card n := Finset.card_le_univ p.vertexFinset
  rw [h_card_verts] at h_card_le_univ
  exact Nat.le_sub_one_of_lt h_card_le_univ

/-! Cycles -/

/-- A path is simple if it does not visit any vertex more than once, with the possible
exception of the final vertex, which may be the same as the start vertex in a cycle. -/
def IsSimple {a b : V} (p : Path a b) : Prop :=
  p.vertices.dropLast.Nodup

/-- A cycle is a non-trivial path from a vertex back to itself that does not repeat vertices,
except for the start/end vertex. -/
@[nolint unusedArguments]
def IsCycle {a : V} (p : Path a a) : Prop :=
  p.length > 0 ∧ IsSimple p

lemma isSimple_of_isStrictlySimple {a b : V} {p : Path a b} (h : IsStrictlySimple p) :
    IsSimple p := by
  unfold IsSimple IsStrictlySimple at *
  simpa using h.sublist (List.dropLast_sublist (l := p.vertices))

lemma not_isStrictlySimple_of_not_isSimple {a b : V} {p : Path a b} (h : ¬IsSimple p) :
    ¬IsStrictlySimple p := by
  intro h_strict
  exact h (isSimple_of_isStrictlySimple h_strict)

section Acyclic

variable {V : Type*} [Quiver V]

/-- A quiver is acyclic if there are no non-trivial paths from a vertex to itself. -/
class IsAcyclic (V : Type*) [Quiver V] : Prop where
  /-- Any path from a vertex to itself must have length zero. -/
  acyclic : ∀ (a : V) (p : Path a a), p.length = 0

lemma IsAcyclic.path_eq_nil {V : Type*} [Quiver V] [IsAcyclic V] {a : V} (p : Path a a) :
    p = Path.nil :=
  Path.eq_nil_of_length_zero p (IsAcyclic.acyclic a p)

lemma isAcyclic_iff_length_eq_zero :
    IsAcyclic V ↔ ∀ {a : V} (p : Path a a), p.length = 0 := by
  constructor
  · intro h; exact fun {a} p ↦ IsAcyclic.acyclic a p
  · intro h; exact { acyclic := fun a p ↦ h p }

/-- If a quiver is acyclic, then it contains no simple cycles. -/
lemma isAcyclic_of_no_cycles :
    IsAcyclic V → ∀ {a : V} (p : Path a a), ¬IsCycle p := by
  intro h_acyclic a p h_cycle
  have h_pos : p.length > 0 := h_cycle.1
  have h_zero : p.length = 0 := IsAcyclic.acyclic a p
  exact (Nat.not_lt.mpr (le_of_eq h_zero)) h_pos

/-- Given a path with a repeated vertex, extract it from the prefix `dropLast`. -/
lemma repeated_vertex_in_prefix_dropLast [DecidableEq V] {a : V} (s : Path a a)
    (h_not_simple : ¬IsStrictlySimple s) :
    ∃ (v : V) (p₁ : Path a v) (p₂ : Path v a),
      v ∈ p₁.vertices.dropLast ∧ s = p₁.comp p₂ ∧ v ∉ p₂.vertices.tail := by
  obtain ⟨v, hv_in, hv_ge₂⟩ := not_strictly_simple_iff_exists_repeated_vertex.mp h_not_simple
  obtain ⟨p₁, p₂, hp, hv_not_tail⟩ := exists_decomp_of_mem_vertices_prop s hv_in
  have h_p2_count : p₂.vertices.count v = 1 := by
    cases hv : p₂.vertices with
    | nil => exact (vertices_nonempty p₂ hv).elim
    | cons hd tl =>
      have h_hd : hd = v := Option.some_inj.mp (by simpa [hv] using vertices_head? p₂)
      rw [h_hd] at hv ⊢
      have h_tl : v ∉ tl := fun h_in ↦ hv_not_tail (by rw [hv]; exact h_in)
      simp [List.count_cons_self, List.count_eq_zero.mpr h_tl]
  have hv_in_p1 : v ∈ p₁.vertices.dropLast := by
    have h_count : s.vertices.count v = (p₁.vertices.dropLast ++ p₂.vertices).count v := by
      rw [hp, vertices_comp]
    rw [h_count, List.count_append, h_p2_count] at hv_ge₂
    exact List.count_pos_iff.mp (by omega)
  exact ⟨v, p₁, p₂, hv_in_p1, hp, hv_not_tail⟩

lemma extract_cycle_from_prefix [DecidableEq V] {a vertex : V} {p₁ : Path a vertex}
    (h_in_drop : vertex ∈ p₁.vertices.dropLast) :
    ∃ (q : Path a vertex) (c : Path vertex vertex),
      p₁ = q.comp c ∧ vertex ∉ q.vertices.dropLast := by
  let i := p₁.vertices.idxOf vertex
  have h_mem := List.mem_of_mem_dropLast h_in_drop
  obtain ⟨v, q, c, h_comp, h_len, h_v⟩ :=
    split_at_vertex p₁ i (List.idxOf_lt_length_of_mem h_mem)
  rcases h_v.trans (List.getElem_idxOf (List.idxOf_lt_length_of_mem h_mem)) with rfl
  refine ⟨q, c, h_comp, fun h ↦ ?_⟩
  have h_pre : q.vertices.dropLast <+: p₁.vertices := by
    rw [h_comp, vertices_comp]
    grind
  have h_idx := (IsPrefix.idxOf_eq_of_mem h_pre h).symm
  have h_lt := List.idxOf_lt_length_of_mem h
  rw [← h_idx, List.length_dropLast, vertices_length] at h_lt
  grind

/-- A cycle extracted from a path with a repeated vertex has positive length. -/
lemma extracted_cycle_has_positive_length {a v : V}
    {p₁ q : Path a v} {c : Path v v}
    (h_p1_split : p₁ = q.comp c)
    (hv_in_p1_dropLast : v ∈ p₁.vertices.dropLast)
    (hv_not_in_q : v ∉ q.vertices.dropLast) : c.length > 0 := by
  by_cases h_len_zero : c.length = 0
  · have hc_nil : c = Path.nil := (length_eq_zero_iff c).mp h_len_zero
    have h_p1_eq_q : p₁ = q := by
      rw [h_p1_split, hc_nil, comp_nil]
    have h_v_in_q : v ∈ q.vertices.dropLast := by
      subst h_p1_eq_q
      exact hv_in_p1_dropLast
    exact False.elim (hv_not_in_q h_v_in_q)
  · exact Nat.pos_of_ne_zero h_len_zero

/-- Removing a cycle from a path creates a strictly shorter path. -/
lemma removing_cycle_gives_shorter_path {a v : V} {s : Path a a}
    {q : Path a v} {c : Path v v} {p₂ : Path v a}
    (hp : s = (q.comp c).comp p₂) (hc_pos : c.length > 0) : (q.comp p₂).length < s.length := by
  rw [hp, comp_assoc]
  simp only [length_comp]
  grind

/-- A shortest positive loop is simple. -/
theorem shortest_positive_loop_is_simple [DecidableEq V] {a : V} {c : Path a a}
    (hc_pos : c.length > 0)
    (hc_min : ∀ p' : Path a a, p'.length > 0 → c.length ≤ p'.length) :
    c.IsSimple := by
  classical
  by_contra h_not_simple
  have h_not_strict : ¬IsStrictlySimple c := not_isStrictlySimple_of_not_isSimple h_not_simple
  obtain ⟨v, p₁, p₂, hv_in_drop, hp_split, hv_not_tail⟩ :=
    repeated_vertex_in_prefix_dropLast c h_not_strict
  obtain ⟨q, c_cycle, hp₁_split, hv_not_in_q⟩ := extract_cycle_from_prefix hv_in_drop
  have hc_cycle_pos : c_cycle.length > 0 :=
    extracted_cycle_has_positive_length hp₁_split hv_in_drop hv_not_in_q
  have hp_comp : c = (q.comp c_cycle).comp p₂ := by
    rw [hp_split, hp₁_split, comp_assoc]
  have h_shorter : (q.comp p₂).length < c.length :=
    removing_cycle_gives_shorter_path hp_comp hc_cycle_pos
  have hq_pos : (q.comp p₂).length > 0 := by
    by_contra hq_zero
    have hq_eq : (q.comp p₂).length = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt hq_zero)
    have hlen : q.length + p₂.length = 0 := by rw [← length_comp, hq_eq]
    have hq_len : q.length = 0 := (Nat.add_eq_zero_iff.mp hlen).1
    have hp₂_len : p₂.length = 0 := (Nat.add_eq_zero_iff.mp hlen).2
    cases q with
    | nil =>
      cases p₂ with
      | nil =>
        have hc_eq : c = c_cycle := by simpa [comp_nil] using hp_comp
        have h_not_simple' : ¬IsSimple c_cycle := hc_eq ▸ h_not_simple
        have h_dup : ∃ x, 2 ≤ (c_cycle.vertices.dropLast).count x := by
          obtain ⟨x, hx⟩ :=
            (List.exists_duplicate_iff_not_nodup (l := c_cycle.vertices.dropLast)).mpr
              (by simpa [IsSimple] using h_not_simple')
          exact ⟨x, (List.duplicate_iff_two_le_count).mp hx⟩
        obtain ⟨xdup, hx_count⟩ := h_dup
        obtain ⟨i, hi_lt, hi_pos, hi_pred, hi_get⟩ :=
          List.exists_pos_get_of_dropLast_count_ge_two hx_count
        by_cases hx : xdup = a
        · obtain ⟨w, p_short, _p_rest, _h_split, h_len, hw_eq⟩ :=
            split_at_vertex c_cycle i hi_lt
          have ha_eq : w = a := hw_eq.trans (hi_get.trans hx)
          subst ha_eq
          have h_short_pos : p_short.length > 0 := by rw [h_len]; exact hi_pos
          have h_short_lt : p_short.length < c.length := by
            rw [h_len, hc_eq]
            have := vertices_length c_cycle
            omega
          exact (lt_irrefl _ (lt_of_le_of_lt (hc_min p_short h_short_pos) h_short_lt)).elim
        · have hx_in_drop : xdup ∈ c_cycle.vertices.dropLast :=
            List.count_pos_iff.mp (Nat.lt_of_lt_of_le (by decide : 0 < 2) hx_count)
          obtain ⟨p₁x, p₂x, hcompx, hx_not_tail⟩ :=
            exists_decomp_of_mem_vertices_prop c_cycle (List.mem_of_mem_dropLast hx_in_drop)
          have h_p2_count : p₂x.vertices.count xdup = 1 := by
            cases hv : p₂x.vertices with
            | nil => exact (vertices_nonempty p₂x hv).elim
            | cons hd tl =>
              have h_hd : hd = xdup := Option.some_inj.mp (by simpa [hv] using vertices_head? p₂x)
              rw [h_hd] at hv ⊢
              have h_tl : xdup ∉ tl := fun h_in =>
                hx_not_tail (by rw [hv, List.tail_cons]; exact h_in)
              simp [List.count_cons_self, List.count_eq_zero.mpr h_tl]
          have hx_in_p1 : xdup ∈ p₁x.vertices.dropLast := by
            have hvert : c_cycle.vertices = c_cycle.vertices.dropLast ++ [a] := by
              cases c_cycle with
              | nil => simp at hc_cycle_pos
              | cons p e => simp [vertices_cons, List.concat_eq_append]
            have h_full : 2 ≤ c_cycle.vertices.count xdup := by
              rw [hvert, List.count_append, List.count_singleton]
              have hxa : (a == xdup) = false := beq_eq_false_iff_ne.mpr (Ne.symm hx)
              simp only [hxa]
              exact hx_count
            have hcount : 1 ≤ (p₁x.vertices.dropLast).count xdup := by
              have h_eq : c_cycle.vertices.count xdup =
                  (p₁x.vertices.dropLast ++ p₂x.vertices).count xdup := by
                rw [hcompx, vertices_comp]
              rw [h_eq, List.count_append, h_p2_count] at h_full
              omega
            exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le (by decide : 0 < 1) hcount)
          obtain ⟨q_x, c_x, hsplit1, hx_not⟩ :=
            extract_cycle_from_prefix (p₁ := p₁x) hx_in_p1
          have hc_x_pos : c_x.length > 0 :=
            extracted_cycle_has_positive_length hsplit1 hx_in_p1 hx_not
          have hcomp' : c_cycle = (q_x.comp c_x).comp p₂x := by
            rw [hcompx, hsplit1, comp_assoc]
          have h_shorter_x : (q_x.comp p₂x).length < c.length := by
            rw [hc_eq]
            exact removing_cycle_gives_shorter_path hcomp' hc_x_pos
          have hq_x_pos : (q_x.comp p₂x).length > 0 := by
            by_contra hzero
            have hlen' : q_x.length + p₂x.length = 0 := by
              rw [← length_comp, Nat.eq_zero_of_le_zero (le_of_not_gt hzero)]
            cases q_x with
            | nil =>
              cases p₂x with
              | nil =>
                exact absurd rfl hx
              | cons _ _ => simp [length_cons] at hlen'
            | cons _ _ => simp [length_cons] at hlen'
          exact (lt_irrefl _ (lt_of_le_of_lt (hc_min _ hq_x_pos) h_shorter_x)).elim
      | cons _ _ => simp [length_cons] at hp₂_len
    | cons _ _ => simp [length_cons] at hq_len
  exact (lt_irrefl _ (lt_of_le_of_lt (hc_min _ hq_pos) h_shorter)).elim

end Acyclic

end Quiver.Path
